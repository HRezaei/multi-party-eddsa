#![allow(non_snake_case)]
/// to run:
/// 1: go to rocket_server -> cargo run
/// 2: cargo run from PARTIES number of terminals
use curv::{arithmetic::traits::Converter, cryptographic_primitives::{
    proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
}, elliptic::curves::ed25519::{FE, GE}, elliptic::curves::{ECPoint, ECScalar}, BigInt, HashChoice};
use multi_party_eddsa::protocols::thresholdsig::{KeyGenBroadcastMessage1, KeyGenDecommitMessage1, Keys, Parameters, SharedKeys};
use reqwest::Client;
use std::{env, fs, time};
use curv::cryptographic_primitives::secret_sharing::feldman_vss::SecretShares;
use curv::elliptic::curves::{Curve, Ed25519, Point, Scalar};
use curv::elliptic::curves::ed25519::Ed25519Scalar;
use sha2::{Sha256, Sha512};

mod common;
use common::{
    aes_decrypt, aes_encrypt, Params,
    PartySignup, AEAD, AES_KEY_BYTES_LEN, PartyClient, ClientPurpose
};
use multi_party_eddsa::Error;
use multi_party_eddsa::Error::InvalidKey;

struct Round1Result {
    party_keys: Keys,
    bc1_vec: Vec<KeyGenBroadcastMessage1>,
    decommit_i: KeyGenDecommitMessage1
}

#[derive(Clone, Debug)]
struct Round2Result {
    public_key: Point<Ed25519>,
    vss_scheme: VerifiableSS<Ed25519>,
    secret_shares: SecretShares<Ed25519>,
    enc_keys: Vec<Vec<u8>>,
    point_vec: Vec<Point<Ed25519>>
}

fn main() {
    if env::args().nth(3).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(2).is_none() {
        panic!("too few arguments")
    }
    //read parameters:
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();

    run_keygen(params);
}

pub fn run_keygen(params: Params) {
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
    let THRESHOLD: u16 = params.threshold.parse::<u16>().unwrap();

    let address = env::args()
        .nth(1)
        .unwrap_or_else(|| "http://127.0.0.1:8001".to_string());

    // delay:
    let delay = time::Duration::from_millis(25);

    let client = PartyClient::new(
        ClientPurpose::Keygen,
        Ed25519::CURVE_NAME,
        address,
        delay,
        params
    );

    let party_num_int = client.party_number;

    let params = Parameters {
        threshold: THRESHOLD,
        share_count: PARTIES,
    };

    let round1_result = run_round1(&client, PARTIES);

    // send ephemeral public keys and check commitments correctness
    let round2_result = run_round2(
        &client,
        &round1_result,
        PARTIES,
        &params
    );

    //////////////////////////////////////////////////////////////////////////////
    let party_shares = run_round3(
        &client,
        PARTIES,
        &round2_result
    );

    // round 4: send vss commitments
    let (shared_keys,
        vss_scheme_vec,
        dlog_proof) = run_round4(
        &client,
        PARTIES,
        &round2_result,
        &round1_result.party_keys,
        party_shares,
        &params
    );

    // round 5: send dlog proof
    run_round5(client, PARTIES, dlog_proof, params, round2_result.point_vec.clone());

    /*let paillier_key_vec = (0..PARTIES)
        .map(|i| bc1_vec[i as usize].e.clone())
        .collect::<Vec<EncryptionKey>>();

     */

    //save key to file:
    let keygen_json = serde_json::to_string(&(
        round1_result.party_keys,
        shared_keys,
        party_num_int,
        vss_scheme_vec,
        //paillier_key_vec,
        round2_result.public_key,
    ))
    .unwrap();
    fs::write(env::args().nth(2).unwrap(), keygen_json).expect("Unable to save !");
}



pub fn verify_dlog_proofs(
    params: &Parameters,
    dlog_proofs_vec: &[DLogProof<Ed25519, Sha512>],
    y_vec: &[Point<Ed25519>],
) -> Result<(), Error> {
    assert_eq!(y_vec.len(), usize::from(params.share_count));
    assert_eq!(dlog_proofs_vec.len(), usize::from(params.share_count));

    let xi_dlog_verify =
        (0..y_vec.len()).all(|i| DLogProof::verify(&dlog_proofs_vec[i]).is_ok());

    if xi_dlog_verify {
        Ok(())
    } else {
        Err(InvalidKey)
    }
}


fn run_round1(client: &PartyClient, PARTIES: u16) -> Round1Result {
    let party_keys = Keys::phase1_create(client.party_number);
    let (bc_i, decommit_i) = party_keys.phase1_broadcast();

    // send commitment to ephemeral public keys, get round 1 commitments of other parties
    assert!(client.broadcast(
        "round1",
        serde_json::to_string(&bc_i).unwrap(),
    )
        .is_ok());
    let round1_ans_vec = client.poll_for_broadcasts(
        PARTIES,
        "round1",
    );

    let mut bc1_vec = round1_ans_vec
        .iter()
        .map(|m| serde_json::from_str::<KeyGenBroadcastMessage1>(m).unwrap())
        .collect::<Vec<_>>();

    bc1_vec.insert(client.party_number as usize - 1, bc_i);

    Round1Result {
        party_keys,
        bc1_vec,
        decommit_i
    }
}

fn run_round2(
    client: &PartyClient,
    round1_result: &Round1Result,
    PARTIES: u16,
    params: &Parameters
) -> Round2Result
{
    let decommit_i = round1_result.decommit_i.clone();

    assert!(client.broadcast(
        "round2",
        serde_json::to_string(&decommit_i).unwrap(),
    )
        .is_ok());
    let round2_ans_vec = client.poll_for_broadcasts(
        PARTIES,
        "round2",
    );

    let mut j = 0;
    let mut point_vec: Vec<Point<Ed25519>> = Vec::new();
    let mut blind_vec: Vec<BigInt> = Vec::new();
    let mut enc_keys: Vec<Vec<u8>> = Vec::new();

    for i in 1..=PARTIES {
        if i == client.party_number {
            point_vec.push(decommit_i.clone().y_i);
            blind_vec.push(decommit_i.clone().blind_factor);
        } else {
            let decom_j: KeyGenDecommitMessage1 = serde_json::from_str::<KeyGenDecommitMessage1>(&round2_ans_vec[j]).unwrap();

            let this_party_private_key = round1_result.party_keys.keypair.expended_private_key.private_key.clone();
            point_vec.push(decom_j.clone().y_i);
            blind_vec.push(decom_j.clone().blind_factor);
            let key_bn: BigInt = (decom_j.clone().y_i * this_party_private_key).x_coord().unwrap();
            let key_bytes = BigInt::to_bytes(&key_bn);
            let mut template: Vec<u8> = vec![0u8; AES_KEY_BYTES_LEN - key_bytes.len()];
            template.extend_from_slice(&key_bytes[..]);
            enc_keys.push(template);
            j = j + 1;
        }
    }

    let (head, tail) = point_vec.split_at(1);
    let public_key = tail.iter().fold(head[0].clone(), |acc, x| acc + x);

    let key_gen_parties_points_vec = (0..PARTIES)
        .map(|i| i + 1)
        .collect::<Vec<u16>>();

    let (vss_scheme, secret_shares) = round1_result.party_keys
        .phase1_verify_com_phase2_distribute(
            &params, &blind_vec, &point_vec, &round1_result.bc1_vec, &key_gen_parties_points_vec
        )
        .expect("invalid key");

    Round2Result {
        public_key,
        vss_scheme,
        secret_shares,
        enc_keys,
        point_vec
    }
}

fn run_round3(client: &PartyClient, PARTIES: u16, round2_result: &Round2Result) -> Vec<Scalar<Ed25519>> {
    let mut j = 0;
    for (k, i) in (1..=PARTIES).enumerate() {
        if i != client.party_number {
            // prepare encrypted ss for party i:
            let key_i = &round2_result.enc_keys[j];
            let plaintext = BigInt::to_bytes(&round2_result.secret_shares[k].to_bigint());
            let aead_pack_i = aes_encrypt(key_i, &plaintext);
            assert!(client.sendp2p(
                i,
                "round3",
                serde_json::to_string(&aead_pack_i).unwrap(),
            )
                .is_ok());
            j += 1;
        }
    }

    let round3_ans_vec = client.poll_for_p2p(
        PARTIES,
        "round3",
    );

    let mut j = 0;
    let mut party_shares: Vec<Scalar<Ed25519>> = Vec::new();
    for i in 1..=PARTIES {
        if i == client.party_number {
            party_shares.push(round2_result.secret_shares[(i - 1) as usize].clone());
        } else {
            let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[j]).unwrap();
            let key_i = &round2_result.enc_keys[j];
            let out = aes_decrypt(key_i, aead_pack);
            let out_bn = BigInt::from_bytes(&out[..]);
            let out_fe = Scalar::<Ed25519>::from(&out_bn);
            party_shares.push(out_fe);

            j += 1;
        }
    }

    party_shares
}

fn run_round4(
    client: &PartyClient,
    PARTIES: u16,
    round2_result: &Round2Result,
    party_keys: &Keys,
    party_shares: Vec<Scalar<Ed25519>>,
    params: &Parameters
) -> (SharedKeys, Vec<VerifiableSS<Ed25519>>, DLogProof<Ed25519, Sha512>)
{
    assert!(client.broadcast(
        "round4",
        serde_json::to_string(&round2_result.vss_scheme).unwrap(),
    )
        .is_ok());
    let round4_ans_vec = client.poll_for_broadcasts(
        PARTIES,
        "round4",
    );

    let mut j = 0;
    let mut vss_scheme_vec: Vec<VerifiableSS<Ed25519>> = Vec::new();
    for i in 1..=PARTIES {
        if i == client.party_number {
            vss_scheme_vec.push(round2_result.vss_scheme.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Ed25519> = serde_json::from_str(&round4_ans_vec[j]).unwrap();

            vss_scheme_vec.push(vss_scheme_j);
            j += 1;
        }
    }

    let shared_keys = party_keys
        .phase2_verify_vss_construct_keypair(
            &params,
            &round2_result.point_vec,
            &party_shares,
            &vss_scheme_vec,
            client.party_number,
        )
        .expect("invalid vss");

    let dlog_proof = DLogProof::prove(&shared_keys.x_i);

    (shared_keys, vss_scheme_vec, dlog_proof)
}

fn run_round5(
    client: PartyClient,
    PARTIES: u16,
    dlog_proof: DLogProof<Ed25519, Sha512>,
    params: Parameters,
    point_vec: Vec<Point<Ed25519>>
)
{
    assert!(client.broadcast(
        "round5",
        serde_json::to_string(&dlog_proof).unwrap(),
    )
        .is_ok());
    let round5_ans_vec = client.poll_for_broadcasts(
        PARTIES,
        "round5",
    );

    let mut j = 0;
    let mut dlog_proof_vec: Vec<DLogProof<Ed25519, Sha512>> = Vec::new();
    for i in 1..=PARTIES {
        if i == client.party_number {
            dlog_proof_vec.push(dlog_proof.clone());
        } else {
            let dlog_proof_j: DLogProof<Ed25519, Sha512> = serde_json::from_str(&round5_ans_vec[j]).unwrap();

            dlog_proof_vec.push(dlog_proof_j);
            j += 1;
        }
    }
    verify_dlog_proofs(&params, &dlog_proof_vec, &point_vec)
        .expect("bad dlog proof");

}