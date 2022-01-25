use std::{env, iter::repeat, thread, time, time::Duration};

use aes_gcm::{Aes256Gcm, Nonce};
use aes_gcm::aead::{NewAead, Aead, Payload};

use reqwest::Client;
use serde::{Deserialize, Serialize};

pub type Key = String;

#[allow(dead_code)]
pub const AES_KEY_BYTES_LEN: usize = 32;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct AEAD {
    pub ciphertext: Vec<u8>,
    pub tag: Vec<u8>,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct PartySignup {
    pub number: u16,
    pub uuid: String,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct Index {
    pub key: Key,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct Entry {
    pub key: Key,
    pub value: String,
}

#[derive(Serialize, Deserialize, Clone)]
pub struct Params {
    pub parties: String,
    pub threshold: String,
}

#[derive(Clone)]
pub struct PartyClient {
    client: Client,
    address: String,
    uuid: String,
    delay: Duration,
    pub party_number: u16,
}

pub enum ClientPurpose {
    Keygen,
    Sign
}

impl ClientPurpose {
    fn as_str(&self) -> &'static str {
        match self {
            ClientPurpose::Keygen => "keygen",
            ClientPurpose::Sign => "sign"
        }
    }
}

#[allow(dead_code)]
pub fn aes_encrypt(key: &[u8], plaintext: &[u8]) -> AEAD {

    let aes_key = aes_gcm::Key::from_slice(key);
    let cipher = Aes256Gcm::new(aes_key);

    let nonce_vector: Vec<u8> = repeat(3).take(12).collect();
    let nonce = Nonce::from_slice(nonce_vector.as_slice());

    let out_tag: Vec<u8> = repeat(0).take(16).collect();

    let text_payload = Payload {
        msg: plaintext,
        aad: &out_tag.as_slice()
    };

    let ciphertext = cipher.encrypt(nonce, text_payload)
        .expect("encryption failure!");

    AEAD {
        ciphertext: ciphertext,
        tag: out_tag.to_vec(),
    }
}

#[allow(dead_code)]
pub fn aes_decrypt(key: &[u8], aead_pack: AEAD) -> Vec<u8> {

    let aes_key = aes_gcm::Key::from_slice(key);

    let nonce_vector: Vec<u8> = repeat(3).take(12).collect();
    let nonce = Nonce::from_slice(nonce_vector.as_slice());

    let gcm = Aes256Gcm::new(aes_key);

    let text_payload = Payload {
        msg: aead_pack.ciphertext.as_slice(),
        aad: aead_pack.tag.as_slice()
    };

    let out = gcm.decrypt(nonce, text_payload);
    out.unwrap()
}

impl PartyClient {
    pub fn new(purpose: ClientPurpose, curve_name: &str, address: String, delay: Duration, tn_params: Params) -> Self {

        let mut instance = Self {
            client: Client::new(),
            address,
            delay,
            uuid: "".to_string(),
            party_number: 0
        };

        //Purpose is set to segregate the sessions on the manager
        let signup_path = "signup".to_owned() + &purpose.as_str();
        let (party_num_int, uuid) = match instance.signup(&signup_path).unwrap() {
            PartySignup { number, uuid } => (number, uuid),
        };

        println!("number: {:?}, uuid: {:?}, curve: {:?}", party_num_int, uuid, curve_name);

        instance.uuid = uuid;
        instance.party_number = party_num_int;

        instance
    }

    pub fn signup(&self, path: &str) -> Result<PartySignup, ()> {

        let res_body = self.post_request(path, ()).unwrap();
        serde_json::from_str(&res_body).unwrap()
    }

    pub fn post_request<T>(&self, path: &str, body: T) -> Option<String>
        where
            T: serde::ser::Serialize,
    {
        let address = self.address.clone();
        let retries = 3;
        let retry_delay = time::Duration::from_millis(250);
        for _i in 1..retries {
            let res = self.client
                .post(&format!("{}/{}", address, path))
                .json(&body)
                .send();

            if let Ok(mut res) = res {
                return Some(res.text().unwrap());
            }
            thread::sleep(retry_delay);
        }
        None
    }

    pub fn broadcast(
        &self,
        round: &str,
        data: String,
    ) -> Result<(), ()> {
        let key = format!("{}-{}-{}", self.party_number, round, self.uuid);
        let entry = Entry {
            key: key.clone(),
            value: data,
        };

        let res_body = self.post_request("set", entry).unwrap();
        serde_json::from_str(&res_body).unwrap()
    }

    pub fn sendp2p(
        &self,
        party_to: u16,
        round: &str,
        data: String,
    ) -> Result<(), ()> {
        let key = format!("{}-{}-{}-{}", self.party_number, party_to, round, self.uuid);

        let entry = Entry {
            key: key.clone(),
            value: data,
        };

        let res_body = self.post_request("set", entry).unwrap();
        serde_json::from_str(&res_body).unwrap()
    }

    pub fn poll_for_broadcasts(
        &self,
        n: u16,
        round: &str,
    ) -> Vec<String> {
        let mut ans_vec = Vec::new();
        for i in 1..=n {
            if i != self.party_number {
                let key = format!("{}-{}-{}", i, round, self.uuid);
                let index = Index { key };
                loop {
                    // add delay to allow the server to process request:
                    thread::sleep(self.delay);
                    let res_body = self.post_request("get", index.clone()).unwrap();
                    let answer: Result<Entry, ()> = serde_json::from_str(&res_body).unwrap();
                    if let Ok(answer) = answer {
                        ans_vec.push(answer.value);
                        println!("[{:?}] party {:?} => party {:?}", round, i, self.party_number);
                        break;
                    }
                }
            }
        }
        ans_vec
    }

    pub fn poll_for_p2p(
        &self,
        n: u16,
        round: &str,
    ) -> Vec<String> {
        let mut ans_vec = Vec::new();
        for i in 1..=n {
            if i != self.party_number {
                let key = format!("{}-{}-{}-{}", i, self.party_number, round, self.uuid);
                let index = Index { key };
                loop {
                    // add delay to allow the server to process request:
                    thread::sleep(self.delay);
                    let res_body = self.post_request("get", index.clone()).unwrap();
                    let answer: Result<Entry, ()> = serde_json::from_str(&res_body).unwrap();
                    if let Ok(answer) = answer {
                        ans_vec.push(answer.value);
                        println!("[{:?}] party {:?} => party {:?}", round, i, self.party_number);
                        break;
                    }
                }
            }
        }
        ans_vec
    }

    pub fn exchange_data<T>(&self, n:u16, round: &str, data:T) -> Vec<T>
        where
            T: Clone + serde::de::DeserializeOwned + serde::Serialize,
    {
        assert!(self.broadcast(
            &round,
            serde_json::to_string(&data).unwrap(),
        )
            .is_ok());
        let round_ans_vec = self.poll_for_broadcasts(
            n,
            &round,
        );

        let json_answers = round_ans_vec.clone();
        let mut j = 0;
        let mut answers: Vec<T> = Vec::new();
        for i in 1..=n {
            if i == self.party_number {
                answers.push(data.clone());
            } else {
                let data_j: T = serde_json::from_str::<T>(&json_answers[j].clone()).unwrap();
                answers.push(data_j);
                j += 1;
            }
        }

        return answers;
    }
}

fn main(){}