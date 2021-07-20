// dkg code dependencies

#![allow(non_snake_case)]

use dist_keygen_with_ecdsa_and_libp2p::protocols::multi_party_ecdsa::gg_2018::party_i::{
    KeyGenBroadcastMessage1, KeyGenDecommitMessage1, Keys, Parameters,
};
use paillier::EncryptionKey;
//use reqwest::Client;
use std::{env, fs, time};

use async_std::{io, task};
use env_logger::{Builder, Env};
use futures::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::{
    error::Error,
    task::{Context, Poll},
};


// p2p code dependencies

use futures::StreamExt;
use libp2p::{
    Multiaddr,
    NetworkBehaviour,
    PeerId,
    Transport,
    core::upgrade,
    identity,
    floodsub::{self, Floodsub, FloodsubEvent},
    mdns::{Mdns, MdnsEvent},
    mplex,
    noise,
    swarm::{NetworkBehaviourEventProcess, SwarmBuilder, SwarmEvent},
    // `TokioTcpConfig` is available through the `tcp-tokio` feature.
    tcp::TokioTcpConfig,
};
use tokio;

use std::{iter::repeat, thread, time::Duration};

use crypto::{
    aead::{AeadDecryptor, AeadEncryptor},
    aes::KeySize::KeySize256,
    aes_gcm::AesGcm,
};
use curv::{
    cryptographic_primitives::{
        proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
    },
    arithmetic::traits::Converter,
    elliptic::curves::secp256_k1::{FE, GE},
    elliptic::curves::traits::{ECPoint, ECScalar},
    BigInt,
};
// use reqwest::Client;
use serde::{Deserialize, Serialize};

use tokio::sync::mpsc;

use async_trait::async_trait;

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

#[derive(Serialize, Deserialize)]
pub struct Params {
    pub parties: String,
    pub threshold: String,
}

#[allow(dead_code)]
pub fn aes_encrypt(key: &[u8], plaintext: &[u8]) -> AEAD {
    let nonce: Vec<u8> = repeat(3).take(12).collect();
    let aad: [u8; 0] = [];
    let mut gcm = AesGcm::new(KeySize256, key, &nonce[..], &aad);
    let mut out: Vec<u8> = repeat(0).take(plaintext.len()).collect();
    let mut out_tag: Vec<u8> = repeat(0).take(16).collect();
    gcm.encrypt(&plaintext[..], &mut out[..], &mut out_tag[..]);
    AEAD {
        ciphertext: out.to_vec(),
        tag: out_tag.to_vec(),
    }
}

#[allow(dead_code)]
pub fn aes_decrypt(key: &[u8], aead_pack: AEAD) -> Vec<u8> {
    let mut out: Vec<u8> = repeat(0).take(aead_pack.ciphertext.len()).collect();
    let nonce: Vec<u8> = repeat(3).take(12).collect();
    let aad: [u8; 0] = [];
    let mut gcm = AesGcm::new(KeySize256, key, &nonce[..], &aad);
    gcm.decrypt(&aead_pack.ciphertext[..], &mut out, &aead_pack.tag[..]);
    out
}


#[allow(dead_code)]
pub fn check_sig(r: &FE, s: &FE, msg: &BigInt, pk: &GE) {
    use secp256k1::{verify, Message, PublicKey, PublicKeyFormat, Signature};

    let raw_msg = BigInt::to_bytes(&msg);
    let mut msg: Vec<u8> = Vec::new(); // padding
    msg.extend(vec![0u8; 32 - raw_msg.len()]);
    msg.extend(raw_msg.iter());

    let msg = Message::parse_slice(msg.as_slice()).unwrap();
    let mut raw_pk = pk.pk_to_key_slice();
    if raw_pk.len() == 64 {
        raw_pk.insert(0, 4u8);
    }
    let pk = PublicKey::parse_slice(&raw_pk, Some(PublicKeyFormat::Full)).unwrap();

    let mut compact: Vec<u8> = Vec::new();
    let bytes_r = &r.get_element()[..];
    compact.extend(vec![0u8; 32 - bytes_r.len()]);
    compact.extend(bytes_r.iter());

    let bytes_s = &s.get_element()[..];
    compact.extend(vec![0u8; 32 - bytes_s.len()]);
    compact.extend(bytes_s.iter());

    let secp_sig = Signature::parse_slice(compact.as_slice()).unwrap();

    let is_correct = verify(&msg, &secp_sig, &pk);
    assert!(is_correct);
}

/// The `tokio::main` attribute sets up a tokio runtime.
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();
    
    // Create a random PeerId
    let id_keys = identity::Keypair::generate_ed25519();
    let peer_id = PeerId::from(id_keys.public());
    println!("Local peer id: {:?}", peer_id);
    println!("CHAT----TOKIO");

    // Create a keypair for authenticated encryption of the transport.
    // priv-pub pair
    let noise_keys = noise::Keypair::<noise::X25519Spec>::new()
        .into_authentic(&id_keys)
        .expect("Signing libp2p-noise static DH keypair failed.");

    // Create a tokio-based TCP transport use noise for authenticated
    // encryption and Mplex for multiplexing of substreams on a TCP stream.
    let transport = TokioTcpConfig::new().nodelay(true)
        .upgrade(upgrade::Version::V1)
        .authenticate(noise::NoiseConfig::xx(noise_keys).into_authenticated())
        .multiplex(mplex::MplexConfig::new())
        .boxed();

    // Create a Floodsub topic
    let floodsub_topic = floodsub::Topic::new("dkg-community");

    let (tx0, mut rx) = mpsc::channel(8); // capacity of 8
    let tx1 = tx0.clone(); // create another sender
    
    #[derive(NetworkBehaviour)]
    struct MyBehaviour {
        floodsub: Floodsub,
        mdns: Mdns,
        #[behaviour(ignore)]
        response_sender: mpsc::UnboundedSender<Entry>,
    }

    impl NetworkBehaviourEventProcess<FloodsubEvent> for MyBehaviour {
        // Called when `floodsub` produces an event.
        //#[tokio::inject_event]
        fn inject_event(&mut self, event: FloodsubEvent) {
            // if let FloodsubEvent::Message(event) = event {
            //     let msg = String::from_utf8_lossy(&event.data);
            //     println!("Received: '{:?}' from {:?}", msg, event.source);
            // }

            match event {
                FloodsubEvent::Message(msg) => {
                    if let Ok(resp) = serde_json::from_slice::<Entry>(&msg.data) {
                        if resp.receiver == PEER_ID.to_string() {
                            info!("Response from {}:", msg.source);
                            resp.data.iter().for_each(|r| info!("{:?}", r));
                        }
                    } else if let Ok(req) = serde_json::from_slice::<ListRequest>(&msg.data) {
                        match req.mode {
                            ListMode::ALL => {
                                info!("Received ALL req: {:?} from {:?}", req, msg.source);
                                respond_with_public_recipes(
                                    self.response_sender.clone(),
                                    msg.source.to_string(),
                                );
                            }
                            ListMode::One(ref peer_id) => {
                                if peer_id == &PEER_ID.to_string() {
                                    info!("Received req: {:?} from {:?}", req, msg.source);
                                    respond_with_public_recipes(
                                        self.response_sender.clone(),
                                        msg.source.to_string(),
                                    );
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    impl NetworkBehaviourEventProcess<MdnsEvent> for MyBehaviour {
        // Called when `mdns` produces an event.
        fn inject_event(&mut self, event: MdnsEvent) {
            match event {
                MdnsEvent::Discovered(list) =>
                    for (peer, _) in list {
                        println!("\nDiscovered: {:?}", &peer);
                        self.floodsub.add_node_to_partial_view(peer);
                    }
                MdnsEvent::Expired(list) =>
                    for (peer, _) in list {
                        if !self.mdns.has_node(&peer) {
                            println!("\nExpired: {:?}", &peer);
                            self.floodsub.remove_node_from_partial_view(&peer);
                        }
                    }
            }
        }
    }

    // Create a Swarm to manage peers and events.
    let mut swarm = {
        let mdns = Mdns::new(Default::default()).await?;
        let mut behaviour = MyBehaviour {
            floodsub: Floodsub::new(peer_id.clone()),
            mdns,
        };

        behaviour.floodsub.subscribe(floodsub_topic.clone());

        SwarmBuilder::new(transport, behaviour, peer_id)
            // We want the connection background tasks to be spawned
            // onto the tokio runtime.
            .executor(Box::new(|fut| { tokio::spawn(fut); }))
            .build()
    };

    // Reach out to another node if specified
    if let Some(to_dial) = std::env::args().nth(1) {
        let addr: Multiaddr = to_dial.parse()?;
        swarm.dial_addr(addr)?;
        println!("Dialed {:?}", to_dial)
    }

    // Read full lines from stdin
    // let mut stdin = tokio::io::BufReader::new(async_std::io::stdin()).lines();

    // Listen on all interfaces and whatever port the OS assigns
    swarm.listen_on("/ip4/0.0.0.0/tcp/0".parse()?)?;


    // dkg code starts here

    let delay = time::Duration::from_millis(25);
    println!("DKG Started.");
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
    let THRESHOLD: u16 = params.threshold.parse::<u16>().unwrap();
    
    let params = Parameters {
        threshold: THRESHOLD,
        share_count: PARTIES,
    };




    // -=-=-=----=-=-=-=-=-=-=-=-=-


    let mut i: u128 = 0;
    // start the libp2p swarm with tokio
    loop { // loop for forever
        println!("\nbefore tokio select");
        tokio::select! {
            Some(resp) = rx.recv().await => {
                // let line = line?.expect("stdin closed");
                handle_response(resp);
                swarm.behaviour_mut().floodsub.publish(floodsub_topic.clone(), line.as_bytes());
            }
            event = swarm.select_next_some() => {
                println!("\nswtch event: {:?}", event);
                if let SwarmEvent::NewListenAddr { address, .. } = event {
                    println!("Listening on {:?}", address);
                }
            }
            
        }
        println!("\nI: {}", i);
        i = i + 1;
    }
}

fn handle_response(resp: string){
    println!("handling response: {}", resp);
}


