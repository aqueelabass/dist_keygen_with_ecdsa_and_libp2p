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
    receiver: String,
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

#[derive(NetworkBehaviour)]
struct DKG_NW_Behaviour {
    floodsub: Floodsub,
    mdns: TokioMdns,
    #[behaviour(ignore)]
    response_sender: mpsc::UnboundedSender<Entry>,
}

impl NetworkBehaviourEventProcess<FloodsubEvent> for DKG_NW_Behaviour {
    // Called when `floodsub` produces an event.
    //#[tokio::inject_event]
    fn inject_event(&mut self, event: FloodsubEvent) { // recieved data on floodsubpub channel in switch from other peer/s
        match event {
            FloodsubEvent::Message(msg) => {
                if let Ok(resp) = serde_json::from_slice::<Entry>(&msg.data) {
                    if resp.receiver == PEER_ID.to_string() { // means response is for this node
                        info!("Response from {}:", msg.source);
                        // resp.data.iter().for_each(|r| info!("{:?}", r));
                    }
                }
                // else check for other kind of response data, above will lead to error
            }
            _ => (),
        }
    }
}

impl NetworkBehaviourEventProcess<MdnsEvent> for DKG_NW_Behaviour {
    // Called when `mdns` produces an event.
    fn inject_event(&mut self, event: MdnsEvent) { // if any peer connects or discconects this will be called
        match event {
            MdnsEvent::Discovered(list) => {
                let mut count = 0;
                for (peer, _) in list {
                    println!("\nDiscovered: {:?}", &peer);
                    self.floodsub.add_node_to_partial_view(peer);
                    count += 1;
                }
                if count == num_of_participant {
                    get_keys_with_peer_num();
                }
                else{
                    println!("waiting for the other participants to join for dkg...");
                }
                
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


static KEYS: Lazy<identity::Keypair> = Lazy::new(|| identity::Keypair::generate_ed25519());
static PEER_ID: Lazy<PeerId> = Lazy::new(|| PeerId::from(KEYS.public()));
static TOPIC: Lazy<Topic> = Lazy::new(|| floodsub::Topic::new("dkg-community"));

static mut peer_num: usize = 1;
static mut num_of_participant: usize = 0;
static mut threshold: usize = 0;
static mut party_nums: HashMap<PeerId, usize>;
/// The `tokio::main` attribute sets up a tokio runtime.
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();
    
    // Create a random PeerId
    // let id_keys = identity::Keypair::generate_ed25519();
    // let peer_id = PeerId::from(id_keys.public());
    println!("Local peer id: {:?}", peer_id);
    println!("CHAT----TOKIO");

    // Create a keypair for authenticated encryption of the transport.
    // priv-pub pair
    let noise_keys = noise::Keypair::<noise::X25519Spec>::new()
        .into_authentic(&KEYS)
        .expect("Signing libp2p-noise static DH keypair failed.");

    // Create a tokio-based TCP transport use noise for authenticated
    // encryption and Mplex for multiplexing of substreams on a TCP stream.
    let transp = TokioTcpConfig::new().nodelay(true)
        .upgrade(upgrade::Version::V1)
        .authenticate(noise::NoiseConfig::xx(noise_keys).into_authenticated())
        .multiplex(mplex::MplexConfig::new())
        .boxed();
    
    let mut behaviour = RecipeBehaviour {
        floodsub: Floodsub::new(PEER_ID.clone()),
        mdns: TokioMdns::new().expect("can create mdns"),
        response_sender,
    };
    
    behaviour.floodsub.subscribe(TOPIC.clone());

    // Create a Swarm to manage peers and events.
    let mut swarm = SwarmBuilder::new(transp, behaviour, PEER_ID.clone())
        .executor(Box::new(|fut| {
            tokio::spawn(fut);
        }))
        .build();


    Swarm::listen_on(
        &mut swarm,
        "/ip4/0.0.0.0/tcp/0"
            .parse()
            .expect("can get a local socket"),
    )
    .expect("swarm can be started");


    // dkg code starts here

    (threshold, num_of_participant) = dkg_init();


    // -=-=-=----=-=-=-=-=-=-=-=-=-

    // start the libp2p swarm with tokio
    loop {
        let evt = { // 6
            tokio::select! {
                event = swarm.select_next_some() => {
                    println!("\nswtch event: {:?}", event);
                    if let SwarmEvent::NewListenAddr { address, .. } = event {
                        println!("Listening on {:?}", address);
                        SwarmEvent::NewListenAddr(address)
                    }
                    None
                }
                resp_to_be_sent = response_rcv.recv() => { // here we take data (response to be sent to other peers) from channel // 4
                    dbg!("\nresponse: {:?}", &resp_to_be_sent);
                    Some(EventType::Response(resp_to_be_sent.expect("response exists"))) // return event type response // 5
                },
            }
        };

        if let Some(event) = evt { // 7
            match event { // 8
                EventType::Response(resp) => { // 9
                    dbg!("event type: Reasponse {:?}", &resp);
                    let json = serde_json::to_string(&resp).expect("can jsonify response"); // prepare the response to be sent to other peers
                    swarm.floodsub.publish(TOPIC.clone(), json.as_bytes()); // 10
                },
                _ => {
                    dbg!("eventype: not implemented");
                },
            }
        }
    }
}

fn uniq_peers(swarm: &mut RecipeBehaviour) {
    info!("Discovered Peers: {:?}", ConnectedPoint::is_dialer(swarm));
    let nodes = swarm.mdns.discovered_nodes();
    let mut unique_peers = HashSet::new();
    for peer in nodes {
        unique_peers.insert(peer);
    }
    unique_peers.iter().for_each(|p| info!("{}", &p));
    info!("peers count: {}", unique_peers.iter().count());
}


fn dkg_init() -> Parameters {
    println!("DKG Started.");
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
    let THRESHOLD: u16 = params.threshold.parse::<u16>().unwrap();
    
    let uuid = PEER_ID.clone(); 
    println!("number: {:?}, uuid: {:?}", peer_num, uuid);
    
    Parameters {
        threshold: THRESHOLD,
        share_count: PARTIES,
    }

}

fn get_keys_with_peer_num() {
    let party_keys = Keys::create(party_num_int as usize);
    let (bc_i, decom_i) = party_keys.phase1_broadcast_phase3_proof_of_correct_key();
    //let str: multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::KeyGenBroadcastMessage1 = bc_i.clone();
    // send commitment to ephemeral public keys, get round 1 commitments of other parties
    assert!(broadcast(
        &client,
        party_num_int,
        "round1",
        serde_json::to_string(&bc_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round1_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round1",
        uuid.clone(),
    );
}



