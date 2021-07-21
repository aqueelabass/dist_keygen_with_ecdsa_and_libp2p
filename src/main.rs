// dkg code dependencies

// #![allow(dead_code)]
#![allow(non_snake_case)]

// ------------------ depedencies section --------------------

use dist_keygen_with_ecdsa_and_libp2p::swarm_api::{
    SwarmApi, 
    M_SwarmEvent
};

use paillier::EncryptionKey;

use dist_keygen_with_ecdsa_and_libp2p::protocols::multi_party_ecdsa::gg_2018::party_i::{
    Keys, 
    Parameters,
    KeyGenBroadcastMessage1, 
    KeyGenDecommitMessage1
};

use libp2p::{
    mplex,
    noise,
    Swarm,
    PeerId,
    identity,
    Multiaddr,
    Transport,
    core::upgrade,
    NetworkBehaviour,
    tcp::TokioTcpConfig,
    
    floodsub::{
        Topic,
        Floodsub, 
        FloodsubEvent, 
    },
    
    mdns::{
        MdnsEvent, 
        TokioMdns
    },
    
    swarm::{
        SwarmEvent, 
        SwarmBuilder, 
        NetworkBehaviour,
        NetworkBehaviourEventProcess
    },
};

use crypto::{
    aead::{
        AeadDecryptor, 
        AeadEncryptor
    },
    aes::KeySize::KeySize256,
    aes_gcm::AesGcm,
};

use curv::{
    cryptographic_primitives::{
        proofs::sigma_dlog::DLogProof, 
        secret_sharing::feldman_vss::VerifiableSS,
    },
    arithmetic::traits::Converter,
    elliptic::curves::secp256_k1::{
        FE, 
        GE
    },
    elliptic::curves::traits::{
        ECPoint, 
        ECScalar
    },
    BigInt
};

use tokio;
use tokio::sync::mpsc;
use async_trait::async_trait;
use once_cell::sync::Lazy;

use futures::{
    StreamExt,
    prelude::*
};

use serde::{Deserialize, Serialize};

use env_logger::{Builder, Env};

use async_std::{io, task};

use std::{ 
    fs, 
    env, 
    time,
    thread,
    hash::{
        Hash, 
        Hasher
    },    
    task::{
        Poll,
        Context
    }, 
    iter::repeat, 
    error::Error,
    time::Duration, 
    collections::HashMap, 
    collections::HashSet,
    collections::hash_map::DefaultHasher
};

// ------------- End of dependencies section ----------------

// ------------- Globals ---------------

static KEYS: Lazy<identity::Keypair> = Lazy::new(|| identity::Keypair::generate_ed25519());
static PEER_ID: Lazy<PeerId> = Lazy::new(|| PeerId::from(KEYS.public()));
static TOPIC: Lazy<Topic> = Lazy::new(|| Topic::new("dkg-community"));
static mut PEER_INDEX: usize = 0;

// --------------------------------------

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
    pub number: usize,
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

enum EventType {
    Response(String),
    Input(String),
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
    swarmapi: SwarmApi,
    #[behaviour(ignore)]
    response_sender: mpsc::UnboundedSender<String>,
    #[behaviour(ignore)]
    peer_indeces:  HashMap<String, usize>,
    #[behaviour(ignore)]
    num_of_participant: usize,
    #[behaviour(ignore)]
    peer_count: usize,
    #[behaviour(ignore)]
    threshold: usize,
    
}

impl NetworkBehaviourEventProcess<M_SwarmEvent> for DKG_NW_Behaviour {
    fn inject_event(&mut self, event: <SwarmApi as NetworkBehaviour>::OutEvent) {
        match event {
            M_SwarmEvent::PeerConnected(peer_id) => {
                println!("peer connected. peerid: {}", peer_id);
                // self.events.push(BehaviourEventOut::PeerConnected(peer_id))
            }
            M_SwarmEvent::PeerDisconnected(peer_id) => {
                let k = peer_id.to_base58();
                println!("peer dis-connected. peerid: {}", k);
                println!("Before: {:?}", &self.peer_indeces);
                self.peer_indeces.remove(&k);
                println!("After: {:?}", &self.peer_indeces);

                // self.events.push(BehaviourEventOut::PeerDisconnected(peer_id))
            }
        }
    }
}

impl NetworkBehaviourEventProcess<FloodsubEvent> for DKG_NW_Behaviour {
    // Called when `floodsub` produces an event.
    //#[tokio::inject_event]
    fn inject_event(&mut self, event: FloodsubEvent) { // recieved data on floodsubpub channel in switch from other peer/s
        match event {
            FloodsubEvent::Message(msg) => {
                //println!("==> Got some response on floodsub. msg: {:?}", std::str::from_utf8(&msg.data));
                if let Ok(resp) = serde_json::from_slice::<PartySignup>(&msg.data) {
                    
                    println!("RPartySignup response");
                    if !self.peer_indeces.contains_key(&resp.uuid) { // means response is for this node
                        // resp.data.iter().for_each(|r| info!("{:?}", r));
                        self.peer_indeces.insert(resp.uuid, resp.number);
                    }
                }else if let Ok(resp) = serde_json::from_slice::<Entry>(&msg.data){

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
                //println!("\nDiscovered a new peer. nop: {}, pc: {}", &self.num_of_participant, &self.peer_count);
                for (peer, _) in list {
                    self.floodsub.add_node_to_partial_view(peer);
                }
                uniq_peers(self);
                if self.num_of_participant > 0 && self.peer_count == self.num_of_participant {
                    get_keys_with_peer_num();
                }
                else{
                    //println!("peer_indeces: {:?}", self.peer_indeces);
                    //println!("waiting for the other participants to join for dkg...");
                }                
            },
                
            MdnsEvent::Expired(list) => {
                //println!("some Node expired");
                for (peer, _) in list {
                    if !self.mdns.has_node(&peer) {
                        //println!("\n[WARNING] ==> Node Expired: {:?}", &peer);
                        self.floodsub.remove_node_from_partial_view(&peer);
                    }
                }
            },
            _ => {
                //println!("[EVENT] ==> Unhandled Floodsub event");
            },
        }
    }
}

/// The `tokio::main` attribute sets up a tokio runtime.
#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();
    println!("my peerid: {:?}", PEER_ID.clone());
    // Create a random PeerId
    // let id_keys = identity::Keypair::generate_ed25519();
    // let peer_id = PeerId::from(id_keys.public());
    //println!("Local peer id: {:?}", &PEER_ID);
    //println!("DKG with TOKIO, LIBP2P and t-ECDSA");

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
    
    let (response_sender, mut response_rcv) = mpsc::unbounded_channel();
    let peer_indeces:  HashMap<String, usize> = HashMap::new();
    let num_of_participant: usize = 0;
    let peer_count: usize = 0;
    let threshold: usize = 0;
    
    let mut behaviour = DKG_NW_Behaviour {
        floodsub: Floodsub::new(PEER_ID.clone()),
        mdns: TokioMdns::new().expect("can create mdns"),
        swarmapi: SwarmApi::new(), 
        response_sender,
        peer_indeces,
        num_of_participant,
        peer_count,
        threshold,
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

    dkg_init(&mut swarm);


    // -=-=-=----=-=-=-=-=-=-=-=-=-

    // start the libp2p swarm with tokio
    loop {
        tokio::select! {
            // branch 1
            resp_to_be_sent = response_rcv.recv() => { // here we take data (response to be sent to other peers) from channel // 4
                //println!("==> getting from channel: {:?}", &resp_to_be_sent);
                println!("==> sending to other peer/s. Topic: {:?}", &TOPIC);
                swarm.floodsub.publish(TOPIC.clone(), resp_to_be_sent.unwrap().as_bytes());
            }
            // branch 2
            event = swarm.select_next_some() => {
                //println!("\nswtch event: {:?}", event);
                //if let SwarmEvent::NewListenAddr { address, .. } = event {
                //    //println!("Listening on {:?}", address);
                //}
            }
        };
    }
}

fn uniq_peers(swarm: &mut DKG_NW_Behaviour) {
    //println!("getting unique peers and then count");
    let nodes = swarm.mdns.discovered_nodes();
    let mut unique_peers = HashSet::new();
    for peer in nodes {
        unique_peers.insert(peer);
    }
    let count = unique_peers.iter().count();
    unique_peers.iter().for_each(|p| {
        //println!("{}", &p)
    });
    //println!("peers count: {}", &count);
    let k = PEER_ID.to_base58();
    if !swarm.peer_indeces.contains_key(&k) {
        swarm.peer_indeces.insert(k.clone(), count);
        
        unsafe{
            PEER_INDEX = count.clone();
        }
        
    }
    
    if count > 1 {
        let k = PEER_ID.to_base58();
        let p = PartySignup {
            number: match swarm.peer_indeces.get(&k){
                Some(&num) => num,
                _ => panic!(),
            },
            uuid: k,
        };
        //println!("==> putting over channel");
        swarm.response_sender.send(serde_json::to_string(&p).unwrap());
    }
    
    swarm.peer_count = count;
    //println!("peer_indeces: {:?}", &swarm.peer_indeces);
}


fn dkg_init(swarm: &mut DKG_NW_Behaviour) {
    //println!("[DKG] ==> DKG Started.");
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    swarm.num_of_participant = params.parties.parse::<u16>().unwrap() as usize;
    swarm.threshold = params.threshold.parse::<u16>().unwrap() as usize;
}

fn get_keys_with_peer_num() {
    //println!("[DKG] ==> getting keys");
    unsafe{
        let peer_keys = Keys::create(PEER_INDEX);
        let (bc_i, decom_i) = peer_keys.phase1_broadcast_phase3_proof_of_correct_key();
        ////println!("[DKG] ==> Keys: bc_i: {:?}, decom_i: {:?}", bc_i, decom_i);
    }
    
    //let str: multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::KeyGenBroadcastMessage1 = bc_i.clone();
    // send commitment to ephemeral public keys, get round 1 commitments of other parties
    // assert!(broadcast(
    //     &client,
    //     party_num_int,
    //     "round1",
    //     serde_json::to_string(&bc_i).unwrap(),
    //     uuid.clone()
    // )
    // .is_ok());
    // let round1_ans_vec = poll_for_broadcasts(
    //     &client,
    //     party_num_int,
    //     PARTIES,
    //     delay,
    //     "round1",
    //     uuid.clone(),
    // );
}



