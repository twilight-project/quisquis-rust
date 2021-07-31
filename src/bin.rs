extern crate quisquislib; // not needed since Rust edition 2018

use quisquislib::{
    keys::{SecretKey, PublicKey},
    ristretto::{
        RistrettoSecretKey,
        RistrettoPublicKey,
        address::Address
    },
    elgamal::{
        ElGamalCommitment,
        signed_integer::SignedInteger
    },
    accounts::{
        Account
    }

    
};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE,
    ristretto::CompressedRistretto,
    ristretto::RistrettoPoint,
    scalar::Scalar
};
use rand::rngs::OsRng;

pub fn main() {
    //test();
    let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
    let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
    println!("{:?}", sk);
    println!("{:?}", pk);
    println!("{:?}", pk.as_bytes());
    let net = quisquislib::ristretto::address::Network::default();
    let addr = Address::standard(net,pk);
   // println!("{:?}", addr.as_bs58());
    println!("{:?}", addr.as_hex());
    println!("{:?}", addr);
    let addr_hex = addr.as_hex();
//let decoded_hex = quisquislib::ristretto::address::hextobytes(&addr_hex);
//println!("{:?}", decoded_hex);
//let decoded_address = Address::from_bytes(&decoded_hex);
//println!("{:?}", decoded_address);
ccheck();
/*
    let random_scalar = Scalar::random(&mut OsRng);
    let updated_pk = RistrettoPublicKey::update_public_key(&pk, random_scalar);
    println!("{:?}", updated_pk);
    let verify_public_key_update = RistrettoPublicKey::verify_public_key_update(&updated_pk, &pk, random_scalar);
    println!("{:?}", verify_public_key_update);

    let generate_base_pk = RistrettoPublicKey::generate_base_pk();
    println!("generate base pk {:?}", generate_base_pk);

    let generate_commitmenta = ElGamalCommitment::generate_commitment(&pk, random_scalar, 12);
    println!("{:?}", generate_commitmenta); 

    let generate_commitmentb = ElGamalCommitment::generate_commitment(&pk, random_scalar, 12);
    println!("{:?}", generate_commitmentb); 

    let add_commitments = ElGamalCommitment::add_commitments(&generate_commitmenta, &generate_commitmentb);
    println!("added commitments here {:?}", add_commitments); 
    
    let num = 10 as u64;
    let sign_int = SignedInteger::from(num);
    let neg_sign_int = -sign_int;
    println!("int = {:?}, Sign Int = {:?}", sign_int, neg_sign_int);
    let possscalar : Scalar = SignedInteger::into(sign_int);
    let negscalar : Scalar = SignedInteger::into(neg_sign_int);
    println!("Scalar = {:?}, Sign Int= {:?}", possscalar, negscalar);

    // lets create a new keypair
    let mut rng = rand::thread_rng();
    let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
    let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

    let acc = Account::generate_account(pk);
    println!("generated account {:?}", acc);

    let updated_keys_scalar = Scalar::random(&mut OsRng);

    // lets get a random scalar
    let comm_scalar = Scalar::random(&mut OsRng);

    let updated_account = Account::update_account(acc, 16, updated_keys_scalar, comm_scalar);
    println!("updated account {:?}", updated_account);

    let rscalar = Scalar::random(&mut OsRng);

    let create_delta_account = Account::create_delta_account(updated_account, 16, rscalar);
    println!("create_delta_account {:?}", create_delta_account);

    let create_epsilon_account = Account::create_epsilon_account(16, rscalar, generate_base_pk);
    println!("create_epsilon_account {:?}", create_epsilon_account);

    let updated_delta_account = Account::update_delta_account(updated_account, create_delta_account);
    println!("updated_delta_account {:?}", updated_delta_account.unwrap());
*/

}

fn ccheck(){
    let point = RistrettoPoint::random(&mut OsRng);
    let scalar = Scalar::random(&mut OsRng);
    let scalar_square = scalar * scalar;
    let scalar_cube = scalar * scalar * scalar;
    let scalar_quad = scalar * scalar * scalar * scalar;
    let sp = point * scalar;
    let spp = sp * scalar;
    let ssp = point * scalar_square;
    assert_eq!(ssp,spp);
    if ssp.eq(&spp){
        println!("Equal");}
    else{
    println!("Different");
    }
    let sppp = spp * scalar;
    let sssp = point * scalar_cube;
    assert_eq!(sssp,sppp);
    let spppp = sppp * scalar;
    let ssssp = point * scalar_quad;
    assert_eq!(ssssp,spppp);

}   