extern crate quisquislib; // not needed since Rust edition 2018

use quisquislib::{
    keys::{SecretKey, PublicKey},
    ristretto::{
        RistrettoSecretKey,
        RistrettoPublicKey
    },
    elgamal::{
        ElGamalCommitment,
        signed_integer::SignedInteger
    },
    
};
use curve25519_dalek::{
    scalar::Scalar
};
use rand::rngs::OsRng;

pub fn main() {
    //test();
    let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
    let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
    println!("{:?}", sk);
    println!("{:?}", pk);
    let random_scalar = Scalar::random(&mut OsRng);
    let updated_pk = RistrettoPublicKey::update_public_key(&pk, random_scalar);
    println!("{:?}", updated_pk);
    let verify_public_key_update = RistrettoPublicKey::verify_public_key_update(&updated_pk, &pk, random_scalar);
    println!("{:?}", verify_public_key_update);

    let generate_commitment = ElGamalCommitment::generate_commitment(&pk, random_scalar, 12);
    println!("{:?}", generate_commitment); 
    
    let num = 10 as u64;
    let sign_int = SignedInteger::from(num);
    let neg_sign_int = -sign_int;
    println!("int = {:?}, Sign Int = {:?}", sign_int, neg_sign_int);
    let possscalar : Scalar = SignedInteger::into(sign_int);
    let negscalar : Scalar = SignedInteger::into(neg_sign_int);
    println!("Scalar = {:?}, Sign Int= {:?}", possscalar, negscalar);
}