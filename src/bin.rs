extern crate quisquislib; // not needed since Rust edition 2018

use quisquislib::{
    keys::{SecretKey, PublicKey},
    ristretto::{
        RistrettoSecretKey,
        RistrettoPublicKey
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
}