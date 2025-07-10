extern crate quisquislib; // not needed since Rust edition 2018

use curve25519_dalek::scalar::Scalar;
use quisquislib::{
    accounts::Account,
    //util::address::{Address}
    elgamal::ElGamalCommitment,
    keys::{PublicKey, SecretKey},
    ristretto::{RistrettoPublicKey, RistrettoSecretKey},
};
use rand::rngs::OsRng;

/// Entry point for the Quisquis binary.
/// Demonstrates key generation, account creation, and cryptographic operations.
pub fn main() {
    // Generate a new Ristretto secret key using a secure RNG.
    let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
    // Derive the corresponding public key from the secret key.
    let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
    println!("{:?}", sk);
    println!("{:?}", pk);

    // Generate a new account using the public key.
    let (acc, _) = Account::generate_account(pk);
    println!("generated account {:?}", acc);

    // Generate a random scalar for updating keys and commitments.
    let updated_keys_scalar = Scalar::random(&mut OsRng);
    let comm_scalar = Scalar::random(&mut OsRng);

    // Update the account with new keys and commitment scalar.
    let updated_account =
        Account::update_account(acc, 16u64.into(), updated_keys_scalar, comm_scalar);
    println!("updated account {:?}", updated_account);

    // Generate another random secret key (unused in this example).
    let _rsk: RistrettoSecretKey = SecretKey::random(&mut OsRng);

    // Demonstrate public key update and verification.
    let random_scalar = Scalar::random(&mut OsRng);
    let updated_pk = RistrettoPublicKey::update_public_key(&pk, random_scalar);
    println!("{:?}", updated_pk);
    let verify_public_key_update =
        RistrettoPublicKey::verify_public_key_update(&updated_pk, &pk, random_scalar);
    println!("{:?}", verify_public_key_update);

    // Generate a base public key (generator point).
    let generate_base_pk = RistrettoPublicKey::generate_base_pk();
    println!("generate base pk {:?}", generate_base_pk);

    // Demonstrate ElGamal commitment generation and addition.
    let generate_commitmenta =
        ElGamalCommitment::generate_commitment(&pk, random_scalar, 12u64.into());
    println!("{:?}", generate_commitmenta);

    let generate_commitmentb =
        ElGamalCommitment::generate_commitment(&pk, random_scalar, 12u64.into());
    println!("{:?}", generate_commitmentb);

    let add_commitments =
        ElGamalCommitment::add_commitments(&generate_commitmenta, &generate_commitmentb);
    println!("added commitments here {:?}", add_commitments);

    // Example for working with signed integers and scalars (commented out).
    // let num = 10 as u64;
    // let sign_int = SignedInteger::from(num);
    // let neg_sign_int = -sign_int;
    // println!("int = {:?}, Sign Int = {:?}", sign_int, neg_sign_int);
    // let possscalar: Scalar = SignedInteger::into(sign_int);
    // let negscalar: Scalar = SignedInteger::into(neg_sign_int);
    // println!("Scalar = {:?}, Sign Int= {:?}", possscalar, negscalar);

    // Demonstrate keypair and account generation with a thread-local RNG.
    let mut rng = rand::thread_rng();
    let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
    let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

    let (acc, _) = Account::generate_account(pk);
    println!("generated account {:?}", acc);

    let updated_keys_scalar = Scalar::random(&mut OsRng);
    let comm_scalar = Scalar::random(&mut OsRng);

    let updated_account =
        Account::update_account(acc, 16u64.into(), updated_keys_scalar, comm_scalar);
    println!("updated account {:?}", updated_account);

    // The following code demonstrates advanced account operations and address handling.
    // It is commented out but left for reference for future maintainers.

    // let rscalar = Scalar::random(&mut OsRng);
    // let create_delta_account = Account::create_delta_account(updated_account, 5, rscalar);
    // println!("create_delta_account {:?}", create_delta_account);

    // let create_epsilon_account = Account::create_epsilon_account(16, rscalar, generate_base_pk);
    // println!("create_epsilon_account {:?}", create_epsilon_account);

    // let updated_delta_account = Account::update_delta_account(updated_account, create_delta_account);
    // println!("updated_delta_account {:?}", updated_delta_account.unwrap());

    // println!("{:?}", pk.as_bytes());
    // let net = quisquislib::util::address::Network::default();
    // let addr = Address::standard(net,pk);
    // // println!("{:?}", addr.as_bs58());
    // println!("{:?}", addr.as_hex());
    // println!("{:?}", addr);
    // let addr_hex = addr.as_hex();

    // let decoded_address = Address::from_hex(&addr_hex);
    // println!("{:?}", decoded_address);

    // let updated_delta_account = Account::update_delta_account(updated_account, create_delta_account).unwrap();
    // println!("updated_delta_account {:?}", updated_delta_account);

    // let updated_delta_account = Account::verify_delta_update(updated_delta_account, create_delta_account, updated_account);
    // println!("updated_delta_account {:?}", updated_delta_account);
}
