use curve25519_dalek::{
    ristretto::CompressedRistretto,
    constants::RISTRETTO_BASEPOINT_TABLE,
    scalar::Scalar
};
use crate::{
    keys::{SecretKey, PublicKey},
    ristretto::{
        RistrettoPublicKey,
        RistrettoSecretKey
    },
    elgamal::{
        elgamal::ElGamalCommitment
    }
};
use rand::rngs::OsRng;


#[derive(Debug)]
pub struct Account {
    pub(crate) pk: RistrettoPublicKey,
    pub(crate) comm: ElGamalCommitment,
}

impl Account {
    // Private constructor
    fn set_account(pk: RistrettoPublicKey, comm: ElGamalCommitment) -> Account {
        Account {
            pk: pk,
            comm: comm,
        }
    }

	pub fn generate_account() -> (Account, RistrettoSecretKey, Scalar)  {

        // lets create a new keypair
        let mut rng = rand::thread_rng();
        let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
        
        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        // lets generate a new commitment using pubkey
        let comm = ElGamalCommitment::generate_commitment(&pk, comm_scalar, 0);

        let account = Account::set_account(pk, comm);

        return (account, sk, comm_scalar)
    }

    pub fn update_account(a: Account, bl: i64, update_key_scalar: Scalar, generate_commitment_scalar: Scalar) -> Account {

        // lets first update the pk
        let updated_pk = RistrettoPublicKey::update_public_key(&a.pk, update_key_scalar);
        println!("{:?}", updated_pk);

        // lets update the commitment
        let new_comm = ElGamalCommitment::generate_commitment(&a.pk, generate_commitment_scalar, bl);
        println!("{:?}", new_comm);

        // lets add old and new commitments
        let updated_comm = ElGamalCommitment::add_commitment(&new_comm, &a.comm);
        println!("added commitments here {:?}", updated_comm);

        Account::set_account(updated_pk, updated_comm)
    }
}