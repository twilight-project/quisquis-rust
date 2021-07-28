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


#[derive(Debug, Copy, Clone)]
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

	pub fn generate_account(pk: RistrettoPublicKey) -> Account  {
        
        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        // lets generate a new commitment using pubkey
        let comm = ElGamalCommitment::generate_commitment(&pk, comm_scalar, 0);

        let account = Account::set_account(pk, comm);

        return account
    }

    pub fn update_account(a: Account, bl: i64, update_key_scalar: Scalar, generate_commitment_scalar: Scalar) -> Account {

        // lets first update the pk
        let updated_pk = RistrettoPublicKey::update_public_key(&a.pk, update_key_scalar);

        // lets update the commitment
        let new_comm = ElGamalCommitment::generate_commitment(&a.pk, generate_commitment_scalar, bl);

        // lets add old and new commitments
        let updated_comm = ElGamalCommitment::add_commitments(&new_comm, &a.comm);

        Account::set_account(updated_pk, updated_comm)
    }

    // create_delta_account creates account delta
    // takes account, vector bl (updated balance), rscalar
    // returns Account Delta
    pub fn create_delta_account(a: Account, bl: i64, rscalar: Scalar) -> Account {

        // lets generate commitment on v for delta using Pk and r'
        let comm_delta = ElGamalCommitment::generate_commitment(&a.pk, rscalar, bl);

        Account::set_account(a.pk, comm_delta)
    }

    // create_epsilon_account creates account delta
    // takes vector bl (updated balance), rscalar and base_pair generated with fixed-g
    // returns Account Epsilon
    pub fn create_epsilon_account(bl: i64, rscalar: Scalar, base_pk: RistrettoPublicKey) -> Account {

        // lets generate commitment on v for epsilon using GP and r
        let comm_epsilon = ElGamalCommitment::generate_commitment(&base_pk, rscalar, bl);

        Account::set_account(base_pk, comm_epsilon)
    }

    // update_delta_account takes updated_account and delta_account, multiplies their commitments
    // returns updated delta account
    pub fn update_delta_account(updated_account: Account, delta_account: Account) ->  Result<Account, &'static str> {

        if updated_account.pk.gr == delta_account.pk.gr && updated_account.pk.grsk == delta_account.pk.grsk {
            let new_comm = ElGamalCommitment::add_commitments(&updated_account.comm, &delta_account.comm);
            let updated_delta_account = Account::set_account(updated_account.pk, new_comm);
            Ok(updated_delta_account)
        }else{
            Err("pks are not equal")
        }
    }

    // verify_delta_update verifies if account delta was updated correctly
    pub fn verify_delta_update(updated_delta_account: Account, delta_account: Account, updated_input_account: Account) -> bool {

        if updated_delta_account.pk.gr == delta_account.pk.gr && updated_delta_account.pk.gr == updated_input_account.pk.gr && delta_account.pk.gr == updated_input_account.pk.gr {
            if updated_delta_account.pk.grsk == delta_account.pk.grsk && updated_delta_account.pk.grsk == updated_input_account.pk.grsk && delta_account.pk.grsk == updated_input_account.pk.grsk {
                
                // lets add delta_account and updated_input_account commitments
                let added_comm = ElGamalCommitment::add_commitments(&delta_account.comm, &updated_input_account.comm);
                if added_comm == updated_delta_account.comm {
                    return true
                }
            }
        }
        return false
    }
}