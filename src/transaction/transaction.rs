use curve25519_dalek::{
    scalar::Scalar
};
use crate::{
    keys::{SecretKey, PublicKey},
    accounts::Account,
    ristretto::{
        RistrettoPublicKey,
        RistrettoSecretKey
    },
    elgamal::{
        elgamal::ElGamalCommitment
    }
};

use rand::rngs::OsRng;
use rand::Rng;

#[derive(Debug, Clone)]
pub struct Transaction {
    pub(crate) input_account_vector: Vec<Account>,
    pub(crate) updated_account_vector: Vec<Account>,
    pub(crate) account_delta_vector: Vec<Account>,
    pub(crate) account_epsilon_vector: Vec<Account>,
    pub(crate) account_updated_delta_vector: Vec<Account>,
    pub(crate) output_account_vector: Vec<Account>,
    pub(crate) non_negative_range_proof: Vec<String>,
    pub(crate) non_negative_range_proof_commitments: Vec<String>,
    pub(crate) settle_program_bytes: Vec<String>,
    pub(crate) settle_program_proof: Vec<String>
}

impl Transaction {
    // Private constructor
    fn set_transaction(input_account_vector: Vec<Account>, updated_account_vector: Vec<Account>, account_delta_vector: Vec<Account>,
    account_epsilon_vector: Vec<Account>, account_updated_delta_vector: Vec<Account>, output_account_vector: Vec<Account>, non_negative_range_proof: Vec<String>,
    non_negative_range_proof_commitments: Vec<String>, settle_program_bytes: Vec<String>, settle_program_proof: Vec<String>) -> Transaction {
        Transaction {
            input_account_vector: input_account_vector,
            updated_account_vector: updated_account_vector,
            account_delta_vector: account_delta_vector,
            account_epsilon_vector: account_epsilon_vector,
            account_updated_delta_vector: account_updated_delta_vector,
            output_account_vector: output_account_vector,
            non_negative_range_proof: non_negative_range_proof,
            non_negative_range_proof_commitments: non_negative_range_proof_commitments,
            settle_program_bytes: settle_program_bytes,
            settle_program_proof: settle_program_proof
        }
    }

    /// generate_input_shuffle generates the first shuffle
    pub fn generate_input_shuffle(balance: i64) -> Vec<i64>  {
        // lets define an vector of values, first place will be for sender, then reciever followed by 7 decoy 0 values
        let value_vector: Vec<i64> = vec![-balance, balance, 0, 0, 0, 0, 0, 0, 0];
        return value_vector
    }

    /// generate_output_shuffle generates the second shuffle
    pub fn generate_output_shuffle(mut account_vector: Vec<Account>) -> Vec<Account>  {

        let size = 9;
        let mut shuffled_vector = Vec::with_capacity(size);

        let mut rng = OsRng;

        for i in 0..size {
            let k = rng.gen_range(i, size);
            let j = account_vector[k];
            account_vector[k] = account_vector[i];
            shuffled_vector.push(j);
        }

        return shuffled_vector
    }

}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn anonymity_and_shuffle_test() {
        // lets say bob is sending alice 5 tokens
        let balance = 5;

        let value_vector = Transaction::generate_input_shuffle(balance);

        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs

        for x in 0..9 {

            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

            let acc = Account::generate_account(pk);

            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account = Account::update_account(acc, value_vector[x], updated_keys_scalar, comm_scalar);

            account_vector.push(updated_account);

        }

        let shuffled_vector = Transaction::generate_output_shuffle(account_vector.to_owned());

        assert_ne!(account_vector, shuffled_vector)
    }
}