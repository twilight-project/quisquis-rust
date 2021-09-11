use curve25519_dalek::{
    scalar::Scalar
};
use crate::{
    keys::{SecretKey, PublicKey},
    accounts::{
        Account,
        Prover,
        Verifier
    },
    transaction::shuffle::Shuffle,
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

    /// generate_value_vector creates a value vector
    pub fn generate_value_vector(balance: i64) -> Vec<i64>  {
        // lets define an vector of values, first place will be for sender, then receiver followed by 7 decoy 0 values
        let value_vector: Vec<i64> = vec![-balance, balance, 0, 0, 0, 0, 0, 0, 0];
        return value_vector
    }

    // generate_output_shuffle generates the second shuffle
    // pub fn generate_output_shuffle(mut account_vector: Vec<Account>) -> (Vec<Account>, Vec<usize>)  {

    //     let size: usize = 9;
    //     let mut shuffled_vector = Vec::with_capacity(size);
    //     let mut permutation = Vec::with_capacity(size);

    //     let mut rng = OsRng;

    //     for i in 0..size {
    //         let k = rng.gen_range(i, size);
    //         let j = account_vector[k];
    //         permutation[i] = k;
    //         account_vector[k] = account_vector[i];
    //         shuffled_vector.push(j);
    //     }

    //     return (shuffled_vector, permutation)
    // }

}

#[derive(Debug, Clone)]
pub struct Receiver {
    amount: i64,
    public_key: RistrettoPublicKey
}

#[derive(Debug, Clone)]
pub struct Sender {
    total_amount: i64,
    account: Account,
    receivers: Vec<Receiver>
}   

impl Sender {

    pub fn generate_value_and_account_vector(tx_vector: Vec<Sender>) -> Result<(Vec<i64>, Vec<Account>, usize), &'static str> {
        
        if tx_vector.len() < 9 {

            let mut value_vector: Vec<i64> = tx_vector.iter().map(|s| s.total_amount).collect();
            let mut account_vector: Vec<Account> = tx_vector.iter().map(|s| s.account).collect();

            let senders_count: usize = tx_vector.iter().count();
            let mut receivers_count = 0;
            let mut receiver_amount_vector: Vec<i64> = Vec::new();
            let mut receiver_account_vector = Vec::new();

            for sender in tx_vector.iter() {

                receivers_count += &sender.receivers.iter().count();

                for rec in sender.receivers.iter(){
                    receiver_amount_vector.push(rec.amount);
                    let receiver_account = Account::generate_account(rec.public_key);
                    receiver_account_vector.push(receiver_account);
                }

            }

            if senders_count < 9 && receivers_count < 9 && senders_count+receivers_count <=9 {

                value_vector.append(&mut receiver_amount_vector);
                account_vector.append(&mut receiver_account_vector);

                // lets create anonymity set - these are randomly generated on the fly
                // note that all these secret keys are made and then destroyed in the process
                // this anonymity set may need to come from the blockchain state itself in the future

                let diff = 9 - (senders_count+receivers_count);

                if diff >= 1 {
                    for _ in 0..diff {
                        value_vector.push(0);
                        account_vector.push(Account::generate_random_account_with_value(0));
                    }
                }
                
                Ok((value_vector, account_vector, diff))
            }else{
                Err("senders and receivers count should be less than 9")
            }
        }else{
            Err("account count is more than 9")
        }

    }

    // create_transaction creates a quisquis transaction
    pub fn create_transaction(value_vector: &Vec<i64>, account_vector: &Vec<Account>, anonymity_account_diff: usize) -> Result<(Vec<Account>, Vec<Account>, Vec<Account>), &'static str> {

        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        //1. update & shuffle accounts
        let first_shuffle = Shuffle::new(&account_vector, 1);
        let updated_accounts = first_shuffle.unwrap().get_outputs_vector();

        //2. create delta_and_epsilon_accounts
        let (delta_accounts, epsilon_accounts, delta_rscalar) = Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, generate_base_pk);

        // generate proofs dleq proof
        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(&delta_accounts, &epsilon_accounts, &delta_rscalar, value_vector);

        // verify dleq proof
        let verify_delta_compact_proof = Verifier::verify_delta_compact_verifier(&delta_accounts, &epsilon_accounts, &zv_vector, &zr1_vector, &zr2_vector, &x);

        if verify_delta_compact_proof == true {

            //3. update delta_accounts
            let updated_delta_accounts = Account::update_delta_accounts(&updated_accounts, &delta_accounts);
            
            // sending anonymity set as we know it at this point
            // lets say we have sender+receier = 5
            // the difference we have is => 9 - 5 = 4
            // if we have add one to the 4, that will start the slice range from 5..9
            let anonymity_index = anonymity_account_diff + 1;
            
            let updated_accounts_slice = &updated_accounts[anonymity_index..9];
            let updated_delta_accounts_slice = &updated_delta_accounts.as_ref().unwrap()[anonymity_index..9];
            let rscalars_slice = &delta_rscalar[anonymity_index..9];

            // generate proofs dlog proof
            let (x, z_vector) = Prover::verify_update_account_prover(&updated_accounts_slice.to_vec(), &updated_delta_accounts_slice.to_vec(), &rscalars_slice.to_vec());

            let verify_update_account_proof = Verifier::verify_update_account_verifier(&updated_accounts_slice.to_vec(), &updated_delta_accounts_slice.to_vec(), &z_vector, &x);

            if verify_update_account_proof == true {

                //Shuffle accounts
                let second_shuffle = Shuffle::new(&updated_delta_accounts.unwrap(), 2);

                let updated_again_account_vector = second_shuffle.unwrap().get_outputs_vector();

                Ok((updated_again_account_vector, delta_accounts, epsilon_accounts))
            }else{
                Err("dlog proof failed")
            }
        }else{
            Err("dleq proof failed")
        }
    }

}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn create_transaction_test() {
        // lets say bob wants to sent 5 tokens to alice from his one account and 2 from his other account to fay
        // and 1 token to jay

        // lets create sender accounts to send these amounts from
        let bob_account_1 = Account::generate_random_account_with_value(10);
        let bob_account_2 = Account::generate_random_account_with_value(20);

        // lets create receiver accounts
        let alice_account = Account::generate_random_account_with_value(10);
        let fay_account = Account::generate_random_account_with_value(20);
        let jay_account = Account::generate_random_account_with_value(20);

        // so we have 2 senders and 3 receivers, rest will be the anonymity set

        let mut tx_vector: Vec<Sender> = Vec::new();

        tx_vector = vec!(
            Sender{
                total_amount: 5,
                account: bob_account_1,
                receivers: vec!(Receiver{
                    amount: 5,
                    public_key: alice_account.pk
                    })
            }, 
            Sender{
                total_amount: 3,
                account: bob_account_2,
                receivers: vec!(
                    Receiver{
                    amount: 2,
                    public_key: fay_account.pk
                    }, 
                    Receiver{
                        amount: 1,
                        public_key: jay_account.pk
                    }
                )
            }
        );

        let (value_vector, account_vector, diff) = Sender::generate_value_and_account_vector(tx_vector).unwrap();

        // let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
        // let mut account_vector: Vec<Account> = Vec::new();

        // for i in 0..9 {

        //     let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        //     let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
    
        //     let acc = Account::generate_account(pk);
        //     account_vector.push(acc);
        // }

        let transaction = Sender::create_transaction(&value_vector, &account_vector, diff);

        println!("{:?}", transaction);
    }

    #[test]
    fn shuffle_get_test() {
        use crate::{
            transaction::shuffle::{Shuffle}
        };
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();
 
        // lets create these accounts and associated keypairs

        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);

        }
        let shuffle = {
            Shuffle::new(&account_vector,1)
        };
        let acc = shuffle.unwrap().get_inputs_vector();
        println!("{:?}", acc);

    }
}