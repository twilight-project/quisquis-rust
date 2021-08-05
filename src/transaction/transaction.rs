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

    /// generate_value_vector creates a value vector
    pub fn generate_value_vector(balance: i64) -> Vec<i64>  {
        // lets define an vector of values, first place will be for sender, then receiver followed by 7 decoy 0 values
        let value_vector: Vec<i64> = vec![-balance, balance, 0, 0, 0, 0, 0, 0, 0];
        return value_vector
    }

    /// generate_output_shuffle generates the second shuffle
    pub fn generate_output_shuffle(mut account_vector: Vec<Account>) -> (Vec<Account>, Vec<usize>)  {

        let size: usize = 9;
        let mut shuffled_vector = Vec::with_capacity(size);
        let mut permutation = Vec::with_capacity(size);

        let mut rng = OsRng;

        for i in 0..size {
            let k = rng.gen_range(i, size);
            let j = account_vector[k];
            permutation[i] = k;
            account_vector[k] = account_vector[i];
            shuffled_vector.push(j);
        }

        return (shuffled_vector, permutation)
    }

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

    pub fn generate_value_and_account_vector(tx_vector: Vec<Sender>) {

        println!("amount {:?}", tx_vector.len());
        
        if tx_vector.len() < 9 {

            let senders_count = tx_vector.iter().count();

            let mut receivers_count = 0;

            let size: usize = 9;
            let mut sender_amount_vector = Vec::new();
            let mut sender_account_vector = Vec::new();
            let mut receiver_amount_vector = Vec::new();
            let mut receiver_account_vector = Vec::new();

            let mut value_vector = Vec::with_capacity(size);
            let mut account_vector = Vec::with_capacity(size);

            for sender in tx_vector.iter() {

                println!("Sender total amount: {:?}", sender.total_amount);

                sender_amount_vector.push(sender.total_amount);
                sender_account_vector.push(sender.account);

                receivers_count += &sender.receivers.iter().count();

                for rec in sender.receivers.iter(){
                    receiver_amount_vector.push(rec.amount);
                    let receiver_account = Account::generate_account(rec.public_key);
                    receiver_account_vector.push(receiver_account);
                    println!("Receiver amount: {:?}", rec.amount);
                }

            }

            if senders_count < 9 && receivers_count < 9 {
                for sender_amount in sender_amount_vector.iter(){
                    value_vector.push(sender_amount);
                }

                for receiver_amount in receiver_amount_vector.iter(){
                    value_vector.push(receiver_amount);
                }

                for sender_account in sender_account_vector.iter(){
                    account_vector.push(sender_account);
                }
                
                for receiver_account in receiver_account_vector.iter(){
                    account_vector.push(receiver_account);
                }
                
                println!("Sender count = {:?}", senders_count);
                println!("Receiver count = {:?}", receivers_count);
                println!("Sender vector = {:?}", sender_amount_vector);
                println!("Receiver vector = {:?}", receiver_amount_vector);
                println!("Value vector = {:?}", value_vector);
                println!("Account vector = {:?}", account_vector);
            }
        }
    }

}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;

    fn test_generate_account(amount: i64) -> Account{
        let mut rng = rand::thread_rng();
        let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

        let acc = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account = Account::update_account(acc, amount, updated_keys_scalar, comm_scalar);
        
        return updated_account
    }

    #[test]
    fn anonymity_and_shuffle_test() {
        // lets say bob wants to sent 5 tokens to alice from his one account and 2 from his other account to fay
        // and 1 token to jay
        let send_amount_1 = 5; // alice
        let send_amount_2 = 2; // fay
        let send_amount_3 = 1; // jay

        // lets create sender accounts to send these amounts from
        let bob_account_1 = test_generate_account(10);
        let bob_account_2 = test_generate_account(20);

        // lets create receiver accounts
        let alice_account = test_generate_account(10);
        let fay_account = test_generate_account(20);
        let jay_account = test_generate_account(20);

        // so we have 2 senders and 3 receivers, rest will be the anonymity set

        let mut tx_vector: Vec<Sender> = Vec::new();

        // lets manually fill the sender_vector, 
        // tx_vector = vec!(
        //     Send{
        //         account: bob_account_1,
        //         receiver: Receiver{
        //             amount: 5,
        //             receiver: alice_account.pk
        //         }
        //     }, 
        //     Send{
        //         account: bob_account_2,
        //         receiver: Receiver{
        //             amount: 2,
        //             receiver: fay_account.pk
        //         }
        //     },  
        //     Send{
        //         account: bob_account_2,
        //         receiver: Receiver{
        //             amount: 1,
        //             receiver: jay_account.pk
        //         }
        //     }, 
        // );

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

        //println!("{:?}", tx_vector);
        Sender::generate_value_and_account_vector(tx_vector);

        // // lets define an vector of values, first place will be for sender, then receiver followed by 7 decoy 0 values
        // let value_vector: Vec<i64> = Transaction::generate_value_vector();

        // // lets define a vector of accounts
        // let mut account_vector: Vec<Account> = Vec::new();

        // // lets create these accounts and associated keypairs

        // for x in 0..9 {

        //     let mut rng = rand::thread_rng();
        //     let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
        //     let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

        //     let acc = Account::generate_account(pk);

        //     let updated_keys_scalar = Scalar::random(&mut OsRng);

        //     // lets get a random scalar
        //     let comm_scalar = Scalar::random(&mut OsRng);

        //     let updated_account = Account::update_account(acc, value_vector[x], updated_keys_scalar, comm_scalar);

        //     account_vector.push(updated_account);

        // }

        // let shuffled_vector = Transaction::generate_output_shuffle(account_vector.to_owned());

        // assert_ne!(account_vector, shuffled_vector)
    }
}