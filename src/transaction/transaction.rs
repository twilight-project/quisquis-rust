
use crate::{
    keys::{PublicKey},
    accounts::{
        Account,
        Prover,
        Verifier,
        RangeProofProver,
        RangeProofVerifier
    },
    transaction::shuffle::Shuffle,
    ristretto::{RistrettoPublicKey, RistrettoSecretKey}
};
use bulletproofs::r1cs;
use bulletproofs::PedersenGens;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::OsRng;


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

    pub fn generate_value_and_account_vector(tx_vector: Vec<Sender>) -> Result<(Vec<i64>, Vec<Account>, usize, usize, usize), &'static str> {
        
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
                        account_vector.push(Account::generate_random_account_with_value(0).0);
                    }
                }
                
                Ok((value_vector, account_vector, diff, senders_count,receivers_count))
            }else{
                Err("senders and receivers count should be less than 9")
            }
        }else{
            Err("account count is more than 9")
        }

    }

    // create_transaction creates a quisquis transaction
    pub fn create_transaction(value_vector: &Vec<i64>, account_vector: &Vec<Account>, sender_updated_balance: Vec<i64>, sender_sk: &Vec<RistrettoSecretKey>, anonymity_account_diff: usize, senders_count: usize, receivers_count:usize) -> Result<(Vec<Account>, Vec<Account>, Vec<Account>), &'static str> {

        let generate_base_pk = RistrettoPublicKey::generate_base_pk();
        // Prepare the constraint system
        let pc_gens = PedersenGens::default();
        let cs_prover = r1cs::Prover::new(&pc_gens, Transcript::new(b"Rangeproof.r1cs"));
        let mut range_prover = RangeProofProver{
            prover: cs_prover,
        };
        
        // Initialise the Verifier `ConstraintSystem` instance representing a merge gadget
        let cs_verifier = r1cs::Verifier::new(Transcript::new(b"Rangeproof.r1cs"));
        let mut range_verifier = RangeProofVerifier{
            verifier: cs_verifier,
        };
        //1. update & shuffle accounts
        let first_shuffle = Shuffle::input_shuffle(&account_vector);
        let updated_accounts = first_shuffle.unwrap().get_outputs_vector();

        //2. create delta_and_epsilon_accounts
        let (delta_accounts, epsilon_accounts, delta_rscalar) = Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, generate_base_pk);

        // generate proofs dleq proof
        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(&delta_accounts, &epsilon_accounts, &delta_rscalar, &delta_rscalar, value_vector);

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
                //generate Sender account proof of remaining balance and signature on sk
                //Create slice of Updated delta accounts of sender
               let updated_delta_account_sender = &updated_delta_accounts.as_ref().unwrap()[0..senders_count];
               //let delta_unwraped = updated_delta_accounts.unwrap();
               //let updated_delta_account_sender: Vec<Account> = vec!(delta_unwraped[0], delta_unwraped[1]);
                //create new sender epsilon accounts
                let mut epsilon_account_vec: Vec<Account> = Vec::new();
                let mut rscalar_sender: Vec<Scalar> = Vec::new();
        
                for i in 0..senders_count{
                    // lets create an epsilon account with the new balance
                    let rscalar = Scalar::random(&mut OsRng);
                    rscalar_sender.push(rscalar);
                    // lets first create a new epsilon account using the passed balance
                    let epsilon_account: Account = Account::create_epsilon_account(generate_base_pk, rscalar, sender_updated_balance[i]);
                    epsilon_account_vec.push(epsilon_account);
                }
                let (zv, zsk, zr, x) = Prover::verify_account_prover(&updated_delta_account_sender.to_vec(), &epsilon_account_vec, sender_updated_balance, sender_sk, rscalar_sender, &mut range_prover);
                
              //  println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
                println!("{:?}", x);
                //verify sender account signature and remaining balance. Rangeproof R1CS is updated
                let verify_sender_account_proof = Verifier::verify_account_verifier(&updated_delta_account_sender.to_vec(), &epsilon_account_vec, generate_base_pk, zv, zsk, zr, x, &mut range_verifier);
                
                //Preparation for Non negative proof
                let reciever_epsilon_accounts_slice = &epsilon_accounts[senders_count..(senders_count+receivers_count)];
                let reciever_rscalars_slice = &delta_rscalar[senders_count..(senders_count+receivers_count)];
               //balance vector for receivers 
                let receiver_bl = &value_vector[senders_count..(senders_count+receivers_count)];

                //Create nonnegative proof on receiver accounts. Zero balance receiver accounts are created by the sender. Pass +bl as balance and the rscalar for creating the commitment
                Prover::verify_non_negative_prover(&reciever_epsilon_accounts_slice.to_vec(), receiver_bl.to_vec(), reciever_rscalars_slice.to_vec(), &mut range_prover);
                //Generate range proof over sender account values. 
                //Should be called after adding all values (sender+receiver) to the R1CS transcript
                let range_proof = range_prover.build_proof();   

                //add nonnegative verification to RangeProofVerifier
                Verifier::verify_non_negative_verifier(&reciever_epsilon_accounts_slice.to_vec(),&mut range_verifier );
                //Verify r1cs rangeproof 
                let bp_check = range_verifier.verify_proof(&range_proof.unwrap(), &pc_gens);
                
                if verify_sender_account_proof == true && bp_check.is_ok(){

                    //Shuffle accounts
                    let second_shuffle = Shuffle::output_shuffle(&updated_delta_accounts.unwrap() );

                    let updated_again_account_vector = second_shuffle.unwrap().get_outputs_vector();

                    Ok((updated_again_account_vector, delta_accounts, epsilon_accounts))
                }else{
                    Err("Sender account proof failed")
                }
            }
            else{
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
        let (bob_account_1, bob_sk_account_1) = Account::generate_random_account_with_value(10);
        let (bob_account_2, bob_sk_account_2) = Account::generate_random_account_with_value(20);

        // lets create receiver accounts
        let alice_account = Account::generate_random_account_with_value(10).0;
        let fay_account = Account::generate_random_account_with_value(20).0;
        let jay_account = Account::generate_random_account_with_value(20).0;

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
        let (value_vector, account_vector, diff, sender_count, receiver_count) = Sender::generate_value_and_account_vector(tx_vector).unwrap();
        //Create sender updated account vector for the verification of sk and bl-v
        let bl_first_sender = 10 - 5;  //bl-v
        let bl_second_sender = 20 - 3;  //bl-v
        let value_vector_sender: Vec<i64> = vec!(bl_first_sender, bl_second_sender);
        //Create vector of sender secret keys
        let sk_sender: Vec<RistrettoSecretKey> = vec!(bob_sk_account_1, bob_sk_account_2);
        let transaction = Sender::create_transaction(&value_vector, &account_vector, value_vector_sender,&sk_sender, diff, sender_count,receiver_count);

        println!("{:?}", transaction);
    }

    #[test]
    fn shuffle_get_test() {
        //use crate::{
          //  transaction::shuffle::{Shuffle}
        //};
        use crate::{
            keys::{PublicKey,SecretKey },
            transaction::shuffle::Shuffle,
            ristretto::{RistrettoPublicKey,RistrettoSecretKey}
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
        println!("{:?}", account_vector);
        let shuffle = {
            Shuffle::input_shuffle(&account_vector)
        };
        let acc = shuffle.unwrap().get_outputs_vector();
        println!("{:?}", acc);

    }
}