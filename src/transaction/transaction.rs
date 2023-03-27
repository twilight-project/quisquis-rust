use crate::shuffle::shuffle::ROWS;
use crate::{
    accounts::{Account, Prover, RangeProofProver, RangeProofVerifier, Verifier},
    keys::PublicKey,
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    shuffle::{Shuffle, ShuffleProof, ShuffleStatement},
};
use bulletproofs::r1cs;
use bulletproofs::r1cs::R1CSProof;
use bulletproofs::{PedersenGens, RangeProof};
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
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
}

impl Transaction {
    // Private constructor
    fn set_transaction(
        input_account_vector: Vec<Account>,
        updated_account_vector: Vec<Account>,
        account_delta_vector: Vec<Account>,
        account_epsilon_vector: Vec<Account>,
        account_updated_delta_vector: Vec<Account>,
        output_account_vector: Vec<Account>,
    ) -> Transaction {
        Transaction {
            input_account_vector: input_account_vector,
            updated_account_vector: updated_account_vector,
            account_delta_vector: account_delta_vector,
            account_epsilon_vector: account_epsilon_vector,
            account_updated_delta_vector: account_updated_delta_vector,
            output_account_vector: output_account_vector,
        }
    }

    /// generate_value_vector creates a value vector
    pub fn generate_value_vector(balance: i64) -> Vec<i64> {
        // lets define an vector of values, first place will be for sender, then receiver followed by 7 decoy 0 values
        let value_vector: Vec<i64> = vec![-balance, balance, 0, 0, 0, 0, 0, 0, 0];
        return value_vector;
    }
}

#[derive(Debug, Clone)]
pub struct Receiver {
    amount: i64,
    public_key: RistrettoPublicKey,
}

#[derive(Debug, Clone)]
pub struct Sender {
    total_amount: i64,
    account: Account,
    receivers: Vec<Receiver>,
}

impl Sender {
    pub fn generate_value_and_account_vector(
        tx_vector: Vec<Sender>,
    ) -> Result<(Vec<i64>, Vec<Account>, Vec<Scalar>, usize, usize, usize), &'static str> {
        if tx_vector.len() < 9 {
            let mut value_vector: Vec<i64> = tx_vector.iter().map(|s| s.total_amount).collect();
            let mut account_vector: Vec<Account> = tx_vector.iter().map(|s| s.account).collect();
            let senders_count: usize = tx_vector.iter().count();
            let mut receivers_count = 0;
            let mut receiver_amount_vector: Vec<i64> = Vec::new();
            let mut receiver_account_vector: Vec<Account> = Vec::new();
            //keep track of all the r used for commitment of value zero
            let mut annonymity_account_commmitment_scalars_vector: Vec<Scalar> = Vec::new();

            for sender in tx_vector.iter() {
                receivers_count += &sender.receivers.iter().count();

                for rec in sender.receivers.iter() {
                    receiver_amount_vector.push(rec.amount);
                    let (receiver_account, _) = Account::generate_account(rec.public_key);
                    receiver_account_vector.push(receiver_account);
                }
            }

            if senders_count < 9 && receivers_count < 9 && senders_count + receivers_count <= 9 {
                value_vector.append(&mut receiver_amount_vector);
                account_vector.append(&mut receiver_account_vector);

                // lets create anonymity set - these are randomly generated on the fly
                // this anonymity set may need to come from the blockchain state itself in the future

                let diff = 9 - (senders_count + receivers_count);
                //use sender key as base pk for annonymity accounts
                let pk_annonymity =
                    PublicKey::update_public_key(&account_vector[0].pk, Scalar::random(&mut OsRng));

                if diff >= 1 {
                    for _ in 0..diff {
                        value_vector.push(0);
                        let (acc, comm_scalar) =
                            Account::generate_account(PublicKey::update_public_key(
                                &pk_annonymity,
                                Scalar::random(&mut OsRng),
                            ));
                        account_vector.push(acc);
                        annonymity_account_commmitment_scalars_vector.push(comm_scalar);
                    }
                }

                Ok((
                    value_vector,
                    account_vector,
                    annonymity_account_commmitment_scalars_vector,
                    diff,
                    senders_count,
                    receivers_count,
                ))
            } else {
                Err("senders and receivers count should be less than 9")
            }
        } else {
            Err("account count is more than 9")
        }
    }
    
    

    //create_transaction creates a quisquis transaction using R1CS constraints for rangeproof
    pub fn create_transaction(
        value_vector: &[i64],
        account_vector: &[Account],
        sender_updated_balance: &[u64],
        sender_sk: &[RistrettoSecretKey],
        anonymity_comm_scalar: &[Scalar],
        anonymity_account_diff: usize,
        senders_count: usize,
        receivers_count: usize,
    ) -> Result<
        (
            Transaction,
            R1CSProof,
            ShuffleProof,
            ShuffleStatement,
            ShuffleProof,
            ShuffleStatement,
        ),
        &'static str,
    > {
        //convert the valur vector into scalar type to be used in the prover
        let mut value_vector_scalar = Vec::<Scalar>::new();
        for v in value_vector.iter() {
            if v >= &0 {
                value_vector_scalar.push(Scalar::from(*v as u64));
            } else {
                value_vector_scalar.push(-Scalar::from(*v as u64));
            }
        }
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();
        //Step 1. update & shuffle input accounts
        let input_shuffle = Shuffle::input_shuffle(account_vector)?;
        let updated_accounts = input_shuffle.get_outputs_vector();
        //Step 2. create proof for shuffle
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        // Prepare the constraint system
        let pc_gens = PedersenGens::default();
        //create shuffle Prover merlin transcript
        let mut transcript_prover = Transcript::new(b"QuisQuisProof");
        let mut qq_prover = Prover::new(b"QuisQuis", &mut transcript_prover);
        //input shuffle proof
        let (input_shuffle_proof, input_shuffle_statement) =
            ShuffleProof::create_shuffle_proof(&mut qq_prover, &input_shuffle, &pc_gens, &xpc_gens);
        //test Verify the input shuffle
        //create shuffle Verifier merlin transcript
        let mut transcript_verifier = Transcript::new(b"QuisQuisProof");
        let mut qq_verifier = Verifier::new(b"QuisQuis", &mut transcript_verifier);
        input_shuffle_proof.verify(
            &mut qq_verifier,
            &input_shuffle_statement,
            &input_shuffle.get_inputs_vector(),
            &updated_accounts,
            &pc_gens,
            &xpc_gens,
        )?;

        //Step 3. create delta_and_epsilon_accounts
        let (delta_accounts, epsilon_accounts, delta_rscalar) =
            Account::create_delta_and_epsilon_accounts(
                &updated_accounts,
                &value_vector_scalar,
                generate_base_pk,
            );
        //Step 4. generate DLEQ proof based on Epsilon and delta account
        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(
            &delta_accounts,
            &epsilon_accounts,
            &delta_rscalar,
            &value_vector_scalar,
            &mut qq_prover,
        )
        .get_dleq();
        //identity check function to verify the construction of epsilon accounts using correct rscalars
        Verifier::verify_delta_identity_check(&epsilon_accounts)?;

        // verify dleq proof
        Verifier::verify_delta_compact_verifier(
            &delta_accounts,
            &epsilon_accounts,
            &zv_vector,
            &zr1_vector,
            &zr2_vector,
            &x,
            &mut qq_verifier,
        )?;

        //Step 5. update delta_accounts
        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts)?;
        //println!("");
        //println!("update_delta_accounts");
        //for x in 0..9 {
        //    println!("{:?}", updated_delta_accounts[x]);
        //}
        // sending anonymity set as we know it at this point
        // lets say we have sender+receier = 5
        // the difference we have is => 9 - 5 = 4
        // if we have add one to the 4, that will start the slice range from 5..9
        let anonymity_index = anonymity_account_diff + 1;
        let updated_accounts_slice = &updated_accounts[anonymity_index..9];
        // println!("updated_accounts_slice");
        //for x in updated_accounts_slice.iter() {
        //   println!("{:?}", x);
        //}
        let updated_delta_accounts_slice = &updated_delta_accounts[anonymity_index..9];
        let rscalars_slice = &delta_rscalar[anonymity_index..9];

        //Step 6. generate proofs DLOG proof on Anonymity accounts in Updated Delta accounts
        let (z_vector, x) = Prover::verify_update_account_prover(
            &updated_accounts_slice,
            &updated_delta_accounts_slice,
            &rscalars_slice,
            &mut qq_prover,
        )
        .get_dlog();
        //verify dlog proof
        let _verify_update_account_proof = Verifier::verify_update_account_verifier(
            &updated_accounts_slice,
            &updated_delta_accounts_slice,
            &z_vector,
            &x,
            &mut qq_verifier,
        )?;

        //Step 7. if annoymity accounts are created on the fly.
        //create zero balance proof for all the anonymity accounts
        let (z_zero_balance, x_zero_balance) = Prover::zero_balance_account_prover(
            &account_vector[anonymity_index..9],
            &anonymity_comm_scalar,
            &mut qq_prover,
        )
        .get_dlog();

        //verify zero balance proof for anonymity set
        Verifier::zero_balance_account_verifier(
            &account_vector[anonymity_index..9],
            &z_zero_balance,
            x_zero_balance,
            &mut qq_verifier,
        )?;

        //Step 8. generate Sender account proof of remaining balance and signature on sk
        //Create slice of Updated delta accounts of sender
        let updated_delta_account_sender = &updated_delta_accounts[0..senders_count];

        //create new sender epsilon accounts
        let mut epsilon_account_vec: Vec<Account> = Vec::new();
        let mut rscalar_sender: Vec<Scalar> = Vec::new();
        // println!("Senders count{:?}", senders_count);
        for i in 0..senders_count {
            // lets create an epsilon account with the new balance
            let rscalar = Scalar::random(&mut OsRng);
            rscalar_sender.push(rscalar);
            // lets first create a new epsilon account using the passed balance
            let epsilon_account: Account = Account::create_epsilon_account(
                generate_base_pk,
                rscalar,
                sender_updated_balance[i] as i64,
            );
            epsilon_account_vec.push(epsilon_account);
        } // Initialise the Prover `ConstraintSystem` instance representing a merge gadget
        let cs_prover = r1cs::Prover::new(&pc_gens, Transcript::new(b"Rangeproof.r1cs"));
        let mut range_prover = RangeProofProver { prover: cs_prover };

        /* let (zv, zsk, zr, x) = Prover::verify_account_prover(
            &updated_delta_account_sender,
            &epsilon_account_vec,
            &sender_updated_balance,
            sender_sk,
            &rscalar_sender,
            &mut range_prover,
            &mut qq_prover,
        );*/
        // Initialise the Verifier `ConstraintSystem` instance representing a merge gadget
        let cs_verifier = r1cs::Verifier::new(Transcript::new(b"Rangeproof.r1cs"));
        let mut range_verifier = RangeProofVerifier {
            verifier: cs_verifier,
        };

        // if verify_delta_compact_proof == true {
        //println!("Account update proof {:?}", verify_update_account_proof);

        // if verify_update_account_proof == true {

        // println!("zv {:?},  zsk {:?}, zr {:?}", zv, zsk, zr);
        // println!("X = {:?}", x);
        //Preparation for Non negative proof i.e, Rangeproof on reciever accaounts -> bl >= 0
        //balance vector for receivers
        let receiver_bl = &value_vector[senders_count..(senders_count + receivers_count)];
        let reciever_rscalars_slice =
            &delta_rscalar[senders_count..(senders_count + receivers_count)];
        //Create nonnegative proof on receiver accounts. Zero balance receiver accounts are created by the sender.
        //Pass +bl as balance and the rscalar for creating the commitment
        Prover::verify_non_negative_prover(
            &receiver_bl,
            &reciever_rscalars_slice,
            &mut range_prover,
        );
        //Generate range proof over sender/reciever account values. i.,e balance >=0 for all
        //Should be called after adding all values (sender+receiver) to the R1CS transcript
        let range_proof = range_prover.build_proof().unwrap();
        //verify sender account signature and remaining balance. Rangeproof R1CS is updated
        // Verifier::verify_account_verifier(
        //     &updated_delta_account_sender,
        //     &epsilon_account_vec,
        //     &generate_base_pk,
        //     &zv,
        //     &zsk,
        //     &zr,
        //     x,
        //     &mut range_verifier,
        //     &mut qq_verifier,
        // )?;
        //Prepare for rangeproof verification
        let reciever_epsilon_accounts_slice =
            &epsilon_accounts[senders_count..(senders_count + receivers_count)];

        //add reciever nonnegative verification to RangeProofVerifier
        let non_negative_verify = Verifier::verify_non_negative_verifier(
            &reciever_epsilon_accounts_slice,
            &mut range_verifier,
        );
        //? operator does not work because the function throws R1CS error
        //Handling error explicitly
        if non_negative_verify.is_err() {
            return Err("Range proof verify: Failed");
        }

        //Verify r1cs rangeproof
        let bp_check = range_verifier.verify_proof(&range_proof, &pc_gens);
        if bp_check.is_err() {
            return Err("Range Proof verification failed");
        }
        println!("Rangeverifier {:?}", bp_check);

        if bp_check.is_ok() {
            //Shuffle accounts
            let output_shuffle = Shuffle::output_shuffle(&updated_delta_accounts)?;
            let updated_again_account_vector = output_shuffle.get_outputs_vector();
            //Create shuffle proof for output shuffle
            //create new shuffle transcript
            let mut transcript_output_shuffle_prover = Transcript::new(b"OutputShuffleProof");
            let mut output_shuffle_prover =
                Prover::new(b"Shuffle", &mut transcript_output_shuffle_prover);
            let (output_shuffle_proof, output_shuffle_statement) =
                ShuffleProof::create_shuffle_proof(
                    &mut output_shuffle_prover,
                    &output_shuffle,
                    &pc_gens,
                    &xpc_gens,
                );
            //Verify shuffle proof
            let mut transcript_output_shuffle_verifier = Transcript::new(b"OutputShuffleProof");
            let mut output_shuffle_verifier =
                Verifier::new(b"Shuffle", &mut transcript_output_shuffle_verifier);
            output_shuffle_proof.verify(
                &mut output_shuffle_verifier,
                &output_shuffle_statement,
                &output_shuffle.get_inputs_vector(),
                &updated_again_account_vector,
                &pc_gens,
                &xpc_gens,
            )?;

            // create transaction struct
            let tx = Transaction::set_transaction(
                input_shuffle.get_inputs_vector(),
                updated_accounts,
                delta_accounts,
                epsilon_accounts,
                updated_delta_accounts,
                output_shuffle.get_outputs_vector(),
            );
            Ok((
                tx,
                range_proof,
                input_shuffle_proof,
                input_shuffle_statement,
                output_shuffle_proof,
                output_shuffle_statement,
            ))
        } else {
            Err("Sender account proof failed")
        }
        //} else {
        //  Err("dlog proof failed")
        //}
        //} else {
        //  Err("dleq proof failed")
        //}
    }
    //create_transaction creates a quisquis transaction using bulletproof implementation for rangeproof
    pub fn create_quuisquis_transaction_bulletproof(
        value_vector: &[i64],
        account_vector: &[Account],
        sender_updated_balance: &[u64],
        sender_sk: &[RistrettoSecretKey],
        anonymity_comm_scalar: &[Scalar],
        anonymity_account_diff: usize,
        reciver_updated_balance: &[u64],
        senders_count: usize,
        receivers_count: usize,
    ) -> Result<
        (
            Transaction,
            Vec<RangeProof>,
            ShuffleProof,
            ShuffleStatement,
            ShuffleProof,
            ShuffleStatement,
        ),
        &'static str,
    > {
        //convert the valur vector into scalar type to be used in the prover
        let mut value_vector_scalar = Vec::<Scalar>::new();
        for v in value_vector.iter() {
            if v >= &0 {
                value_vector_scalar.push(Scalar::from(*v as u64));
            } else {
                value_vector_scalar.push(-Scalar::from((-*v) as u64));
            }
        }
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();
        //Step 1. update & shuffle input accounts
        let input_shuffle = Shuffle::input_shuffle(account_vector)?;
        let updated_accounts = input_shuffle.get_outputs_vector();
        //Step 2. create proof for shuffle
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        // Prepare the constraint system
        let pc_gens = PedersenGens::default();
        //create shuffle Prover merlin transcript
        let mut transcript_prover = Transcript::new(b"QuisQuisProof");
        let mut qq_prover = Prover::new(b"QuisQuis", &mut transcript_prover);
        //input shuffle proof
        let (input_shuffle_proof, input_shuffle_statement) =
            ShuffleProof::create_shuffle_proof(&mut qq_prover, &input_shuffle, &pc_gens, &xpc_gens);

        //test Verify the input shuffle
        //create shuffle Verifier merlin transcript
        let mut transcript_verifier = Transcript::new(b"QuisQuisProof");
        let mut qq_verifier = Verifier::new(b"QuisQuis", &mut transcript_verifier);
        input_shuffle_proof.verify(
            &mut qq_verifier,
            &input_shuffle_statement,
            &input_shuffle.get_inputs_vector(),
            &updated_accounts,
            &pc_gens,
            &xpc_gens,
        )?;
        //Step 3. create delta_and_epsilon_accounts
        let (delta_accounts, epsilon_accounts, delta_rscalar) =
            Account::create_delta_and_epsilon_accounts(
                &updated_accounts,
                &value_vector_scalar,
                generate_base_pk,
            );

        //Step 4. generate DLEQ proof for same balance value committed based on Epsilon and delta account
        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(
            &delta_accounts,
            &epsilon_accounts,
            &delta_rscalar,
            &value_vector_scalar,
            &mut qq_prover,
        )
        .get_dleq();
        //identity check function to verify the construction of epsilon accounts using correct rscalars
        Verifier::verify_delta_identity_check(&epsilon_accounts)?;

        // verify dleq proof
        Verifier::verify_delta_compact_verifier(
            &delta_accounts,
            &epsilon_accounts,
            &zv_vector,
            &zr1_vector,
            &zr2_vector,
            &x,
            &mut qq_verifier,
        )?;

        //Step 5. update delta_accounts
        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts)?;
        // sending anonymity set as we know it at this point
        // lets say we have sender+receier = 5
        // num_anonymity_accounts => 9 - 5 = 4
        // anonymity_index = 9 - num_anonymity_accounts
        let anonymity_index = 9 - anonymity_account_diff;
        let updated_accounts_slice = &updated_accounts[anonymity_index..9];
        let updated_delta_accounts_slice = &updated_delta_accounts[anonymity_index..9];
        let rscalars_slice = &delta_rscalar[anonymity_index..9];

        //Step 6. generate proofs DLOG proof on Anonymity accounts in Updated Delta accounts
        let (z_vector, x) = Prover::verify_update_account_prover(
            &updated_accounts_slice,
            &updated_delta_accounts_slice,
            &rscalars_slice,
            &mut qq_prover,
        )
        .get_dlog();
        //verify dlog proof
        let _verify_update_account_proof = Verifier::verify_update_account_verifier(
            &updated_accounts_slice,
            &updated_delta_accounts_slice,
            &z_vector,
            &x,
            &mut qq_verifier,
        )?;

        //Step 7. if annoymity accounts are created on the fly.
        //create zero balance proof for all the anonymity accounts
        let (z_zero_balance, x_zero_balance) = Prover::zero_balance_account_prover(
            &account_vector[anonymity_index..9],
            &anonymity_comm_scalar,
            &mut qq_prover,
        )
        .get_dlog();

        //verify zero balance proof for anonymity set
        Verifier::zero_balance_account_verifier(
            &account_vector[anonymity_index..9],
            &z_zero_balance,
            x_zero_balance,
            &mut qq_verifier,
        )?;

        //Step 8. generate Sender account proof of remaining balance and signature on sk
        //Create slice of Updated delta accounts of sender
        let updated_delta_account_sender = &updated_delta_accounts[0..senders_count];

        //println!(" Account{:?}", updated_delta_account_sender);
        // println!("Balance {:?}", sender_updated_balance);
        //println!("sk {:?}", sender_sk);
        let (epsilon_sender_account_vec, epsilon_sender_rscalar_vector, sigma_dleq) =
            Prover::verify_account_prover(
                &updated_delta_account_sender,
                sender_updated_balance,
                sender_sk,
                &mut qq_prover,
                generate_base_pk,
            );
        let (zv_v_acc, zsk_v_acc, zr_v_acc, x_v_acc) = sigma_dleq.get_dleq();
        //verify sender account signature and remaining balance. Rangeproof R1CS is updated
        Verifier::verify_account_verifier_bulletproof(
            &updated_delta_account_sender,
            &epsilon_sender_account_vec,
            &generate_base_pk,
            &zv_v_acc,
            &zsk_v_acc,
            &zr_v_acc,
            x_v_acc,
            &mut qq_verifier,
        )?;

        //create rangeproof on senders and receivers
        //create sender_final + reciver balance vector
        let bl_rp_vector: Vec<u64> = sender_updated_balance
            .into_iter()
            .cloned()
            .chain(reciver_updated_balance.iter().cloned())
            .collect();
        //create rscalar vector for sender and reciver epsilon accounts.
        //extract rscalars for reciever epsilon accounts
        let rec_rscalars_slice = &delta_rscalar[senders_count..senders_count + receivers_count];
        //receiver rscalars are extracted from rscalars vector returned in create_delta_and_epsilon_accounts

        let scalars_bp_vector: Vec<Scalar> = epsilon_sender_rscalar_vector
            .iter()
            .cloned()
            .chain(rec_rscalars_slice.iter().cloned())
            .collect();
        //Generate range proof over sender/reciever account values. i.,e balance >=0 for all
        let range_proof =
            qq_prover.verify_non_negative_sender_reciver_prover(&bl_rp_vector, &scalars_bp_vector);
        //Verify the bulletproofs
        let reciever_epsilon_accounts_slice =
            &epsilon_accounts[senders_count..(senders_count + receivers_count)].to_vec();
        //prepare epsilon account vector for sender + reciver
        let bp_epsilon_vec: Vec<Account> = epsilon_sender_account_vec
            .iter()
            .cloned()
            .chain(reciever_epsilon_accounts_slice.iter().cloned())
            .collect();
        //check if batched or vector proof
        if range_proof.len() == 1 {
            assert!(qq_verifier
                .verify_non_negative_sender_receiver_bulletproof_batch_verifier(
                    &bp_epsilon_vec,
                    &range_proof[0],
                )
                .is_ok())
        } else {
            assert!(qq_verifier
                .verify_non_negative_sender_receiver_bulletproof_vector_verifier(
                    &bp_epsilon_vec,
                    &range_proof,
                )
                .is_ok())
        }

        //Shuffle accounts
        let output_shuffle = Shuffle::output_shuffle(&updated_delta_accounts)?;
        let updated_again_account_vector = output_shuffle.get_outputs_vector();
        //Create shuffle proof for output shuffle
        //create new shuffle transcript
        //let mut transcript_output_shuffle_prover = Transcript::new(b"OutputShuffleProof");
        //let mut output_shuffle_prover =
        //  Prover::new(b"Shuffle", &mut transcript_output_shuffle_prover);
        let (output_shuffle_proof, output_shuffle_statement) = ShuffleProof::create_shuffle_proof(
            &mut qq_prover,
            &output_shuffle,
            &pc_gens,
            &xpc_gens,
        );
        //Verify shuffle proof
        //let mut transcript_output_shuffle_verifier = Transcript::new(b"OutputShuffleProof");
        //let mut output_shuffle_verifier =
        //  Verifier::new(b"Shuffle", &mut transcript_output_shuffle_verifier);
        output_shuffle_proof.verify(
            &mut qq_verifier,
            &output_shuffle_statement,
            &output_shuffle.get_inputs_vector(),
            &updated_again_account_vector,
            &pc_gens,
            &xpc_gens,
        )?;

        // create transaction struct
        let tx = Transaction::set_transaction(
            input_shuffle.get_inputs_vector(),
            updated_accounts,
            delta_accounts,
            epsilon_accounts,
            updated_delta_accounts,
            output_shuffle.get_outputs_vector(),
        );
        Ok((
            tx,
            range_proof,
            input_shuffle_proof,
            input_shuffle_statement,
            output_shuffle_proof,
            output_shuffle_statement,
        ))
        //  } else {
        //    Err("Sender account proof failed")
        // }
        //} else {
        //  Err("dlog proof failed")
        //}
        //} else {
        //  Err("dleq proof failed")
        //}
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
        let (bob_account_1, bob_sk_account_1) =
            Account::generate_random_account_with_value(10u64.into());
        let (bob_account_2, bob_sk_account_2) =
            Account::generate_random_account_with_value(20u64.into());

        // lets create receiver accounts
        let alice_account = Account::generate_random_account_with_value(10u64.into()).0;
        let fay_account = Account::generate_random_account_with_value(20u64.into()).0;
        let jay_account = Account::generate_random_account_with_value(20u64.into()).0;

        // so we have 2 senders and 3 receivers, rest will be the anonymity set

        //let mut tx_vector: Vec<Sender> = Vec::new();

        let tx_vector: Vec<Sender> = vec![
            Sender {
                total_amount: -5,
                account: bob_account_1,
                receivers: vec![Receiver {
                    amount: 5,
                    public_key: alice_account.pk,
                }],
            },
            Sender {
                total_amount: -3,
                account: bob_account_2,
                receivers: vec![
                    Receiver {
                        amount: 2,
                        public_key: fay_account.pk,
                    },
                    Receiver {
                        amount: 1,
                        public_key: jay_account.pk,
                    },
                ],
            },
        ];
        let (
            value_vector,
            account_vector,
            annonymity_com_scalar_vector,
            diff,
            sender_count,
            receiver_count,
        ) = Sender::generate_value_and_account_vector(tx_vector).unwrap();
        //Create sender updated account vector for the verification of sk and bl-v
        let bl_first_sender = 10 - 5; //bl-v
        let bl_second_sender = 20 - 3; //bl-v
        let updated_balance_sender: Vec<u64> = vec![bl_first_sender, bl_second_sender];
        //Create vector of sender secret keys
        let sk_sender: Vec<RistrettoSecretKey> = vec![bob_sk_account_1, bob_sk_account_2];
        let result = Sender::create_transaction(
            &value_vector,
            &account_vector,
            &updated_balance_sender,
            &sk_sender,
            &annonymity_com_scalar_vector,
            diff,
            sender_count,
            receiver_count,
        );
        // let (
        //     tx,
        //     _range_proof,
        //     _input_shuf_proof,
        //     _input_shuffle_statement,
        //     _out_shuffle_proof,
        //     _out_shuffle_statement,
        // ) = Result.unwrap();
        println!("{:?}", result);
        // assert!(result.is_ok());
    }
    #[test]
    fn create_transaction_bulletproof_batch_test() {
        // lets say bob wants to sent 5 tokens to alice from his one account and
        // and 3 token to jay

        // lets create sender accounts to send these amounts from
        let (bob_account_1, bob_sk_account_1) =
            Account::generate_random_account_with_value(10u64.into());
        // let (bob_account_2, bob_sk_account_2) =
        //   Account::generate_random_account_with_value(20u64.into());
        // lets create receiver accounts
        let (alice_account, alice_account_sk) =
            Account::generate_random_account_with_value(10u64.into());
        //let jay_account = Account::generate_random_account_with_value(20u64.into()).0;

        // so we have 2 senders and 2 receivers, rest will be the anonymity set

        //let mut tx_vector: Vec<Sender> = Vec::new();

        let tx_vector: Vec<Sender> = vec![
            Sender {
                total_amount: -5,
                account: bob_account_1,
                receivers: vec![Receiver {
                    amount: 5,
                    public_key: alice_account.pk,
                }],
            },
            /*Sender {
                total_amount: -3,
                account: bob_account_2,
                receivers: vec![Receiver {
                    amount: 3,
                    public_key: jay_account.pk,
                }],
            },*/
        ];
        let (
            value_vector,
            account_vector,
            annonymity_com_scalar_vector,
            diff,
            sender_count,
            receiver_count,
        ) = Sender::generate_value_and_account_vector(tx_vector).unwrap();
        // println!(
        //   "Value vector {:?} \t diff {:?} \t sender{:?} \t rec {:?} ",
        // value_vector, diff, sender_count, receiver_count,
        //);
        // let b_kacc = account_vector[0].verify_account(&bob_sk_account_1, Scalar::from(10u64));
        // println!("bob_acc   {:?}", b_kacc);

        // let a_kacc = account_vector[1].verify_account(&alice_account_sk, Scalar::from(0u64));
        // println!("alice_acc   {:?}", a_kacc);
        //Create sender updated account vector for the verification of sk and bl-v
        let bl_first_sender = 5u64; //bl-v = 10 -5
        let bl_second_sender = 17u64; //bl-v = 20 - 3
        let updated_balance_sender: Vec<u64> = vec![bl_first_sender /* bl_second_sender*/];
        let updated_balance_receiver: Vec<u64> = vec![5u64];
        //Create vector of sender secret keys
        let sk_sender: Vec<RistrettoSecretKey> = vec![
            bob_sk_account_1,
            /* bob_sk_account_2*/
        ];
        let result = Sender::create_quuisquis_transaction_bulletproof(
            &value_vector,
            &account_vector,
            &updated_balance_sender,
            &sk_sender,
            &annonymity_com_scalar_vector,
            diff,
            &updated_balance_receiver,
            sender_count,
            receiver_count,
        );
        // let (
        //     tx,
        //     _range_proof,
        //     _input_shuf_proof,
        //     _input_shuffle_statement,
        //     _out_shuffle_proof,
        //     _out_shuffle_statement,
        // ) = Result.unwrap();
        //println!("{:?}", result);
        assert!(result.is_ok());
    }
    #[test]
    fn create_transaction_bulletproof_vector_test() {
        // lets say bob wants to sent 5 tokens to alice from his one account and 2 from his other account to fay
        // and 1 token to jay

        // lets create sender accounts to send these amounts from
        let (bob_account_1, bob_sk_account_1) =
            Account::generate_random_account_with_value(10u64.into());
        let (bob_account_2, bob_sk_account_2) =
            Account::generate_random_account_with_value(20u64.into());

        // lets create receiver accounts
        let alice_account = Account::generate_random_account_with_value(10u64.into()).0;
        let fay_account = Account::generate_random_account_with_value(20u64.into()).0;
        let jay_account = Account::generate_random_account_with_value(20u64.into()).0;

        // so we have 2 senders and 3 receivers, rest will be the anonymity set

        //let mut tx_vector: Vec<Sender> = Vec::new();

        let tx_vector: Vec<Sender> = vec![
            Sender {
                total_amount: -5,
                account: bob_account_1,
                receivers: vec![Receiver {
                    amount: 5,
                    public_key: alice_account.pk,
                }],
            },
            Sender {
                total_amount: -3,
                account: bob_account_2,
                receivers: vec![
                    Receiver {
                        amount: 2,
                        public_key: fay_account.pk,
                    },
                    Receiver {
                        amount: 1,
                        public_key: jay_account.pk,
                    },
                ],
            },
        ];
        let (
            value_vector,
            account_vector,
            annonymity_com_scalar_vector,
            diff,
            sender_count,
            receiver_count,
        ) = Sender::generate_value_and_account_vector(tx_vector).unwrap();
        //Create sender updated account vector for the verification of sk and bl-v
        let bl_first_sender = 5u64; //bl-v
        let bl_second_sender = 17u64; //bl-v
        let updated_balance_sender: Vec<u64> = vec![bl_first_sender, bl_second_sender];
        //Create vector of sender secret keys
        let sk_sender: Vec<RistrettoSecretKey> = vec![bob_sk_account_1, bob_sk_account_2];
        let updated_balance_receiver: Vec<u64> = vec![5u64, 2u64, 1u64];
        let result = Sender::create_quuisquis_transaction_bulletproof(
            &value_vector,
            &account_vector,
            &updated_balance_sender,
            &sk_sender,
            &annonymity_com_scalar_vector,
            diff,
            &updated_balance_receiver,
            sender_count,
            receiver_count,
        );
        // let (
        //     tx,
        //     _range_proof,
        //     _input_shuf_proof,
        //     _input_shuffle_statement,
        //     _out_shuffle_proof,
        //     _out_shuffle_statement,
        // ) = Result.unwrap();
        // println!("{:?}", result);
        assert!(result.is_ok());
    }
    #[test]
    fn shuffle_get_test() {
        //use crate::{
        //  transaction::shuffle::{Shuffle}
        //};
        use crate::{
            keys::{PublicKey, SecretKey},
            ristretto::{RistrettoPublicKey, RistrettoSecretKey},
            shuffle::Shuffle,
        };
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs

        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        println!("{:?}", account_vector);
        let shuffle = { Shuffle::input_shuffle(&account_vector) };
        let acc = shuffle.unwrap().get_outputs_vector();
        println!("{:?}", acc);
    }
}
