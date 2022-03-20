#![allow(non_snake_case)]

use rand::thread_rng;

use crate::accounts::{RangeProofProver, TranscriptProtocol};
use crate::{accounts::Account, ristretto::RistrettoSecretKey};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE, ristretto::CompressedRistretto, scalar::Scalar,
};
use merlin::Transcript;

pub struct Prover<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>,
}

impl<'a> Prover<'a> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Prover {
            transcript,
            scalars: Vec::default(),
        }
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(self) -> (Self, merlin::TranscriptRng) {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.as_bytes());
        }
        let transcript_rng = rng_builder.finalize(&mut thread_rng());
        return (self, transcript_rng);
    }

    /// Allocate and assign a secret variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar) {
        self.transcript.append_scalar_var(label, &assignment);
        self.scalars.push(assignment);
    }

    /// Allocate and assign a public variable with the given `label`.
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: CompressedRistretto) {
        self.transcript.append_point_var(label, &assignment);
    }

    /// Allocate and assign an account with the given `label`.
    pub fn allocate_account(&mut self, label: &'static [u8], account: Account) {
        self.transcript.append_account_var(label, &account);
    }

    /// Allocate a new domain to create another transcript for embedded proof with new `label`.
    pub fn new_domain_sep(&mut self, label: &'static [u8]) {
        self.transcript.domain_sep(label);
    }
    /// Wrapper for getting a challenge in Other modules.
    pub fn get_challenge(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.get_challenge(label)
    }

    // verify_delta_compact_prover generates proves values committed in delta_accounts and epsilon_accounts are the same
    // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-voprf-03#section-5.1
    pub fn verify_delta_compact_prover(
        delta_accounts: &[Account],
        epsilon_accounts: &[Account],
        rscalar1: &[Scalar],
        rscalar2: &[Scalar],
        value_vector: &[Scalar],
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let mut v_dash_vector: Vec<Scalar> = Vec::new();
        let mut r1_dash_vector: Vec<Scalar> = Vec::new();
        let mut r2_dash_vector: Vec<Scalar> = Vec::new();
        let mut v_doubledash_vector: Vec<Scalar> = Vec::new();
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");
        let mut prover = Prover::new(b"DLEQProof", &mut transcript);

        for value in value_vector.iter() {
            v_dash_vector.push(*value);
        }
        prover.scalars = rscalar1
            .iter()
            .cloned()
            .chain(rscalar2.iter().cloned())
            .chain(v_dash_vector.iter().cloned())
            .collect();

        for i in 0..delta_accounts.iter().count() {
            prover.allocate_account(b"delta_account", delta_accounts[i]);
            prover.allocate_account(b"epsilon_account", epsilon_accounts[i]);
        }

        let (mut prover, mut transcript_rng) = prover.prove_impl(); //confirm

        for _ in 0..delta_accounts.iter().count() {
            // Generate and collect three blindings
            r1_dash_vector.push(Scalar::random(&mut transcript_rng));
            r2_dash_vector.push(Scalar::random(&mut transcript_rng));
            v_doubledash_vector.push(Scalar::random(&mut transcript_rng));
        }

        // lets create e_delta
        let e_delta = delta_accounts
            .iter()
            .zip(r1_dash_vector.iter())
            .map(|(d, r1)| d.pk.gr.decompress().unwrap() * r1)
            .collect::<Vec<_>>();

        // lets create f_delta

        let gv_doubledash = v_doubledash_vector
            .iter()
            .map(|vd| &RISTRETTO_BASEPOINT_TABLE * vd)
            .collect::<Vec<_>>();

        let h_delta_r1_dash = delta_accounts
            .iter()
            .zip(r1_dash_vector.iter())
            .map(|(d, r1)| d.pk.grsk.decompress().unwrap() * r1)
            .collect::<Vec<_>>();

        let f_delta = gv_doubledash
            .iter()
            .zip(h_delta_r1_dash.iter())
            .map(|(gv, hd)| gv + hd)
            .collect::<Vec<_>>();
        // lets create e_epsilon
        let e_epsilon = epsilon_accounts
            .iter()
            .zip(r2_dash_vector.iter())
            .map(|(e, r2)| e.pk.gr.decompress().unwrap() * r2)
            .collect::<Vec<_>>();

        // lets create f_epsilon

        let h_epsilon_r2_dash = epsilon_accounts
            .iter()
            .zip(r2_dash_vector.iter())
            .map(|(e, r2)| e.pk.grsk.decompress().unwrap() * r2)
            .collect::<Vec<_>>();

        let f_epsilon = gv_doubledash
            .iter()
            .zip(h_epsilon_r2_dash.iter())
            .map(|(g, h)| g + h)
            .collect::<Vec<_>>();

        for i in 0..delta_accounts.iter().count() {
            // lets append e_delta, f_delta, e_epsilon and f_epsilon to the transcript
            prover.allocate_point(b"e_delta", e_delta[i].compress());
            prover.allocate_point(b"f_delta", f_delta[i].compress());
            prover.allocate_point(b"e_epsilon", e_epsilon[i].compress());
            prover.allocate_point(b"f_epsilon", f_epsilon[i].compress());
        }

        // obtain a scalar challenge
        let x = transcript.get_challenge(b"chal");

        // lets create the outputs

        // lets create zv
        let xv_dash_vector = v_dash_vector
            .iter()
            .map(|v_dash| v_dash * x)
            .collect::<Vec<_>>();

        let zv_vector = v_doubledash_vector
            .iter()
            .zip(xv_dash_vector.iter())
            .map(|(vd, xv_dash)| vd - xv_dash)
            .collect::<Vec<_>>();

        // lets create zr1
        let x_rscalar1_vector = rscalar1.iter().map(|r| r * x).collect::<Vec<_>>();

        let zr1_vector = r1_dash_vector
            .iter()
            .zip(x_rscalar1_vector.iter())
            .map(|(r1, x_r)| r1 - x_r)
            .collect::<Vec<_>>();

        // lets create zr2
        let xr2_vector = rscalar2.iter().map(|r| r * x).collect::<Vec<_>>();

        let zr2_vector = r2_dash_vector
            .iter()
            .zip(xr2_vector.iter())
            .map(|(r2, xr2)| r2 - xr2)
            .collect::<Vec<_>>();

        return (zv_vector, zr1_vector, zr2_vector, x);
    }

    // verify_update_account_prover confirms if anonymity set in delta accounts was updated correctly
    pub fn verify_update_account_prover(
        updated_input_accounts: &[Account],
        updated_delta_accounts: &[Account],
        delta_rscalar: &[Scalar],
    ) -> (Scalar, Vec<Scalar>) {
        // check if (c,d)/c,d) = pkdelta_r
        // lets do c-c and d-d for the commitments in both updated_input and updated_delta account vectors
        let check_delta = updated_input_accounts
            .iter()
            .zip(updated_delta_accounts.iter())
            .map(|(i, d)| Account {
                pk: d.pk,
                comm: d.comm - i.comm,
            })
            .collect::<Vec<_>>();
        // lets create pkdelta_r that is the collection of all delta account pks with r multiplied
        let pkdelta_r = updated_delta_accounts
            .iter()
            .zip(delta_rscalar.iter())
            .map(|(d, r)| d.pk * r)
            .collect::<Vec<_>>();

        // now check if the updated commitments are equal to pkdelta_r, collect them in a vector
        // t(hat is the anonymity set
        let anonymity_set = check_delta
            .iter()
            .enumerate()
            .zip(pkdelta_r.iter())
            .filter(|((_i, cd), pk)| cd.comm.c == pk.gr && cd.comm.d == pk.grsk)
            .collect::<Vec<_>>();

        let anonymity_set_index: Vec<_> = anonymity_set.iter().map(|i| i.0 .0).collect();

        // lets create random scalar s with the transcript
        let mut transcript = Transcript::new(b"VerifyUpdateAcct");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);

        prover.scalars = delta_rscalar.to_vec();

        let (mut prover, mut transcript_rng) = prover.prove_impl(); //confirm

        // Generate a single blinding factor
        let s_scalar = Scalar::random(&mut transcript_rng);

        // lets multiply s_scalar with the g of updated_input and the h of updated_delta accounts
        let updated_input_pk_with_s_scalar = anonymity_set
            .iter()
            .map(|i| i.0 .1.pk * &s_scalar)
            .collect::<Vec<_>>();

        // lets do x <- H(pk_input || pk_output || a)
        // pk_input is in updated_input_accounts
        // pk_output is in updated_delta_accounts
        // a is updated_input_pk_with_s_scalar )
        for i in anonymity_set_index {
            prover.allocate_point(b"inputgr", updated_input_accounts[i].pk.gr);
            prover.allocate_point(b"inputgrsk", updated_input_accounts[i].pk.grsk);
            prover.allocate_point(b"outputgr", updated_delta_accounts[i].pk.gr);
            prover.allocate_point(b"outputgrsk", updated_delta_accounts[i].pk.grsk);
        }

        for pk in updated_input_pk_with_s_scalar.iter() {
            prover.allocate_point(b"commitmentgr", pk.gr);
            prover.allocate_point(b"commitmentgrsk", pk.grsk);
        }

        // obtain a scalar challenge
        let x = transcript.get_challenge(b"chal");

        let mut z_vector: Vec<Scalar> = Vec::new();

        // lets do z = s - xrdelta
        for i in anonymity_set.iter() {
            z_vector.push(s_scalar - (x * delta_rscalar[i.0 .0]));
        }

        return (x, z_vector);
    }

    // verify_account_prover creates a signature for the sender account
    // it proves the sender has secretkey and enough balance using rangeproof
    pub fn verify_account_prover(
        updated_delta_account_sender: &[Account],
        epsilon_account_sender: &[Account],
        bl: &[i64],
        sk: &[RistrettoSecretKey],
        rscalar: &[Scalar],
        rp_prover: &mut RangeProofProver,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        // lets start a transcript and a prover script
        let mut transcript = Transcript::new(b"VerifyAccountProver");
        let mut prover = Prover::new(b"DLEQProof", &mut transcript);

        //adding witness to initialze transcript RNG (Random Number Generator)
        let v_vector: Vec<Scalar> = bl
            .iter()
            .map(|balance| Scalar::from(*balance as u64))
            .collect();
        //for balance in bl {
        //    v_dash_vector.push(SignedInteger::into(SignedInteger::from(balance as u64)));
        //}

        prover.scalars = rscalar
            .iter()
            .cloned()
            .chain(v_vector.iter().cloned())
            .collect();
        //add statement accounts to transcript
        for i in 0..updated_delta_account_sender.iter().count() {
            prover.allocate_account(b"delta_account", updated_delta_account_sender[i]);
            prover.allocate_account(b"epsilon_account", epsilon_account_sender[i]);
        }

        let (mut prover, mut transcript_rng) = prover.prove_impl(); //confirm

        // create random vectors of r_v, r_sk and r_dash
        let rv_vector: Vec<Scalar> = (0..bl.len())
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();
        let rsk_vector: Vec<Scalar> = (0..bl.len())
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();
        let r_dash_vector: Vec<Scalar> = (0..bl.len())
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();

        //let create e_delta = g_delta * r_sk
        let e_delta = updated_delta_account_sender
            .iter()
            .zip(rsk_vector.iter())
            .map(|(updated_account, rsk)| updated_account.pk.gr.decompress().unwrap() * rsk)
            .collect::<Vec<_>>();

        // lets create f_delta = g * r_v + c_delta * r_sk
        let g_rv = epsilon_account_sender
            .iter()
            .zip(rv_vector.iter())
            .map(|(epsilon, rv)| epsilon.pk.gr.decompress().unwrap() * rv)
            .collect::<Vec<_>>();

        let c_rsk = updated_delta_account_sender
            .iter()
            .zip(rsk_vector.iter())
            .map(|(updated_account, rsk)| updated_account.comm.c.decompress().unwrap() * rsk)
            .collect::<Vec<_>>();
        let f_delta = g_rv
            .iter()
            .zip(c_rsk.iter())
            .map(|(grv, crsk)| grv + crsk)
            .collect::<Vec<_>>();

        //let create e_epsilon = g * r_dash
        let e_epsilon = epsilon_account_sender
            .iter()
            .zip(r_dash_vector.iter())
            .map(|(epsilon, rdash)| epsilon.pk.gr.decompress().unwrap() * rdash)
            .collect::<Vec<_>>();

        // lets create f_epsilon = g * r_v + h * r_dash
        let h_rdash = epsilon_account_sender
            .iter()
            .zip(r_dash_vector.iter())
            .map(|(epsilon, rdash)| epsilon.pk.grsk.decompress().unwrap() * rdash)
            .collect::<Vec<_>>();

        let f_epsilon = g_rv
            .iter()
            .zip(h_rdash.iter())
            .map(|(grv, hrdash)| grv + hrdash)
            .collect::<Vec<_>>();

        //adding e,f to transcript
        for (i, e_delta) in e_delta.iter().enumerate() {
            prover.allocate_point(b"e_delta", e_delta.compress());
            prover.allocate_point(b"f_delta", f_delta[i].compress());
            prover.allocate_point(b"e_epsilon", e_epsilon[i].compress());
            prover.allocate_point(b"f_epsilon", f_epsilon[i].compress());
        }
        // obtain a scalar challenge
        let x = transcript.get_challenge(b"challenge");

        // lets create zv = r_v - x * v
        let xv_dash_vector = v_vector.iter().map(|v_dash| v_dash * x).collect::<Vec<_>>();

        let zv_vector = rv_vector
            .iter()
            .zip(xv_dash_vector.iter())
            .map(|(rv, xv_dash)| rv - xv_dash)
            .collect::<Vec<_>>();

        // lets create zsk = r_sk - x * sk
        let x_sk_vector = sk.iter().map(|s| s.0 * x).collect::<Vec<_>>();

        let zsk_vector = rsk_vector
            .iter()
            .zip(x_sk_vector.iter())
            .map(|(rsk, xsk)| rsk - xsk)
            .collect::<Vec<_>>();

        // lets create zr = r_dash - x * rscalar
        let x_rscalar_vector = rscalar.iter().map(|r| r * x).collect::<Vec<_>>();

        let zr_vector = r_dash_vector
            .iter()
            .zip(x_rscalar_vector.iter())
            .map(|(r_dash, x_rscalar)| r_dash - x_rscalar)
            .collect::<Vec<_>>();

        //create RICS constraint based range proof over sneder account value : bl - v > 0
        for (b, r) in bl.iter().zip(rscalar.iter()) {
            //panics in case range proof is not constructed properly
            //println!("bl {:?}", bl[i]);
            if *b >= 0i64 {
                match rp_prover.range_proof_prover(*b as u64, *r) {
                    Ok(_commit) => continue,
                    Err(err) => eprintln!("RangeProof Error! {}", err),
                };
            } else {
                panic!("Receiver balance is negative");
            }
            //println!("res {:?}", res.is_ok());

            //println!("res {:?}", res.unwrap());
        }

        return (zv_vector, zsk_vector, zr_vector, x);
    }
    //verify_non_negative_prover creates range proof on Receiver accounts with zero balance
    pub fn verify_non_negative_prover(
        /*epsilon_account: &Vec<Account>,*/
        bl: &[i64],
        rscalar: &[Scalar],
        rp_prover: &mut RangeProofProver,
    ) {
        for (b, r) in bl.iter().zip(rscalar.iter()) {
            //panics in case range proof is not constructed properly
            //println!("bl {:?}", bl[i]);
            if *b >= 0i64 {
                match rp_prover.range_proof_prover(*b as u64, *r) {
                    Ok(_commit) => continue,
                    Err(err) => eprintln!("RangeProof Error! {}", err),
                };
            } else {
                panic!("Receiver balance is negative");
            }
            //println!("res {:?}", res.is_ok());
            //println!("res {:?}", res.unwrap());
        }
    }
}
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::{
//         accounts::{Account, Prover, RangeProofVerifier, Verifier},
//         keys::{PublicKey, SecretKey},
//         ristretto::{RistrettoPublicKey, RistrettoSecretKey},
//     };
//     use bulletproofs::r1cs;
//     use bulletproofs::{BulletproofGens, PedersenGens};
//     use rand::rngs::OsRng;

//     #[test]
//     fn verify_delta_compact_prover_test() {
//         let generate_base_pk = RistrettoPublicKey::generate_base_pk();

//         let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
//         let mut account_vector: Vec<Account> = Vec::new();

//         for i in 0..9 {
//             let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
//             let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
//             let acc = Account::generate_account(pk);

//             // lets get a random scalar to update the account
//             let updated_keys_scalar = Scalar::random(&mut OsRng);

//             // lets get a random scalar to update the commitments
//             let comm_scalar = Scalar::random(&mut OsRng);

//             let updated_account = Account::update_account(acc, 0, updated_keys_scalar, comm_scalar);

//             account_vector.push(updated_account);
//         }
//         let (delta_accounts, epislon_accounts, rscalar) =
//             Account::create_delta_and_epsilon_accounts(
//                 &account_vector,
//                 &value_vector,
//                 generate_base_pk,
//             );

//         let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(
//             &delta_accounts,
//             &epislon_accounts,
//             &rscalar,
//             &rscalar,
//             &value_vector,
//         );

//         println!("{:?}{:?}{:?}{:?}", zv_vector, zr1_vector, zr2_vector, x);
//     }

//     #[test]
//     fn verify_update_account_prover_test() {
//         let generate_base_pk = RistrettoPublicKey::generate_base_pk();

//         let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
//         let mut updated_accounts: Vec<Account> = Vec::new();

//         for i in 0..9 {
//             let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
//             let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
//             let acc = Account::generate_account(pk);

//             // lets get a random scalar to update the account
//             let updated_keys_scalar = Scalar::random(&mut OsRng);

//             // lets get a random scalar to update the commitments
//             let comm_scalar = Scalar::random(&mut OsRng);

//             let updated_account = Account::update_account(acc, 0, updated_keys_scalar, comm_scalar);

//             updated_accounts.push(updated_account);
//         }

//         let (delta_accounts, _, rscalars) = Account::create_delta_and_epsilon_accounts(
//             &updated_accounts,
//             &value_vector,
//             generate_base_pk,
//         );

//         let updated_delta_accounts =
//             Account::update_delta_accounts(&updated_accounts, &delta_accounts);

//         // sending anonymity set as we know it at this point
//         let updated_accounts_slice = &updated_accounts[2..9];

//         let updated_delta_accounts_slice = &updated_delta_accounts.as_ref().unwrap()[2..9];

//         let rscalars_slice = &rscalars[2..9];

//         let verify_update_proof = Prover::verify_update_account_prover(
//             &updated_accounts_slice.to_vec(),
//             &updated_delta_accounts_slice.to_vec(),
//             &rscalars_slice.to_vec(),
//         );
//         println!("{:?}", verify_update_proof);
//     }

//     #[test]
//     fn verify_account_prover_test() {
//         let base_pk = RistrettoPublicKey::generate_base_pk();

//         let value_vector: Vec<i64> = vec![-5, -3, 5, 3, 0, 0, 0, 0, 0];
//         let mut updated_accounts: Vec<Account> = Vec::new();
//         let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

//         for i in 0..9 {
//             let (updated_account, sk) = Account::generate_random_account_with_value(10);

//             updated_accounts.push(updated_account);

//             // lets save the first and second sk as sender's sk as we discard the rest
//             if i == 0 || i == 1 {
//                 sender_sk.push(sk);
//             }
//         }

//         let (delta_accounts, _, _) =
//             Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

//         let updated_delta_accounts =
//             Account::update_delta_accounts(&updated_accounts, &delta_accounts);

//         // balance that we want to prove should be sender balance - the balance user is trying to send

//         let bl_first_sender = 10 - 5;
//         let bl_second_sender = 10 - 3;

//         let delta_unwraped = updated_delta_accounts.unwrap();
//         let updated_delta_account_sender: Vec<Account> = vec![delta_unwraped[0], delta_unwraped[1]];
//         //let sender_sk_vector: Vec<Scalar> = vec!(sender_sk[0].0, sender_sk[1].0);
//         let value_vector_sender: Vec<i64> = vec![bl_first_sender, bl_second_sender];

//         let mut epsilon_account_vec: Vec<Account> = Vec::new();
//         let mut rscalar_sender: Vec<Scalar> = Vec::new();

//         for i in 0..value_vector_sender.iter().count() {
//             // lets create an epsilon account with the new balance
//             let rscalar = Scalar::random(&mut OsRng);
//             rscalar_sender.push(rscalar);
//             // lets first create a new epsilon account using the passed balance
//             let epsilon_account: Account =
//                 Account::create_epsilon_account(base_pk, rscalar, value_vector_sender[i]);
//             epsilon_account_vec.push(epsilon_account);
//         }
//         // Prepare the constraint system
//         let pc_gens = PedersenGens::default();
//         let cs = r1cs::Prover::new(&pc_gens, Transcript::new(b"bulletproof.r1cs"));
//         let mut prover = RangeProofProver { prover: cs };
//         let (zv, zsk, zr, x) = Prover::verify_account_prover(
//             &updated_delta_account_sender,
//             &epsilon_account_vec,
//             &value_vector_sender,
//             &sender_sk,
//             &rscalar_sender,
//             &mut prover,
//         );
//         let generate_base_pk = RistrettoPublicKey::generate_base_pk();
//         let cs_verifier = r1cs::Verifier::new(Transcript::new(b"Rangeproof.r1cs"));
//         let mut range_verifier = RangeProofVerifier {
//             verifier: cs_verifier,
//         };
//         println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
//         //verify sender account signature and remaining balance. Rangeproof R1CS is updated
//         let verify_sender_account_proof = Verifier::verify_account_verifier(
//             &updated_delta_account_sender.to_vec(),
//             &epsilon_account_vec,
//             &generate_base_pk,
//             &zv,
//             &zsk,
//             &zr,
//             x,
//             &mut range_verifier,
//         );
//         //let range_proof = prover.build_proof();
//         //println!("{:?}", range_proof);
//         //let (zv, zsk, zr, x) = Prover::verify_delta_compact_prover(&updated_delta_account_sender, &epsilon_account, &sender_sk, &rscalar_sender, &value_vector_sender);
//         println!("Verify {:?}", verify_sender_account_proof);
//         // we need to verify that the sender has enough balance and posesses the sk
//         //let (zv, zsk, zr, x) = Prover::verify_account_prover(updated_delta_accounts.unwrap()[0], generate_base_pk, 5, &sender_sk[0]);
//         //println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
//     }
//}
