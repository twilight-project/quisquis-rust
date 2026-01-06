//! Prover logic for Quisquis protocol zero-knowledge proofs.
//!
//! This module provides the [`Prover`] struct and related proof-generation logic for
//! account updates, range proofs, and various sigma protocols in the Quisquis protocol.

#![allow(non_snake_case)]

use crate::accounts::{RangeProofProver, TranscriptProtocol};
use crate::{accounts::Account, ristretto::RistrettoPublicKey, ristretto::RistrettoSecretKey};
//use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use merlin::Transcript;
use rand::thread_rng;
// use serde::{Deserialize, Serialize};
use serde::{Deserialize, Serialize};
/// Enum for representing different types of sigma proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SigmaProof {
    /// Discrete logarithm proof.
    Dlog(Vec<Scalar>, Scalar),
    /// Discrete log equality proof.
    Dleq(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar),
}

impl SigmaProof {
    /// Extracts the DLOG proof components.
    ///
    pub fn get_dlog(self) -> (Vec<Scalar>, Scalar) {
        match self {
            SigmaProof::Dlog(x, y) => (x, y),
            _ => panic!("Not a DLOG sigma proof"),
        }
    }
    /// Extracts the DLEQ proof components.
    ///     
    pub fn get_dleq(self) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        match self {
            SigmaProof::Dleq(a, b, c, d) => (a, b, c, d),
            _ => panic!("Not a DLEQ sigma proof"),
        }
    }
}
/// Prover for Quisquis protocol zero-knowledge proofs.
///
/// This struct manages the transcript and witness data for proof generation.
pub struct Prover<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>,
}

impl<'a> Prover<'a> {
    /// Construct a new prover.  The `proof_label` disambiguates proof statements.
    ///     
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Prover {
            transcript,
            scalars: Vec::default(),
        }
    }

    /// Internal: Build a transcript RNG using the current witness scalars.
    fn prove_impl(&self) -> merlin::TranscriptRng {
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.as_bytes());
        }
        rng_builder.finalize(&mut thread_rng())
    }

    /// Build a transcript RNG using a custom set of witness scalars.
    pub fn prove_rekey_witness_transcript_rng(&self, scalars: &[Scalar]) -> merlin::TranscriptRng {
        let mut rng_builder = self.transcript.build_rng();
        for scalar in scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.as_bytes());
        }
        rng_builder.finalize(&mut thread_rng())
    }

    /// Allocate and assign a secret scalar variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: &Scalar) {
        self.transcript.append_scalar_var(label, assignment);
        self.scalars.push(*assignment);
    }

    /// Allocate and assign a public point variable with the given `label`.
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: &CompressedRistretto) {
        self.transcript.append_point_var(label, assignment);
    }

    /// Allocate and assign an account with the given `label`.
    pub fn allocate_account(&mut self, label: &'static [u8], account: &Account) {
        self.transcript.append_account_var(label, account);
    }

    /// Allocate a new domain to create another transcript for embedded proof with new `label`.
    pub fn new_domain_sep(&mut self, label: &'static [u8]) {
        self.transcript.domain_sep(label);
    }

    /// Wrapper for getting a challenge in other modules.
    pub fn get_challenge(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.get_challenge(label)
    }

    /// verify_delta_compact_prover generates proves values committed in delta_accounts and epsilon_accounts are the same
    /// <https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-voprf-03#section-5.1>
    ///
    /// # Arguments
    /// * `delta_accounts` - The delta accounts.
    /// * `epsilon_accounts` - The epsilon accounts.
    /// * `rscalar` - The rscalars used for the delta accounts.
    /// * `value_vector` - The values committed in the delta accounts.
    /// * `prover` - The prover.
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn verify_delta_compact_prover(
        delta_accounts: &[Account],
        epsilon_accounts: &[Account],
        rscalar: &[Scalar],
        value_vector: &[Scalar],
        prover: &mut Prover,
    ) -> SigmaProof {
        //lenghts of both delta and epsilon account slices should be same.
        assert_eq!(delta_accounts.len(), epsilon_accounts.len());

        //let mut v_dash_vector: Vec<Scalar> = Vec::new();
        let mut r1_dash_vector: Vec<Scalar> = Vec::new();
        let mut r2_dash_vector: Vec<Scalar> = Vec::new();
        let mut v_doubledash_vector: Vec<Scalar> = Vec::new();
        //Create new transcript
        prover.new_domain_sep(b"VerifyDeltaCompact");
        //let mut transcript = Transcript::new(b"VerifyDeltaCompact");
        //let mut prover = Prover::new(b"DLEQProof", &mut transcript);

        //for value in value_vector.iter() {
        //  v_dash_vector.push(*value);
        //}
        prover.scalars = rscalar
            .iter()
            .cloned()
            //.chain(rscalar2.iter().cloned())
            .chain(value_vector.iter().cloned())
            .collect();

        for (delta, epsilon) in delta_accounts.iter().zip(epsilon_accounts.iter()) {
            prover.allocate_account(b"delta_account", delta);
            prover.allocate_account(b"epsilon_account", epsilon);
        }

        let mut transcript_rng = prover.prove_impl(); //confirm

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
            .map(|vd| RistrettoPoint::mul_base(vd))
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
            prover.allocate_point(b"e_delta", &e_delta[i].compress());
            prover.allocate_point(b"f_delta", &f_delta[i].compress());
            prover.allocate_point(b"e_epsilon", &e_epsilon[i].compress());
            prover.allocate_point(b"f_epsilon", &f_epsilon[i].compress());
        }

        // obtain a scalar challenge
        //let x = transcript.get_challenge(b"chal");
        let x = prover.get_challenge(b"challenge");
        // lets create the outputs

        // lets create zv
        let xv_dash_vector = value_vector
            .iter()
            .map(|v_dash| v_dash * x)
            .collect::<Vec<_>>();

        let zv_vector = v_doubledash_vector
            .iter()
            .zip(xv_dash_vector.iter())
            .map(|(vd, xv_dash)| vd - xv_dash)
            .collect::<Vec<_>>();

        // lets create zr1
        let x_rscalar_vector = rscalar.iter().map(|r| r * x).collect::<Vec<_>>();

        let zr1_vector = r1_dash_vector
            .iter()
            .zip(x_rscalar_vector.iter())
            .map(|(r1, x_r)| r1 - x_r)
            .collect::<Vec<_>>();

        // lets create zr2
        // let xr2_vector = x_rscalar1_vector.cloned(); //rscalar.iter().map(|r| r * x).collect::<Vec<_>>();
        //using the same xr_scalar_vector again
        let zr2_vector = r2_dash_vector
            .iter()
            .zip(x_rscalar_vector.iter())
            .map(|(r2, xr2)| r2 - xr2)
            .collect::<Vec<_>>();

        return SigmaProof::Dleq(zv_vector, zr1_vector, zr2_vector, x);
    }

    /// verify_update_account_prover confirms if anonymity set in delta accounts was updated correctly
    ///
    /// # Arguments
    /// * `updated_input_accounts` - The updated input accounts.
    /// * `updated_delta_accounts` - The updated delta accounts.
    /// * `delta_rscalar` - The rscalars used for the delta accounts.
    /// * `prover` - The prover.
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn verify_update_account_prover(
        updated_input_accounts: &[Account],
        updated_delta_accounts: &[Account],
        delta_rscalar: &[Scalar],
        prover: &mut Prover,
    ) -> SigmaProof {
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
        // let mut transcript = Transcript::new(b"VerifyUpdateAcct");
        // let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        prover.new_domain_sep(b"DLOGProof");
        prover.scalars = delta_rscalar.to_vec();

        let mut transcript_rng = prover.prove_impl(); //confirm

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
            prover.allocate_point(b"inputgr", &updated_input_accounts[i].pk.gr);
            prover.allocate_point(b"inputgrsk", &updated_input_accounts[i].pk.grsk);
            prover.allocate_point(b"outputgr", &updated_delta_accounts[i].pk.gr);
            prover.allocate_point(b"outputgrsk", &updated_delta_accounts[i].pk.grsk);
        }

        for pk in updated_input_pk_with_s_scalar.iter() {
            prover.allocate_point(b"commitmentgr", &pk.gr);
            prover.allocate_point(b"commitmentgrsk", &pk.grsk);
        }

        // obtain a scalar challenge
        let x = prover.get_challenge(b"chal");

        let mut z_vector: Vec<Scalar> = Vec::new();

        // lets do z = s - xrdelta
        for i in anonymity_set.iter() {
            z_vector.push(s_scalar - (x * delta_rscalar[i.0 .0]));
        }

        return SigmaProof::Dlog(z_vector, x);
    }

    /// verify_account_prover creates a signature for the sender account
    /// it proves the sender has secretkey and enough balance after updation to make the transfer using rangeproof
    ///
    /// # Arguments
    /// * `updated_delta_account_sender` - The updated delta accounts for the sender.
    /// * `bl_updated_sender` - The balances for the sender.
    /// * `sk` - The secret keys for the sender.
    /// * `prover` - The prover.
    /// * `base_pk` - The base public key.
    /// # Returns
    /// A tuple containing the epsilon accounts, the rscalars used for creating the epsilon accounts, and the sigma proof.
    pub fn verify_account_prover(
        updated_delta_account_sender: &[Account],
        bl_updated_sender: &[u64],
        sk: &[RistrettoSecretKey],
        prover: &mut Prover,
        base_pk: RistrettoPublicKey,
    ) -> (
        Vec<Account>, /*Epsilon accounts for Updated sender balance*/
        Vec<Scalar>, /*Rscalars used for creating the epsilon accounts. Will be needed at the time of Rangeproof*/
        SigmaProof,
    ) {
        //check length is same
        assert_eq!(updated_delta_account_sender.len(), bl_updated_sender.len());
        // lets start a transcript and a prover script
        prover.new_domain_sep(b"VerifyAccountProof");
        //adding witness to initialze transcript RNG (Random Number Generator)
        let v_vector: Vec<Scalar> = bl_updated_sender
            .iter()
            .map(|balance| Scalar::from(*balance as u64))
            .collect();

        prover.scalars = v_vector.iter().cloned().collect();

        let mut transcript_rng = prover.prove_impl(); //confirm

        //create epsilon accounts for updated sender balance
        let num_senders = updated_delta_account_sender.len();
        let mut epsilon_account_vector: Vec<Account> = Vec::with_capacity(num_senders);

        let mut epsilon_rscalar_vector: Vec<Scalar> = Vec::with_capacity(num_senders);
        for i in 0..num_senders {
            // lets generate commitment on v for epsilon using GP and r
            let rscalar = Scalar::random(&mut transcript_rng);
            let account_epsilon =
                Account::create_epsilon_account(base_pk, rscalar, bl_updated_sender[i] as i64);
            epsilon_account_vector.push(account_epsilon);
            epsilon_rscalar_vector.push(rscalar);
        }
        //add statement accounts to transcript
        for (delta, epsilon) in updated_delta_account_sender
            .iter()
            .zip(epsilon_account_vector.iter())
        {
            //   println!("c {:?} d {:?}", delta.comm.c, delta.comm.d);
            prover.allocate_account(b"delta_account", delta);
            prover.allocate_account(b"epsilon_account", epsilon);
        }

        // create random vectors of r_v, r_sk and r_dash
        let rv_vector: Vec<Scalar> = (0..num_senders)
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();
        let rsk_vector: Vec<Scalar> = (0..num_senders)
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();
        let r_dash_vector: Vec<Scalar> = (0..num_senders)
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();

        //let create e_delta = g_delta * r_sk
        let e_delta = updated_delta_account_sender
            .iter()
            .zip(rsk_vector.iter())
            .map(|(updated_account, rsk)| updated_account.pk.gr.decompress().unwrap() * rsk)
            .collect::<Vec<_>>();
        // lets create f_delta = g * r_v + c_delta * r_sk
        let g_rv = epsilon_account_vector
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
        let e_epsilon = epsilon_account_vector
            .iter()
            .zip(r_dash_vector.iter())
            .map(|(epsilon, rdash)| epsilon.pk.gr.decompress().unwrap() * rdash)
            .collect::<Vec<_>>();

        // lets create f_epsilon = g * r_v + h * r_dash
        let h_rdash = epsilon_account_vector
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
            // println!("e delta {:?}", e_delta.compress());
            // println!("f delta {:?}", f_delta[i].compress());
            // println!("f epsilon {:?}", e_epsilon[i].compress());
            // println!("f epsilon {:?}", f_epsilon[i].compress());
            prover.allocate_point(b"e_delta", &e_delta.compress());
            prover.allocate_point(b"f_delta", &f_delta[i].compress());
            prover.allocate_point(b"e_epsilon", &e_epsilon[i].compress());
            prover.allocate_point(b"f_epsilon", &f_epsilon[i].compress());
        }
        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");

        // lets create zv = r_v - x * v
        //let xv_dash_vector = v_vector.iter().map(|v_dash| v_dash * x).collect::<Vec<_>>();

        let zv_vector = rv_vector
            .iter()
            .zip(v_vector.iter())
            .map(|(rv, v)| rv - v * x)
            .collect::<Vec<_>>();

        // lets create zsk = r_sk - x * sk
        //let x_sk_vector = sk.iter().map(|s| s.0 * x).collect::<Vec<_>>();

        let zsk_vector = rsk_vector
            .iter()
            .zip(sk.iter())
            .map(|(rsk, sk)| rsk - sk.0 * x)
            .collect::<Vec<_>>();

        // lets create zr = r_dash - x * rscalar
        /* let x_rscalar_vector = epsilon_rscalar_vector
        .iter()
        .map(|r| r * x)
        .collect::<Vec<_>>();*/

        let zr_vector = r_dash_vector
            .iter()
            .zip(epsilon_rscalar_vector.iter())
            .map(|(r_dash, rscalar)| r_dash - rscalar * x)
            .collect::<Vec<_>>();

        return (
            epsilon_account_vector,
            epsilon_rscalar_vector,
            SigmaProof::Dleq(zv_vector, zsk_vector, zr_vector, x),
        );
    }
    /// verify_non_negative_prover creates range proof on Receiver accounts with zero balance
    ///
    /// # Arguments
    /// * `bl` - The balances.
    /// * `rscalar` - The scalars used for commitment.
    /// * `rp_prover` - The range proof prover.
    /// # Returns
    /// A vector of RangeProofs.
    pub fn verify_non_negative_prover(
        /*epsilon_account: &Vec<Account>,*/
        bl: &[i64],
        rscalar: &[Scalar],
        rp_prover: &mut RangeProofProver<Transcript>,
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

    /// verify_non_negative_sender_receiver_prover creates range proof on sender accounts and Receiver accounts with +ve balance
    ///
    /// # Arguments
    /// * `bl` - The balances.
    /// * `rscalar` - The scalars used for commitment.
    /// * `prover` - The prover.
    /// # Returns
    /// A vector of RangeProofs.
    pub fn verify_non_negative_sender_receiver_prover(
        &mut self,
        bl: &[u64],
        rscalar: &[Scalar],
    ) -> Vec<RangeProof> {
        let size = bl.len();

        //check if number of values for range proof are a power of 2
        //if true use batch bulletproof
        let power_of_2 = (size & (size - 1)) == 0;

        // Generators for Pedersen commitments.  These can be selected
        // independently of the Bulletproofs generators.
        let pc_gens = PedersenGens::default();
        let mut proof_vector: Vec<RangeProof> = Vec::new();
        // The proof can be chained to an existing transcript.
        // Here we create a transcript with a doctest domain separator.
        self.new_domain_sep(b"AggregateBulletProof");
        if power_of_2 {
            // Generators for Bulletproofs, valid for proofs up to bitsize 64
            // and aggregation size up to 16.
            let bp_gens = BulletproofGens::new(64, 16);

            //  let mut prover_transcript = Transcript::new(b"doctest example");

            // Create an aggregated 64-bit rangeproof and corresponding commitments.
            let (proof, _) =
                RangeProof::prove_multiple(&bp_gens, &pc_gens, self.transcript, bl, rscalar, 64)
                    .expect("Batch RangeProof creation failed");
            proof_vector.push(proof);
        } else {
            let bp_gens = BulletproofGens::new(64, 1);
            // Create a 64-bit rangeproof for all values.
            for (balance, scalar) in bl.iter().zip(rscalar.iter()) {
                let (proof, _committed_value) = RangeProof::prove_single(
                    &bp_gens,
                    &pc_gens,
                    self.transcript,
                    *balance,
                    scalar,
                    64,
                )
                .expect("RangeProof creation failed");
                proof_vector.push(proof);
            }
        }
        return proof_vector;
    }

    /// zero_balance_account_vector_prover creates a sigma proof for zero
    /// balance commitment of all the random anonymity account
    ///
    /// # Arguments
    /// * `anonymity_accounts` - The anonymity accounts.
    /// * `comm_rscalar` - The scalar used for commitment.
    /// * `prover` - The prover.
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn zero_balance_account_vector_prover(
        anonymity_accounts: &[Account],
        comm_rscalar: &[Scalar],
        prover: &mut Prover,
    ) -> SigmaProof {
        //check length is same
        assert_eq!(anonymity_accounts.len(), comm_rscalar.len());
        // lets start a transcript and a prover script
        //let mut transcript = Transcript::new(b"ZeroBalanceAccountProof");
        //let mut prover = Prover::new(b"DLOGProof", &mut transcript);

        prover.new_domain_sep(b"ZeroBalanceAccountVectorProof");
        //adding witness to initialze transcript RNG (Random Number Generator)
        prover.scalars = comm_rscalar.iter().cloned().collect();
        //add statement accounts to transcript
        for acc in anonymity_accounts {
            prover.allocate_account(b"anonymity_account", acc);
        }

        let mut transcript_rng = prover.prove_impl(); //confirm

        // create random vectors of r,
        let r_vector: Vec<Scalar> = (0..comm_rscalar.len())
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();

        //let create e_i = pk.g ^ r
        let e_i = anonymity_accounts
            .iter()
            .zip(r_vector.iter())
            .map(|(acc, r)| acc.pk.gr.decompress().unwrap() * r)
            .collect::<Vec<_>>();

        //let create f_i = pk.h ^ r
        let f_i = anonymity_accounts
            .iter()
            .zip(r_vector.iter())
            .map(|(acc, r)| acc.pk.grsk.decompress().unwrap() * r)
            .collect::<Vec<_>>();
        //adding e,f to transcript
        for (e, f) in e_i.iter().zip(f_i.iter()) {
            prover.allocate_point(b"e", &e.compress());
            prover.allocate_point(b"f", &f.compress());
        }
        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");

        // lets create z = r - x * comm_scalar
        let x_comm_scalar = comm_rscalar.iter().map(|s| s * x).collect::<Vec<_>>();

        let z_vector = r_vector
            .iter()
            .zip(x_comm_scalar.iter())
            .map(|(r, x_comm)| r - x_comm)
            .collect::<Vec<_>>();

        return SigmaProof::Dlog(z_vector, x);
    }

    /// zero_balance_account_prover creates a sigma proof for zero
    /// balance commitment of all the random anonymity account
    ///
    /// # Arguments
    /// * `account` - The account.
    /// * `comm_rscalar` - The scalar used for commitment.
    /// * `prover` - The prover.
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn zero_balance_account_prover(
        account: Account,
        comm_rscalar: Scalar,
        prover: &mut Prover,
    ) -> SigmaProof {
        prover.new_domain_sep(b"ZeroBalanceAccountProof");
        //adding witness to initialze transcript RNG (Random Number Generator)
        prover.scalars.push(comm_rscalar.clone());
        //add statement accounts to transcript

        prover.allocate_account(b"zero_account", &account);

        let mut transcript_rng = prover.prove_impl(); //confirm

        // create random  scalar r,
        let r: Scalar = Scalar::random(&mut transcript_rng);

        //let create e = pk.g ^ r
        let e = account.pk.gr.decompress().unwrap() * r;

        //let create f = pk.h ^ r
        let f = account.pk.grsk.decompress().unwrap() * r;
        //adding e,f to transcript

        prover.allocate_point(b"e", &e.compress());
        prover.allocate_point(b"f", &f.compress());

        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");

        // lets create z = r - x * comm_scalar
        let z = r - comm_rscalar * x;

        return SigmaProof::Dlog(vec![z], x);
    }
    /// destroy_account_prover generates a sigma proof for the zero balance commitment
    /// and demonstrates knowledge of the secret keys for all accounts
    ///
    /// # Arguments
    /// * `accounts` - The accounts.
    /// * `sk` - The secret keys.
    /// * `prover` - The prover.
    ///
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn destroy_account_prover(
        accounts: &[Account],
        sk: &[RistrettoSecretKey],
        prover: &mut Prover,
    ) -> SigmaProof {
        //check length is same
        assert_eq!(accounts.len(), sk.len());
        // lets start a transcript and a prover script
        // let mut transcript = Transcript::new(b"DestroyAccountProof");
        // let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        prover.new_domain_sep(b"DestroyAccountProof");
        //adding witness to initialze transcript RNG (Random Number Generator)
        let sk_scalar_vector: Vec<Scalar> = sk.iter().map(|s| s.0).collect();
        prover.scalars = sk_scalar_vector.iter().cloned().collect();
        //add statement accounts to transcript
        for acc in accounts {
            prover.allocate_account(b"account", acc);
        }

        let mut transcript_rng = prover.prove_impl(); //confirm

        // create random vectors of r to commit on sk,
        let r_vector: Vec<Scalar> = (0..sk.len())
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect();

        //let create e_i = pk.g ^ r
        let e_i = accounts
            .iter()
            .zip(r_vector.iter())
            .map(|(acc, r)| acc.pk.gr.decompress().unwrap() * r)
            .collect::<Vec<_>>();

        //let create f_i = acc.c ^ r
        let f_i = accounts
            .iter()
            .zip(r_vector.iter())
            .map(|(acc, r)| acc.comm.c.decompress().unwrap() * r)
            .collect::<Vec<_>>();
        //adding e,f to transcript
        for (e, f) in e_i.iter().zip(f_i.iter()) {
            prover.allocate_point(b"e", &e.compress());
            prover.allocate_point(b"f", &f.compress());
        }
        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");

        // lets create z = r - x * comm_scalar
        let x_sk = sk_scalar_vector.iter().map(|s| s * x).collect::<Vec<_>>();

        let z_vector = r_vector
            .iter()
            .zip(x_sk.iter())
            .map(|(r, x_comm)| r - x_comm)
            .collect::<Vec<_>>();

        return SigmaProof::Dlog(z_vector, x);
    }
    /// Implements the Same Value Sigma proof protocol.
    /// Ensures the value and scalar used for commitment are identical for both encryption and Pedersen commitment.
    ///
    /// # Arguments
    /// * `enc_account` - The encrypted account.
    /// * `rscalar` - The scalar used for commitment.
    /// * `value` - The value used for commitment.
    /// * `pedersen_commitment` - The pedersen commitment.
    ///
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn same_value_compact_prover(
        enc_account: Account,
        rscalar: Scalar,
        value: Scalar,
        pedersen_commitment: CompressedRistretto,
    ) -> SigmaProof {
        //For pedersen commitment
        let pc_gens = PedersenGens::default();

        let mut transcript = Transcript::new(b"SameValueProof");
        let mut prover = Prover::new(b"DLEQProof", &mut transcript);

        //add witness to initialze transcript RNG (Random Number Generator)
        prover.scalars = vec![rscalar, value];

        //add elgmal encrypted accounts to transcript
        prover.allocate_account(b"encrypted_account", &enc_account);
        // add pedersen commitment and keys to the transcript
        prover.allocate_point(b"G", &pc_gens.B.compress());
        prover.allocate_point(b"H", &pc_gens.B_blinding.compress());
        prover.allocate_point(b"d", &pedersen_commitment);

        let mut transcript_rng = prover.prove_impl(); //confirm

        // Step 1. Generate and collect two random blindings for value and scalar
        let r1_dash = Scalar::random(&mut transcript_rng);
        let v_doubledash = Scalar::random(&mut transcript_rng);

        // lets create f_encrypted

        let gv_doubledash = RistrettoPoint::mul_base(&v_doubledash);

        let h_delta_r1_dash = enc_account.pk.grsk.decompress().unwrap() * &r1_dash;

        let f_delta = gv_doubledash + h_delta_r1_dash;

        // lets create f_epsilon

        let h_epsilon_r2_dash = pc_gens.B_blinding * &r1_dash;

        let f_epsilon = gv_doubledash + h_epsilon_r2_dash;

        // lets append f_delta, and f_epsilon to the transcript

        prover.allocate_point(b"f_delta", &f_delta.compress());

        prover.allocate_point(b"f_epsilon", &f_epsilon.compress());

        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");
        // lets create the outputs

        // lets create zv
        let xv_dash = x * &value;

        let zv_vector = vec![v_doubledash - xv_dash];

        // lets create zr1
        let x_rscalar = rscalar * &x;

        let zr1 = r1_dash - x_rscalar;
        //returning Empty vector for zr2 as it is not needed in this case
        return SigmaProof::Dleq(zv_vector, vec![zr1], vec![], x);
    }

    /// verify_update_account_dark_tx_prover confirms that the set of output accounts
    /// have been properly updated from inputs using the same key and commitment scalar
    /// pk' = pk * pk_rscalar
    /// comm' = comm + pk * comm_rscalar
    /// comm is updated with 0 balance
    ///
    /// # Arguments
    /// * `delta_updated_accounts` - The updated delta accounts.
    /// * `output_accounts` - The output accounts.
    /// * `pk_rscalar` - The scalar used to update the public keys.
    /// * `comm_rscalar` - The scalar used to update the commitments.
    /// * `prover` - The prover.
    ///
    /// # Returns
    /// A SigmaProof containing the proof components.
    pub fn verify_update_account_dark_tx_prover(
        delta_updated_accounts: &[Account],
        output_accounts: &[Account],
        pk_rscalar: Scalar,
        comm_rscalar: Scalar,
        prover: &mut Prover,
    ) -> SigmaProof {
        //check length is same
        assert_eq!(delta_updated_accounts.len(), output_accounts.len());
        // Using a single scalar to update all the pks and another same scalar to update account commitments to save proof data

        prover.new_domain_sep(b"VerifyUpdateAccountDarkTx");
        prover.scalars.push(pk_rscalar);
        prover.scalars.push(comm_rscalar);
        let mut transcript_rng = prover.prove_impl(); //confirm

        // Generate blinding factors to commit on the updated accounts
        let pk_blinding_scalar = Scalar::random(&mut transcript_rng);
        let comm_blinding_scalar = Scalar::random(&mut transcript_rng);

        // lets multiply pk_blinding_scalar with the pk of the updated delta accounts
        let delta_pk_blinding_scalar = delta_updated_accounts
            .iter()
            .map(|i| i.pk * &pk_blinding_scalar)
            .collect::<Vec<_>>();

        //check if (c,d)/c,d) = pkdelta_r
        //lets do c-c and d-d for the commitments in both input and updated_account vectors
        let check_zero_commitment = delta_updated_accounts
            .iter()
            .zip(output_accounts.iter())
            .map(|(d, o)| o.comm - d.comm)
            .collect::<Vec<_>>();

        // lets create pkdelta_comm_rscalar that is the collection of all delta account pks with comm_rscalar multiplied
        let pkdelta_comm_rscalar = delta_updated_accounts
            .iter()
            .map(|d| d.pk * &comm_rscalar)
            .collect::<Vec<_>>();

        // now check if the difference between output_accounts.comm and updated_delta_accounts.comm are equal to pkdelta_comm_rscalar
        // check if len is same first
        assert_eq!(check_zero_commitment.len(), pkdelta_comm_rscalar.len());
        for (comm_diff, pk_scalar) in check_zero_commitment
            .iter()
            .zip(pkdelta_comm_rscalar.iter())
        {
            if comm_diff.c != pk_scalar.gr || comm_diff.d != pk_scalar.grsk {
                panic!("Commitments are not properly updated. Every Commitment should be updated with 0 balance");
            }
        }

        //Lets commit on comm_rscalar
        // lets multiply comm_blinding_scalar with the pk of the updated delta accounts
        let delta_pk_comm_blinding_scalar = delta_updated_accounts
            .iter()
            .map(|i| i.pk * &comm_blinding_scalar)
            .collect::<Vec<_>>();
        // println!("Prover");
        // lets do x <- H(updated_delta_accounts || output_accounts ||delta_pk_blinding_scalar ||delta_pk_comm_blinding_scalar)
        for (inp, out) in delta_updated_accounts.iter().zip(output_accounts.iter()) {
            prover.allocate_account(b"account", inp);
            prover.allocate_account(b"updatedaccount", &out);
            //   println!("inp {:?}", inp);
            //   println!("out {:?}", out);
        }

        for pk in delta_pk_blinding_scalar.iter() {
            prover.allocate_point(b"commitmentgr", &pk.gr);
            prover.allocate_point(b"commitmentgrsk", &pk.grsk);
            //   println!("gr {:?}", pk.gr);
            //   println!("grsk {:?}", pk.grsk);
        }

        for pk in delta_pk_comm_blinding_scalar.iter() {
            prover.allocate_point(b"commitmentc", &pk.gr);
            prover.allocate_point(b"commitmentd", &pk.grsk);
        }
        // obtain a scalar challenge
        let x = prover.get_challenge(b"challenge");
        // println!("x {:?}", x);
        // lets do z = blinding_scalar - (x * rscalar)
        let z_pk_x_rscalar = pk_blinding_scalar - (x * pk_rscalar);
        let z_comm_x_rscalar = comm_blinding_scalar - (x * comm_rscalar);
        let z_vector: Vec<Scalar> = vec![z_pk_x_rscalar, z_comm_x_rscalar];
        // println!("z_vector {:?}", z_vector);
        return SigmaProof::Dlog(z_vector, x);
    }
}
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::accounts::Prover;
    // use bulletproofs::*;
    //use bulletproofs::{BulletproofGens, PedersenGens};
    use rand::rngs::OsRng;
    #[test]
    fn verify_non_negative_sender_receiver_prover_test() {
        let balance: Vec<u64> = vec![5, 3, 0, 0];
        let r: Vec<Scalar> = vec![
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
        ];

        let mut transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(b"Bulletproof", &mut transcript);
        let proof = prover.verify_non_negative_sender_receiver_prover(&balance, &r);
        println!("{:?}", proof);

        let balance_odd: Vec<u64> = vec![5, 3, 0, 0, 0];
        let r_odd: Vec<Scalar> = vec![
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
            Scalar::random(&mut OsRng),
        ];

        let mut transcript = Transcript::new(b"Test_notPower");
        let mut prover = Prover::new(b"Bulletproof", &mut transcript);
        let proof = prover.verify_non_negative_sender_receiver_prover(&balance_odd, &r_odd);
        println!("{:?}", proof);
    }

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
}
