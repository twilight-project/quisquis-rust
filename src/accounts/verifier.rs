use bulletproofs::r1cs::R1CSError;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_COMPRESSED,
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::IsIdentity,
    traits::VartimeMultiscalarMul,
};

use crate::accounts::{RangeProofVerifier, TranscriptProtocol};
use crate::{accounts::Account, ristretto::RistrettoPublicKey};
use bulletproofs::{BulletproofGens, PedersenGens, ProofError, RangeProof};
use merlin::Transcript;
pub struct Verifier<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>,
}

impl<'a> Verifier<'a> {
    /// Construct a new Verifier.  
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Verifier {
            transcript,
            scalars: Vec::default(),
        }
    }

    /// Allocate and assign a secret variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar) {
        self.transcript.append_scalar_var(label, &assignment);
        self.scalars.push(assignment);
    }

    /// Allocate and assign a public variable with the given `label`.
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: &CompressedRistretto) {
        self.transcript.append_point_var(label, assignment);
    }

    /// Allocate and assign an account with the given `label`.
    pub fn allocate_account(&mut self, label: &'static [u8], account: &Account) {
        self.transcript.append_account_var(label, account);
    }

    pub fn multiscalar_multiplication(
        combined_scalars: &Vec<Scalar>,
        point: &Vec<CompressedRistretto>,
    ) -> Option<RistrettoPoint> {
        RistrettoPoint::optional_multiscalar_mul(
            combined_scalars,
            point.iter().map(|pt| pt.decompress()),
        )
    }
    /// Allocate a new domain to create another transcript for embedded proof with new `label`.
    pub fn new_domain_sep(&mut self, label: &'static [u8]) {
        self.transcript.domain_sep(label);
    }
    /// Wrapper for getting a challenge in Other modules.
    pub fn get_challenge(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.get_challenge(label)
    }

    // verify_delta_compact_verifier verifies proves values committed in delta_accounts and epsilon_accounts are the same
    // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-voprf-03#section-5.2
    pub fn verify_delta_compact_verifier(
        delta_accounts: &Vec<Account>,
        epsilon_accounts: &Vec<Account>,
        zv_vector: &Vec<Scalar>,
        zr1_vector: &Vec<Scalar>,
        zr2_vector: &Vec<Scalar>,
        x: &Scalar,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        //let mut transcript = Transcript::new(b"VerifyDeltaCompact");
        //let mut verifier = Verifier::new(b"DLEQProof", &mut transcript);
        //Create new transcript
        verifier.new_domain_sep(b"VerifyDeltaCompact");
        for (d, e) in delta_accounts.iter().zip(epsilon_accounts.iter()) {
            verifier.allocate_account(b"delta_account", d);
            verifier.allocate_account(b"epsilon_account", e);
        }

        for i in 0..delta_accounts.iter().count() {
            // lets create four points for the proof
            // e_delta = g_delta ^ zr1 ^ cdelta ^ x
            // f_delta = g ^ zv + h_delta ^ zr + cdelta ^ x
            // e_epsilon = g_epsilon ^ zr2 + cepsilon ^ x
            // f_epsilon = g ^ zv + h_epsilon ^ zr2 + cepsilon ^ x

            let combined_scalars = vec![zr1_vector[i], *x];
            let point = vec![delta_accounts[i].pk.gr, delta_accounts[i].comm.c];
            let e_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Delta Compact Proof Verify: Failed")?;

            // lets create f_delta
            let combined_scalars = vec![zr1_vector[i], *x, zv_vector[i]];
            let point = vec![
                delta_accounts[i].pk.grsk,
                delta_accounts[i].comm.d,
                RISTRETTO_BASEPOINT_COMPRESSED,
            ];
            let f_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Delta Compact Proof Verify: Failed")?;

            // lets create e_epsilon
            let combined_scalars = vec![zr2_vector[i], *x];
            let point = vec![epsilon_accounts[i].pk.gr, epsilon_accounts[i].comm.c];
            let e_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Delta Compact Proof Verify: Failed")?;

            // lets create f_epsilon
            let combined_scalars = vec![zr2_vector[i], *x, zv_vector[i]];
            let point = vec![
                epsilon_accounts[i].pk.grsk,
                epsilon_accounts[i].comm.d,
                RISTRETTO_BASEPOINT_COMPRESSED,
            ];
            let f_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Delta Compact Proof Verify: Failed")?;

            // lets append e_delta, f_delta, e_epsilon and f_epsilon to the transcript
            verifier.allocate_point(b"e_delta", &e_delta.compress());
            verifier.allocate_point(b"f_delta", &f_delta.compress());
            verifier.allocate_point(b"e_epsilon", &e_epsilon.compress());
            verifier.allocate_point(b"f_epsilon", &f_epsilon.compress());
        }

        // Obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"challenge");

        if x == &verify_x {
            Ok(())
        } else {
            Err("Dleq Proof Verify: Failed")
        }
    }

    // verify_update_account_verifier verifies delta accounts were updated correctly
    pub fn verify_update_account_verifier(
        updated_input_accounts: &[Account],
        updated_delta_accounts: &[Account],
        z_vector: &[Scalar],
        x: &Scalar,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        let a = updated_input_accounts
            .iter()
            .zip(updated_delta_accounts.iter())
            .map(|(i, d)| d.comm - i.comm)
            .collect::<Vec<_>>();

        let mut e11: Vec<CompressedRistretto> = Vec::new();
        let mut e12: Vec<CompressedRistretto> = Vec::new();

        for i in 0..z_vector.iter().count() {
            let combined_scalars = vec![z_vector[i], *x];
            let point = vec![updated_input_accounts[i].pk.gr, a[i].c];
            e11.push(
                Verifier::multiscalar_multiplication(&combined_scalars, &point)
                    .ok_or("DLOG Proof Verify: Failed")?
                    .compress(),
            );

            let combined_scalars = vec![z_vector[i], *x];
            let point = vec![updated_input_accounts[i].pk.grsk, a[i].d];
            e12.push(
                Verifier::multiscalar_multiplication(&combined_scalars, &point)
                    .ok_or("DLOG Proof Verify: Failed")?
                    .compress(),
            );
        }

        //let mut transcript = Transcript::new(b"VerifyUpdateAcct");
        //let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);
        verifier.new_domain_sep(b"DLOGProof");
        // lets do x <- H(pk_input || pk_output || e)
        // pk_input is in updated_input_accounts
        // pk_output is in updated_delta_accounts
        for (input, output) in updated_input_accounts
            .iter()
            .zip(updated_delta_accounts.iter())
        {
            verifier.allocate_point(b"inputgr", &input.pk.gr);
            verifier.allocate_point(b"inputgrsk", &input.pk.grsk);
            verifier.allocate_point(b"outputgr", &output.pk.gr);
            verifier.allocate_point(b"outputgrsk", &output.pk.grsk);
        }

        for (e11, e12) in e11.iter().zip(e12.iter()) {
            verifier.allocate_point(b"commitmentgr", e11);
            verifier.allocate_point(b"commitmentgrsk", e12);
        }

        // obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"chal");

        if x == &verify_x {
            Ok(())
        } else {
            Err("DLOG Proof Verify: Failed")
        }
    }

    // verify_account_verifier verifies the knowledge of secret key and balance
    pub fn verify_account_verifier(
        updated_delta_account_sender: &[Account],
        account_epsilon_sender: &[Account],
        base_pk: &RistrettoPublicKey,
        zv: &[Scalar],
        zsk: &[Scalar],
        zr: &[Scalar],
        x: Scalar,
        rp_verifier: &mut RangeProofVerifier<Transcript>,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        //lets start a transcript and a verifier script

        // let mut transcript = Transcript::new(b"VerifyAccountProver");
        // let mut verifier = Verifier::new(b"DLEQProof", &mut transcript);
        verifier.new_domain_sep(b"VerifyAccountProof");
        //add statement accounts to transcript
        for (delta, epsilon) in updated_delta_account_sender
            .iter()
            .zip(account_epsilon_sender.iter())
        {
            verifier.allocate_account(b"delta_account", delta);
            verifier.allocate_account(b"epsilon_account", epsilon);
        }

        //recreate e,f delta and epsilon
        for (i, delta_account) in updated_delta_account_sender.iter().enumerate() {
            let combined_scalars = vec![zsk[i], x];
            let point = vec![delta_account.pk.gr, delta_account.pk.grsk];
            //let create e_delta = (h_delta * x)  + (g_delta * z_sk)
            let e_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            let combined_scalars = vec![zv[i], zsk[i], x];
            let point = vec![base_pk.gr, delta_account.comm.c, delta_account.comm.d];
            // lets create f_delta = d_delta * x + g * z_v + c_delta * z_sk
            let f_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();

            let combined_scalars = vec![x, zr[i]];
            let point = vec![account_epsilon_sender[i].comm.c, base_pk.gr];

            //let create e_epsilon = c_epsilon * x + g * z_dash

            let e_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            let combined_scalars = vec![zv[i], zr[i], x];
            let point = vec![base_pk.gr, base_pk.grsk, account_epsilon_sender[i].comm.d];

            // lets create f_epsilon = d_epsilon * x + g * z_v + h * z_r
            let f_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            // add e and f points to transcript
            verifier.allocate_point(b"e_delta", &e_delta);
            verifier.allocate_point(b"f_delta", &f_delta);
            verifier.allocate_point(b"e_epsilon", &e_epsilon);
            verifier.allocate_point(b"f_epsilon", &f_epsilon);
        }
        // obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"challenge");
        println!("Verifier {:?}", verify_x);
        for i in 0..account_epsilon_sender.iter().count() {
            let res = rp_verifier.range_proof_verifier(account_epsilon_sender[i].comm.d);
            if res.is_err() {
                return Err("Range Proof verification failed");
            }
        }
        if x == verify_x {
            Ok(())
        } else {
            Err("sender account verification failed")
        }
    }
    // verify_account_verifier_bulletproof verifies the knowledge of secret key for sender and
    // the same balance commitment between epsilon and updated delta accounts
    pub fn verify_account_verifier_bulletproof(
        updated_delta_account_sender: &[Account],
        account_epsilon_sender: &[Account],
        base_pk: &RistrettoPublicKey,
        zv: &[Scalar],
        zsk: &[Scalar],
        zr: &[Scalar],
        x: Scalar,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        println!("Verifier");

        //lets start a transcript and a verifier script
        verifier.new_domain_sep(b"VerifyAccountProof");
        //add statement accounts to transcript
        for (delta, epsilon) in updated_delta_account_sender
            .iter()
            .zip(account_epsilon_sender.iter())
        {
            //println!("Account {:?}", delta);
            verifier.allocate_account(b"delta_account", delta);
            verifier.allocate_account(b"epsilon_account", epsilon);
        }
        //recreate e,f delta and epsilon
        for (i, delta_account) in updated_delta_account_sender.iter().enumerate() {
            let combined_scalars = vec![zsk[i], x];
            let point = vec![delta_account.pk.gr, delta_account.pk.grsk];
            //let create e_delta = (h_delta * x)  + (g_delta * z_sk)
            let e_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            //let minus_v_x = x * Scalar::from(5u64);
            // let combined_scalars = vec![minus_v_x, zv[i]];
            let combined_scalars = vec![zv[i], zsk[i], x];
            let point = vec![base_pk.gr, delta_account.comm.c, delta_account.comm.d];
            // [base_pk.gr, delta_account.comm.c, delta_account.comm.d];
            // println!("Point {:?}", point);
            // lets create f_delta = d_delta * x + g * z_v + c_delta * z_sk
            let f_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();

            let combined_scalars = vec![x, zr[i]];
            let point = vec![account_epsilon_sender[i].comm.c, base_pk.gr];

            //let create e_epsilon = c_epsilon * x + g * z_dash

            let e_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            let combined_scalars = vec![zv[i], zr[i], x];
            let point = vec![base_pk.gr, base_pk.grsk, account_epsilon_sender[i].comm.d];

            // lets create f_epsilon = d_epsilon * x + g * z_v + h * z_r
            let f_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Account Verify: Failed")?
                .compress();
            // println!("e delta {:?}", e_delta);
            //println!("Account {:?}", delta_account);
            // println!("f delta {:?}", f_delta);
            //println!("e epsilon delta {:?}", e_epsilon);
            // println!("f epsilon{:?}", f_epsilon);

            // add e and f points to transcript
            verifier.allocate_point(b"e_delta", &e_delta);
            verifier.allocate_point(b"f_delta", &f_delta);
            verifier.allocate_point(b"e_epsilon", &e_epsilon);
            verifier.allocate_point(b"f_epsilon", &f_epsilon);
        }
        // obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"challenge");
        // println!("Verifier {:?}", verify_x);
        if x == verify_x {
            Ok(())
        } else {
            Err("sender account verification failed")
        }
    }
    //verify_non_negative_verifier verifies range proof on Receiver accounts with zero balance
    pub fn verify_non_negative_verifier(
        epsilon_account: &[Account],
        rp_verifier: &mut RangeProofVerifier<Transcript>,
    ) -> Result<(), R1CSError> {
        for i in 0..epsilon_account.iter().count() {
            let _ = rp_verifier.range_proof_verifier(epsilon_account[i].comm.d)?;
        }
        Ok(())
    }

    //verify_non_negative_verifier verifies range proof on Receiver accounts with zero balance
    pub fn verify_non_negative_sender_receiver_bulletproof_batch_verifier(
        &mut self,
        epsilon_account: &[Account],
        proof: &RangeProof,
    ) -> Result<(), ProofError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 16);

        self.new_domain_sep(b"AggregateBulletProof");
        //extract commitments from epsilon accounts
        let commitments: Vec<CompressedRistretto> =
            epsilon_account.iter().map(|acc| acc.comm.d).collect();

        proof.verify_multiple(&bp_gens, &pc_gens, self.transcript, &commitments, 64)?;
        Ok(())
    }
    //verify_non_negative_verifier verifies range proof on Receiver accounts with zero balance
    pub fn verify_non_negative_sender_receiver_bulletproof_vector_verifier(
        &mut self,
        epsilon_account: &[Account],
        proof_vector: &[RangeProof],
    ) -> Result<(), ProofError> {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(64, 1);

        self.new_domain_sep(b"AggregateBulletProof");
        //extract commitments from epsilon accounts
        let commitments: Vec<CompressedRistretto> =
            epsilon_account.iter().map(|acc| acc.comm.d).collect();

        for (proof, com) in proof_vector.iter().zip(commitments.iter()) {
            proof.verify_single(&bp_gens, &pc_gens, self.transcript, &com, 64)?;
        }

        Ok(())
    }

    // verify_delta_identity_check sums the epsilon vector commitments c, d as indidivual points and checks if they are identity
    // else returns error
    pub fn verify_delta_identity_check(epsilon_accounts: &[Account]) -> Result<(), &'static str> {
        let sum_c: RistrettoPoint = epsilon_accounts
            .iter()
            .map(|s| s.comm.c.decompress().unwrap())
            .sum();
        let sum_d: RistrettoPoint = epsilon_accounts
            .iter()
            .map(|s| s.comm.d.decompress().unwrap())
            .sum();
        // sum should be Identity
        if !sum_c.is_identity() || !sum_d.is_identity() {
            Err("Identity sum verify: Failed")
        } else {
            Ok(())
        }
    }
    // zero_balance_account_verifier verifies the knowledge of commitment scalar for anonymity set accounts created randomly
    pub fn zero_balance_account_verifier(
        anonymity_accounts: &[Account],
        z: &[Scalar],
        x: Scalar,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        //check length is same
        assert_eq!(anonymity_accounts.len(), z.len());

        // lets start a transcript and a verifier script
        // let mut transcript = Transcript::new(b"ZeroBalanceAccountProof");
        // let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);
        verifier.new_domain_sep(b"ZeroBalanceAccountProof");
        //add statement accounts to transcript
        for acc in anonymity_accounts {
            verifier.allocate_account(b"anonymity_account", acc);
        }

        //recreate e,f
        for (i, acc) in anonymity_accounts.iter().enumerate() {
            let combined_scalars = vec![z[i], x];
            let point = vec![acc.pk.gr, acc.comm.c];
            //let create e = (pk.g * z)  + (c * x)
            let e = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Zero balance Account Verify: Failed")?
                .compress();
            let point = vec![acc.pk.grsk, acc.comm.d];
            // lets create f = d * x + pk.h * z
            let f = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Zero balance Account Verify: Failed")?
                .compress();
            verifier.allocate_point(b"e", &e);
            verifier.allocate_point(b"f", &f);
        }
        // obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"challenge");
        if x == verify_x {
            Ok(())
        } else {
            Err("Zero balance account verification failed")
        }
    }

    // destroy_account_verifier verifies the knowledge
    // of secret keys and the balance of the account to be destroyed is zero
    pub fn destroy_account_verifier(
        accounts: &[Account],
        z: &[Scalar],
        x: Scalar,
        verifier: &mut Verifier,
    ) -> Result<(), &'static str> {
        //check length is same
        assert_eq!(accounts.len(), z.len());

        // lets start a transcript and a verifier script
        // let mut transcript = Transcript::new(b"DestroyAccountProof");
        // let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);

        verifier.new_domain_sep(b"DestroyAccountProof");
        //add statement accounts to transcript
        for acc in accounts {
            verifier.allocate_account(b"account", acc);
        }

        //recreate e,f
        for (i, acc) in accounts.iter().enumerate() {
            let combined_scalars = vec![z[i], x];
            let point = vec![acc.pk.gr, acc.pk.grsk];
            //let create e = (pk.g * z)  + (c * x)
            let e = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Destroy Account Verify: Failed")?
                .compress();
            let point = vec![acc.comm.c, acc.comm.d];
            // lets create f = d * x + pk.h * z
            let f = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .ok_or("Destroy Account Verify: Failed")?
                .compress();
            verifier.allocate_point(b"e", &e);
            verifier.allocate_point(b"f", &f);
        }
        // obtain a scalar challenge
        let verify_x = verifier.get_challenge(b"challenge");
        if x == verify_x {
            Ok(())
        } else {
            Err("Destroy account verification failed")
        }
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::accounts::RangeProofProver;
    use crate::elgamal::elgamal::ElGamalCommitment;
    use crate::{
        accounts::Account,
        accounts::Prover,
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;

    use bulletproofs::r1cs;
    use bulletproofs::PedersenGens;
    use rand::rngs::OsRng;
    #[test]
    fn verify_delta_compact_verifier_test() {
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(5u64),
            5u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut account_vector: Vec<Account> = Vec::new();

        for _i in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let (acc, _) = Account::generate_account(pk);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account =
                Account::update_account(acc, Scalar::zero(), updated_keys_scalar, comm_scalar);

            account_vector.push(updated_account);
        }
        let (delta_accounts, epislon_accounts, rscalar) =
            Account::create_delta_and_epsilon_accounts(
                &account_vector,
                &value_vector,
                generate_base_pk,
            );
        //create Prover
        let mut transcript = Transcript::new(b"DeltaCompact");
        let mut prover = Prover::new(b"DLEQProof", &mut transcript);
        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(
            &delta_accounts,
            &epislon_accounts,
            &rscalar,
            // &rscalar,
            &value_vector,
            &mut prover,
        )
        .get_dleq();
        //create Verifier
        let mut transcript_verifier = Transcript::new(b"DeltaCompact");
        let mut verifier = Verifier::new(b"DLEQProof", &mut transcript_verifier);
        let check = Verifier::verify_delta_compact_verifier(
            &delta_accounts,
            &epislon_accounts,
            &zv_vector,
            &zr1_vector,
            &zr2_vector,
            &x,
            &mut verifier,
        );

        assert!(check.is_ok());
    }

    #[test]
    fn verify_update_account_verifier_test() {
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();
        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(5u64),
            5u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut updated_accounts: Vec<Account> = Vec::new();

        for _i in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let (acc, _) = Account::generate_account(pk);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account =
                Account::update_account(acc, Scalar::zero(), updated_keys_scalar, comm_scalar);

            updated_accounts.push(updated_account);
        }

        let (delta_accounts, _, rscalars) = Account::create_delta_and_epsilon_accounts(
            &updated_accounts,
            &value_vector,
            generate_base_pk,
        );

        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // sending anonymity set as we know it at this point
        let updated_accounts_slice = &updated_accounts[2..9];

        let updated_delta_accounts_slice = &updated_delta_accounts.as_ref().unwrap()[2..9];

        let rscalars_slice = &rscalars[2..9];
        //create Prover
        let mut transcript = Transcript::new(b"UpdateAccount");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        let (z_vector, x) = Prover::verify_update_account_prover(
            &updated_accounts_slice.to_vec(),
            &updated_delta_accounts_slice.to_vec(),
            &rscalars_slice.to_vec(),
            &mut prover,
        )
        .get_dlog();
        let mut transcript = Transcript::new(b"UpdateAccount");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);
        let check = Verifier::verify_update_account_verifier(
            &updated_accounts_slice.to_vec(),
            &updated_delta_accounts_slice.to_vec(),
            &z_vector,
            &x,
            &mut verifier,
        );
        assert!(check.is_ok());
    }
    // #[test]
    // fn verify_account_verifier_test() {
    //     let base_pk = RistrettoPublicKey::generate_base_pk();
    //     let value_vector: Vec<Scalar> = vec![
    //         -Scalar::from(5u64),
    //         -Scalar::from(3u64),
    //         5u64.into(),
    //         3u64.into(),
    //         0u64.into(),
    //         0u64.into(),
    //         0u64.into(),
    //         0u64.into(),
    //         0u64.into(),
    //     ];
    //     let mut updated_accounts: Vec<Account> = Vec::new();
    //     let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

    //     for i in 0..9 {
    //         let (updated_account, sk) = Account::generate_random_account_with_value(10u64.into());

    //         updated_accounts.push(updated_account);

    //         // lets save the first and second sk as sender's sk as we discard the rest
    //         if i == 0 || i == 1 {
    //             sender_sk.push(sk);
    //         }
    //     }

    //     let (delta_accounts, _, _) =
    //         Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

    //     let updated_delta_accounts =
    //         Account::update_delta_accounts(&updated_accounts, &delta_accounts);

    //     // balance that we want to prove should be sender balance - the balance user is trying to send

    //     let bl_first_sender = 10 - 5;
    //     let bl_second_sender = 10 - 3;

    //     let delta_unwraped = updated_delta_accounts.unwrap();
    //     let updated_delta_account_sender: Vec<Account> = vec![delta_unwraped[0], delta_unwraped[1]];
    //     //let sender_sk_vector: Vec<Scalar> = vec!(sender_sk[0].0, sender_sk[1].0);
    //     let value_vector_sender: Vec<i64> = vec![bl_first_sender, bl_second_sender];

    //     let mut epsilon_account_vec: Vec<Account> = Vec::new();
    //     let mut rscalar_sender: Vec<Scalar> = Vec::new();

    //     for i in 0..value_vector_sender.iter().count() {
    //         // lets create an epsilon account with the new balance
    //         let rscalar = Scalar::random(&mut OsRng);
    //         rscalar_sender.push(rscalar);
    //         // lets first create a new epsilon account using the passed balance
    //         let epsilon_account: Account =
    //             Account::create_epsilon_account(base_pk, rscalar, value_vector_sender[i]);
    //         epsilon_account_vec.push(epsilon_account);
    //     }
    //     // Create R1CS rangeproof Prover
    //     let pc_gens = PedersenGens::default();
    //     let cs = r1cs::Prover::new(&pc_gens, Transcript::new(b"Rangeproof.r1cs"));
    //     let mut prover = RangeProofProver { prover: cs };
    //     //Create Prover
    //     let mut transcript = Transcript::new(b"SenderAccountProof");
    //     let mut prover_sender = Prover::new(b"DLOGProof", &mut transcript);
    //     let (zv, zsk, zr, x) = Prover::verify_account_prover(
    //         &updated_delta_account_sender,
    //         &epsilon_account_vec,
    //         &value_vector_sender,
    //         &sender_sk,
    //         &rscalar_sender,
    //         &mut prover,
    //         &mut prover_sender,
    //     );
    //     //Create R1CS rangeproof on all sender accounts
    //     let range_proof = prover.build_proof();
    //     // //println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
    //     println!("Verifier");
    //     // Initialise the Verifier `ConstraintSystem` instance representing a merge gadget
    //     let verifier_initial =
    //         bulletproofs::r1cs::Verifier::new(Transcript::new(b"Rangeproof.r1cs"));
    //     let mut rp_verifier = RangeProofVerifier {
    //         verifier: verifier_initial,
    //     };
    //     //create Verifier
    //     let mut transcript = Transcript::new(b"SenderAccountProof");
    //     let mut verifier_sender = Verifier::new(b"DLOGProof", &mut transcript);

    //     let check = Verifier::verify_account_verifier(
    //         &updated_delta_account_sender,
    //         &epsilon_account_vec,
    //         &base_pk,
    //         &zv,
    //         &zsk,
    //         &zr,
    //         x,
    //         &mut rp_verifier,
    //         &mut verifier_sender,
    //     );
    //     //Verify r1cs rangeproof
    //     let bp_check = rp_verifier.verify_proof(&range_proof.unwrap(), &pc_gens);
    //     assert!(bp_check.is_ok());
    //     // println!("{:?}", bp_check.is_ok());
    //     assert!(check.is_ok());
    // }
    #[test]
    fn verify_account_verifier_bulletproof_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(5u64),
            Scalar::from(5u64),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut updated_accounts: Vec<Account> = Vec::new();
        let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

        for i in 0..9 {
            let (updated_account, sk) = Account::generate_random_account_with_value(10u64.into());

            updated_accounts.push(updated_account);

            // lets save the first and second sk as sender's sk as we discard the rest
            if i == 0
            /*|| i == 1*/
            {
                sender_sk.push(sk);
            }
        }

        let (delta_accounts, _, _) =
            Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // balance that we want to prove should be sender balance - the balance user is trying to send

        let bl_first_sender = 5u64;
        let bl_second_sender = 7u64;

        let delta_unwraped = updated_delta_accounts.unwrap();
        let updated_delta_account_sender: Vec<Account> =
            vec![delta_unwraped[0] /*delta_unwraped[1]*/];
        //let sender_sk_vector: Vec<_> = vec![sender_sk[0] /*sender_sk[1].0*/];
        let value_vector_sender: Vec<u64> = vec![bl_first_sender /*bl_second_sender*/];
        /* HARD CODE VALUES */
        //  Account[Account { pk: RistrettoPublicKey { gr: CompressedRistretto: [120, 139, 41, 68, 244, 251, 197, 104, 216, 148, 37, 70, 12, 187, 94, 144, 217, 41, 218, 163, 182, 128, 219, 86, 87, 165, 197, 225, 228, 102, 157, 86], grsk: CompressedRistretto: [20, 17, 124, 250, 164, 206, 124, 184, 108, 27, 99, 165, 23, 44, 123, 174, 79, 120, 23, 107, 73, 81, 238, 160, 218, 13, 241, 73, 207, 152, 55, 123] },
        //comm: ElGamalCommitment { c: CompressedRistretto: [200, 65, 189, 121, 30, 95, 202, 52, 59, 247, 204, 244, 17, 21, 183, 76, 141, 22, 188, 66, 9, 40, 221, 78, 210, 123, 191, 52, 21, 46, 37, 69], d: CompressedRistretto: [42, 98, 219, 228, 242, 47, 54, 197, 0, 235, 183, 161, 168, 114, 251, 10, 35, 189, 190, 223, 16, 174, 185, 145, 203, 114, 17, 102, 181, 240, 188, 121] } }]
        let gr: CompressedRistretto = CompressedRistretto([
            120, 139, 41, 68, 244, 251, 197, 104, 216, 148, 37, 70, 12, 187, 94, 144, 217, 41, 218,
            163, 182, 128, 219, 86, 87, 165, 197, 225, 228, 102, 157, 86,
        ]);
        let grsk: CompressedRistretto = CompressedRistretto([
            20, 17, 124, 250, 164, 206, 124, 184, 108, 27, 99, 165, 23, 44, 123, 174, 79, 120, 23,
            107, 73, 81, 238, 160, 218, 13, 241, 73, 207, 152, 55, 123,
        ]);
        let pk_hard = RistrettoPublicKey { gr: gr, grsk: grsk };
        let comm_hard = ElGamalCommitment {
            c: CompressedRistretto([
                200, 65, 189, 121, 30, 95, 202, 52, 59, 247, 204, 244, 17, 21, 183, 76, 141, 22,
                188, 66, 9, 40, 221, 78, 210, 123, 191, 52, 21, 46, 37, 69,
            ]),
            d: CompressedRistretto([
                42, 98, 219, 228, 242, 47, 54, 197, 0, 235, 183, 161, 168, 114, 251, 10, 35, 189,
                190, 223, 16, 174, 185, 145, 203, 114, 17, 102, 181, 240, 188, 121,
            ]),
        };

        let account = Account {
            pk: pk_hard,
            comm: comm_hard,
        };
        let account_hard = vec![account];
        //sk [RistrettoSecretKey(Scalar{
        //	bytes: [22, 84, 54, 73, 13, 9, 237, 178, 165, 112, 250, 66, 127, 127, 161, 93, 55, 15, 24, 81, 126, 102, 109, 89, 127, 196, 98, 10, 224, 30, 66, 2],
        //})]
        let balance_sender = vec![5]; //Balance [5]
                                      //bytes: [22, 84, 54, 73, 13, 9, 237, 178, 165, 112, 250, 66, 127, 127, 161, 93, 55, 15, 24, 81, 126, 102, 109, 89, 127, 196, 98, 10, 224, 30, 66, 2]

        let scalar_bytes: [u8; 32] = [
            22, 84, 54, 73, 13, 9, 237, 178, 165, 112, 250, 66, 127, 127, 161, 93, 55, 15, 24, 81,
            126, 102, 109, 89, 127, 196, 98, 10, 224, 30, 66, 2,
        ];
        let sk_scalar: Scalar = Scalar::from_canonical_bytes(scalar_bytes).unwrap();
        let sk_hard = vec![RistrettoSecretKey(sk_scalar)];
        let v_kacc = account.verify_account(&RistrettoSecretKey(sk_scalar), Scalar::from(5u64));
        println!("v kp {:?}", v_kacc);
        let dec =
            account.decrypt_account_balance(&RistrettoSecretKey(sk_scalar), Scalar::from(5u64));
        let g_bp = &Scalar::from(5u64) * &RISTRETTO_BASEPOINT_TABLE;
        if dec.unwrap() == g_bp.compress() {
            println!("Yes");
        }
        //Create Prover
        let mut transcript = Transcript::new(b"SenderAccountProof");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        let (ep, _rs, sigma_dleq) = Prover::verify_account_prover(
            // &updated_delta_account_sender,
            &account_hard,
            //&balance_sender,
            &value_vector_sender,
            //&sender_sk,
            &sk_hard,
            &mut prover,
            base_pk,
        );
        let (zv, zsk, zr, x) = sigma_dleq.get_dleq();
        // //println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
        println!("Verifier");
        //create Verifier
        let mut transcript = Transcript::new(b"SenderAccountProof");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);

        let check = Verifier::verify_account_verifier_bulletproof(
            &account_hard,
            //&updated_delta_account_sender,
            &ep,
            &base_pk,
            &zv,
            &zsk,
            &zr,
            x,
            &mut verifier,
        );
        println!("{:?}", check);
        assert!(check.is_ok());
    }
    #[test]
    fn zero_balance_account_verifier_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let mut updated_key = PublicKey::update_public_key(&base_pk, Scalar::random(&mut OsRng));
        let mut anonymity_accounts: Vec<Account> = Vec::new();
        let mut rscalar_comm: Vec<Scalar> = Vec::new();

        for _i in 0..4 {
            let (acc, r) = Account::generate_account(PublicKey::update_public_key(
                &updated_key,
                Scalar::random(&mut OsRng),
            ));
            updated_key = PublicKey::update_public_key(&updated_key, Scalar::random(&mut OsRng));
            anonymity_accounts.push(acc);
            rscalar_comm.push(r);
        }
        //create Prover
        let mut transcript = Transcript::new(b"ZeroBalanceAccount");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        let (z, x) =
            Prover::zero_balance_account_prover(&anonymity_accounts, &rscalar_comm, &mut prover)
                .get_dlog();
        //create Verifier
        let mut transcript = Transcript::new(b"ZeroBalanceAccount");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);
        let check =
            Verifier::zero_balance_account_verifier(&anonymity_accounts, &z, x, &mut verifier);
        //println!("{:?}", check.unwrap());
        assert!(check.is_ok());
    }
    #[test]
    fn zero_balance_account_verifier_fail_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let mut updated_key = PublicKey::update_public_key(&base_pk, Scalar::random(&mut OsRng));
        let mut anonymity_accounts: Vec<Account> = Vec::new();
        let mut rscalar_comm: Vec<Scalar> = Vec::new();

        for _i in 0..4 {
            let (acc, r) = Account::generate_account(PublicKey::update_public_key(
                &updated_key,
                Scalar::random(&mut OsRng),
            ));
            updated_key = PublicKey::update_public_key(&updated_key, Scalar::random(&mut OsRng));
            anonymity_accounts.push(acc);
            rscalar_comm.push(r);
        }
        let c_scalar = Scalar::random(&mut OsRng);
        //let upk_scalar = Scalar::random(&mut OsRng);
        let pk = RistrettoPublicKey::generate_base_pk();
        let new_comm = ElGamalCommitment::generate_commitment(&pk, c_scalar, Scalar::from(0u64));
        anonymity_accounts.push(Account {
            pk: pk,
            comm: new_comm,
        });
        rscalar_comm.push(rscalar_comm[0]);

        let mut transcript = Transcript::new(b"ZeroBalanceAccount");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        let (z, x) =
            Prover::zero_balance_account_prover(&anonymity_accounts, &rscalar_comm, &mut prover)
                .get_dlog();
        //create Verifier
        let mut transcript = Transcript::new(b"ZeroBalanceAccount");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);

        let check =
            Verifier::zero_balance_account_verifier(&anonymity_accounts, &z, x, &mut verifier);
        //  println!("{:?}", check.unwrap());
        assert!(check.is_err());
    }

    #[test]
    fn destroy_account_verifier_test() {
        let mut zero_accounts: Vec<Account> = Vec::new();
        let mut sk_vec: Vec<RistrettoSecretKey> = Vec::new();

        for _i in 0..4 {
            let (acc, sk) = Account::generate_random_account_with_value(0u64.into());
            zero_accounts.push(acc);
            sk_vec.push(sk);
        }
        // let (acc1, _) = Account::generate_random_account_with_value(0u64.into());
        // zero_accounts.push(acc1);
        // sk_vec.push(RistrettoSecretKey(Scalar::random(&mut OsRng)));
        //create Prover

        let mut transcript = Transcript::new(b"DestroyAccount");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);
        let (z, x) =
            Prover::destroy_account_prover(&zero_accounts, &sk_vec, &mut prover).get_dlog();
        //create Verifier
        let mut transcript = Transcript::new(b"DestroyAccount");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);

        let check = Verifier::destroy_account_verifier(&zero_accounts, &z, x, &mut verifier);
        //println!("{:?}", check.unwrap());
        assert!(check.is_ok());
    }
    #[test]
    fn verify_delta_identity_check_test() {
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(-(-5i64) as u64),
            5u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut account_vector: Vec<Account> = Vec::new();

        for _ in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let (acc, _) = Account::generate_account(pk);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account =
                Account::update_account(acc, Scalar::zero(), updated_keys_scalar, comm_scalar);

            account_vector.push(updated_account);
        }

        let delta_and_epsilon_accounts = Account::create_delta_and_epsilon_accounts(
            &account_vector,
            &value_vector,
            generate_base_pk,
        );

        let check = Verifier::verify_delta_identity_check(&delta_and_epsilon_accounts.1);
        assert!(check.is_ok());
    }
    #[test]
    fn verify_non_negative_sender_receiver_bulletproof_batch_verifier_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(5u64),
            -Scalar::from(3u64),
            5u64.into(),
            3u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut updated_accounts: Vec<Account> = Vec::new();
        let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

        for i in 0..9 {
            let (updated_account, sk) = Account::generate_random_account_with_value(10u64.into());

            updated_accounts.push(updated_account);

            // lets save the first and second sk as sender's sk as we discard the rest
            if i == 0 || i == 1 {
                sender_sk.push(sk);
            }
        }

        let (delta_accounts, epsilon_accounts, r_scalars) =
            Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // balance that we want to prove should be sender balance - the balance user is trying to send

        let bl_first_sender = 10 - 5;
        let bl_second_sender = 10 - 3;

        let delta_unwraped = updated_delta_accounts.unwrap();
        let updated_delta_account_sender: Vec<Account> = vec![delta_unwraped[0], delta_unwraped[1]];
        //let sender_sk_vector: Vec<Scalar> = vec!(sender_sk[0].0, sender_sk[1].0);
        let value_vector_sender: Vec<u64> = vec![bl_first_sender, bl_second_sender];

        //Create Prover
        let mut transcript = Transcript::new(b"SenderAccountProof");
        let mut prover = Prover::new(b"BulletProof", &mut transcript);
        let (ep_sender, rs_sender, sigma_dleq) = Prover::verify_account_prover(
            &updated_delta_account_sender,
            &value_vector_sender,
            &sender_sk,
            &mut prover,
            base_pk,
        );
        let (zv, zsk, zr, x) = sigma_dleq.get_dleq();
        //create updated balance vector for updated sender + receiver
        let balance_vector_bp: Vec<u64> =
            vec![bl_first_sender, bl_second_sender, 5u64.into(), 3u64.into()];
        //create rscalar for epsilon vector for updated sender + receiver
        let r_scalar_bp = vec![rs_sender[0], rs_sender[1], r_scalars[2], r_scalars[3]];
        let proof =
            prover.verify_non_negative_sender_reciver_prover(&balance_vector_bp, &r_scalar_bp);

        // let balance_odd: Vec<u64> = vec![5, 3, 0, 0, 0];
        // let r_odd: Vec<Scalar> = vec![
        //     Scalar::random(&mut OsRng),
        //     Scalar::random(&mut OsRng),
        //     Scalar::random(&mut OsRng),
        //     Scalar::random(&mut OsRng),
        //     Scalar::random(&mut OsRng),
        // ];

        // let mut transcript = Transcript::new(b"Test_notPower");
        // let mut prover = Prover::new(b"Bulletproof", &mut transcript);
        // let proof = prover.verify_non_negative_sender_reciver_prover(&balance_odd, &r_odd);
        // println!("{:?}", proof);
        //Verify

        let mut transcript_v = Transcript::new(b"SenderAccountProof");
        let mut verifier = Verifier::new(b"BulletProof", &mut transcript_v);

        let check = Verifier::verify_account_verifier_bulletproof(
            &updated_delta_account_sender,
            &ep_sender,
            &base_pk,
            &zv,
            &zsk,
            &zr,
            x,
            &mut verifier,
        );
        // println!("{:?}", bp_check.is_ok());
        assert!(check.is_ok());
        let epsilon_accounts_bp = vec![
            ep_sender[0],
            ep_sender[1],
            epsilon_accounts[2],
            epsilon_accounts[3],
        ];
        assert!(verifier
            .verify_non_negative_sender_receiver_bulletproof_batch_verifier(
                &epsilon_accounts_bp,
                &proof[0],
            )
            .is_ok());
    }
    #[test]
    fn verify_non_negative_sender_receiver_bulletproof_vector_verifier_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(6u64),
            -Scalar::from(3u64),
            5u64.into(),
            3u64.into(),
            1u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
            0u64.into(),
        ];
        let mut updated_accounts: Vec<Account> = Vec::new();
        let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

        for i in 0..9 {
            let (updated_account, sk) = Account::generate_random_account_with_value(10u64.into());

            updated_accounts.push(updated_account);

            // lets save the first and second sk as sender's sk as we discard the rest
            if i == 0 || i == 1 {
                sender_sk.push(sk);
            }
        }

        let (delta_accounts, epsilon_accounts, r_scalars) =
            Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // balance that we want to prove should be sender balance - the balance user is trying to send

        let bl_first_sender = 10 - 6;
        let bl_second_sender = 10 - 3;

        let delta_unwraped = updated_delta_accounts.unwrap();
        let updated_delta_account_sender: Vec<Account> = vec![delta_unwraped[0], delta_unwraped[1]];
        //let sender_sk_vector: Vec<Scalar> = vec!(sender_sk[0].0, sender_sk[1].0);
        let value_vector_sender: Vec<u64> = vec![bl_first_sender, bl_second_sender];

        //Create Prover
        let mut transcript = Transcript::new(b"SenderAccountProof");
        let mut prover = Prover::new(b"BulletProof", &mut transcript);
        let (ep_sender, rs_sender, sigma_dleq) = Prover::verify_account_prover(
            &updated_delta_account_sender,
            &value_vector_sender,
            &sender_sk,
            &mut prover,
            base_pk,
        );
        let (zv, zsk, zr, x) = sigma_dleq.get_dleq();
        //create updated balance vector for updated sender + receiver
        let balance_vector_bp: Vec<u64> = vec![
            bl_first_sender,
            bl_second_sender,
            5u64.into(),
            3u64.into(),
            1u64.into(),
        ];
        //create rscalar for epsilon vector for updated sender + receiver
        let r_scalar_bp = vec![
            rs_sender[0],
            rs_sender[1],
            r_scalars[2],
            r_scalars[3],
            r_scalars[4],
        ];
        let proof =
            prover.verify_non_negative_sender_reciver_prover(&balance_vector_bp, &r_scalar_bp);

        //Verify

        let mut transcript_v = Transcript::new(b"SenderAccountProof");
        let mut verifier = Verifier::new(b"BulletProof", &mut transcript_v);

        let check = Verifier::verify_account_verifier_bulletproof(
            &updated_delta_account_sender,
            &ep_sender,
            &base_pk,
            &zv,
            &zsk,
            &zr,
            x,
            &mut verifier,
        );
        println!("{:?}", check);
        assert!(check.is_ok());
        let epsilon_accounts_bp = vec![
            ep_sender[0],
            ep_sender[1],
            epsilon_accounts[2],
            epsilon_accounts[3],
            epsilon_accounts[4],
        ];
        assert!(verifier
            .verify_non_negative_sender_receiver_bulletproof_vector_verifier(
                &epsilon_accounts_bp,
                &proof,
            )
            .is_ok());
    }
}
