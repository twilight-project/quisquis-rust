use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_COMPRESSED,
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::VartimeMultiscalarMul,
};

use crate::accounts::{RangeProofVerifier, TranscriptProtocol};
use merlin::Transcript;

use crate::{accounts::Account, ristretto::RistrettoPublicKey};
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
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: CompressedRistretto) {
        self.transcript.append_point_var(label, &assignment);
    }

    /// Allocate and assign an account with the given `label`.
    pub fn allocate_account(&mut self, label: &'static [u8], account: Account) {
        self.transcript.append_account_var(label, &account);
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
    ) -> bool {
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");
        let mut verifier = Verifier::new(b"DLEQProof", &mut transcript);

        for i in 0..delta_accounts.iter().count() {
            verifier.allocate_account(b"delta_account", delta_accounts[i]);
            verifier.allocate_account(b"epsilon_account", epsilon_accounts[i]);
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
                .unwrap()
                .compress();

            // lets create f_delta
            let combined_scalars = vec![zr1_vector[i], *x, zv_vector[i]];
            let point = vec![
                delta_accounts[i].pk.grsk,
                delta_accounts[i].comm.d,
                RISTRETTO_BASEPOINT_COMPRESSED,
            ];
            let f_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();

            // lets create e_epsilon
            let combined_scalars = vec![zr2_vector[i], *x];
            let point = vec![epsilon_accounts[i].pk.gr, epsilon_accounts[i].comm.c];
            let e_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();

            // lets create f_epsilon
            let combined_scalars = vec![zr2_vector[i], *x, zv_vector[i]];
            let point = vec![
                epsilon_accounts[i].pk.grsk,
                epsilon_accounts[i].comm.d,
                RISTRETTO_BASEPOINT_COMPRESSED,
            ];
            let f_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();

            // lets append e_delta, f_delta, e_epsilon and f_epsilon to the transcript
            verifier.allocate_point(b"e_delta", e_delta);
            verifier.allocate_point(b"f_delta", f_delta);
            verifier.allocate_point(b"e_epsilon", e_epsilon);
            verifier.allocate_point(b"f_epsilon", f_epsilon);
        }

        // Obtain a scalar challenge
        let verify_x = transcript.get_challenge(b"chal");

        if x == &verify_x {
            return true;
        } else {
            return false;
        }
    }

    // verify_update_account_verifier verifies delta accounts were updated correctly
    pub fn verify_update_account_verifier(
        updated_input_accounts: &Vec<Account>,
        updated_delta_accounts: &Vec<Account>,
        z_vector: &Vec<Scalar>,
        x: &Scalar,
    ) -> bool {
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
                    .unwrap()
                    .compress(),
            );

            let combined_scalars = vec![z_vector[i], *x];
            let point = vec![updated_input_accounts[i].pk.grsk, a[i].d];
            e12.push(
                Verifier::multiscalar_multiplication(&combined_scalars, &point)
                    .unwrap()
                    .compress(),
            );
        }

        let mut transcript = Transcript::new(b"VerifyUpdateAcct");
        let mut verifier = Verifier::new(b"DLOGProof", &mut transcript);

        // lets do x <- H(pk_input || pk_output || e)
        // pk_input is in updated_input_accounts
        // pk_output is in updated_delta_accounts
        for (input, output) in updated_input_accounts
            .iter()
            .zip(updated_delta_accounts.iter())
        {
            verifier.allocate_point(b"inputgr", input.pk.gr);
            verifier.allocate_point(b"inputgrsk", input.pk.grsk);
            verifier.allocate_point(b"outputgr", output.pk.gr);
            verifier.allocate_point(b"outputgrsk", output.pk.grsk);
        }

        for i in 0..z_vector.iter().count() {
            verifier.allocate_point(b"commitmentgr", e11[i]);
            verifier.allocate_point(b"commitmentgrsk", e12[i]);
        }

        // obtain a scalar challenge
        let verify_x = transcript.get_challenge(b"chal");

        if x == &verify_x {
            return true;
        } else {
            return false;
        }
    }

    // verify_account_verifier verifies the knowledge of secret key and balance
    pub fn verify_account_verifier(
        updated_delta_account: &Vec<Account>,
        account_epsilon: &Vec<Account>,
        base_pk: RistrettoPublicKey,
        zv: Vec<Scalar>,
        zsk: Vec<Scalar>,
        zr: Vec<Scalar>,
        x: Scalar,
        rp_verifier: &mut RangeProofVerifier,
    ) -> bool {
        let mut transcript = Transcript::new(b"VerifyAccountProver");
        let mut verifier = Verifier::new(b"DLEQProof", &mut transcript);

        for i in 0..updated_delta_account.iter().count() {
            verifier.allocate_account(b"delta_account", updated_delta_account[i]);
            verifier.allocate_account(b"epsilon_account", account_epsilon[i]);
        }
        println!("Verifier");
        for i in 0..updated_delta_account.iter().count() {
            let combined_scalars = vec![zsk[i], x];
            let point = vec![
                updated_delta_account[i].pk.gr,
                updated_delta_account[i].pk.grsk,
            ];
            let e_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();

            let combined_scalars = vec![zv[i], zsk[i], x];
            let point = vec![
                account_epsilon[i].pk.gr,
                updated_delta_account[i].comm.c,
                updated_delta_account[i].comm.d,
            ];
            let f_delta = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();

            let combined_scalars = vec![x, zr[i]];
            let point = vec![account_epsilon[i].comm.c, base_pk.gr];
            let e_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();
            let combined_scalars = vec![zv[i], zr[i], x];
            let point = vec![base_pk.gr, base_pk.grsk, account_epsilon[i].comm.d];
            let f_epsilon = Verifier::multiscalar_multiplication(&combined_scalars, &point)
                .unwrap()
                .compress();
            // lets create hash
            verifier.allocate_point(b"e_delta", e_delta);
            verifier.allocate_point(b"f_delta", f_delta);
            verifier.allocate_point(b"e_epsilon", e_epsilon);
            verifier.allocate_point(b"f_epsilon", f_epsilon);
            println!("{:?}", e_delta);
            println!("{:?}", f_delta);
            println!("{:?}", e_epsilon);
            println!("{:?}", f_epsilon);
        }

        // obtain a scalar challenge
        let verify_x = transcript.get_challenge(b"chal");
        println!("{:?}", verify_x);
        for i in 0..account_epsilon.iter().count() {
            let _ = rp_verifier.range_proof_verifier(account_epsilon[i].comm.d);
        }
        if x == verify_x {
            return true;
        } else {
            return false;
        }
    }
    //verify_non_negative_verifier verifies range proof on Receiver accounts with zero balance
    pub fn verify_non_negative_verifier(
        epsilon_account: &Vec<Account>,
        rp_verifier: &mut RangeProofVerifier,
    ) {
        for i in 0..epsilon_account.iter().count() {
            let _ = rp_verifier.range_proof_verifier(epsilon_account[i].comm.d);
        }
    }

    // verify_update_ddh_prover confirms if (G,H,G',H') is a DDH tuple and (G,H) is updated correctly
    pub fn verify_update_ddh_verifier(
        g: CompressedRistretto,
        h: CompressedRistretto,
        g_dash: CompressedRistretto,
        h_dash: CompressedRistretto,
        z: Scalar,
        x: Scalar,
    ) -> bool {
        // lets create random scalar r with the transcript
        let mut transcript = Transcript::new(b"VerifyUpdateDDH");
        let mut verifier = Verifier::new(b"DDHTuple", &mut transcript);

        //allocates points to Transcript
        verifier.allocate_point(b"g", g);
        verifier.allocate_point(b"g_dash", g_dash);
        verifier.allocate_point(b"h", h);
        verifier.allocate_point(b"h_dash", h_dash);
        //recreate g_r and h_r
        let combined_scalars = vec![z, x];
        let g_point = vec![g, g_dash];
        let g_r = Verifier::multiscalar_multiplication(&combined_scalars, &g_point)
            .unwrap()
            .compress();
        let h_point = vec![h, h_dash];
        let h_r = Verifier::multiscalar_multiplication(&combined_scalars, &h_point)
            .unwrap()
            .compress();

        verifier.allocate_point(b"gr", g_r);
        verifier.allocate_point(b"hr", h_r);
        // obtain a scalar challenge
        let c = transcript.get_challenge(b"chal");
        if x == c {
            return true;
        } else {
            return false;
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
    use crate::{
        accounts::Account,
        accounts::Prover,
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use bulletproofs::r1cs;
    use bulletproofs::PedersenGens;
    use rand::rngs::OsRng;
    #[test]
    fn verify_delta_compact_verifier_test() {
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
        let mut account_vector: Vec<Account> = Vec::new();

        for i in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let acc = Account::generate_account(pk);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account = Account::update_account(acc, 0, updated_keys_scalar, comm_scalar);

            account_vector.push(updated_account);
        }
        let (delta_accounts, epislon_accounts, rscalar) =
            Account::create_delta_and_epsilon_accounts(
                &account_vector,
                &value_vector,
                generate_base_pk,
            );

        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(
            &delta_accounts,
            &epislon_accounts,
            &rscalar,
            &rscalar,
            &value_vector,
        );

        let check = Verifier::verify_delta_compact_verifier(
            &delta_accounts,
            &epislon_accounts,
            &zv_vector,
            &zr1_vector,
            &zr2_vector,
            &x,
        );

        assert!(check);
    }

    #[test]
    fn verify_update_account_verifier_test() {
        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
        let mut updated_accounts: Vec<Account> = Vec::new();

        for i in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let acc = Account::generate_account(pk);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);

            let updated_account = Account::update_account(acc, 0, updated_keys_scalar, comm_scalar);

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

        let (x, z_vector) = Prover::verify_update_account_prover(
            &updated_accounts_slice.to_vec(),
            &updated_delta_accounts_slice.to_vec(),
            &rscalars_slice.to_vec(),
        );

        let check = Verifier::verify_update_account_verifier(
            &updated_accounts_slice.to_vec(),
            &updated_delta_accounts_slice.to_vec(),
            &z_vector,
            &x,
        );
        assert!(check);
    }
    #[test]
    fn verify_account_verifier_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<i64> = vec![-5, -3, 5, 3, 0, 0, 0, 0, 0];
        let mut updated_accounts: Vec<Account> = Vec::new();
        let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

        for i in 0..9 {
            let (updated_account, sk) = Account::generate_random_account_with_value(10);

            updated_accounts.push(updated_account);

            // lets save the first and second sk as sender's sk as we discard the rest
            if i == 0 || i == 1 {
                sender_sk.push(sk);
            }
        }

        let (delta_accounts, _, rscalars) =
            Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

        let updated_delta_accounts =
            Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // balance that we want to prove should be sender balance - the balance user is trying to send

        let bl_first_sender = 10 - 5;
        let bl_second_sender = 10 - 3;

        let delta_unwraped = updated_delta_accounts.unwrap();
        let updated_delta_account_sender: Vec<Account> = vec![delta_unwraped[0], delta_unwraped[1]];
        //let sender_sk_vector: Vec<Scalar> = vec!(sender_sk[0].0, sender_sk[1].0);
        let value_vector_sender: Vec<i64> = vec![bl_first_sender, bl_second_sender];

        let mut epsilon_account_vec: Vec<Account> = Vec::new();
        let mut rscalar_sender: Vec<Scalar> = Vec::new();

        for i in 0..value_vector_sender.iter().count() {
            // lets create an epsilon account with the new balance
            let rscalar = Scalar::random(&mut OsRng);
            rscalar_sender.push(rscalar);
            // lets first create a new epsilon account using the passed balance
            let epsilon_account: Account =
                Account::create_epsilon_account(base_pk, rscalar, value_vector_sender[i]);
            epsilon_account_vec.push(epsilon_account);
        }
        // Create R1CS rangeproof Prover
        let pc_gens = PedersenGens::default();
        let cs = r1cs::Prover::new(&pc_gens, Transcript::new(b"Rangeproof.r1cs"));
        let mut prover = RangeProofProver { prover: cs };
        let (zv, zsk, zr, x) = Prover::verify_account_prover(
            &updated_delta_account_sender,
            &epsilon_account_vec,
            value_vector_sender,
            &sender_sk,
            rscalar_sender,
            &mut prover,
        );
        //Create R1CS rangeproof on all sender accounts
        let range_proof = prover.build_proof();
        // //println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
        println!("Verifier");
        // Initialise the Verifier `ConstraintSystem` instance representing a merge gadget
        let verifier_initial =
            bulletproofs::r1cs::Verifier::new(Transcript::new(b"Rangeproof.r1cs"));
        let mut rp_verifier = RangeProofVerifier {
            verifier: verifier_initial,
        };
        let check = Verifier::verify_account_verifier(
            &updated_delta_account_sender,
            &epsilon_account_vec,
            base_pk,
            zv,
            zsk,
            zr,
            x,
            &mut rp_verifier,
        );
        //Verify r1cs rangeproof
        let bp_check = rp_verifier.verify_proof(&range_proof.unwrap(), &pc_gens);
        println!("{:?}", bp_check.is_ok());
        assert!(check);
    }
}
