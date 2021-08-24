use curve25519_dalek::{
    ristretto::{CompressedRistretto},
    scalar::Scalar,
    constants::RISTRETTO_BASEPOINT_TABLE
};

use merlin::Transcript;
use crate::accounts::TranscriptProtocol;

use crate::{
    accounts::Account,
    elgamal::{
        signed_integer::SignedInteger
    }
};

pub struct Verifier<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>,
    points: Vec<CompressedRistretto>
}

impl<'a> Verifier<'a> {
    /// Construct a new Verifier.  
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Verifier {
            transcript,
            scalars: Vec::default(),
            points: Vec::default()
        }
    }

     /// Allocate and assign a secret variable with the given `label`.
     pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar) {
        self.transcript.append_scalar_var(label, &assignment);
        self.scalars.push(assignment);
    }

    /// Allocate and assign a public variable with the given `label`.
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: CompressedRistretto)  {
        self.transcript.append_point_var(label, &assignment);
        self.points.push(assignment);
    }

    // verify_delta_compact_verifier verifies proves values committed in delta_accounts and epsilon_accounts are the same
    // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-voprf-03#section-5.2
    pub fn verify_delta_compact_verifier(delta_accounts: &Vec<Account>, epsilon_accounts: &Vec<Account>, zv_vector: &Vec<Scalar>, zr1_vector: &Vec<Scalar>, zr2_vector: &Vec<Scalar>, x: &Scalar) -> bool{
        
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");

        for i in 0..9{

            let mut verifier = Verifier::new(b"DLEQProof", &mut transcript);

            verifier.allocate_point(b"gr", delta_accounts[i].pk.gr);
            verifier.allocate_point(b"grsk", delta_accounts[i].pk.grsk); 
            verifier.allocate_point(b"commc", delta_accounts[i].comm.c); 
            verifier.allocate_point(b"commd", delta_accounts[i].comm.d);

            verifier.allocate_point(b"gr", epsilon_accounts[i].pk.gr);
            verifier.allocate_point(b"grsk", epsilon_accounts[i].pk.grsk); 
            verifier.allocate_point(b"commc", epsilon_accounts[i].comm.c);
            verifier.allocate_point(b"commd", epsilon_accounts[i].comm.d);

            // lets create four points for the proof
            // e_delta = g_delta ^ zr1 ^ cdelta ^ x
            // f_delta = g ^ zv + h_delta ^ zr + cdelta ^ x
            // e_epsilon = g_epsilon ^ zr2 + cepsilon ^ x
            // f_epsilon = g ^ zv + h_epsilon ^ zr2 + cepsilon ^ x

            // lets first create e_delta
            let gdelta_zr1 = &delta_accounts[i].pk.gr.decompress().unwrap() * &zr1_vector[i];
            let cdelta_x =  &delta_accounts[i].comm.c.decompress().unwrap() * x;

            let e_delta = gdelta_zr1 + cdelta_x;

            // lets create f_delta
            let g_zv = &RISTRETTO_BASEPOINT_TABLE * &zv_vector[i];
            let hdelta_zr1 = &delta_accounts[i].pk.grsk.decompress().unwrap() * &zr1_vector[i];

            let ddelta_x =  &delta_accounts[i].comm.d.decompress().unwrap() * x;
            
            let f_delta = g_zv + hdelta_zr1 + ddelta_x;

            let cepsilon_x =  &epsilon_accounts[i].comm.c.decompress().unwrap() * x;

            // lets create e_epsilon
            let g_zr2 = &epsilon_accounts[i].pk.gr.decompress().unwrap() * &zr2_vector[i];
            let e_epsilon = g_zr2 + cepsilon_x;

            let depsilon_x =  &epsilon_accounts[i].comm.d.decompress().unwrap() * x;

            // lets create f_epsilon
            let h_epsilon_zr2 = &epsilon_accounts[i].pk.grsk.decompress().unwrap() * &zr2_vector[i];
            let f_epsilon = g_zv + h_epsilon_zr2 + depsilon_x;

            // lets append e_delta, f_delta, e_epsilon and f_epsilon to the transcript
            verifier.allocate_point(b"e_delta", e_delta.compress());
            verifier.allocate_point(b"f_delta", f_delta.compress());
            verifier.allocate_point(b"e_epsilon", e_epsilon.compress());
            verifier.allocate_point(b"f_epsilon", f_epsilon.compress());

        }

        // Obtain a scalar challenge
        let verify_x = transcript.get_challenge(b"chal");

        println!("{:?}", x);
        println!("{:?}", verify_x);

        if x == &verify_x{
            return true
        }else{
            return false
        }
    }
}


// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use rand::rngs::OsRng;
    use crate::{
        keys::{PublicKey, SecretKey},
        accounts::Account,
        accounts::Prover,
        ristretto::{
            RistrettoPublicKey,
            RistrettoSecretKey
        }
    };
    #[test]
    fn verify_delta_compact_verifier_test(){
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
        let (delta_accounts, epislon_accounts, rscalar) = Account::create_delta_and_epsilon_accounts(account_vector, &value_vector, generate_base_pk);

        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(&delta_accounts, &epislon_accounts, &rscalar, &value_vector);

        let check = Verifier::verify_delta_compact_verifier(&delta_accounts, &epislon_accounts, &zv_vector, &zr1_vector, &zr2_vector, &x);

        assert!(check);
    }
}
