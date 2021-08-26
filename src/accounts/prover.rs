use rand::thread_rng;

use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
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

pub struct Prover<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>
}

impl<'a> Prover<'a> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        transcript.domain_sep(proof_label);
        Prover {
            transcript,
            scalars: Vec::default()
        }
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(self) -> (Self, merlin::TranscriptRng){
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.as_bytes());
        }
        let transcript_rng = rng_builder.finalize(&mut thread_rng());
        return (self, transcript_rng)
    }

     /// Allocate and assign a secret variable with the given `label`.
     pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar) {
        self.transcript.append_scalar_var(label, &assignment);
        self.scalars.push(assignment);
    }

    /// Allocate and assign a public variable with the given `label`.
    pub fn allocate_point(&mut self, label: &'static [u8], assignment: CompressedRistretto)  {
        self.transcript.append_point_var(label, &assignment);
    }

    /// Allocate and assign an account with the given `label`.
    pub fn allocate_account(&mut self, label: &'static [u8], account: Account)  {
        self.transcript.append_account_var(label, &account);
    }

    // verify_delta_compact_prover generates proves values committed in delta_accounts and epsilon_accounts are the same
    // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-voprf-03#section-5.1
    pub fn verify_delta_compact_prover(delta_accounts: &Vec<Account>, epsilon_accounts: &Vec<Account>, rscalar: &Vec<Scalar>, value_vector: &Vec<i64>) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar){
        
        let mut v_dash_vector: Vec<Scalar> = Vec::new();
        let mut r1_dash_vector: Vec<Scalar> = Vec::new();
        let mut r2_dash_vector: Vec<Scalar> = Vec::new();
        let mut v_doubledash_vector: Vec<Scalar> = Vec::new();
        
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");

        for i in 0..9{

            let mut prover = Prover::new(b"DLEQProof", &mut transcript);

            let signed_int = SignedInteger::from(value_vector[i] as u64);
            let v_dash : Scalar = SignedInteger::into(signed_int);

            prover.scalars.push(v_dash);
            prover.scalars.push(rscalar[i]);

            prover.allocate_account(b"delta_account", delta_accounts[i]); 
            prover.allocate_account(b"epsilon_account", epsilon_accounts[i]);
            
            let (mut prover, mut transcript_rng) = prover.prove_impl(); //confirm

            // Generate three blinding factors
            let r1_dash = Scalar::random(&mut transcript_rng);
            let r2_dash = Scalar::random(&mut transcript_rng);
            let v_doubledash = Scalar::random(&mut transcript_rng);

            // collect blindings and v_dash scalar in vectors to create outputs later 
            r1_dash_vector.push(r1_dash);
            r2_dash_vector.push(r2_dash);
            v_doubledash_vector.push(v_doubledash);
            v_dash_vector.push(v_dash);

            // lets create four points for the proof
            // e_delta = g_delta ^ r1_dash
            // f_delta = g ^ v_doubledash + h_delta ^ r1_dash
            // e_epsilon = g_epsilon ^ r2_dash
            // f_epsilon = g ^ v_doubledash + h_epsilon ^ r2_dash
            // lets first create e_delta
            let e_delta = &delta_accounts[i].pk.gr.decompress().unwrap() * &r1_dash;

            // lets create f_delta
            let gv_doubledash = &RISTRETTO_BASEPOINT_TABLE * &v_doubledash;
            let h_delta_r1_dash = &delta_accounts[i].pk.grsk.decompress().unwrap() * &r1_dash;
            let f_delta = gv_doubledash + h_delta_r1_dash;

            // lets create e_epsilon
            let e_epsilon = &epsilon_accounts[i].pk.gr.decompress().unwrap() * &r2_dash;

            // lets create f_epsilon
            let h_epsilon_r2_dash = &epsilon_accounts[i].pk.grsk.decompress().unwrap() * &r2_dash;
            let f_epsilon = gv_doubledash + h_epsilon_r2_dash;

            // lets append e_delta, f_delta, e_epsilon and f_epsilon to the transcript
            prover.allocate_point(b"e_delta", e_delta.compress());
            prover.allocate_point(b"f_delta", f_delta.compress());
            prover.allocate_point(b"e_epsilon", e_epsilon.compress());
            prover.allocate_point(b"f_epsilon", f_epsilon.compress());

        }

        // Obtain a scalar challenge
        let x = transcript.get_challenge(b"chal");

        // lets create the outputs
        // zv = v_doubledash - x ^ v_dash (value vector v)
        // zr1 = r1_dash - x ^ r (rscalar)
        // zr2 = r2_dash - x ^ r (rscalar)

        let mut zv_vector: Vec<Scalar> = Vec::new();
        let mut zr1_vector: Vec<Scalar> = Vec::new();
        let mut zr2_vector: Vec<Scalar> = Vec::new();

        for i in 0..9 {
            // lets create zv
            let xv_dash = x * v_dash_vector[i];
            let zv = v_doubledash_vector[i] - xv_dash;
            zv_vector.push(zv);

            // lets create zr1
            let xr = x * rscalar[i];
            let zr1 = r1_dash_vector[i] - xr;
            zr1_vector.push(zr1);

            // lets create zr2
            let zr2 = r2_dash_vector[i] - xr;
            zr2_vector.push(zr2);
        }
        
        return (zv_vector, zr1_vector, zr2_vector, x)
    }


    // verify_update_account_prover confirms if anonymity set in delta accounts was updated correctly
    pub fn verify_update_account_prover(updated_input_accounts: &Vec<Account>, updated_delta_accounts: &Vec<Account>, delta_rscalar: &Vec<Scalar>){

        let commc_commd = updated_input_accounts.iter().zip(updated_delta_accounts.iter()).map(|(i, d)|
            d.comm - i.comm
        ).collect::<Vec<_>>();

        let pkdelta_r = updated_delta_accounts.iter().zip(delta_rscalar.iter()).map(|(d, r)|
            d.pk * r
        ).collect::<Vec<_>>();

        if commc_commd.iter().zip(pkdelta_r.iter()).all(|(comm, pk)| 
            comm.c == pk.gr && comm.d == pk.grsk
        ){
            println!("true");
        }else{
            println!("false");
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
        ristretto::{
            RistrettoPublicKey,
            RistrettoSecretKey
        }
    };
    #[test]
    fn verify_delta_compact_prover_test(){
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
        let (delta_accounts, epislon_accounts, rscalar) = Account::create_delta_and_epsilon_accounts(&account_vector, &value_vector, generate_base_pk);

        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(&delta_accounts, &epislon_accounts, &rscalar, &value_vector);

        println!("{:?}{:?}{:?}{:?}", zv_vector, zr1_vector, zr2_vector, x);
    }

    #[test]
    fn verify_update_account_prover_test(){
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

        let (delta_accounts, _, rscalars) = Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, generate_base_pk);

        let updated_delta_accounts = Account::update_delta_accounts(&updated_accounts, &delta_accounts);
          
        let verify_update_proof = Prover::verify_update_account_prover(&updated_accounts, &updated_delta_accounts.unwrap(), &rscalars);
        
    }
}
