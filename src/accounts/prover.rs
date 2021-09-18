use rand::thread_rng;
//use std::time::Instant;

use curve25519_dalek::{
    ristretto::CompressedRistretto,
    scalar::Scalar,
    constants::RISTRETTO_BASEPOINT_TABLE
};

use merlin::Transcript;
use crate::accounts::TranscriptProtocol;

use crate::{
    accounts::Account,
    elgamal::{
        signed_integer::SignedInteger,
        elgamal::ElGamalCommitment
    },
    ristretto::{
        RistrettoPublicKey,
        RistrettoSecretKey
    }
};

use rand::rngs::OsRng;

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
    pub fn verify_delta_compact_prover(delta_accounts: &Vec<Account>, epsilon_accounts: &Vec<Account>, rscalar1: &Vec<Scalar>, rscalar2: &Vec<Scalar>, value_vector: &Vec<i64>) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar){
        
        let mut v_dash_vector: Vec<Scalar> = Vec::new();
        let mut r1_dash_vector: Vec<Scalar> = Vec::new();
        let mut r2_dash_vector: Vec<Scalar> = Vec::new();
        let mut v_doubledash_vector: Vec<Scalar> = Vec::new();
        
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");

        for i in 0..delta_accounts.iter().count(){

            let mut prover = Prover::new(b"DLEQProof", &mut transcript);

            let signed_int = SignedInteger::from(value_vector[i] as u64);
            let v_dash : Scalar = SignedInteger::into(signed_int);

            prover.scalars.push(v_dash);
            prover.scalars.push(rscalar1[i]);
            prover.scalars.push(rscalar2[i]);

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

        // obtain a scalar challenge
        let x = transcript.get_challenge(b"chal");

        // lets create the outputs
        // zv = v_doubledash - x ^ v_dash (value vector v)
        // zr1 = r1_dash - x ^ r (rscalar)
        // zr2 = r2_dash - x ^ r (rscalar)

        let mut zv_vector: Vec<Scalar> = Vec::new();
        let mut zr1_vector: Vec<Scalar> = Vec::new();
        let mut zr2_vector: Vec<Scalar> = Vec::new();

        for i in 0..delta_accounts.iter().count() {
            // lets create zv
            let xv_dash = x * v_dash_vector[i];
            let zv = v_doubledash_vector[i] - xv_dash;
            zv_vector.push(zv);

            // lets create zr1
            let xr1 = x * rscalar1[i];
            let zr1 = r1_dash_vector[i] - xr1;
            zr1_vector.push(zr1);

            // lets create zr2
            let xr2 = x * rscalar2[i];
            let zr2 = r2_dash_vector[i] - xr2;
            zr2_vector.push(zr2);
        }
        
        return (zv_vector, zr1_vector, zr2_vector, x)
    }


    // verify_update_account_prover confirms if anonymity set in delta accounts was updated correctly
    pub fn verify_update_account_prover(updated_input_accounts: &Vec<Account>, updated_delta_accounts: &Vec<Account>, delta_rscalar: &Vec<Scalar>) -> (Scalar, Vec<Scalar>){
        // check if (c,d)/c,d) = pkdelta_r
        // lets do c-c and d-d for the commitments in both updated_input and updated_delta account vectors
        let check_delta = updated_input_accounts.iter().zip(updated_delta_accounts.iter()).map(|(i, d)|
            Account{
                pk: d.pk, 
                comm: d.comm - i.comm
            }
        ).collect::<Vec<_>>();
        // lets create pkdelta_r that is the collection of all delta account pks with r multiplied
        let pkdelta_r = updated_delta_accounts.iter().zip(delta_rscalar.iter()).map(|(d, r)|
            d.pk * r
        ).collect::<Vec<_>>();

        // now check if the updated commitments are equal to pkdelta_r, collect them in a vector
        // t(hat is the anonymity set
        let anonymity_set = check_delta.iter().enumerate().zip(pkdelta_r.iter()).filter(|((_i, cd), pk)| 
            cd.comm.c == pk.gr && cd.comm.d == pk.grsk 
        ).collect::<Vec<_>>();

        let anonymity_set_index: Vec<_> = anonymity_set.iter().map(|i| i.0.0).collect();

        // lets create random scalar s with the transcript
        let mut transcript = Transcript::new(b"VerifyUpdateAcct");
        let mut prover = Prover::new(b"DLOGProof", &mut transcript);

        prover.scalars = delta_rscalar.to_vec();

        let (mut prover, mut transcript_rng) = prover.prove_impl(); //confirm

        // Generate a single blinding factor
        let s_scalar = Scalar::random(&mut transcript_rng);

        // lets multiply s_scalar with the g of updated_input and the h of updated_delta accounts
        let updated_input_pk_with_s_scalar = anonymity_set.iter().map(|i|
                i.0.1.pk * &s_scalar
            
        ).collect::<Vec<_>>();

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

        for pk in updated_input_pk_with_s_scalar.iter(){
            prover.allocate_point(b"commitmentgr", pk.gr);
            prover.allocate_point(b"commitmentgrsk", pk.grsk);  
        }

        // obtain a scalar challenge
        let x = transcript.get_challenge(b"chal");

        let mut z_vector: Vec<Scalar> = Vec::new();

        // lets do z = s - xrdelta
        for i in anonymity_set.iter() {
            z_vector.push(s_scalar - (x * delta_rscalar[i.0.0]));
        }

        return (x, z_vector)
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

        let (zv_vector, zr1_vector, zr2_vector, x) = Prover::verify_delta_compact_prover(&delta_accounts, &epislon_accounts, &rscalar, &rscalar, &value_vector);

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

        // sending anonymity set as we know it at this point
        let updated_accounts_slice = &updated_accounts[2..9];

        let updated_delta_accounts_slice = &updated_delta_accounts.as_ref().unwrap()[2..9];

        let rscalars_slice = &rscalars[2..9];
          
        let verify_update_proof = Prover::verify_update_account_prover(&updated_accounts_slice.to_vec(), &updated_delta_accounts_slice.to_vec(), &rscalars_slice.to_vec());
        
        println!("{:?}", verify_update_proof);
    }

    #[test]
    fn verify_account_prover_test(){
        let base_pk = RistrettoPublicKey::generate_base_pk();

        let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];
        let mut updated_accounts: Vec<Account> = Vec::new();
        let mut sender_sk: Vec<RistrettoSecretKey> = Vec::new();

        for i in 0..9 {

            let (updated_account, sk) = Account::generate_random_account_with_value(10);

            updated_accounts.push(updated_account);

            // lets save the first sk as sender's sk as we discard the rest
            if i == 0 {
                sender_sk.push(sk);
            }

          }

        let (delta_accounts, _, rscalars) = Account::create_delta_and_epsilon_accounts(&updated_accounts, &value_vector, base_pk);

        let updated_delta_accounts = Account::update_delta_accounts(&updated_accounts, &delta_accounts);

        // balance that we want to prove should be sender balance - the balance user is trying to send

        let bl = 10 - 5;
        // lets create an epsilon account with the new balance
        let rscalar = Scalar::random(&mut OsRng);
        // lets first create a new epsilon account using the passed balance
        let epsilon_account: Vec<Account> = vec!(Account::create_epsilon_account(base_pk, rscalar, bl));

        let updated_delta_account_sender: Vec<Account> = vec!(updated_delta_accounts.unwrap()[0]);
        let rscalar_sender: Vec<Scalar> = vec!(rscalars[0]);
        let sender_sk: Vec<Scalar> = vec!(sender_sk[0].0);
        let value_vector_sender: Vec<i64> = vec!(bl);

        let (zv, zsk, zr, x) = Prover::verify_delta_compact_prover(&updated_delta_account_sender, &epsilon_account, &sender_sk, &rscalar_sender, &value_vector_sender);

        // we need to verify that the sender has enough balance and posesses the sk
        //let (zv, zsk, zr, x) = Prover::verify_account_prover(updated_delta_accounts.unwrap()[0], generate_base_pk, 5, &sender_sk[0]);
        
        println!("{:?}{:?}{:?}{:?}", zv, zsk, zr, x);
    }
}
