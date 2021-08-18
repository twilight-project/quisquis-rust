use rand::thread_rng;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use merlin::Transcript;
use crate::transcript::TranscriptProtocol;

use crate::{
    accounts::Account
};

pub struct Prover<'a> {
    transcript: &'a mut Transcript,
    scalars: Vec<Scalar>
}

impl<'a> Prover<'a> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], transcript: &'a mut Transcript) -> Self {
        //transcript.domain_sep(proof_label);
        Prover {
            transcript,
            scalars: Vec::default()
        }
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(self)  {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.as_bytes());
        }
        let mut transcript_rng = rng_builder.finalize(&mut thread_rng());

        // Generate a blinding factor for each secret variable
        let blindings = self
            .scalars
            .iter()
            .map(|_| Scalar::random(&mut transcript_rng))
            .collect::<Vec<Scalar>>();
    }

     /// Allocate and assign a secret variable with the given `label`.
     pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar) {
        //self.transcript.append_scalar_var(label);
        self.scalars.push(assignment);
        //ScalarVar(self.scalars.len() - 1)
    }


    pub fn verify_delta_compact_prover(delta_accounts: Vec<Account>, epsilon_accounts: Vec<Account>){
        let mut transcript = Transcript::new(b"VerifyDeltaCompact");
        let mut prover = Prover::new(b"DLEQProof", &mut transcript);
        let var_x = prover.allocate_scalar(b"x", delta_accounts[1].pk.gr); //its a point, not a scalar
        prover.prove_impl();
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
        let delta_and_epsilon_accounts = Account::create_delta_and_epsilon_accounts(account_vector, value_vector, generate_base_pk);

        Prover::verify_delta_compact_prover(delta_and_epsilon_accounts.0, delta_and_epsilon_accounts.1);
    }
}
