use curve25519_dalek::{
    ristretto::{CompressedRistretto,RistrettoPoint},  
    constants::RISTRETTO_BASEPOINT_TABLE,
    scalar::Scalar,
    traits::IsIdentity
};
use crate::{
    keys::{PublicKey, SecretKey},
    ristretto::{
        RistrettoPublicKey,
        RistrettoSecretKey
    },
    elgamal::{
        elgamal::ElGamalCommitment
    }
};
use rand::rngs::OsRng;


#[derive(Debug, Copy, Clone)]
pub struct Account {
    pub(crate) pk: RistrettoPublicKey,
    pub(crate) comm: ElGamalCommitment,
}

impl Account {
    // Private constructor
    fn set_account(pk: RistrettoPublicKey, comm: ElGamalCommitment) -> Account {
        Account {
            pk: pk,
            comm: comm,
        }
    }

    /// generate_account creates a new account
    /// returns PublicKey, SecretKey and a Commitment with 0 balance
	pub fn generate_account(pk: RistrettoPublicKey) -> Account  {
        
        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        // lets generate a new commitment using pubkey
        let comm = ElGamalCommitment::generate_commitment(&pk, comm_scalar, 0);

        let account = Account::set_account(pk, comm);

        return account
    }
    /// Verifies the account balance stored in commitment
    /// Verifies the Private key and balance passed as input
    pub fn verify_account (self: &Self, sk: &RistrettoSecretKey, bl: i64)-> bool {
        self.pk.verify_keypair(sk) && self.comm.verify_commitment(sk,bl) 
    }

    /// Decrypts the account balance and returns G*bl. Discrete log should be solved to extract bl 
    /// The function shall be used with extreme caution. Ensure that account is verifiable before calling this method
    pub fn decrypt_account_balance (self: &Self, sk: &RistrettoSecretKey, bl: i64)-> Result<CompressedRistretto, &'static str> {
        if self.verify_account(sk,bl) {
            Ok(self.comm.decommit(sk))
        }
        else{
            Err("Invalid Account")
        }
    }


    // update_account updates an account by creating pk' and comm' with 0 balance
    // returns acc'(pk', comm')
    pub fn update_account(a: Account, bl: i64, update_key_scalar: Scalar, generate_commitment_scalar: Scalar) -> Account {

        // lets first update the pk
        let updated_pk = RistrettoPublicKey::update_public_key(&a.pk, update_key_scalar);

        // lets update the commitment
        let new_comm = ElGamalCommitment::generate_commitment(&a.pk, generate_commitment_scalar, bl);

        // lets add old and new commitments
        let updated_comm = ElGamalCommitment::add_commitments(&new_comm, &a.comm);

        Account::set_account(updated_pk, updated_comm)
    }

    // create_delta_account creates account delta
    // takes account, vector bl (updated balance), rscalar
    // returns Account Delta
    pub fn create_delta_account(a: Account, bl: i64, rscalar: Scalar) -> Account {

        // lets generate commitment on v for delta using Pk and r'
        let comm_delta = ElGamalCommitment::generate_commitment(&a.pk, rscalar, bl);

        Account::set_account(a.pk, comm_delta)
    }

    // create_epsilon_account creates account delta
    // takes vector bl (updated balance), rscalar and base_pair generated with fixed-g
    // returns Account Epsilon
    pub fn create_epsilon_account(bl: i64, rscalar: Scalar, base_pk: RistrettoPublicKey) -> Account {

        // lets generate commitment on v for epsilon using GP and r
        let comm_epsilon = ElGamalCommitment::generate_commitment(&base_pk, rscalar, bl);

        Account::set_account(base_pk, comm_epsilon)
    }

    // update_delta_account takes updated_account and delta_account, multiplies their commitments
    // returns updated delta account
    pub fn update_delta_account(updated_account: Account, delta_account: Account) ->  Result<Account, &'static str> {

        if updated_account.pk.gr == delta_account.pk.gr && updated_account.pk.grsk == delta_account.pk.grsk {
            let new_comm = ElGamalCommitment::add_commitments(&updated_account.comm, &delta_account.comm);
            let updated_delta_account = Account::set_account(updated_account.pk, new_comm);
            Ok(updated_delta_account)
        }else{
            Err("pks are not equal")
        }
    }
    // verify_delta_update verifies if account delta was updated correctly
    pub fn verify_delta_update(updated_delta_account: Account, delta_account: Account, updated_input_account: Account) -> bool {

        if updated_delta_account.pk.gr == delta_account.pk.gr && updated_delta_account.pk.gr == updated_input_account.pk.gr && delta_account.pk.gr == updated_input_account.pk.gr {
            if updated_delta_account.pk.grsk == delta_account.pk.grsk && updated_delta_account.pk.grsk == updated_input_account.pk.grsk && delta_account.pk.grsk == updated_input_account.pk.grsk {
                
                // lets add delta_account and updated_input_account commitments
                let added_comm = ElGamalCommitment::add_commitments(&delta_account.comm, &updated_input_account.comm);
                if added_comm == updated_delta_account.comm {
                    return true
                }
            }
        }
        return false
    }

    // generate_sum_and_negate_rscalar generates scalars for delta and epsilon function
    // first 8 scalars are random, here returned in a vector
    // last scalar is the sum and then neg of the first 8 random scalars, here returned as a scalar
    pub fn generate_sum_and_negate_rscalar() -> (Vec<Scalar>, Scalar) {
        let mut random_scalars: Vec<Scalar> = Vec::new();
        for _x in 0..8 {
            random_scalars.push(Scalar::random(&mut OsRng));
        }
        let sum: Scalar = random_scalars.iter().sum();
        return (random_scalars, -sum)
    }

    // cheating_prover sums the epsilon vector commitments c, d as indidivual points and checks if they are identity
    // else returns false
    pub fn cheating_prover(epsilon_accounts: Vec<Account>) -> bool{

        let sum_c: RistrettoPoint = epsilon_accounts.iter().map(|s| s.comm.c.decompress().unwrap()).sum();
        let sum_d: RistrettoPoint = epsilon_accounts.iter().map(|s| s.comm.d.decompress().unwrap()).sum();
        
        if !sum_c.is_identity() || !sum_d.is_identity(){
            return false
        }else{
            return true
        }
        
    }
}

impl PartialEq for Account {
    fn eq(&self, other: &Account) -> bool {
        // Although this is slower than `self.compressed == other.compressed`, expanded point comparison is an equal
        // time comparision
        self.pk == other.pk && self.comm == other.comm
    }
}

impl Eq for Account {}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use rand::rngs::OsRng;
    #[test]
    fn verify_account_test(){
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        //generate a Zero balance account
        let acc = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account = Account::update_account(acc, 16, updated_keys_scalar, comm_scalar);
     
        assert!(updated_account.verify_account(&sk, 16), "Invalid Account or Invalid Secret Key");
    }

    #[test]
    fn decrypt_account_test(){
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        //generate a Zero balance account
        let acc = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account = Account::update_account(acc, 16, updated_keys_scalar, comm_scalar);

        let bl_scalar = Scalar::from(16 as u64);
        assert_eq!(updated_account.decrypt_account_balance(&sk, 16).unwrap(), (&bl_scalar * &RISTRETTO_BASEPOINT_TABLE).compress());
    }


    
    use crate::{
        keys::PublicKey,
        ristretto::RistrettoPublicKey
    };
    #[test]
    fn test_epsilon_and_delta() {

        let generate_base_pk = RistrettoPublicKey::generate_base_pk();

        let rscalar_sum_neg = Account::generate_sum_and_negate_rscalar();

        let mut rscalar : Scalar;
        let mut epsilon_accounts: Vec<Account> = Vec::new();

        let value_vector: Vec<i64> = vec![-5, 5, 0, 0, 0, 0, 0, 0, 0];

        for i in 0..9 {

            if i < 8 {
                rscalar = rscalar_sum_neg.0[i];
            }else{
                rscalar = rscalar_sum_neg.1;
            }

            let create_epsilon_account = Account::create_epsilon_account(value_vector[i], rscalar, generate_base_pk);

            epsilon_accounts.push(create_epsilon_account);
            
          }

          let check = Account::cheating_prover(epsilon_accounts);
          assert!(check);
    }
}
