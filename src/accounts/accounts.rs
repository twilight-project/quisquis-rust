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

    // create_delta_and_epsilon_accounts creates account delta and account epsilon
    // takes Accounts vector, bl (updated balance), base_pair generated with fixed-g
    // returns Account Epsilon and Delta
    pub fn create_delta_and_epsilon_accounts(a: &Vec<Account>, bl: &Vec<i64>, base_pk: RistrettoPublicKey) -> (Vec<Account>, Vec<Account>, Vec<Scalar>) {

        let rscalar = Account::generate_sum_and_negate_rscalar();
        //let mut rscalar : Scalar;
        let mut delta_account_vector: Vec<Account> = Vec::new();
        let mut epsilon_account_vector: Vec<Account> = Vec::new();

        for i in 0..9 {
            // lets generate commitment on v for delta using Pk and r'
            let comm_delta = ElGamalCommitment::generate_commitment(&a[i].pk, rscalar[i], bl[i]);
            let account_delta = Account::set_account(a[i].pk, comm_delta);
            delta_account_vector.push(account_delta);

            // lets generate commitment on v for epsilon using GP and r
            let comm_epsilon = ElGamalCommitment::generate_commitment(&base_pk, rscalar[i], bl[i]);
            let account_epsilon = Account::set_account(base_pk, comm_epsilon);
            epsilon_account_vector.push(account_epsilon);
        }

        return (delta_account_vector, epsilon_account_vector, rscalar)

    }

    // update_delta_accounts takes vectors of updated_accounts and delta_accounts, multiplies their commitments
    // returns updated delta accounts
    pub fn update_delta_accounts(updated_accounts: &Vec<Account>, delta_accounts: &Vec<Account>) ->  Result<Vec<Account>, &'static str> 
    {

        if updated_accounts.iter().zip(delta_accounts.iter()).all(|(u, d)| u.pk.eq(&d.pk)){
            Ok(
                updated_accounts.iter().zip(delta_accounts.iter())
                .map(|(updated_account, delta_account)|
                    Account::set_account(
                        updated_account.pk, 
                        ElGamalCommitment::add_commitments(&updated_account.comm, &delta_account.comm)
                    )
                ).collect::<Vec<_>>()
            )
        }else{
            Err("pks are not equal")
        }
    }
    // verify_delta_update verifies if account delta was updated correctly
    pub fn verify_delta_update(updated_delta_accounts: &Vec<Account>, delta_accounts: &Vec<Account>, updated_input_accounts: &Vec<Account>) -> Result<bool>, &'static str> 
    {

        if updated_delta_accounts.iter().zip(delta_accounts.iter()).all(|(u, d)| u.pk.eq(&d.pk)) && updated_delta_accounts.iter().zip(updated_input_accounts.iter()).all(|(u, i)| u.pk.eq(&i.pk)){
            println!("hello");
            Ok(
                ElGamalCommitment::add_commitments(&delta_account.comm, &updated_input_account.comm)
            )
        }else{
            Err("pks are not equal")
        }
            //Ok(
                // updated_accounts.iter().zip(delta_accounts.iter())
                // .map(|(updated_account, delta_account)|
                //     Account::set_account(
                //         updated_account.pk, 
                //         ElGamalCommitment::add_commitments(&updated_account.comm, &delta_account.comm)
                //     )
                // ).collect::<Vec<_>>();
            //)
        // }else{
        //     Err("pks are not equal")
        // }

        // if updated_delta_account.pk.gr == delta_account.pk.gr && updated_delta_account.pk.gr == updated_input_account.pk.gr && delta_account.pk.gr == updated_input_account.pk.gr {
        //     if updated_delta_account.pk.grsk == delta_account.pk.grsk && updated_delta_account.pk.grsk == updated_input_account.pk.grsk && delta_account.pk.grsk == updated_input_account.pk.grsk {
                
        //         // lets add delta_account and updated_input_account commitments
        //         let added_comm = ElGamalCommitment::add_commitments(&delta_account.comm, &updated_input_account.comm);
        //         if added_comm == updated_delta_account.comm {
        //             return true
        //         }
        //     }
        // }
        // return false
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


    ///////////////////////////////////////////// Misc. Methods /////////////////////////////////////////////

    // generate_sum_and_negate_rscalar generates scalars for delta and epsilon function
    // first 8 scalars are random, here returned in a vector
    // last scalar is the sum and then neg of the first 8 random scalars, here returned as a scalar
    pub fn generate_sum_and_negate_rscalar() -> Vec<Scalar> {
        let mut random_scalars: Vec<Scalar> = Vec::new();
        for _x in 0..8 {
            random_scalars.push(Scalar::random(&mut OsRng));
        }
        let sum: Scalar = random_scalars.iter().sum();
        random_scalars.push(-sum);
        return random_scalars
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
        keys::{PublicKey, SecretKey},
        ristretto::{
            RistrettoPublicKey,
            RistrettoSecretKey
        }
    };
    #[test]
    fn cheating_prover_test() {

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
          let delta_and_epsilon_accounts = Account::create_delta_and_epsilon_accounts(&account_vector, &value_vector, generate_base_pk); 

          let check = Account::cheating_prover(delta_and_epsilon_accounts.1);
          assert!(check);
    }

    #[test]
    fn update_delta_account_test() {
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
          let delta_and_epsilon_accounts = Account::create_delta_and_epsilon_accounts(&account_vector, &value_vector, generate_base_pk);

          let updated_delta_accounts = Account::update_delta_accounts(&account_vector, &delta_and_epsilon_accounts.0);

          for i in 0..9 {
            let updated_delta_account = Account::verify_delta_update(&updated_delta_accounts.as_ref().unwrap(), &delta_and_epsilon_accounts.0, &account_vector);
            println!("updated_delta_account {:?}", updated_delta_account);
          }
    }
}
