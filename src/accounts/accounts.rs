use crate::{
    elgamal::elgamal::ElGamalCommitment,
    keys::{PublicKey, SecretKey},
    ristretto::{RistrettoPublicKey, RistrettoSecretKey},
};
use curve25519_dalek::{
    ristretto::CompressedRistretto,
    // constants::RISTRETTO_BASEPOINT_TABLE,
    scalar::Scalar,
};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
//use crate::ristretto::keys::_::_serde::ser::SerializeStruct;
#[derive(Serialize, Deserialize, Debug, Copy, Clone)]
pub struct Account {
    pub(crate) pk: RistrettoPublicKey,
    pub(crate) comm: ElGamalCommitment,
}

impl Account {
    // Private constructor
    fn set_account(pk: RistrettoPublicKey, comm: ElGamalCommitment) -> Account {
        Account { pk: pk, comm: comm }
    }
    /// generate_account creates a new account
    /// returns an account with (pk and Commitment with 0 balance) and commitment scalar for Annoynimity account proof
    pub fn generate_account(pk: RistrettoPublicKey) -> (Account, Scalar) {
        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        // lets generate a new commitment using pubkey
        let comm = ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::zero());

        let account = Account::set_account(pk, comm);

        return (account, comm_scalar);
    }
    /// Verifies the account balance stored in commitment
    /// Verifies the Private key and balance passed as input
    pub fn verify_account(
        self: &Self,
        sk: &RistrettoSecretKey,
        bl: Scalar,
    ) -> Result<(), &'static str> {
        self.pk.verify_keypair(sk)?;
        self.comm.verify_commitment(sk, bl)
    }
    /// Verifies the account public key belongs to a secret key
    ///
    pub fn verify_account_keypair(
        self: &Self,
        sk: &RistrettoSecretKey,
    ) -> Result<(), &'static str> {
        self.pk.verify_keypair(sk)
    }

    /// Decrypts the account balance and returns G*bl. Discrete log should be solved to extract bl
    /// The function shall be used with extreme caution. Ensure that account is verifiable before calling this method
    pub fn decrypt_account_balance(
        self: &Self,
        sk: &RistrettoSecretKey,
        bl: Scalar,
    ) -> Result<CompressedRistretto, &'static str> {
        self.verify_account(sk, bl)?;
        Ok(self.comm.decommit(sk))
    }

    // update_account updates an account by creating pk' and comm' with 0 balance
    // returns acc'(pk', comm')
    pub fn update_account(
        a: Account,
        bl: Scalar,
        update_key_scalar: Scalar,
        generate_commitment_scalar: Scalar,
    ) -> Account {
        // lets first update the pk
        let updated_pk = RistrettoPublicKey::update_public_key(&a.pk, update_key_scalar);

        // lets update the commitment
        let new_comm =
            ElGamalCommitment::generate_commitment(&a.pk, generate_commitment_scalar, bl);

        // lets add old and new commitments
        let updated_comm = ElGamalCommitment::add_commitments(&new_comm, &a.comm);

        Account::set_account(updated_pk, updated_comm)
    }

    // verify_update_account verifies if an account was updated properly
    pub fn verify_account_update(
        updated_input_accounts: &Vec<Account>,
        accounts: &Vec<Account>,
        updated_keys_scalar: &Vec<Scalar>,
        generate_commitment_scalar: &Vec<Scalar>,
    ) -> bool {
        let mut updated_accounts: Vec<Account> = Vec::new();
        for i in 0..9 {
            updated_accounts.push(Account::update_account(
                accounts[i],
                Scalar::zero(),
                updated_keys_scalar[i],
                generate_commitment_scalar[i],
            ));
        }

        if updated_accounts
            .iter()
            .zip(updated_input_accounts.iter())
            .all(|(u, i)| u.eq(&i))
        {
            return true;
        } else {
            return false;
        }
    }

    // create_delta_and_epsilon_accounts creates account delta and account epsilon
    // takes Accounts vector, bl (updated balance), base_pair generated with fixed-g
    // returns Account Epsilon and Delta
    pub fn create_delta_and_epsilon_accounts(
        a: &[Account],
        bl: &[Scalar],
        base_pk: RistrettoPublicKey,
    ) -> (Vec<Account>, Vec<Account>, Vec<Scalar>) {
        let rscalar = Account::generate_sum_and_negate_rscalar();
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

        return (delta_account_vector, epsilon_account_vector, rscalar);
    }

    // update_delta_accounts takes vectors of updated_accounts and delta_accounts, multiplies their commitments
    // returns updated delta accounts
    pub fn update_delta_accounts(
        updated_accounts: &[Account],
        delta_accounts: &[Account],
    ) -> Result<Vec<Account>, &'static str> {
        if updated_accounts
            .iter()
            .zip(delta_accounts.iter())
            .all(|(u, d)| u.pk.eq(&d.pk))
        {
            Ok(updated_accounts
                .iter()
                .zip(delta_accounts.iter())
                .map(|(updated_account, delta_account)| {
                    Account::set_account(
                        updated_account.pk,
                        ElGamalCommitment::add_commitments(
                            &updated_account.comm,
                            &delta_account.comm,
                        ),
                    )
                })
                .collect::<Vec<_>>())
        } else {
            Err("pks are not equal")
        }
    }
    // verify_delta_update verifies if account delta was updated correctly
    pub fn verify_delta_update(
        updated_delta_accounts: &Vec<Account>,
        delta_accounts: &Vec<Account>,
        updated_input_accounts: &Vec<Account>,
    ) -> Result<bool, &'static str> {
        // first check if pks of all accounts passed are the same
        if updated_delta_accounts
            .iter()
            .zip(delta_accounts.iter())
            .all(|(u, d)| u.pk.eq(&d.pk))
            && updated_delta_accounts
                .iter()
                .zip(updated_input_accounts.iter())
                .all(|(u, i)| u.pk.eq(&i.pk))
        {
            // now add the commitments of delta_accounts and updated_input_accounts and collect them in a vector
            let added_comms = delta_accounts
                .iter()
                .zip(updated_input_accounts.iter())
                .map(|(delta_account, updated_input_account)| {
                    ElGamalCommitment::add_commitments(
                        &delta_account.comm,
                        &updated_input_account.comm,
                    )
                })
                .collect::<Vec<_>>();

            // now check if added commitments are equal to the commitments in updated_delta_accounts
            Ok(updated_delta_accounts
                .iter()
                .zip(added_comms.iter())
                .all(|(u, a)| u.comm.eq(a)))
        } else {
            Err("pks are not equal")
        }
    }

    // create_epsilon_account generates a single epsilon account for sender
    pub fn create_epsilon_account(
        base_pk: RistrettoPublicKey,
        rscalar: Scalar,
        bl: i64,
    ) -> Account {
        let bl_scalar: Scalar;
        if bl >= 0i64 {
            bl_scalar = Scalar::from(bl as u64);
        } else {
            panic!("Not enough balance in the sender account");
        }
        let comm_epsilon = ElGamalCommitment::generate_commitment(&base_pk, rscalar, bl_scalar);
        Account::set_account(base_pk, comm_epsilon)
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
        return random_scalars;
    }

    // generate_random_account_with_value generates a random account with a given value
    // this function is being used to produce tests and for anonymity account generation
    pub fn generate_random_account_with_value(amount: Scalar) -> (Account, RistrettoSecretKey) {
        let mut rng = rand::thread_rng();
        let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);

        let (acc, _) = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account =
            Account::update_account(acc, amount, updated_keys_scalar, comm_scalar);

        return (updated_account, sk);
    }
}

impl PartialEq for Account {
    fn eq(&self, other: &Account) -> bool {
        // Although this is slower than `self.compressed == other.compressed`, expanded point comparison is an equal
        // time comparision
        self.pk == other.pk && self.comm == other.comm
    }
}

// impl Serialize for Account {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//     where
//         S: Serializer,
//     {
//         // 3 is the number of fields in the struct.
//         let mut state = serializer.serialize_struct("Account", 2)?;
//         state.serialize_field("pk", &self.pk)?;
//         state.serialize_field("comm", &self.comm)?;
//         state.end()
//     }
// }

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use rand::rngs::OsRng;
    #[test]
    fn verify_account_test() {
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        //generate a Zero balance account
        let (acc, _) = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account =
            Account::update_account(acc, Scalar::from(16u64), updated_keys_scalar, comm_scalar);

        assert!(updated_account.verify_account(&sk, 16u64.into()).is_ok());
    }

    #[test]
    fn decrypt_account_test() {
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        //generate a Zero balance account
        let (acc, _) = Account::generate_account(pk);

        let updated_keys_scalar = Scalar::random(&mut OsRng);

        // lets get a random scalar
        let comm_scalar = Scalar::random(&mut OsRng);

        let updated_account =
            Account::update_account(acc, 16u64.into(), updated_keys_scalar, comm_scalar);

        let bl_scalar = Scalar::from(16 as u64);
        assert_eq!(
            updated_account
                .decrypt_account_balance(&sk, 16u64.into())
                .unwrap(),
            (&bl_scalar * &RISTRETTO_BASEPOINT_TABLE).compress()
        );
    }

    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;

    #[test]
    fn update_delta_account_test() {
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
                Account::update_account(acc, 0u64.into(), updated_keys_scalar, comm_scalar);

            account_vector.push(updated_account);
        }

        let delta_and_epsilon_accounts = Account::create_delta_and_epsilon_accounts(
            &account_vector,
            &value_vector,
            generate_base_pk,
        );

        let updated_delta_accounts =
            Account::update_delta_accounts(&account_vector, &delta_and_epsilon_accounts.0);

        let check = Account::verify_delta_update(
            &updated_delta_accounts.as_ref().unwrap(),
            &delta_and_epsilon_accounts.0,
            &account_vector,
        );
        assert!(check.unwrap());
    }

    #[test]
    fn verify_account_update_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        let mut updated_account_vector: Vec<Account> = Vec::new();
        let mut updated_keys_scalar_vector: Vec<Scalar> = Vec::new();
        let mut generate_commitment_scalar_vector: Vec<Scalar> = Vec::new();

        for _i in 0..9 {
            let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);

            // lets get a random scalar to update the account
            let updated_keys_scalar = Scalar::random(&mut OsRng);
            updated_keys_scalar_vector.push(updated_keys_scalar);

            // lets get a random scalar to update the commitments
            let comm_scalar = Scalar::random(&mut OsRng);
            generate_commitment_scalar_vector.push(comm_scalar);

            let updated_account =
                Account::update_account(acc, 0u64.into(), updated_keys_scalar, comm_scalar);

            updated_account_vector.push(updated_account);
        }

        let check = Account::verify_account_update(
            &updated_account_vector,
            &account_vector,
            &updated_keys_scalar_vector,
            &generate_commitment_scalar_vector,
        );
        assert!(check);
    }
}
