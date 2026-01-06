//! Account structure and operations for the Quisquis protocol.
//!
//! This module defines the [`Account`] type and provides methods for account creation,
//! updates, verification, and privacy-preserving balance management.

use crate::{
    elgamal::elgamal::ElGamalCommitment,
    keys::{PublicKey, SecretKey},
    ristretto::{RistrettoPublicKey, RistrettoSecretKey},
};
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

/// A privacy-preserving account in the Quisquis protocol.
///
/// An `Account` consists of a public key and an ElGamal commitment that encrypts
/// the account balance. This design enables privacy-preserving transactions where
/// account balances remain hidden while still allowing verification of transaction validity.
///
/// ## Privacy Properties
///
/// - **Balance Privacy**: Account balances are encrypted using ElGamal commitments
/// - **Unlinkability**: Account updates create new unlinkable account representations
/// - **Zero-Knowledge**: Proofs can be generated without revealing sensitive information
///
/// ## Example
///
/// ```rust
/// use quisquislib::accounts::Account;
/// use quisquislib::ristretto::{RistrettoSecretKey, RistrettoPublicKey};
/// use quisquislib::keys::{SecretKey, PublicKey};
/// use curve25519_dalek::scalar::Scalar;
/// use rand::rngs::OsRng;
///
/// // Generate a keypair
/// let mut rng = OsRng;
/// let secret_key = RistrettoSecretKey::random(&mut rng);
/// let public_key = RistrettoPublicKey::from_secret_key(&secret_key, &mut rng);
///
/// // Create a new account with zero balance
/// let (account, commitment_scalar) = Account::generate_account(public_key);
///
/// // Verify the account
/// assert!(account.verify_account(&secret_key, Scalar::ZERO).is_ok());
/// ```
#[derive(Clone, Debug, Serialize, Deserialize, Copy)]
pub struct Account {
    /// The public key component of the account.
    pub(crate) pk: RistrettoPublicKey,
    /// The ElGamal commitment encrypting the account balance.
    pub(crate) comm: ElGamalCommitment,
}

impl Account {
    /// Creates a new account from a public key and ElGamal commitment.
    ///
    /// This is a low-level constructor. For most use cases, prefer
    /// [`generate_account`](Account::generate_account) which creates a properly
    /// initialized account with zero balance.
    pub fn set_account(pk: RistrettoPublicKey, comm: ElGamalCommitment) -> Account {
        Account { pk, comm }
    }

    /// Generates a new account with zero balance.
    ///
    /// Creates a fresh account with the given public key and a commitment to zero balance.
    /// The commitment uses a random scalar for privacy, which is returned alongside the account.
    pub fn generate_account(pk: RistrettoPublicKey) -> (Account, Scalar) {
        let comm_scalar = Scalar::random(&mut OsRng);
        let comm = ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::ZERO);
        let account = Account::set_account(pk, comm);
        (account, comm_scalar)
    }

    /// Verifies that the account is valid for the given secret key and balance.
    ///
    /// This method performs two checks:
    /// 1. Verifies that the secret key corresponds to the account's public key
    /// 2. Verifies that the commitment correctly encrypts the claimed balance
    pub fn verify_account(&self, sk: &RistrettoSecretKey, bl: Scalar) -> Result<(), &'static str> {
        self.pk.verify_keypair(sk)?;
        self.comm.verify_commitment(sk, bl)
    }

    /// Verifies that the secret key corresponds to the account's public key.
    ///
    /// This is a subset of [`verify_account`](Account::verify_account) that only
    /// checks the keypair validity without verifying the balance commitment.
    pub fn verify_account_keypair(&self, sk: &RistrettoSecretKey) -> Result<(), &'static str> {
        self.pk.verify_keypair(sk)
    }

    /// Decrypts the account balance using the secret key.
    ///
    /// ⚠️ **Security Warning**: This method requires the claimed balance to verify
    /// the account first. Use with extreme caution and ensure the account is valid
    /// before calling this method.
    ///
    /// The returned group element represents G*balance. To extract the actual
    /// balance value, you need to solve the discrete logarithm problem, which
    /// is only feasible for small balance values.
    pub fn decrypt_account_balance(
        &self,
        sk: &RistrettoSecretKey,
        bl: Scalar,
    ) -> Result<CompressedRistretto, &'static str> {
        self.verify_account(sk, bl)?;
        Ok(self.comm.decommit(sk))
    }

    /// Decrypts and returns the account balance value.
    ///
    /// This method attempts to decrypt the account balance and extract the actual
    /// scalar value. It first verifies the keypair validity before attempting decryption.
    ///
    /// This method may only work for small balance values due to the discrete
    /// logarithm problem complexity.
    pub fn decrypt_account_balance_value(
        &self,
        sk: &RistrettoSecretKey,
    ) -> Result<Scalar, &'static str> {
        self.pk.verify_keypair(sk)?;
        match self.comm.decommit_value(sk) {
            Some(bl) => Ok(bl),
            None => Err("Decryption value failed."),
        }
    }

    /// Returns the account's public key and commitment.
    ///
    /// This method provides access to the account's components, which can be
    /// used for creating transaction outputs or other cryptographic operations.
    pub fn get_account(&self) -> (RistrettoPublicKey, ElGamalCommitment) {
        (self.pk, self.comm)
    }

    /// Updates an account with a new balance and key.
    ///
    /// This creates a new account representation that is unlinkable to the original
    /// account while maintaining the same underlying identity. The balance is updated
    /// and the public key is refreshed for privacy.
    pub fn update_account(
        a: Account,
        bl: Scalar,
        update_key_scalar: Scalar,
        generate_commitment_scalar: Scalar,
    ) -> Account {
        let updated_pk = RistrettoPublicKey::update_public_key(&a.pk, update_key_scalar);
        let new_comm =
            ElGamalCommitment::generate_commitment(&a.pk, generate_commitment_scalar, bl);
        let updated_comm = ElGamalCommitment::add_commitments(&new_comm, &a.comm);
        Account::set_account(updated_pk, updated_comm)
    }

    /// Verifies if an account was updated properly.
    ///
    /// This method checks if the updated account matches the expected state after
    /// applying the update operations. It verifies the updated account's public key
    /// and commitment against the expected values.
    ///
    /// # Arguments
    ///
    /// * `updated_input_accounts` - The expected updated accounts
    /// * `accounts` - The original accounts
    /// * `updated_keys_scalar` - The scalars used to update the public keys
    /// * `generate_commitment_scalar` - The scalars used to generate the commitments
    ///
    /// # Returns
    ///
    /// * `true` if the account was updated properly
    /// * `false` if the account was not updated properly
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
                Scalar::ZERO,
                updated_keys_scalar[i],
                generate_commitment_scalar[i],
            ));
        }

        updated_accounts
            .iter()
            .zip(updated_input_accounts.iter())
            .all(|(u, i)| u.eq(&i))
    }

    /// Creates delta and epsilon accounts for a set of input accounts and balances.
    ///
    /// Returns vectors of delta and epsilon accounts, and the random scalars used.
    pub fn create_delta_and_epsilon_accounts(
        a: &[Account],
        bl: &[Scalar],
        base_pk: RistrettoPublicKey,
    ) -> (Vec<Account>, Vec<Account>, Vec<Scalar>) {
        let rscalar = Account::generate_sum_and_negate_rscalar(a.len());
        let mut delta_account_vector: Vec<Account> = Vec::new();
        let mut epsilon_account_vector: Vec<Account> = Vec::new();

        for (i, acc) in a.iter().enumerate() {
            // Commitment for delta using Pk and r'
            let comm_delta = ElGamalCommitment::generate_commitment(&acc.pk, rscalar[i], bl[i]);
            let account_delta = Account::set_account(a[i].pk, comm_delta);
            delta_account_vector.push(account_delta);

            // Commitment for epsilon using base_pk and r
            let comm_epsilon = ElGamalCommitment::generate_commitment(&base_pk, rscalar[i], bl[i]);
            let account_epsilon = Account::set_account(base_pk, comm_epsilon);
            epsilon_account_vector.push(account_epsilon);
        }

        (delta_account_vector, epsilon_account_vector, rscalar)
    }

    /// Updates delta accounts by adding commitments from updated and delta accounts.
    ///
    /// Returns a vector of updated delta accounts if the public keys match.
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

    /// Verifies if delta accounts were updated correctly.
    ///
    /// Checks that the commitments in `updated_delta_accounts` are the sum of the
    /// corresponding commitments in `delta_accounts` and `updated_input_accounts`.
    pub fn verify_delta_update(
        updated_delta_accounts: &[Account],
        delta_accounts: &[Account],
        updated_input_accounts: &[Account],
    ) -> Result<bool, &'static str> {
        // Check if all public keys match
        if updated_delta_accounts
            .iter()
            .zip(delta_accounts.iter())
            .all(|(u, d)| u.pk.eq(&d.pk))
            && updated_delta_accounts
                .iter()
                .zip(updated_input_accounts.iter())
                .all(|(u, i)| u.pk.eq(&i.pk))
        {
            // Add the commitments and compare
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

    /// Creates a single epsilon account for a sender.
    ///
    /// # Panics
    ///
    /// Panics if the balance is negative.
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

    /// Generates random scalars for delta and epsilon functions.
    ///
    /// The first `len-1` scalars are random, and the last is the negative sum of the previous.
    pub fn generate_sum_and_negate_rscalar(len: usize) -> Vec<Scalar> {
        let mut random_scalars: Vec<Scalar> = Vec::new();
        for _x in 0..len - 1 {
            random_scalars.push(Scalar::random(&mut OsRng));
        }
        let sum: Scalar = random_scalars.iter().sum();
        random_scalars.push(-sum);
        random_scalars
    }

    /// Generates a random account with a given value.
    ///
    /// This function is used for tests and anonymity account generation.
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

        (updated_account, sk)
    }
}

impl PartialEq for Account {
    fn eq(&self, other: &Account) -> bool {
        // Although this is slower than `self.compressed == other.compressed`, expanded point comparison is an equal
        // time comparison
        self.pk == other.pk && self.comm == other.comm
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use curve25519_dalek::ristretto::RistrettoPoint;
    use rand::rngs::OsRng;
    use std::i64;
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
            (RistrettoPoint::mul_base(&bl_scalar)).compress()
        );
    }
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
    #[test]
    fn verify_delta_account_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        let mut sk_vector: Vec<RistrettoSecretKey> = Vec::new();

        //create random accounts
        for _i in 0..9 {
            let (acc, sk) = Account::generate_random_account_with_value(10u64.into());
            account_vector.push(acc);
            sk_vector.push(sk);
        }
        println!(
            "{:?}",
            account_vector[0].verify_account(&sk_vector[0], Scalar::from(10u64))
        );
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let minus: i64 = -5i64;
        let five: u64 = minus.unsigned_abs();
        let value_vector: Vec<Scalar> = vec![
            -Scalar::from(five),
            4u64.into(),
            3u64.into(),
            2u64.into(),
            1u64.into(),
            Scalar::ZERO - Scalar::from(5i64 as u64),
            -Scalar::from(5u64),
            0u64.into(),
            0u64.into(),
        ];

        println!("Value : {:?}", value_vector);
        let delta =
            Account::create_delta_and_epsilon_accounts(&account_vector, &value_vector, base_pk).0;
        //println!("Delta : {:?}", delta);
        let updated_delta_vector = Account::update_delta_accounts(&account_vector, &delta).unwrap();

        //test accounts for there sk
        println!(
            "{:?}",
            delta[0].verify_account(&sk_vector[0], value_vector[0].clone())
        );
        println!(
            "{:?}",
            updated_delta_vector[0].verify_account(&sk_vector[0], Scalar::from(5u64))
        );
        // println!(
        //     "{:?}",
        //     delta[2]
        //         .comm
        //         .verify_commitment(&sk_vector[2], value_vector[2].clone())
        // );
        // println!(
        //     "{:?}",
        //     delta[3]
        //         .comm
        //         .verify_commitment(&sk_vector[3], value_vector[3].clone())
        // );
        // println!(
        //     "{:?}",
        //     delta[4]
        //         .comm
        //         .verify_commitment(&sk_vector[4], value_vector[4].clone())
        // );
        // for i in 0..9 {
        //     println!(
        //         "check : {:?}",
        //         delta[i].verify_account(&sk_vector[i], value_vector[i].clone())
        //     );
        // }
        //assert!(check);
    }
    #[test]
    fn get_account_test() {
        let mut account_vector: Vec<Account> = Vec::new();

        //create random accounts
        for _i in 0..2 {
            let (acc, _sk) = Account::generate_random_account_with_value(10u64.into());
            account_vector.push(acc);
        }
        let (pk, comm) = account_vector[0].get_account();
        println!("{:?} \n {:?}", pk, comm);
    }
    #[test]
    fn test_account_decrypt_value() {
        use rand::rngs::OsRng;
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        let comm_scalar = Scalar::random(&mut OsRng);
        let comm =
            ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::from(16734 as u64));
        let account = Account::set_account(pk, comm);
        let decrypted_scalar = account.decrypt_account_balance_value(&sk).unwrap();
        assert_eq!(decrypted_scalar, Scalar::from(16734 as u64));
    }
}
