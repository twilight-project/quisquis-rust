//! Ristretto key types and operations for the Quisquis protocol.
//!
//! This module provides secret and public key types for the Ristretto group, along with
//! implementations of key generation, serialization, key updates, and digital signature operations.

use crate::{
    keys::{PublicKey, SecretKey},
    ristretto::constants::BASE_PK_BTC_COMPRESSED,
};
use core::ops::{Add, Mul};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE, ristretto::CompressedRistretto, scalar::Scalar,
};
use std::convert::TryInto;

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use sha2::Sha512;
use zkschnorr::{Signature, VerificationKey};

const SCALAR_LENGTH: usize = 32;
const PUBLIC_KEY_LENGTH: usize = 32;

// ------- SecretKey ------- //

/// Secret key for the Ristretto group, used in the Quisquis protocol.
///
/// Wraps a Curve25519 scalar and provides secure key operations.
#[derive(Debug)]
pub struct RistrettoSecretKey(pub(crate) Scalar);

impl SecretKey for RistrettoSecretKey {
    /// Returns the length of the secret key in bytes.
    fn key_length() -> usize {
        SCALAR_LENGTH
    }

    /// Generates a new random secret key using the provided random number generator.
    fn random<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        RistrettoSecretKey(Scalar::random(rng))
    }

    /// Constructs a secret key from a byte slice using a hash-to-scalar function.
    fn from_bytes(slice: &[u8]) -> Self {
        RistrettoSecretKey(Scalar::hash_from_bytes::<Sha512>(slice))
    }

    /// Serializes the secret key to a 32-byte array.
    fn as_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

// Implement equality and copy/clone for secret keys.
impl Eq for RistrettoSecretKey {}
impl PartialEq for RistrettoSecretKey {
    fn eq(&self, other: &RistrettoSecretKey) -> bool {
        // Uses constant-time equality defined for Scalar
        self.0.eq(&other.0)
    }
}

impl Copy for RistrettoSecretKey {}
impl Clone for RistrettoSecretKey {
    fn clone(&self) -> RistrettoSecretKey {
        *self
    }
}

// ------- PublicKey ------- //

/// Public key for the Ristretto group, used in the Quisquis protocol.
///
/// Consists of two compressed Ristretto points: `gr` and `grsk`.
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct RistrettoPublicKey {
    pub(crate) gr: CompressedRistretto,
    pub(crate) grsk: CompressedRistretto,
}

impl RistrettoPublicKey {
    /// Constructs a new public key from two compressed Ristretto points.
    ///
    /// # Arguments
    ///
    /// * `gr` - The base point multiplied by a random scalar.
    /// * `grsk` - The base point multiplied by the secret key and the random scalar.
    pub fn new_from_pk(gr: CompressedRistretto, grsk: CompressedRistretto) -> RistrettoPublicKey {
        RistrettoPublicKey { gr, grsk }
    }
}

impl PublicKey for RistrettoPublicKey {
    type K = RistrettoSecretKey;

    /// Generates a new public key from the given secret key and a random scalar.
    ///
    /// In Quisquis, the public key is constructed as (gr, grsk) where
    /// `gr = random_scalar * basepoint` and `grsk = sk * gr`.
    fn from_secret_key<R: Rng + CryptoRng>(k: &Self::K, rng: &mut R) -> RistrettoPublicKey {
        let random_scalar = Scalar::random(rng);
        let gr = &random_scalar * &RISTRETTO_BASEPOINT_TABLE;
        let grsk = &k.0 * &gr;
        RistrettoPublicKey::new_from_pk(gr.compress(), grsk.compress())
    }

    /// Returns the length of the public key in bytes.
    fn key_length() -> usize {
        PUBLIC_KEY_LENGTH
    }

    /// Serializes the public key to a 64-byte array.
    fn as_bytes(&self) -> [u8; 64] {
        let mut bytes: Vec<u8> = Vec::new();
        bytes.extend_from_slice(self.gr.as_bytes());
        bytes.extend_from_slice(self.grsk.as_bytes());
        bytes
            .try_into()
            .expect("slice with incorrect length. Should be 64 bytes")
    }

    /// Constructs a public key from a 64-byte slice.
    ///
    /// # Errors
    ///
    /// Returns an error if the slice is not 64 bytes or the points are invalid.
    fn from_bytes(slice: &[u8]) -> Result<RistrettoPublicKey, &'static str> {
        if slice.len() != 64 {
            return Err("slice with incorrect length. Should be 64 bytes");
        }
        let gr = CompressedRistretto::from_slice(&slice[0..32]);
        let grsk = CompressedRistretto::from_slice(&slice[32..64]);
        Ok(RistrettoPublicKey::new_from_pk(gr, grsk))
    }

    /// Updates the public key by multiplying both points with a random scalar.
    ///
    /// # Arguments
    ///
    /// * `p` - The original public key.
    /// * `rscalar` - The random scalar used for the update.
    ///
    /// # Returns
    ///
    /// The updated public key.
    fn update_public_key(p: &RistrettoPublicKey, rscalar: Scalar) -> RistrettoPublicKey {
        *p * &rscalar
    }

    /// Verifies that a public key update was performed correctly.
    ///
    /// # Arguments
    ///
    /// * `u` - The updated public key.
    /// * `p` - The original public key.
    /// * `rscalar` - The random scalar used for the update.
    ///
    /// # Returns
    ///
    /// `true` if the update is valid, `false` otherwise.
    fn verify_public_key_update(
        u: &RistrettoPublicKey,
        p: &RistrettoPublicKey,
        rscalar: Scalar,
    ) -> bool {
        let grr = &rscalar * &p.gr.decompress().unwrap();
        let grrsk = &rscalar * &p.grsk.decompress().unwrap();
        grr == u.gr.decompress().unwrap() && grrsk == u.grsk.decompress().unwrap()
    }

    /// Generates a base public key for the Ristretto group.
    ///
    /// This is a temporary solution using statically defined compressed points.
    fn generate_base_pk() -> RistrettoPublicKey {
        RistrettoPublicKey::new_from_pk(BASE_PK_BTC_COMPRESSED[0], BASE_PK_BTC_COMPRESSED[1])
    }

    /// Verifies that the given secret key corresponds to this public key.
    ///
    /// # Arguments
    ///
    /// * `privkey` - The secret key to verify against.
    ///
    /// # Errors
    ///
    /// Returns an error if the key pair is invalid.
    fn verify_keypair(self: &Self, privkey: &Self::K) -> Result<(), &'static str> {
        if self.grsk
            == (&privkey.0 * &self.gr.decompress().ok_or("Error::Decompression Failed")?).compress()
        {
            Ok(())
        } else {
            Err("Invalid Account::Keypair Verification Failed")
        }
    }

    /// Signs a message using the ZkSchnorr signature scheme.
    ///
    /// # Arguments
    ///
    /// * `msg` - The message to sign.
    /// * `privkey` - The secret key used for signing.
    /// * `label` - A domain separation label.
    ///
    /// # Returns
    ///
    /// The generated signature.
    fn sign_msg(&self, msg: &[u8], privkey: &Self::K, label: &'static [u8]) -> Signature {
        let verifying_key = VerificationKey::new(self.gr, self.grsk);
        Signature::sign_message(label, &msg, verifying_key, privkey.0)
    }

    /// Verifies a message signature using the ZkSchnorr signature scheme.
    ///
    /// # Arguments
    ///
    /// * `msg` - The signed message.
    /// * `signature` - The signature to verify.
    /// * `label` - A domain separation label.
    ///
    /// # Errors
    ///
    /// Returns an error if the signature is invalid.
    fn verify_msg(
        &self,
        msg: &[u8],
        signature: &Signature,
        label: &'static [u8],
    ) -> Result<(), &'static str> {
        let verifying_key = VerificationKey::new(self.gr, self.grsk);
        let verify = Signature::verify_message(&signature, label, msg, verifying_key);
        match verify {
            Ok(_) => Ok(()),
            Err(_) => Err("Invalid Signature"),
        }
    }
}

// ------- PublicKey Partial Eq, Eq, Add, Mul ------- //

impl PartialEq for RistrettoPublicKey {
    fn eq(&self, other: &RistrettoPublicKey) -> bool {
        // Although this is slower than `self.compressed == other.compressed`, expanded point comparison is an equal
        // time comparison
        self.gr == other.gr && self.grsk == other.grsk
    }
}

impl Eq for RistrettoPublicKey {}

impl<'a, 'b> Add<&'b RistrettoPublicKey> for &'a RistrettoPublicKey {
    type Output = RistrettoPublicKey;

    /// Adds two public keys by subtracting their decompressed points.
    ///
    /// # Returns
    ///
    /// A new public key representing the difference.
    fn add(self, other: &'b RistrettoPublicKey) -> RistrettoPublicKey {
        let grr = &self.gr.decompress().unwrap() - &other.gr.decompress().unwrap();
        let grsk = &self.grsk.decompress().unwrap() - &other.grsk.decompress().unwrap();
        RistrettoPublicKey::new_from_pk(grr.compress(), grsk.compress())
    }
}

impl<'b> Mul<&'b Scalar> for RistrettoPublicKey {
    type Output = RistrettoPublicKey;
    /// Multiplies the public key by a scalar.
    ///
    /// # Arguments
    ///
    /// * `scalar` - The scalar to multiply by.
    ///
    /// # Returns
    ///
    /// The resulting public key.
    fn mul(self, scalar: &'b Scalar) -> RistrettoPublicKey {
        let grr = scalar * self.gr.decompress().unwrap();
        let grsk = scalar * self.grsk.decompress().unwrap();
        RistrettoPublicKey::new_from_pk(grr.compress(), grsk.compress())
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use bulletproofs::PedersenGens;
    use rand::rngs::OsRng;
    #[test]
    fn update_key_test() {
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        // If you want to save a pk at this stage and not broadcast it, you can do so here
        // Use updated_pk below for further functions

        let random_scalar = Scalar::random(&mut OsRng);
        let updated_pk = RistrettoPublicKey::update_public_key(&pk, random_scalar);

        assert_ne!(pk, updated_pk)
    }
    #[test]
    fn verify_keypair_test() {
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        let _rsk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let random_scalar = Scalar::random(&mut OsRng);
        let updated_pk = RistrettoPublicKey::update_public_key(&pk, random_scalar);

        assert!(updated_pk.verify_keypair(&sk).is_ok(), "Invalid Key Pair")
    }
    #[test]
    fn base_pk_test() {
        let base_pk = RistrettoPublicKey::generate_base_pk();
        println!("{:?}", base_pk);

        let pd_gens = PedersenGens::default();
        println!("{:?}", pd_gens.B.compress());
        println!("{:?}", pd_gens.B_blinding.compress());

        assert_eq!(base_pk.gr, BASE_PK_BTC_COMPRESSED[0]);
        assert_eq!(base_pk.grsk, BASE_PK_BTC_COMPRESSED[1]);
    }
    #[test]
    fn signature_test() {
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        //convert to ZkSchnorr types

        let msg = "This is a signing message";
        let sign = pk.sign_msg(msg.as_bytes(), &sk, ("valueSign").as_bytes());
        let verify = pk.verify_msg(msg.as_bytes(), &sign, ("valueSign").as_bytes());
        assert!(verify.is_ok(), "Invalid Signature");
    }
}
