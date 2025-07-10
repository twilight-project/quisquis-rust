use curve25519_dalek::scalar::Scalar;
use rand::{CryptoRng, Rng};
use zkschnorr::Signature;

use crate::ristretto::RistrettoPublicKey;

/// Trait for secret (private) key operations in cryptographic schemes.
///
/// Implementors of this trait provide methods for key generation,
/// serialization, and deserialization.
pub trait SecretKey {
    /// Returns the length of the secret key in bytes.
    fn key_length() -> usize;

    /// Generates a new random secret key using the provided random number generator.
    ///
    /// # Arguments
    ///
    /// * `rng` - A cryptographically secure random number generator.
    fn random<R: Rng + CryptoRng>(rng: &mut R) -> Self;

    /// Constructs a secret key from a byte slice.
    ///
    /// # Arguments
    ///
    /// * `slice` - A byte slice containing the secret key material.
    fn from_bytes(slice: &[u8]) -> Self;

    /// Serializes the secret key to a 32-byte array.
    fn as_bytes(&self) -> [u8; 32];
}

/// Trait for public key operations in cryptographic schemes.
///
/// This trait defines methods for deriving public keys from secret keys,
/// serialization, verification, and digital signature operations.
pub trait PublicKey {
    /// The associated secret key type for this public key.
    type K: SecretKey;

    /// Derives a public key from the given secret key using the provided RNG.
    ///
    /// # Arguments
    ///
    /// * `k` - The secret key.
    /// * `rng` - A cryptographically secure random number generator.
    fn from_secret_key<R: Rng + CryptoRng>(k: &Self::K, rng: &mut R) -> Self;

    /// Returns the length of the public key in bytes.
    fn key_length() -> usize;

    /// Serializes the public key to a 64-byte array.
    fn as_bytes(&self) -> [u8; 64];

    /// Constructs a public key from a byte slice.
    ///
    /// # Arguments
    ///
    /// * `slice` - A byte slice containing the public key material.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte slice is not a valid public key.
    fn from_bytes(slice: &[u8]) -> Result<RistrettoPublicKey, &'static str>;

    /// Updates the public key using a random scalar.
    ///
    /// # Arguments
    ///
    /// * `p` - The original public key.
    /// * `rscalar` - The random scalar used for the update.
    /// Returns the updated public key.
    fn update_public_key(p: &Self, rscalar: Scalar) -> Self;

    /// Verifies that a public key update was performed correctly.
    ///
    /// # Arguments
    ///
    /// * `u` - The updated public key.
    /// * `p` - The original public key.
    /// * `rscalar` - The random scalar used for the update.
    /// Returns true if the update was performed correctly, false otherwise.
    fn verify_public_key_update(u: &Self, p: &Self, rscalar: Scalar) -> bool;

    /// Generates a base public key (e.g., the generator point).
    fn generate_base_pk() -> Self;

    /// Verifies that the given secret key corresponds to this public key.
    ///
    /// # Arguments
    ///
    /// * `privkey` - The secret key to verify against.
    ///
    /// # Errors
    ///
    /// Returns an error if the key pair is invalid.
    fn verify_keypair(self: &Self, privkey: &Self::K) -> Result<(), &'static str>;

    /// Signs a message with the given secret key and label.
    ///
    /// # Arguments
    ///
    /// * `msg` - The message to sign.
    /// * `privkey` - The secret key used for signing.
    /// * `label` - A domain separation label.
    /// Returns the signature.
    fn sign_msg(&self, msg: &[u8], privkey: &Self::K, label: &'static [u8]) -> Signature;

    /// Verifies a message signature with the given label.
    ///
    /// # Arguments
    ///
    /// * `msg` - The signed message.
    /// * `sig` - The signature to verify.
    /// * `label` - A domain separation label.
    ///
    /// # Errors
    ///
    /// Returns an error if the signature is invalid.
    fn verify_msg(
        &self,
        msg: &[u8],
        sig: &Signature,
        label: &'static [u8],
    ) -> Result<(), &'static str>;
}
