use rand::{CryptoRng, Rng};
use curve25519_dalek::scalar::Scalar;

pub trait SecretKey {
    fn key_length() -> usize;
    fn random<R: Rng + CryptoRng>(rng: &mut R) -> Self;
}

pub trait PublicKey {
    type K: SecretKey;

    fn from_secret_key<R: Rng + CryptoRng>(k: &Self::K, rng: &mut R) -> Self;

    fn key_length() -> usize;

    fn as_bytes(&self) -> Vec<u8>;

    fn update_public_key(p: &Self, rscalar: Scalar) -> Self;

    fn verify_public_key_update(u: &Self, p: &Self, rscalar: Scalar) -> bool;

    fn generate_base_pk() -> Self;
}
