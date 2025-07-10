//! Ristretto group operations and key management.
//!
//! This module provides cryptographic key operations built on the Ristretto group
//! over Curve25519. Ristretto provides a secure, high-performance elliptic curve
//! group that is resistant to various attacks and provides clean abstractions
//! for cryptographic protocols.
//!
//! ## Features
//!
//! - **Secure Key Generation**: Cryptographically secure key pair generation
//! - **Key Updates**: Privacy-preserving key updates for unlinkability
//! - **Digital Signatures**: Schnorr signature scheme integration
//! - **Constant-time Operations**: Resistance to timing attacks
//!
//! ## Security Properties
//!
//! - Based on the discrete logarithm problem in the Ristretto group
//! - Provides 128-bit security level
//! - Resistant to small subgroup attacks
//! - Clean, uniform random point encoding
//!
//! ## Example
//!
//! ```rust
//! use quisquislib::ristretto::{RistrettoSecretKey, RistrettoPublicKey};
//! use quisquislib::keys::{SecretKey, PublicKey};
//! use rand::rngs::OsRng;
//!
//! // Generate a secure keypair
//! let mut rng = OsRng;
//! let secret_key = RistrettoSecretKey::random(&mut rng);
//! let public_key = RistrettoPublicKey::from_secret_key(&secret_key, &mut rng);
//!
//! // Verify the keypair
//! assert!(public_key.verify_keypair(&secret_key).is_ok());
//! ```

pub mod constants;
pub mod keys;

// Re-export commonly used types
pub use self::keys::{RistrettoPublicKey, RistrettoSecretKey};
