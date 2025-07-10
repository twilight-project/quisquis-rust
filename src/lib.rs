#![doc = include_str!("../README.md")]
#![doc(html_root_url = "https://docs.rs/quisquislib/latest")]
#![deny(missing_docs)]
#![deny(unsafe_code)]
#![warn(clippy::all)]
#![cfg_attr(docsrs, feature(doc_cfg))]
//#[doc = "For full documentation and guides, please refer to the `docs/` directory in this repository."]

/// Account management and cryptographic operations for privacy-preserving accounts.
///
/// This module provides the core functionality for creating, updating, and managing
/// accounts in the Quisquis protocol. Accounts consist of a public key and an ElGamal
/// commitment to the account balance, enabling privacy-preserving transactions.
pub mod accounts;

/// ElGamal commitment scheme implementation.
///
/// Provides homomorphic commitments that allow encrypted balance operations
/// while preserving privacy guarantees essential for the Quisquis protocol.
pub mod elgamal;

/// Generic cryptographic key management traits.
///
/// Defines common interfaces for public and secret key operations that
/// are implemented by specific cryptographic schemes.
pub mod keys;

/// Ristretto group operations and key management.
///
/// Built on the Ristretto group over Curve25519, providing secure elliptic curve
/// operations with strong security guarantees and resistance to various attacks.
pub mod ristretto;

/// Pedersen commitment scheme implementation.
///
/// Provides computationally binding and perfectly hiding commitments
/// used in various cryptographic protocols within Quisquis.
pub mod pedersen;

/// Cryptographic shuffle protocols for enhanced anonymity.
///
/// Implements advanced shuffling techniques that enhance transaction privacy
/// by mixing and reordering cryptographic elements.
pub mod shuffle;

// Re-export commonly used types for convenience
pub use accounts::Account;
pub use elgamal::ElGamalCommitment;
pub use ristretto::{RistrettoPublicKey, RistrettoSecretKey};

//pub mod transaction;
