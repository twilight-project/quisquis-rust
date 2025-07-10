//! Account management and cryptographic operations.
//!
//! This module provides the core functionality for managing privacy-preserving accounts
//! in the Quisquis protocol. It includes account creation, updates, verification,
//! and various cryptographic proofs.
//!
//! ## Core Components
//!
//! - [`crate::accounts::Account`] - The main account structure with encrypted balances
//! - [`crate::accounts::prover::Prover`] - Zero-knowledge proof generation for account operations
//! - [`crate::accounts::verifier::Verifier`] - Verification of zero-knowledge proofs
//! - [`crate::accounts::rangeproof::RangeProofProver`] / [`crate::accounts::rangeproof::RangeProofVerifier`] - Range proof operations
//! - [`crate::accounts::transcript::TranscriptProtocol`] - Transcript utilities for Fiat-Shamir transforms
//!
//! ## Examples
//!
//! ### Basic Account Operations
//!
//! ```rust
//! use quisquis_rust::accounts::Account;
//! use quisquis_rust::ristretto::{RistrettoSecretKey, RistrettoPublicKey};
//! use quisquis_rust::keys::{SecretKey, PublicKey};
//! use rand::rngs::OsRng;
//!
//! let mut rng = OsRng;
//! let secret_key = RistrettoSecretKey::random(&mut rng);
//! let public_key = RistrettoPublicKey::from_secret_key(&secret_key, &mut rng);
//!
//! // Create new account
//! let (account, _) = Account::generate_account(public_key);
//! ```

/// Account management and cryptographic operations.
pub mod accounts;
/// Prover for the Quisquis protocol.
pub mod prover;
/// Range proof operations for the Quisquis protocol.
pub mod rangeproof;
/// Transcript for the Quisquis protocol.
pub mod transcript;
/// Verifier for the Quisquis protocol.
pub mod verifier;

/// Re-export of the [`Account`] type for convenience.
pub use self::accounts::Account;
/// Re-export of the [`Prover`] and [`SigmaProof`] types for convenience.
pub use self::prover::{Prover, SigmaProof};
/// Re-export of the [`RangeProofProver`] and [`RangeProofVerifier`] types for convenience.
pub use self::rangeproof::{RangeProofProver, RangeProofVerifier};
/// Re-export of the [`TranscriptProtocol`] type for convenience.
pub use self::transcript::TranscriptProtocol;
/// Re-export of the [`Verifier`] type for convenience.
pub use self::verifier::Verifier;
