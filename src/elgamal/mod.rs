//! ElGamal commitment scheme for the Quisquis protocol.
//!
//! This module provides types and functions for creating and manipulating ElGamal commitments
//! using the Ristretto group.

/// ElGamal commitment implementation and API.
pub mod elgamal;

/// Re-export of the [`ElGamalCommitment`] type for convenience.
pub use self::elgamal::ElGamalCommitment;
