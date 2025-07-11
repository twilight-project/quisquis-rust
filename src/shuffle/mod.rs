//! Shuffle proof implementation and cryptographic utilities for the Quisquis protocol.
//!
//! This module provides types and functions for cryptographic shuffling, permutation proofs,
//! and supporting vector/matrix operations. It includes the main shuffle argument, permutation
//! matrix logic, and helpers for polynomial, hadamard, and DDH proofs.
//!
//! ## Core Components
//!
//! - [`crate::shuffle::shuffle::Shuffle`] - Main shuffle protocol structure
//! - [`crate::shuffle::shuffle::Permutation`] - Permutation matrix logic
//! - [`crate::shuffle::shuffle::ShuffleProof`] / [`crate::shuffle::shuffle::ShuffleStatement`] - Shuffle argument proof and statement
//! - [`crate::shuffle::ddh::DDHProof`] / [`crate::shuffle::ddh::DDHStatement`] - DDH argument proof and statement
//! - [`crate::shuffle::MultiexpoProof`] - Multiexponential argument proof and statement
//! - [`crate::shuffle::ProductProof`] / [`crate::shuffle::ProductStatement`] - Product argument proof and statement
//! - [`crate::shuffle::hadamard::HadamardProof`] / [`crate::shuffle::hadamard::HadamardStatement`] - Hadamard argument proof and statement
//! - [`crate::shuffle::SVPProof`] / [`crate::shuffle::SVPStatement`] - Single value product argument proof and statement
//
//!
//! ## Example
//!
//! ```rust
//! use quisquislib::shuffle::{Shuffle, Permutation};
//! // ...
//! ```

/// Decisional Diffie-Hellman proof and statement types.
pub mod ddh;
/// Hadamard product proof and statement types.
pub mod hadamard;
/// Multiexponential product proof logic (internal).
mod multiexponential;
/// Polynomial proof and statement types.
pub mod polynomial;
/// Product proof logic (internal).
mod product;
/// Main shuffle protocol implementation.
pub mod shuffle;
/// Single-value product proof logic (internal).
mod singlevalueproduct;
/// Vector and matrix utility functions (internal, but re-exports ScalarExp).
mod vectorutil;

// Re-export commonly used types for convenience
pub use self::{
    multiexponential::MultiexpoProof, // Multiexponential proof
    product::{
        MultiHadamardProof, MultiHadamardStatement, ProductProof, ProductStatement, ZeroProof,
        ZeroStatement,
    }, // Product proof and statement
    shuffle::Permutation,             // Permutation matrix logic
    shuffle::Shuffle,                 // Main shuffle protocol
    shuffle::ShuffleProof,            // Shuffle argument proof
    shuffle::ShuffleStatement,        // Shuffle argument statement
    singlevalueproduct::{SVPProof, SVPStatement}, // Single value product proof and statement
    vectorutil::ScalarExp,            // Iterator for scalar exponentiation
};
