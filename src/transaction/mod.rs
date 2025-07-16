//! Transaction subsystem handling Quisquis transfers.
//!
//! This module groups the building blocks used to construct and verify
//! transactions. [`transaction`] defines the [`Sender`] and [`Receiver`] roles
//! participating in a transfer while [`signature`] provides the
//! Schnorr-style primitives used to authorise them.

//pub mod transaction;
//pub mod signature;

// Re-export commonly used items for convenience.
//pub use self::{
  //  transaction::{Sender, Receiver},
    //signature::{Signature, VerificationKey},
//};