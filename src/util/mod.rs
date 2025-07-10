//! Utility functions to manipulate addresses, amounts etc.
//!
//! Shared functions needed in different part of the library or utility types for external
//! integrations.

/// Address handling utilities for the Quisquis protocol.
pub mod address;

/// Re-export of the [`Address`] type for convenience.
pub use self::address::Address;
/// Re-export of the [`Network`] enum for convenience.
pub use self::address::Network;
