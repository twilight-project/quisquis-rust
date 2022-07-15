//! Utility functions to manipulate addresses, amounts etc.
//!
//! Shared functions needed in different part of the library or utility types for external
//! integrations.
//!

pub mod address;

// Re-export
pub use self::{address::Address, address::AddressType, address::Network};
