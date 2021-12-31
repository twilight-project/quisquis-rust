//! Vector pedersen and vector multiply implementation.
//!
//! Shared functions needed in shuffle proof part of the library 
//!
//!

pub mod vectorpedersen;

// Re-export
pub use self::{
    vectorpedersen::VectorPedersenGens
};