pub mod ddh;
mod multiexponential;
mod product;
pub mod shuffle;
mod singlevalueproduct;
mod vectorutil;
pub mod hadamard;
pub mod polynomial;

// Re-export structures, functions, and constants
pub use self::{
    shuffle::{Permutation, Shuffle, ShuffleProof, ShuffleStatement, N, ROWS, COLUMNS},
    vectorutil::ScalarExp,
    // ... other re-exports as needed
};
