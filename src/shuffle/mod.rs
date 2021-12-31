
pub mod shuffle;
mod vectorutil;



// Re-export
pub use self::{
    shuffle::Permutation,
    shuffle::Shuffle,
    vectorutil::ScalarExp,
};