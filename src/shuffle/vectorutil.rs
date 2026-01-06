//! Vector and scalar utilities for the Quisquis shuffle protocol.
//!
//! This module provides iterators, vector operations, and helper functions for
//! exponentiation, vector multiplication, and Hadamard products used in shuffle arguments.
//!
//! ## Core Components
//!
//! - [`ScalarExp`] - Iterator for scalar exponentiation
//! - Utility functions for vector and scalar operations

#![allow(dead_code)]

use curve25519_dalek::scalar::Scalar;
//use std::num::Zero;
/// Iterator for generating successive powers of a scalar (x, x^2, x^3, ...).
///
/// This struct is created by the `exp_iter` function.
///
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;
    /// Returns the next power of the scalar in the sequence.
    ///
    /// # Returns
    /// The next power of the scalar in the sequence.
    ///
    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }
    /// Provides a size hint for the iterator.
    ///
    /// # Returns
    /// A tuple containing the maximum size hint and an optional size hint.
    ///
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

/// Returns an iterator over successive powers of a scalar (x, x^2, x^3, ...).
///
/// # Arguments
/// * `x` - The scalar to exponentiate.
///
/// # Returns
/// An iterator over successive powers of the scalar.
///
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::ONE;
    ScalarExp { x, next_exp_x }
}

/// Computes the dot product of a vector of usize and a vector of Scalars.
///
/// This function calculates the dot product of a vector of integers and a vector of scalars.
/// It panics if the lengths of the vectors do not match.
///
/// # Arguments
/// * `row` - The row vector of integers.
/// * `col` - The column vector of scalars.
///
/// # Returns
/// A scalar that is the dot product of the two input vectors.
///
pub fn vector_multiply(row: &[usize], col: &[Scalar]) -> Scalar {
    if row.len() != col.len() {
        panic!("vector_multiply(a,b): lengths of vectors do not match");
    }
    row.iter()
        .zip(col.iter())
        .fold(Scalar::ZERO, |sum, (i, j)| {
            sum + Scalar::from(*i as u64) * j
        })
}

/// Computes the dot product of two vectors of Scalars.
///
/// This function calculates the dot product of two vectors of scalars.
/// It panics if the lengths of the vectors do not match.
///
/// # Arguments
/// * `row` - The row vector of scalars.
/// * `col` - The column vector of scalars.
///
/// # Returns
/// A scalar that is the dot product of the two input vectors.
///
pub fn vector_multiply_scalar(row: &[Scalar], col: &[Scalar]) -> Scalar {
    if row.len() != col.len() {
        panic!("vector_multiply_scalar(a,b): lengths of vectors do not match");
    }
    row.iter()
        .zip(col.iter())
        .fold(Scalar::ZERO, |sum, (i, j)| sum + i * j)
}

/// Computes the Hadamard (element-wise) product of two vectors of Scalars.
///
/// This function calculates the Hadamard product of two vectors of scalars.
/// It panics if the lengths of the vectors do not match.
///
/// # Arguments
/// * `a` - The first vector of scalars.
/// * `b` - The second vector of scalars.
///
/// # Returns
/// A vector of scalars that is the Hadamard product of the two input vectors.
///
pub fn hadamard_product(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.len() != b.len() {
        panic!("hadamard_product(a,b): lengths of vectors do not match");
    }
    a.iter().zip(b.iter()).map(|(i, j)| i * j).collect()
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use curve25519_dalek::scalar::Scalar;
    #[test]

    fn exp_iter_test() {
        let x = Scalar::from(3u64);
        let exp_2: Vec<_> = exp_iter(x).take(5).collect();
        let reference: Vec<Scalar> = vec![
            Scalar::from(1u64),
            Scalar::from(3u64),
            Scalar::from(9u64),
            Scalar::from(27u64),
            Scalar::from(81u64),
        ];
        assert_eq!(reference, exp_2);
    }

    #[test]
    fn test_vector_multiply_scalar() {
        let a = vec![
            Scalar::from(1u64),
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
        ];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), vector_multiply_scalar(&a, &b));
    }

    #[test]
    fn test_vector_multiply() {
        let a: Vec<usize> = vec![1, 2, 3, 4];
        let b = vec![
            Scalar::from(2u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(5u64),
        ];
        assert_eq!(Scalar::from(40u64), vector_multiply(&a, &b));
    }
}
