//! Utility functions to manipulate vectors and Matrices.
//! 
//! Vector multiplication and Matrix multiplication functions
//!  
//! Shared functions needed in shuffle proof implementation

use curve25519_dalek::scalar::Scalar;


/// Provides an iterator over the powers of a `Scalar`.
///
/// This struct is created by the `exp_iter` function.
/// 
pub struct ScalarExp {
    x: Scalar,
    next_exp_x: Scalar,
}

impl Iterator for ScalarExp {
    type Item = Scalar;

    fn next(&mut self) -> Option<Scalar> {
        let exp_x = self.next_exp_x;
        self.next_exp_x *= self.x;
        Some(exp_x)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}


/// Return an iterator of the powers of `x`.
pub fn exp_iter(x: Scalar) -> ScalarExp {
    let next_exp_x = Scalar::one();
    ScalarExp { x, next_exp_x }
}

/// Scalar product of a vector of usize elements with a vector of Scalars 
/// 
pub fn vector_multiply(row: &Vec<usize>, col: &Vec<Scalar>)-> Scalar{
    let sum: Vec<_> = row.iter().zip(col.iter()).map(|(i,j)| Scalar::from(*i as u64) *j).collect();
    sum.iter().sum()
}

/// Scalar product of 2 scalar vectors    
/// 
pub fn vector_multiply_scalar(row: &Vec<Scalar>, col: &Vec<Scalar>)-> Scalar{
    let sum: Vec<_> = row.iter().zip(col.iter()).map(|(i,j)| i *j).collect();
    sum.iter().sum()
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
        let reference: Vec<Scalar> = vec![Scalar::from(1u64), Scalar::from(3u64), Scalar::from(9u64), Scalar::from(27u64), Scalar::from(81u64)];
        assert_eq!(reference, exp_2);
    }

}

