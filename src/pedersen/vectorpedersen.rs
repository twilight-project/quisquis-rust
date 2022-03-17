//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;
use core::iter;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use sha3::Sha3_512;

/// Represents a vector of base points for vector-Pedersen commitments.
///
///
/// The default generators are:
///
/// * `B`: the `ristretto255` basepoint;
/// * `B_blinding`: the result of `ristretto255` SHA3-512
/// hash-to-group on input `B_bytes`.
#[derive(Clone)]
pub struct VectorPedersenGens {
    /// The total number of generators based on the size of the vector used for commitment.
    pub gens_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators.
    G_vec: Vec<RistrettoPoint>,
    /// Precomputed \\(\mathbf H\\) generator.
    H: RistrettoPoint,
}

impl VectorPedersenGens {
    /// Create a new `VectorpedersenGens` object.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for vector commitment.  
    ///
    pub fn new(gens_capacity: usize) -> Self {
        let mut gens = VectorPedersenGens {
            gens_capacity: 0,
            G_vec: Vec::new(),
            H: RistrettoPoint::hash_from_bytes::<Sha3_512>(
                RISTRETTO_BASEPOINT_COMPRESSED.as_bytes(),
            ),
        };
        gens.increase_capacity(gens_capacity);
        gens
    }

    /// Increases the number of generators to the amount specified.
    /// If less than or equal to the current capacity, does nothing.
    /// generators arecreated by incrementally hashing the BASE_POINT
    ///
    pub fn increase_capacity(&mut self, new_capacity: usize) {
        if self.gens_capacity >= new_capacity {
            return;
        }
        self.G_vec.push(RISTRETTO_BASEPOINT_POINT);
        let mut other_gens = Vec::<RistrettoPoint>::new();
        other_gens.push(self.H);
        for i in 0..(new_capacity - 2) {
            other_gens.push(RistrettoPoint::hash_from_bytes::<Sha3_512>(
                other_gens[i].compress().as_bytes(),
            ));
        }
        self.G_vec.extend(&other_gens[1..]);
        self.gens_capacity = new_capacity;
    }

    ///Creates extended pedersen commit on vector using a blinding scalar
    pub fn commit(&self, values: &[Scalar], blinding: Scalar) -> RistrettoPoint {
        //let mut scalar = vec![rscalar];
        //scalar.extend(msg);
        RistrettoPoint::multiscalar_mul(
            iter::once(&blinding).chain(values.iter()),
            iter::once(&self.H).chain(self.G_vec.iter()),
        )
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use bulletproofs::PedersenGens;
    use curve25519_dalek::scalar::Scalar;

    ///Extended Pedersen Gen
    ///
    fn extended_pedersen_gen(
        capacity: usize,
        g: RistrettoPoint,
        h: RistrettoPoint,
    ) -> Vec<RistrettoPoint> {
        let mut gens = Vec::<RistrettoPoint>::new();
        gens.push(h);
        for i in 0..(capacity - 2) {
            gens.push(RistrettoPoint::hash_from_bytes::<Sha3_512>(
                gens[i].compress().as_bytes(),
            ));
        }
        let mut final_gens = Vec::<RistrettoPoint>::new();
        final_gens.push(h);
        final_gens.push(g);
        let len = gens.len();
        final_gens.extend(&gens[1..len]);
        final_gens
    }
    ///Extended Pedersen Commit
    ///
    fn extended_commit(
        msg: &Vec<Scalar>,
        rscalar: Scalar,
        gens: &Vec<RistrettoPoint>,
    ) -> RistrettoPoint {
        let mut scalar = vec![rscalar];
        scalar.extend(msg);
        RistrettoPoint::multiscalar_mul(scalar.iter().clone(), gens.iter().clone())
    }
    #[test]
    fn extended_pedersen_gen_test() {
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let gens = extended_pedersen_gen(6, pc_gens.B, pc_gens.B_blinding);
        let vec_ped_gens = VectorPedersenGens::new(6);
        //println!("{:?}",gens);
        //create vectors of points from VectorPedersenGens Object
        let mut vec_gens = Vec::<RistrettoPoint>::new();
        vec_gens.push(vec_ped_gens.H);
        vec_gens.extend(&vec_ped_gens.G_vec);

        //println!("{:?}",vec_gens);
        assert_eq!(vec_gens, gens);
    }
    #[test]
    fn extended_commit_test() {
        let cols: Vec<usize> = vec![2, 5, 7, 10, 3];
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let gens = extended_pedersen_gen(6, pc_gens.B, pc_gens.B_blinding);
        let shuffle_scalar: Vec<_> = cols
            .iter()
            .map(|i| Scalar::from(*i as u64).clone())
            .collect();
        let rscalar = Scalar::from(15u64);
        let c = extended_commit(&shuffle_scalar, rscalar, &gens);

        let vec_ped_gens = VectorPedersenGens::new(6);
        let comit = vec_ped_gens.commit(&shuffle_scalar, rscalar);
        assert_eq!(c, comit);
    }
}
