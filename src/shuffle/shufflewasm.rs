//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::{
    accounts::{Account, Prover, Verifier, transcript},
    elgamal::ElGamalCommitment,
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    shuffle::ddh::{DDHProof, DDHStatement},
    shuffle::hadamard::{HadamardProof, HadamardStatement},
    shuffle::multiexponential::MultiexpoProof,
    shuffle::product::{ProductProof, ProductStatement},
    shuffle::vectorutil,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::{MultiscalarMul, Identity};
use std::convert::TryInto;

use crate::keys::PublicKey;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;
use rand::{CryptoRng, Rng};
// use serde::{Deserialize, Serialize};
use serde_derive::{Deserialize, Serialize};

use super::{Permutation, Shuffle};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShuffleWasm {
    pub inputs: Vec<Account>,          //Before shuffle     mxn as row major
    pub outputs: Vec<Account>,         //After shuffle and update    mxn as row major
    pub shuffled_tau: Vec<Scalar>, //Scalars after shuffle for PK update   mxn as row major
    pub rho: Scalar,                   //Scalar for Commitment Update
    pub pi: Vec<usize>,               //Permutaion matrix in the form m x n as row major
}

impl ShuffleWasm {
    pub fn new(
        inputs: Vec<Account>,
        outputs: Vec<Account>,
        shuffled_tau: Vec<Scalar>,
        rho: Scalar,
        pi: Vec<usize>,
    ) -> Self {
        ShuffleWasm {
            inputs,
            outputs,
            shuffled_tau,
            rho,
            pi,
        }
    }

}

// impl from Shuffle for ShuffleWasm 
impl From<Shuffle> for ShuffleWasm {
    fn from(shuffle: Shuffle) -> Self {
        ShuffleWasm {
            inputs: shuffle.get_inputs_vector(),
            outputs: shuffle.get_outputs_vector(),
            shuffled_tau: shuffle.get_shuffled_tau_vector(),
            rho: shuffle.rho,
            pi: shuffle.get_permutation_as_vector(),
        }
    }
}

// impl from ShuffleWasm for Shuffle
impl From<ShuffleWasm> for Shuffle {
    fn from(shuffle_wasm: ShuffleWasm) -> Self {
        let perm = Array2D::from_row_major(&shuffle_wasm.pi, 3, 3);
        let pi = Permutation::from_array2D(perm);
        Shuffle{
            inputs: Array2D::from_row_major(&shuffle_wasm.inputs, 3, 3),
            outputs: Array2D::from_row_major(&shuffle_wasm.inputs, 3, 3),
            shuffled_tau: Array2D::from_row_major(&shuffle_wasm.shuffled_tau, 3,3),
            rho: shuffle_wasm.rho,
            pi
        }
    }
}


