//! Shuffle proof implementation for the Quisquis protocol.
//!
//! This module provides the main shuffle argument, permutation matrix logic, shuffle proof construction and verification,
//! and supporting types for privacy-preserving account shuffling. It includes the main shuffle protocol implementation, and integrates all other submodules like
//! product, hadamard, ddh, polynomial, singlevalueproduct, multiexponential, etc.
//!
//! ## Core Components
//!
//! - [Shuffle`] - Main shuffle protocol structure
//! - [`Permutation`] - Permutation matrix logic
//! - [`ShuffleProof`] / [`ShuffleStatement`] - Shuffle argument proof and statement
//!
//! ## Example
//!
//! ```rust
//! use quisquislib::shuffle::Shuffle;
//! // ...
//! ```

#![allow(non_snake_case)]

use crate::{
    accounts::{Account, Prover, Verifier},
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
use curve25519_dalek::traits::MultiscalarMul;
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

/// Represents a permutation matrix for shuffling accounts in the protocol.
#[derive(Debug, Clone)]
pub struct Permutation {
    /// The permutation matrix as a 2D array (row-major order).
    perm_matrix: Array2D<usize>,
}
/// Number of accounts to shuffle (vector length).
pub const N: usize = 9;
/// Number of rows in the permutation/account matrix.
pub const ROWS: usize = 3;
/// Number of columns in the permutation/account matrix.
pub const COLUMNS: usize = 3;

impl Permutation {
    /// Creates a new random permutation matrix of size `n` using the provided RNG.
    ///
    /// # Arguments
    /// * `rng` - a mutable `Rng` instance carrying the random number generator
    /// * `n` - the size of the permutation matrix
    ///
    /// # Returns
    /// A `Permutation` instance.
    pub fn new<R: Rng + CryptoRng>(rng: &mut R, n: usize) -> Self {
        let mut permutation: Vec<usize> = (1..n + 1).collect();
        for i in (1..permutation.len()).rev() {
            // invariant: elements with index > i have been locked in place.
            permutation.swap(i, rng.gen_range(0, i + 1));
        }

        let perm_matrix = Array2D::from_row_major(&permutation, ROWS, COLUMNS);
        Self { perm_matrix }
    }

    /// Sets the permutation matrix explicitly.
    ///
    /// # Arguments
    /// * `matrix` - a `Array2D<usize>` instance carrying the permutation matrix
    ///
    /// # Returns
    /// A `Permutation` instance.
    pub fn set(&mut self, matrix: Array2D<usize>) {
        self.perm_matrix = matrix;
    }

    /// Returns the permutation matrix as a row-major 1D array.
    ///
    /// # Returns
    /// A `[usize; 9]` instance carrying the permutation matrix.
    pub fn get_row_major(&self) -> [usize; 9] {
        self.perm_matrix
            .as_row_major()
            .try_into()
            .unwrap_or_else(|_v: Vec<usize>| panic!("Expected a Vec of length {}", 9))
    }

    /// Returns the inverse of the permutation matrix (for input shuffle).
    ///
    /// # Returns
    /// A `Array2D<usize>` instance carrying the inverse permutation matrix.
    pub fn invert_permutation(&self) -> Array2D<usize> {
        let mut inverse = vec![0; self.perm_matrix.num_elements()];
        let permutation = self.perm_matrix.as_row_major();
        for i in 0..permutation.len() {
            inverse[permutation[i] - 1] = i + 1;
        }
        let perm_matrix = Array2D::from_row_major(&inverse, ROWS, COLUMNS);
        perm_matrix
    }
    /// Returns the permutation matrix as a matrix of Scalars (for proof input).
    ///
    /// # Returns
    /// A `Array2D<Scalar>` instance carrying the permutation matrix.
    pub fn get_permutation_as_scalar_matrix(&self) -> Array2D<Scalar> {
        Array2D::from_row_major(
            &self
                .perm_matrix
                .elements_row_major_iter()
                .map(|x| Scalar::from(*x as u64))
                .collect::<Vec<Scalar>>(),
            ROWS,
            COLUMNS,
        )
    }
    // Produces a commitment to the permutation matrix> TBI
    // fn commit(&self ) -> Result<()>
}

/// Represents a shuffle operation and its associated data.
#[derive(Debug, Clone)]
pub struct Shuffle {
    /// Accounts before shuffling (m x n matrix).
    pub inputs: Array2D<Account>, //Before shuffle     mxn
    /// Accounts after shuffling and update (m x n matrix).
    pub outputs: Array2D<Account>, //After shuffle and update    mxn
    /// Scalars after shuffle for PK update (m x n matrix).
    pub shuffled_tau: Array2D<Scalar>, //Scalars after shuffle for PK update   mxn
    /// Scalar for commitment update.
    pub rho: Scalar, //Scalar for Commitment Update
    /// Permutation matrix in m x n form.
    pub pi: Permutation, //Permutaion matrix in the form m x n
}
///Shuffle argument proof
///

/// Shuffle argument statement for proof verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShuffleStatement {
    /// Hadamard argument statement.
    pub hadamard_statement: HadamardStatement,
    /// Product argument statement.
    pub product_statement: ProductStatement,
    /// DDH argument statement.
    pub ddh_statement: DDHStatement,
}

/// Shuffle argument proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShuffleProof {
    /// Commitments to permutation matrix rows.
    pub c_A: Vec<CompressedRistretto>,
    /// Commitments to tau vectors.
    pub c_tau: Vec<CompressedRistretto>,
    /// Commitments to b vectors.
    pub c_B: Vec<CompressedRistretto>,
    /// Commitments to b' vectors.
    pub c_B_dash: Vec<CompressedRistretto>,
    /// Hadamard argument proof.
    pub hadmard_proof: HadamardProof,
    /// Product argument proof.
    pub product_proof: ProductProof,
    /// Multiexponential proof for public key update.
    pub multi_exponen_pk: MultiexpoProof,
    /// Multiexponential proof for commitment update.
    pub multi_exponen_commit: MultiexpoProof,
    /// DDH argument proof.
    pub ddh_proof: DDHProof,
}

impl Shuffle {
    /// Generates random values for permutation and scalars for shuffle initialization.
    ///
    /// # Arguments
    /// * `len` - the size of the shuffle
    ///
    /// # Returns
    /// A tuple containing a `Permutation`, a vector of `Scalar`s, and a `Scalar`.
    fn random_initialization(len: usize) -> (Permutation, Vec<Scalar>, Scalar) {
        //Create a new random permutation Matrix
        let pi = { Permutation::new(&mut OsRng, len) };
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..len).map(|_| Scalar::random(&mut OsRng)).collect();
        //Create Random rho used for updating the Account Commitments
        let rho = Scalar::random(&mut OsRng);
        (pi, tau, rho)
    }

    /// Performs an input shuffle on the provided accounts, updating them with random tau and rho.
    ///
    /// # Arguments
    /// * `inputs` - a `Vec<Account>` instance carrying the accounts to be shuffled
    ///
    /// # Returns
    /// A `Shuffle` instance.
    pub fn input_shuffle(
        inputs: &[Account], //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }
        //Get random inital values
        let (mut pi, tau, rho) = Self::random_initialization(len);

        //Convert Matrix to Vector in row major order
        let permutation = pi.perm_matrix.as_row_major();

        //shuffle Input accounts randomly using permutation matrix
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| inputs[permutation[i] - 1].clone())
            .collect();
        //Invert the permutation Matrix for Inputs shuffle
        pi.set(pi.invert_permutation());
        //Input accounts == input` in this case. updating input accounts with tau and rho
        let updated_inputs: Vec<_> = inputs
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
            .collect();
        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&updated_inputs, ROWS, COLUMNS);
        let inputs = Array2D::from_row_major(&shuffled_accounts, ROWS, COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS, COLUMNS);

        return Ok(Self {
            inputs,
            outputs,
            shuffled_tau,
            rho,
            pi,
        });
    }

    /// Performs an output shuffle on the provided accounts, updating them with random tau and rho.
    ///
    /// # Arguments
    /// * `inputs` - a `Vec<Account>` instance carrying the accounts to be shuffled
    ///
    /// # Returns
    /// A `Shuffle` instance.
    pub fn output_shuffle(
        inputs: &Vec<Account>, //Accounts to be shuffled
    ) -> Result<Self, &'static str> {
        let len = inputs.len();
        if len == 0 {
            return Err("Error::EmptyShuffle");
        }

        //Get random inital values
        let (pi, tau, rho) = Self::random_initialization(len);
        let permutation = pi.perm_matrix.as_row_major();

        //shuffle Inputs
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| inputs[permutation[i] - 1].clone())
            .collect();
        //Shuffled and Updated Accounts
        let shuffled_outputs: Vec<_> = shuffled_accounts
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
            .collect();

        //Convert to a 2D array representation
        let outputs = Array2D::from_row_major(&shuffled_outputs, ROWS, COLUMNS);
        let inputs = Array2D::from_row_major(&inputs, ROWS, COLUMNS);
        let shuffled_tau = Array2D::from_row_major(&tau, ROWS, COLUMNS);
        return Ok(Self {
            inputs,
            outputs,
            shuffled_tau,
            rho,
            pi,
        });
    }

    /// Returns a reference to the input accounts matrix.
    ///
    /// # Returns
    /// A `Array2D<Account>` instance carrying the input accounts matrix.
    pub fn get_inputs(&self) -> &Array2D<Account> {
        &self.inputs
    }

    /// Returns a reference to the output accounts matrix.
    ///
    /// # Returns
    /// A `Array2D<Account>` instance carrying the output accounts matrix.
    pub fn get_outputs(&self) -> &Array2D<Account> {
        &self.outputs
    }

    /// Returns a reference to the permutation matrix.
    ///
    /// # Returns
    /// A `Permutation` instance carrying the permutation matrix.
    pub fn get_permutation(&self) -> &Permutation {
        &self.pi
    }

    /// Returns a reference to the rho scalar.
    ///
    /// # Returns
    /// A `Scalar` instance carrying the rho scalar.
    pub fn get_rho(&self) -> &Scalar {
        &self.rho
    }

    /// Returns a reference to the tau matrix.
    ///
    /// # Returns
    /// A `Array2D<Scalar>` instance carrying the tau matrix.
    pub fn get_tau(&self) -> &Array2D<Scalar> {
        &self.shuffled_tau
    }

    /// Returns the input accounts as a row-major vector.
    ///
    /// # Returns
    /// A `Vec<Account>` instance carrying the input accounts vector.
    pub fn get_inputs_vector(&self) -> Vec<Account> {
        self.inputs.as_row_major()
    }

    /// Returns the output accounts as a row-major vector.
    ///
    /// # Returns
    /// A `Vec<Account>` instance carrying the output accounts vector.
    pub fn get_outputs_vector(&self) -> Vec<Account> {
        self.outputs.as_row_major()
    }
}

impl ShuffleProof {
    /// Creates a shuffle proof and its statement for the given shuffle instance.
    ///
    /// # Arguments
    /// * `prover` - a mutable `Prover` instance carrying the transcript
    /// * `shuffle` - a `Shuffle` instance carrying the shuffle argument
    /// * `pc_gens` - a `PedersenGens` instance carrying the pedersen generators
    /// * `xpc_gens` - a `VectorPedersenGens` instance carrying the vector pedersen generators  
    ///
    /// # Returns
    /// A tuple containing a `ShuffleProof` and a `ShuffleStatement`.
    pub fn create_shuffle_proof(
        prover: &mut Prover,
        shuffle: &Shuffle,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> (ShuffleProof, ShuffleStatement) {
        //extract permuatation witness
        let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        //commit on Witness A using r
        let r: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        //arrange the witness as vec of vec in row major order
        let perm_scalar_as_rows = witness.as_rows();
        //compute Xcomit on rows of witness "A" Matrix.
        let mut commitment_witness = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_witness.push(xpc_gens.commit(&perm_scalar_as_rows[i], r[i]).compress());
        }
        // transcriptRng using public transcript data + secret for proof + external source
        let mut rng =
            prover.prove_rekey_witness_transcript_rng(&shuffle.shuffled_tau.as_row_major());
        //commitment on tau using r'
        let r_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //convert to column major representation
        let tau_as_rows = shuffle.shuffled_tau.as_rows();

        //compute Xcomit on columns of tau
        let mut commitment_tau = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            commitment_tau.push(xpc_gens.commit(&tau_as_rows[i], r_dash[i]).compress());
        }
        //Tau commitment from HadamardProduct should be used here.
        //add commitment_witness and commitment_tau in Transcript
        for (a, tau) in commitment_witness.iter().zip(commitment_tau.iter()) {
            prover.allocate_point(b"ACommitment", a);
            prover.allocate_point(b"tauCommitment", tau);
        }
        //create challenge x
        let x = prover.get_challenge(b"xChallenge");
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_matrix, b_dash_matrix) =
            create_b_b_dash(&exp_x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);

        //convert b and b' to row major representation
        let b_as_rows = b_matrix.as_rows();
        let b_dash_as_rows = b_dash_matrix.as_rows();
        //commitment on b using s and b' using s'
        let s: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        let s_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut rng)).collect();
        //compute Xcomit on rows of b
        let mut commitment_b = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_b.push(xpc_gens.commit(&b_as_rows[i], s[i]).compress());
        }
        //compute Xcomit on rows of b'
        let mut commitment_b_dash = Vec::<CompressedRistretto>::new();
        for i in 0..ROWS {
            commitment_b_dash.push(xpc_gens.commit(&b_dash_as_rows[i], s_dash[i]).compress());
        }
        //add comit_b and comit_b_dash in Transcript
        for (cb, cbdash) in commitment_b.iter().zip(commitment_b_dash.iter()) {
            prover.allocate_point(b"BCommitment", cb);
            prover.allocate_point(b"BDashCommitment", cbdash);
        }
        // Hadamard proof: b' o tau = b
        let (hadamard_proof, hadamard_statement) = HadamardProof::create_hadamard_argument_proof(
            prover,
            &xpc_gens,
            &b_dash_matrix,
            &shuffle.shuffled_tau,
            &b_matrix,
            &commitment_b_dash,
            &commitment_tau,
            &commitment_b,
            &s_dash,
            &r_dash,
            &s,
        );

        //create challenge y,z for product argument creation
        let y = prover.get_challenge(b"yChallenge");
        let z = prover.get_challenge(b"zChallenge");
        //Prepare for Product argument.
        // [f] =  y [a] + [b]
        let a_as_rows = witness.as_row_major();
        let b_as_rows = b_matrix.as_row_major();
        let f: Vec<_> = a_as_rows
            .iter()
            .zip(b_as_rows.iter())
            .map(|(a, b)| a * y + b)
            .collect();
        // [t] =  y [r] + [s]
        let t: Vec<_> = r.iter().zip(s.iter()).map(|(r, s)| r * y + s).collect();

        let e: Vec<_> = f.iter().map(|f| f - z).collect();
        let e_2d = Array2D::from_column_major(&e, ROWS, COLUMNS);
        let (product_proof, product_state) =
            ProductProof::create_product_argument_proof(prover, &e_2d, &t, &pc_gens, &xpc_gens);
        //Create G,H for DDH and Multiexpo proof generation
        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        // gather g, h from Public key
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        //create DDH Proof
        let (ddh_proof, ddh_statement) =
            DDHProof::create_verify_update_ddh_prove(prover, &g_i, &h_i, &exp_x, G, H, shuffle.rho);

        //create the ciphertext vector of pk and commitment
        let mut upk: Vec<_> = Vec::<RistrettoPublicKey>::new();
        let mut updated_commitment: Vec<_> = Vec::<ElGamalCommitment>::new();
        for acc in shuffle.outputs.as_row_major().iter() {
            upk.push(acc.pk);
            updated_commitment.push(acc.comm);
        }
        // create base pk pair for reencryption in proof
        let base_pk = RistrettoPublicKey::generate_base_pk();
        //Calling Multiexponentiation Prove for Pk Update and shuffle
        let multiexpo_pk_proof = MultiexpoProof::create_multiexponential_pubkey_proof(
            prover,
            &upk,
            &b_dash_matrix,
            &s_dash,
            &pc_gens,
            &xpc_gens,
            &base_pk,
        );
        //create -rho as witness for Multiexpo_commitment_proof
        let neg_rho = -shuffle.rho;
        //Calling Multiexponentiation Prove for Commitment Update and shuffle
        let multiexpo_commit_proof = MultiexpoProof::create_multiexponential_elgamal_commit_proof(
            prover,
            &updated_commitment,
            &b_matrix,
            &s,
            &pc_gens,
            &xpc_gens,
            &pk_GH,
            neg_rho,
        );
        (
            ShuffleProof {
                c_A: commitment_witness,
                c_tau: commitment_tau,
                c_B: commitment_b,
                c_B_dash: commitment_b_dash,
                hadmard_proof: hadamard_proof,
                product_proof: product_proof,
                multi_exponen_pk: multiexpo_pk_proof,
                multi_exponen_commit: multiexpo_commit_proof,
                ddh_proof: ddh_proof,
            },
            ShuffleStatement {
                hadamard_statement: hadamard_statement,
                product_statement: product_state,
                ddh_statement: ddh_statement,
            },
        )
    }

    /// Verifies the shuffle proof against the provided statement and account vectors.
    ///
    /// # Arguments
    /// * `verifier` - a mutable `Verifier` instance carrying the transcript
    /// * `statement` - a `ShuffleStatement` instance carrying the statement
    /// * `shuffle_input` - a `Vec<Account>` instance carrying the input accounts
    /// * `shuffle_output` - a `Vec<Account>` instance carrying the output accounts
    /// * `pc_gens` - a `PedersenGens` instance carrying the pedersen generators
    /// * `xpc_gens` - a `VectorPedersenGens` instance carrying the vector pedersen generators
    ///
    /// # Returns
    /// - `Ok(())` if the proof verifies correctly
    /// - `Err(&'static str)` if any step fails (e.g. point decompression or challenge mismatch)
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        statement: &ShuffleStatement,
        shuffle_input: &[Account],
        shuffle_output: &[Account],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> Result<(), &'static str> {
        //check length of commitment vectors

        if self.c_A.len() == ROWS
            && self.c_B.len() == ROWS
            && self.c_B_dash.len() == ROWS
            && self.c_tau.len() == ROWS
        {
            //recreate challenge x

            //add c_A and c_tau in Transcript
            for (ca, ctau) in self.c_A.iter().zip(self.c_tau.iter()) {
                verifier.allocate_point(b"ACommitment", ca);
                verifier.allocate_point(b"tauCommitment", ctau);
            }
            //create challenge x
            let x = verifier.get_challenge(b"xChallenge");

            //create x^i for i = 1..N
            let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
            let base_pk = RistrettoPublicKey::generate_base_pk();
            //add comit_b and comit_b_dash in Transcript
            for (b, bdash) in self.c_B.iter().zip(self.c_B_dash.iter()) {
                verifier.allocate_point(b"BCommitment", b);
                verifier.allocate_point(b"BDashCommitment", bdash);
            }

            //Verify Hadamard Proof : b' o tau = b
            self.hadmard_proof.verify(
                verifier,
                &xpc_gens,
                &statement.hadamard_statement,
                &self.c_B_dash,
                &self.c_tau,
                &self.c_B,
            )?;

            //create challenge y,z for product argument verification
            let y = verifier.get_challenge(b"yChallenge");
            let z = verifier.get_challenge(b"zChallenge");
            //test prod of i..N (e_i) == prod pf i .. N (yi + x^i -z)
            let mut product = Scalar::one();
            let mut scalar: Scalar;
            for (i, xi) in exp_x.iter().enumerate() {
                scalar = Scalar::from((i + 1) as u64);
                product = product * (y * scalar + xi - z);
            }
            //check bvec == prod i =[1..N] {yi + x^i -z}
            if product == statement.product_statement.svp_statement.b {
                //recreate c_E from C_F & C_-Z

                let mut c_F = Vec::<RistrettoPoint>::new();
                for (ca, cb) in self.c_A.iter().zip(self.c_B.iter()) {
                    c_F.push(
                        ca.decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")?
                            * y
                            + cb.decompress()
                                .ok_or("ShuffleProof Verify: Decompression Failed")?,
                    );
                }
                // let c_F: Vec<_> = self
                //     .c_A
                //     .iter()
                //     .zip(self.c_B.iter())
                //     .map(|(ca, cb)| {
                //         ca.decompress()
                //             .ok_or("ShuffleProof Verify: Decompression Failed")?
                //             * y
                //             + cb.decompress()
                //                 .ok_or("ShuffleProof Verify: Decompression Failed")?
                //     })
                //     .collect();
                //create  C_-Z
                let z_neg: Vec<Scalar> = (0..N).map(|_| -z.clone()).collect();
                let z_neg_2d_as_cols = Array2D::from_row_major(&z_neg, ROWS, COLUMNS).as_columns();
                let mut comit_z_neg = Vec::<RistrettoPoint>::new();
                for i in 0..COLUMNS {
                    comit_z_neg.push(xpc_gens.commit(&z_neg_2d_as_cols[i], Scalar::zero()));
                }
                //recreate c_E to verified in product proof
                let c_E: Vec<_> = c_F
                    .iter()
                    .zip(comit_z_neg.iter())
                    .map(|(ca, cb)| ca + cb)
                    .collect();
                //product proof verify
                self.product_proof.verify(
                    verifier,
                    &statement.product_statement,
                    &c_E,
                    &pc_gens,
                    &xpc_gens,
                )?;
                //prepare for multiexponentiation and DDH proof on account public keys
                let pk: Vec<RistrettoPublicKey> = shuffle_input.iter().map(|acc| acc.pk).collect();
                let g_i: Vec<_> = pk
                    .iter()
                    .map(|pt| {
                        pt.gr
                            .decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let h_i: Vec<_> = pk
                    .iter()
                    .map(|pt| {
                        pt.grsk
                            .decompress()
                            .ok_or("ShuffleProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                // (G, H) = sum of all i (pk_i * x^i)
                let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
                let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());

                let pk_GH = RistrettoPublicKey {
                    gr: G.compress(),
                    grsk: H.compress(),
                };
                //verify DDH proof on pk's
                self.ddh_proof.verify_ddh_proof(
                    verifier,
                    &statement.ddh_statement,
                    pk_GH.gr,
                    pk_GH.grsk,
                )?;
                //multiexponentiation proof on account public keys

                self.multi_exponen_pk.verify_multiexponential_pubkey_proof(
                    verifier,
                    &self.c_B_dash,
                    shuffle_output,
                    &pc_gens,
                    &xpc_gens,
                    &base_pk,
                    &pk_GH,
                )?;
                //multiexponentiation proof on account commitments
                self.multi_exponen_commit
                    .verify_multiexponential_elgamal_commit_proof(
                        verifier,
                        &self.c_B,
                        shuffle_output,
                        shuffle_input,
                        &pc_gens,
                        &xpc_gens,
                        &pk_GH,
                        &exp_x,
                    )?;
                Ok(())
            } else {
                Err("Shuffle Proof Verify:prod pf i .. N (yi + x^i -z) failed")
            }
        } else {
            Err("Shuffle Proof Verify: Invalid length of commitment vectors")
        }
    }
}
/// Prepares b and b' vectors to be passed as witness to multiexponentiation proof
///
/// # Arguments
/// * `exp_x` - Exponent vector (x^i)
/// * `tau` - Tau vector
/// * `p` - Permutation
///
/// # Returns
/// Tuple of `(b_matrix, b_dash_matrix)` as `Array2D<Scalar>`.
pub fn create_b_b_dash(
    exp_x: &[Scalar],
    tau: &[Scalar],
    p: &Permutation,
) -> (Array2D<Scalar>, Array2D<Scalar>) {
    let perm = p.perm_matrix.as_row_major();
    let mut x_psi: Vec<Scalar> = Vec::with_capacity(N);

    //create 1/tau
    let tau_inv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();

    let mut b_dash: Vec<Scalar> = Vec::with_capacity(N);
    for (i, _) in exp_x.iter().enumerate() {
        x_psi.push(exp_x[perm[i] - 1]);
        b_dash.push(x_psi[i] * tau_inv[i]);
    }
    //Convert to a 2D array representation
    let b_matrix = Array2D::from_row_major(&x_psi, ROWS, COLUMNS);
    let b_dash_matrix = Array2D::from_row_major(&b_dash, ROWS, COLUMNS);

    (b_matrix, b_dash_matrix)
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use merlin::Transcript;
    #[test]
    fn shuffle_proof_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::input_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        //let witness = shuffle.pi.get_permutation_as_scalar_matrix();
        //println!("Shuffle witness {:?}", witness);

        let (proof, statement) =
            ShuffleProof::create_shuffle_proof(&mut prover, &shuffle, &pc_gens, &xpc_gens);

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        let verify = proof.verify(
            &mut verifier,
            &statement,
            &shuffle.get_inputs_vector(),
            &shuffle.get_outputs_vector(),
            &pc_gens,
            &xpc_gens,
        );
        println!("Shuffle verify: {:?}", verify);
        assert!(verify.is_ok());
    }

    #[test]
    fn permutation_matrix_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Matrix {:?}", perm.perm_matrix.as_rows());
    }
    #[test]
    fn inverse_permutation_test() {
        let perm = Permutation::new(&mut OsRng, N);
        println!("Permuted Vector {:?}", perm);
        let inv = perm.invert_permutation();
        println!("Inverted Vector {:?}", inv);
    }
    #[test]
    fn account_permutation_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs

        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let len = account_vector.len();
        let pi = { Permutation::new(&mut OsRng, len) };
        let permutation = pi.perm_matrix.as_row_major();
        //shuffle Account Vector
        let shuffled_accounts: Vec<_> = (0..len)
            .map(|i| account_vector[permutation[i] - 1].clone())
            .collect();
        assert_ne!(account_vector, shuffled_accounts)
    }
    #[test]
    fn shuffle_output_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::output_shuffle(&account_vector) };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;

        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i] - 1].clone()).collect();
        let shuffled_updated: Vec<_> = shuffled_inputs
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
            .collect();
        assert_eq!(out, shuffled_updated)
    }
    // Testing the update of input and assignment to output
    #[test]
    fn shuffle_input_update_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::input_shuffle(&account_vector) };
        let out = shuffle.as_ref().unwrap().outputs.as_row_major();
        let tau = shuffle.as_ref().unwrap().shuffled_tau.as_row_major();
        let rho = shuffle.as_ref().unwrap().rho;

        let input_updated: Vec<_> = account_vector
            .iter()
            .zip(tau.iter())
            .map(|(acc, t)| Account::update_account(*acc, 0u64.into(), *t, rho))
            .collect();
        assert_eq!(out, input_updated)
    }

    // Testing the inverse permutation and assignment to input
    #[test]
    fn shuffle_input_perm_test() {
        // lets define a vector of accounts
        let mut account_vector: Vec<Account> = Vec::new();

        // lets create these accounts and associated keypairs
        for _x in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        // 1 for input , 2 for output
        let shuffle = { Shuffle::input_shuffle(&account_vector) };
        let inp = shuffle.as_ref().unwrap().inputs.as_row_major();
        let pi = &shuffle.as_ref().unwrap().pi;
        let perm = pi.perm_matrix.as_row_major();
        //shuffle the input and compare with the account_vector
        let shuffled_inputs: Vec<_> = (0..9).map(|i| inp[perm[i] - 1].clone()).collect();
        assert_eq!(account_vector, shuffled_inputs)
    }

    #[test]
    fn scalar_batch_invert_test() {
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();
        let tau_inv: Vec<_> = tau.iter().map(|i| Scalar::invert(i)).collect();

        // tau * tau_inv should be == 1
        let result: Vec<_> = tau.iter().zip(tau_inv.iter()).map(|(a, b)| a * b).collect();

        assert!(result
            .get(0)
            .map(|first| result.iter().all(|x| x == first))
            .unwrap_or(true));
    }
    #[test]
    fn b_dash_vector_test() {
        //Create Random tau used for updating the Account Pks
        let x = Scalar::random(&mut OsRng);
        //let x = Scalar::from(3u64);
        let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();
        let perm = Permutation::new(&mut OsRng, N);
        //let perm_vec = perm.perm_matrix.as_row_major();
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        let (b, b_dash) = create_b_b_dash(&exp_x, &tau, &perm);
        //test
        let b_dash_tau: Vec<Scalar> = b_dash
            .as_row_major()
            .iter()
            .zip(tau.iter())
            .map(|(b, t)| b * t)
            .collect();

        assert_eq!(b_dash_tau, b.as_row_major());
    }
    #[test]
    fn b_vector_test() {
        //test for N = 9
        let x = Scalar::from(3u64);
        //Create Random tau used for updating the Account Pks
        let tau: Vec<_> = (0..N).map(|_| Scalar::random(&mut OsRng)).collect();
        let matrix = Array2D::from_row_major(&vec![2, 1, 3, 8, 7, 6, 4, 5, 9], ROWS, COLUMNS);
        let mut permutation = Permutation::new(&mut OsRng, N);
        permutation.set(matrix);
        //create x^i for i = 1..N
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(N).collect();
        let (b, _) = create_b_b_dash(&exp_x, &tau, &permutation);

        let b_reference: Vec<Scalar> = vec![
            Scalar::from(9u64),
            Scalar::from(3u64),
            Scalar::from(27u64),
            Scalar::from(6561u64),
            Scalar::from(2187u64),
            Scalar::from(729u64),
            Scalar::from(81u64),
            Scalar::from(243u64),
            Scalar::from(19683u64),
        ];
        //test

        assert_eq!(b_reference, b.as_row_major());
    }
}
