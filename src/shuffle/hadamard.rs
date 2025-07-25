//! Hadamard product argument proof for the Quisquis shuffle protocol.
//!
//! This module provides types and functions for constructing and verifying Hadamard product proofs
//! using vector and matrix commitments, as part of the shuffle argument.

use crate::shuffle::shuffle::COLUMNS;
use crate::{
    accounts::{Prover, Verifier},
    pedersen::vectorpedersen::VectorPedersenGens,
    shuffle::polynomial,
    shuffle::polynomial::Polynomial,
    shuffle::vectorutil,
};
use array2d::Array2D;
use core::fmt::Debug;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use itertools::Itertools;
///Single value Product argument
///
use serde::{Deserialize, Serialize};
use std::convert::TryInto;

/// Statement for a Hadamard product proof, containing interpolation parameters.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HadamardStatement {
    /// Omega values used for creating Lagrange interpolation polynomials on Prover and Verifier.
    pub omega: [Scalar; 3],
}
/// Hadamard product proof for vector/matrix commitments.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HadamardProof {
    /// Commitment to a_0 vector.
    pub commitment_a_0: CompressedRistretto,
    /// Commitment to b_0 vector.
    pub commitment_b_0: CompressedRistretto,
    /// Commitment to c_0 vector.
    pub commitment_c_0: CompressedRistretto,
    /// Commitment to delta vector.
    pub commitment_delta: [CompressedRistretto; 4],
    /// Evaluated a_bar vector at challenge x.
    pub a_bar: [Scalar; 3],
    /// Evaluated b_bar vector at challenge x.
    pub b_bar: [Scalar; 3],
    /// Evaluated c_bar vector.
    pub c_bar: [Scalar; 3],
    /// Opening for r_bar commitment.
    pub r_bar: Scalar,
    /// Opening for s_bar commitment.
    pub s_bar: Scalar,
    /// Opening for t_bar commitment.
    pub t_bar: Scalar,
    /// Opening for rho_bar commitment.
    pub rho_bar: Scalar,
}

impl HadamardProof {
    ///Create Hadamard Argument proof
    ///
    /// # Arguments
    ///
    /// * `prover` - a mutable `Prover` instance carrying the proof transcript
    /// * `xpc_gens` - a `VectorPedersenGens` instance carrying the vector pedersen generators
    /// * `a` - a `Array2D<Scalar>` instance carrying the matrix A
    /// * `b` - a `Array2D<Scalar>` instance carrying the matrix B
    /// * `c` - a `Array2D<Scalar>` instance carrying the matrix C  
    /// * `commit_a` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix A
    /// * `commit_b` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix B
    /// * `commit_c` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix C
    /// * `witness_r` - a `Vec<Scalar>` instance carrying the witness for the commitment to the matrix A
    /// * `witness_s` - a `Vec<Scalar>` instance carrying the witness for the commitment to the matrix B
    /// * `witness_t` - a `Vec<Scalar>` instance carrying the witness for the commitment to the matrix C
    ///
    /// # Returns
    ///
    /// A tuple containing a `HadamardProof` and a `HadamardStatement`.
    pub fn create_hadamard_argument_proof(
        prover: &mut Prover,
        xpc_gens: &VectorPedersenGens,
        a: &Array2D<Scalar>,
        b: &Array2D<Scalar>,
        c: &Array2D<Scalar>,
        commit_a: &[CompressedRistretto],
        commit_b: &[CompressedRistretto],
        commit_c: &[CompressedRistretto],
        witness_r: &[Scalar],
        witness_s: &[Scalar],
        witness_t: &[Scalar], //random scalar vector of length m for Commiting on witness
    ) -> (HadamardProof, HadamardStatement) {
        assert_eq!(commit_a.len(), commit_b.len());
        assert_eq!(commit_b.len(), commit_c.len());
        //Create new transcript
        prover.new_domain_sep(b"HadamardProductProof");
        //create witness scalar vector
        let combined = [
            witness_r.to_vec(),
            witness_s.to_vec(),
            witness_t.to_vec(),
            a.as_row_major(),
            b.as_row_major(),
            c.as_row_major(),
        ]
        .concat();
        // transcriptRng using public transcript data + secret for proof + external source
        let mut rng = prover.prove_rekey_witness_transcript_rng(&combined);
        //add commit_a, commit_b, commit_c to transcript
        for ((a, b), c) in commit_a.iter().zip(commit_b.iter()).zip(commit_c.iter()) {
            prover.allocate_point(b"c_a", a);
            prover.allocate_point(b"c_b", b);
            prover.allocate_point(b"c_c", c);
        }

        //compute the first message
        //create ca_0,cb_0,cc_0
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut rng)).collect();
        let b_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut rng)).collect();
        let c_0 = vectorutil::hadamard_product(&a_0, &b_0);
        //  println!("a_0 {:?}", a_0);

        //pick r0, s0, t0
        let r_0 = Scalar::random(&mut rng);
        let s_0 = Scalar::random(&mut rng);
        let t_0 = Scalar::random(&mut rng);

        //comit on a0 and b0 and c0
        let c_a_0 = xpc_gens.commit(&a_0, r_0).compress();
        let c_b_0 = xpc_gens.commit(&b_0, s_0).compress();
        let c_c_0 = xpc_gens.commit(&c_0, t_0).compress();

        //Finding Polynomials l(X) and li(X) for 1 <= i <= 3
        //These polynomials are stored in "l" array
        //l[0] stores l(X), l[1] stores l1(X), l[2] stores l2(X), and so on as required
        //Both Prover and Verifier agrees on w_i (omega) values

        //ensure that omega are distinct / unique
        let omega: [Scalar; 3] = [
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
        ];
        // let w: Vec<_> = (0..4).map(|_| Scalar::random(&mut OsRng)).collect();
        let l_x_vec = polynomial::create_l_i_x_polynomial(&omega);
        //check if the vector is constructed properly
        if l_x_vec.len() != 4 {
            panic!("L(X) polynomials are not constructed properly");
        }

        //Finding Delta_i for 0 <= i <= 3 from Step 4 equation (Page 84) of Stephanie Bayer Thesis
        //Need a loop if committed vectors are "k", here k = 3, since we have a0, a1, a2, a3
        //RHS of the equation is directly calculated below

        let a_expression = polynomial::compute_polynomial_expression(&l_x_vec, a, &a_0);
        let b_expression = polynomial::compute_polynomial_expression(&l_x_vec, b, &b_0);
        let c_expression = polynomial::compute_polynomial_expression(&l_x_vec, c, &c_0);

        //Evaluates (a.l(X) x b.l(X)) - cl(X))
        let a_b_c: Vec<_> = a_expression
            .iter()
            .zip(b_expression.iter())
            .zip(c_expression.iter())
            .map(|((a, b), c)| &a.multiply(b) - c)
            .collect();
        //println!("abc size {}", a_b_c.len());
        //Evaluates (a.l(X) x b.l(X)) - cl(X)) / l(X)
        let div_res: Vec<Polynomial> = a_b_c
            .into_iter()
            .map(|mut poly| poly.divide(&mut l_x_vec[0].clone(), poly.degree - l_x_vec[0].degree))
            .collect();

        //extract delta_i from delta_i * X^i
        let mut delta_vec: Vec<Vec<Scalar>> = Vec::new();
        for i in 0..4 {
            let mut inner_vec: Vec<Scalar> = Vec::new();
            for j in 0..3 {
                inner_vec.push(div_res[j].coefficients[i]);
            }
            delta_vec.push(inner_vec);
        }

        //commit on Delta vector
        let rho: Vec<_> = (0..a.num_rows() + 1)
            .map(|_| Scalar::random(&mut rng))
            .collect();
        let mut comit_delta_vec = Vec::<CompressedRistretto>::new();

        for (i, row) in delta_vec.iter().enumerate() {
            comit_delta_vec.push(xpc_gens.commit(row, rho[i]).compress());
        }

        //Send: ca0,cb0,cc0,c 0,...,c m

        //Add variables to Merlin transcript for challenge generation
        prover.allocate_point(b"c_a_0", &c_a_0);
        prover.allocate_point(b"c_b_0", &c_b_0);
        prover.allocate_point(b"c_c_0", &c_c_0);
        for cd in comit_delta_vec.iter() {
            prover.allocate_point(b"c_delta", cd);
        }

        // compute Challenge x
        let x = prover.get_challenge(b"challenge");
        //Prover evaluates a_bar, b_bar, c_bar, r_bar, s_bar, t_bar, rho_bar
        let mut a_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
        let mut b_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
        let mut c_bar: [Scalar; 3] = [Scalar::zero(), Scalar::zero(), Scalar::zero()];
        for i in 0..3
        // evaluates a_bar, b_bar, c_bar,
        {
            a_bar[i] = a_expression[i].evaluate_polynomial(x);
            b_bar[i] = b_expression[i].evaluate_polynomial(x);
            c_bar[i] = c_expression[i].evaluate_polynomial(x);
        }
        let mut eval = l_x_vec[0].evaluate_polynomial(x);
        let mut r_bar = r_0 * eval;
        let mut s_bar = s_0 * eval;
        let mut t_bar = t_0 * eval;
        // evaluates r_bar, s_bar, t_bar, rho_bar
        for i in 0..3 {
            eval = l_x_vec[i + 1].evaluate_polynomial(x);
            r_bar = r_bar + (witness_r[i] * eval);
            s_bar = s_bar + (witness_s[i] * eval);
            t_bar = t_bar + (witness_t[i] * eval);
        }
        let exp_x: Vec<_> = vectorutil::exp_iter(x).take(4).collect();
        let x_i_rho_i: Scalar = exp_x.iter().zip(rho.iter()).map(|(x, r)| x * r).sum();
        let rho_bar = l_x_vec[0].evaluate_polynomial(x) * x_i_rho_i;

        //send all this to verifier
        (
            HadamardProof {
                commitment_a_0: c_a_0,
                commitment_b_0: c_b_0,
                commitment_c_0: c_c_0,
                commitment_delta: comit_delta_vec.try_into().unwrap_or_else(
                    |v: Vec<CompressedRistretto>| {
                        panic!("Expected a Vec of length {} but it was {}", 4, v.len())
                    },
                ),
                a_bar: a_bar,
                b_bar: b_bar,
                c_bar: c_bar,
                r_bar: r_bar,
                s_bar: s_bar,
                t_bar: t_bar,
                rho_bar: rho_bar,
            },
            HadamardStatement { omega: omega },
        )
    }

    ///This method is for verifying the Hadamard product proof
    ///
    /// # Arguments
    ///
    /// * `verifier` - a mutable `Verifier` instance carrying the transcript
    /// * `xpc_gens` - a `VectorPedersenGens` instance carrying the vector pedersen generators
    /// * `hstatement` - a `HadamardStatement` instance carrying the statement
    /// * `commit_a` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix A
    /// * `commit_b` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix B
    /// * `commit_c` - a `Vec<CompressedRistretto>` instance carrying the commitments to the matrix C
    ///
    /// # Returns
    ///
    /// A `Result` containing `Ok(())` if the proof verifies correctly, or an error message if it fails.
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        xpc_gens: &VectorPedersenGens,
        hstatement: &HadamardStatement,
        commit_a: &[CompressedRistretto],
        commit_b: &[CompressedRistretto],
        commit_c: &[CompressedRistretto],
    ) -> Result<(), &'static str> {
        //Verification Code
        //check if omega are unique
        let omega = hstatement.omega.iter().unique();
        if omega.count() == 3 {
            //recreate l(x) from omega
            let l_x_vec = polynomial::create_l_i_x_polynomial(&hstatement.omega);
            //check if the vector is constructed properly
            if l_x_vec.len() == 4 {
                //recreate challenge x
                //Create new transcript
                verifier.new_domain_sep(b"HadamardProductProof");
                //Add variables to Merlin transcript for challenge generation
                //add commit_a, commit_b, commit_c to transcript
                for ((a, b), c) in commit_a.iter().zip(commit_b.iter()).zip(commit_c.iter()) {
                    verifier.allocate_point(b"c_a", a);
                    verifier.allocate_point(b"c_b", b);
                    verifier.allocate_point(b"c_c", c);
                }
                verifier.allocate_point(b"c_a_0", &self.commitment_a_0);

                verifier.allocate_point(b"c_b_0", &self.commitment_b_0);
                verifier.allocate_point(b"c_c_0", &self.commitment_c_0);
                for cd in self.commitment_delta.iter() {
                    verifier.allocate_point(b"c_delta", cd);
                }

                // Compute Challenge x
                let x = verifier.get_challenge(b"challenge");

                //Check for a_bar
                let commit_a_bar = xpc_gens.commit(&self.a_bar, self.r_bar);
                let commit_b_bar = xpc_gens.commit(&self.b_bar, self.s_bar);
                let commit_c_bar = xpc_gens.commit(&self.c_bar, self.t_bar);

                let mut eval_l = l_x_vec[0].evaluate_polynomial(x);
                let mut commit_a_0: RistrettoPoint = self
                    .commitment_a_0
                    .decompress()
                    .ok_or("HadamardProof Verify: Decompression Failed")?
                    * eval_l;
                let mut commit_b_0: RistrettoPoint = self
                    .commitment_b_0
                    .decompress()
                    .ok_or("HadamardProof Verify: Decompression Failed")?
                    * eval_l;
                let mut commit_c_0: RistrettoPoint = self
                    .commitment_c_0
                    .decompress()
                    .ok_or("HadamardProof Verify: Decompression Failed")?
                    * eval_l;

                for i in 0..3 {
                    eval_l = l_x_vec[i + 1].evaluate_polynomial(x);
                    commit_a_0 = commit_a_0
                        + (commit_a[i]
                            .decompress()
                            .ok_or("HadamardProof Verify: Decompression Failed")?
                            * eval_l);
                    commit_b_0 = commit_b_0
                        + (commit_b[i]
                            .decompress()
                            .ok_or("HadamardProof Verify: Decompression Failed")?
                            * eval_l);
                    commit_c_0 = commit_c_0
                        + (commit_c[i]
                            .decompress()
                            .ok_or("HadamardProof Verify: Decompression Failed")?
                            * eval_l);
                }

                // //check
                if commit_a_0 == commit_a_bar
                    && commit_b_0 == commit_b_bar
                    && commit_c_0 == commit_c_bar
                {
                    //check delta
                    let exp_x: Vec<_> = vectorutil::exp_iter(x).take(4).collect();

                    let mut commitment_delta: RistrettoPoint = self.commitment_delta[0]
                        .decompress()
                        .ok_or("HadamardProof Verify: Decompression Failed")?;
                    for i in 1..4 {
                        commitment_delta = commitment_delta
                            + (self.commitment_delta[i]
                                .decompress()
                                .ok_or("HadamardProof Verify: Decompression Failed")?
                                * exp_x[i]);
                    }
                    let lhs = commitment_delta * l_x_vec[0].evaluate_polynomial(x);
                    let a_bar_b_bar = vectorutil::hadamard_product(&self.a_bar, &self.b_bar);
                    let a_bar_b_bar_c_bar: Vec<_> = a_bar_b_bar
                        .iter()
                        .zip(self.c_bar.iter())
                        .map(|(ab, c)| ab - c)
                        .collect();
                    let rhs = xpc_gens.commit(&a_bar_b_bar_c_bar, self.rho_bar);
                    if lhs == rhs {
                        Ok(())
                    } else {
                        Err("Hadamard Proof Verify: Delta Commitment check failed")
                    }
                } else {
                    Err("Hadamard Proof Verify: A_bar , B_bar, C_bar check failed")
                }
            } else {
                Err("Hadamard Proof Verify: L(X) polynomials are not constructed properly")
            }
        } else {
            Err("Hadamard Proof Verify: Omega values are not unique")
        }
    }
}
#[cfg(test)]
mod test {
    use super::*;
    use crate::shuffle::shuffle::ROWS;
    use array2d::Array2D;
    use merlin::Transcript;
    #[test]
    fn hadamard_proof_test() {
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        let a_scalar: Vec<_> = vec![
            Scalar::from(7u64),
            Scalar::from(6u64),
            Scalar::from(1u64),
            Scalar::from(5u64),
            Scalar::from(3u64),
            Scalar::from(4u64),
            Scalar::from(2u64),
            Scalar::from(8u64),
            Scalar::from(9u64),
        ];

        let b_scalar: Vec<_> = vec![
            Scalar::from(3u64),
            Scalar::from(2u64),
            Scalar::from(1u64),
            Scalar::from(7u64),
            Scalar::from(3u64),
            Scalar::from(5u64),
            Scalar::from(8u64),
            Scalar::from(3u64),
            Scalar::from(6u64),
        ];

        let c_scalar = vectorutil::hadamard_product(&a_scalar, &b_scalar);
        let a_2d = Array2D::from_row_major(&a_scalar, ROWS, COLUMNS);
        let b_2d = Array2D::from_row_major(&b_scalar, ROWS, COLUMNS);
        let c_2d = Array2D::from_row_major(&c_scalar, ROWS, COLUMNS);

        let r: Vec<_> = vec![Scalar::from(6u64), Scalar::from(2u64), Scalar::from(5u64)];
        let s: Vec<_> = vec![Scalar::from(7u64), Scalar::from(1u64), Scalar::from(3u64)];
        let t: Vec<_> = vec![Scalar::from(5u64), Scalar::from(2u64), Scalar::from(1u64)];

        let a_2d_as_rows = a_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_a_vec = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            comit_a_vec.push(xpc_gens.commit(&a_2d_as_rows[i], r[i]).compress());
        }

        let b_2d_as_rows = b_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_b_vec = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            comit_b_vec.push(xpc_gens.commit(&b_2d_as_rows[i], s[i]).compress());
        }
        let c_2d_as_rows = c_2d.as_rows();
        //let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_c_vec = Vec::<CompressedRistretto>::new();
        for i in 0..COLUMNS {
            comit_c_vec.push(xpc_gens.commit(&c_2d_as_rows[i], t[i]).compress());
        }
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"Hadamard");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        let (proof, statement) = HadamardProof::create_hadamard_argument_proof(
            &mut prover,
            &xpc_gens,
            &a_2d,
            &b_2d,
            &c_2d,
            &comit_a_vec,
            &comit_b_vec,
            &comit_c_vec,
            &r,
            &s,
            &t,
        );

        let mut transcript_v = Transcript::new(b"Hadamard");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        let verify = proof.verify(
            &mut verifier,
            &xpc_gens,
            &statement,
            &comit_a_vec,
            &comit_b_vec,
            &comit_c_vec,
        );
        assert!(verify.is_ok());
        // println!("Polya {:?}", polya.evaluate_polynomial(x));
        // println!("Polyb {:?}", polyb.evaluate_polynomial(x));
        //  assert_eq!(polya.evaluate_polynomial(x), Scalar::from(11u64));
        // assert_eq!(polyb.evaluate_polynomial(x), Scalar::from(142u64));
    }
}
