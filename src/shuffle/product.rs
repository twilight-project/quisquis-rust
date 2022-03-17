//! The `product` module contains API for producing a
//! product argument proof and verify it.

#![allow(non_snake_case)]

use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;
use crate::{
    accounts::{Prover, Verifier},
    pedersen::vectorpedersen::VectorPedersenGens,
    shuffle::singlevalueproduct::{SVPProof, SVPStatement},
    shuffle::vectorutil,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::{MultiscalarMul, VartimeMultiscalarMul};
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;
use std::iter;

///Zero argument
///
#[derive(Debug, Clone)]
pub struct ZeroStatement {
    pub c_A: Vec<CompressedRistretto>,
}
///Zero argument proof
///
#[derive(Debug, Clone)]
pub struct ZeroProof {
    pub c_A_0: CompressedRistretto,
    pub c_B_m: CompressedRistretto,
    pub c_D: Vec<CompressedRistretto>,
    pub a_vec: Vec<Scalar>,
    pub b_vec: Vec<Scalar>,
    pub r: Scalar,
    pub s: Scalar,
    pub t: Scalar,
}

///MultiHadamard argument
///
#[derive(Debug, Clone)]
pub struct MultiHadamardStatement {
    pub c_b: CompressedRistretto,
    pub zero_statement: ZeroStatement,
}
///MultiHadamard argument proof
///
#[derive(Debug, Clone)]
pub struct MultiHadamardProof {
    pub c_B: Vec<CompressedRistretto>,
    pub zero_proof: ZeroProof,
}

///Product Proof argument
/// an argument that a set of committed values have a particular product
///
#[derive(Debug, Clone)]
pub struct ProductStatement {
    pub multi_hadamard_statement: MultiHadamardStatement,
    pub svp_statement: SVPStatement,
}
///Product argument proof
///
#[derive(Debug, Clone)]
pub struct ProductProof {
    pub multi_hadamard_proof: MultiHadamardProof,
    pub svp_proof: SVPProof,
}
impl ProductProof {
    pub fn create_product_argument_proof(
        prover: &mut Prover,
        witness_matrix: &Array2D<Scalar>, //witness in column major order
        witness_r: &[Scalar], //random scalar vector of length m for Commiting on witness
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> (ProductProof, ProductStatement) {
        //convert witness to column major representation
        let witness_as_cols = witness_matrix.as_columns();

        //compute Xcomit on Witness Matrix
        let mut c_prod_A = Vec::<RistrettoPoint>::new();
        for i in 0..ROWS {
            c_prod_A.push(xpc_gens.commit(&witness_as_cols[i], witness_r[i]));
        }
        // cb = com(product (from 1 to m) a1j, ..., product (from 1 to m)
        let mut bvec = Vec::<Scalar>::new();
        let mut product: Scalar;
        for row_iter in witness_matrix.rows_iter() {
            product = Scalar::one();
            for element in row_iter {
                product = product * element;
            }
            bvec.push(product);
        }

        //create challenge s for bvec comit
        let s = Scalar::random(&mut OsRng);
        let cb = xpc_gens.commit(&bvec, s);

        //create b. i.e., product of all elements in A
        let b = bvec.iter().product::<Scalar>();

        let svp_state = SVPStatement {
            commitment_a: cb.compress(),
            b: b,
        };

        //create multihadamard product proof
        let (multihadamard_proof, multi_hadamard_state) =
            MultiHadamardProof::create_multi_hadamard_product_arg(
                prover,
                &witness_matrix,
                &pc_gens,
                &xpc_gens,
                &bvec,
                &c_prod_A,
                &cb,
                witness_r,
                s,
            );

        //create single value product proof
        let svp_proof = SVPProof::create_single_value_argument_proof(prover, &xpc_gens, s, &bvec);

        //Product Proof struct
        (
            ProductProof {
                multi_hadamard_proof: multihadamard_proof,
                svp_proof: svp_proof,
            },
            ProductStatement {
                multi_hadamard_statement: multi_hadamard_state,
                svp_statement: svp_state,
            },
        )
    }
    ///Product Argument proof verification
    ///
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        prod_statement: &ProductStatement,
        c_prod_A: &[RistrettoPoint],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> Result<(), &'static str> {
        //The verifier accepts if cb ∈ G and both SHVZK arguments (Mutihadamard and SingleValue Product) are convincing.
        // cb ∈ G is always valid if cb is a CompressedRistretto

        //check Mutihadamard Proof
        self.multi_hadamard_proof.verify(
            verifier,
            &prod_statement.multi_hadamard_statement,
            c_prod_A,
            pc_gens,
            xpc_gens,
        )?;
        /*check Single Value Product Proof*/
        self.svp_proof
            .verify(verifier, &prod_statement.svp_statement, xpc_gens)
    }
}

impl MultiHadamardProof {
    pub fn create_multi_hadamard_product_arg(
        prover: &mut Prover,
        pi_2d: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        bvec: &[Scalar],
        comit_a: &[RistrettoPoint],
        cb: &RistrettoPoint,
        r: &[Scalar],
        s_3: Scalar,
    ) -> (MultiHadamardProof, MultiHadamardStatement) {
        //Create new transcript
        prover.new_domain_sep(b"MultiHadamardProductProof");

        //create b1,b2....bm using  columns of Matrix A. a1,a2...
        let perm_scalar_as_cols = pi_2d.as_columns();
        // b1 =a1
        let b1 = perm_scalar_as_cols[0].clone();
        // b2 = a1 * a2
        let a2 = perm_scalar_as_cols[1].clone();
        let b2: Vec<_> = b1.iter().zip(a2.iter()).map(|(i, j)| i * j).collect();

        //bm = b
        let bm = bvec.clone();

        //Vector holding b1, b2 and bm
        let b_2d_vec = vec![
            perm_scalar_as_cols[0].clone(),
            b2.clone(),
            bvec.clone().to_vec(),
        ];

        //creating s vector before challenge.
        // s_1 = r_1,
        //Pick s2,...,s_m−1 ← Zq ,
        //s_m = s from calling function
        let s_vec_product: Vec<Scalar> = iter::once(r[0])
            .chain((1..COLUMNS - 1).map(|_| Scalar::random(&mut OsRng)))
            .chain(iter::once(s_3))
            .collect::<Vec<Scalar>>();
        //create C_B vector. Send C_B vector to verifier
        let c_B_inital: Vec<RistrettoPoint> = vec![
            comit_a[0].clone(),
            xpc_gens.commit(&b_2d_vec[1], s_vec_product[1]),
            cb.clone(),
        ];
        //
        //Commit C_B vector to Transcript for y challenge generation
        for cr in c_B_inital.iter() {
            prover.allocate_point(b"BVectorCommitment", cr.compress());
        }
        //CREATE CHALLENGE X AND Y
        let x = prover.get_challenge(b"XChallenge");

        let y = prover.get_challenge(b"YChallenge");

        let x_exp: Vec<_> = vectorutil::exp_iter(x).skip(1).take(ROWS).collect();
        // c_D_i = c_B_i * x^i
        let c_D_multihadamard: Vec<RistrettoPoint> = c_B_inital
            .iter()
            .zip(x_exp.iter())
            .map(|(pt, x)| pt * x)
            .collect();

        let c_D = RistrettoPoint::multiscalar_mul(&x_exp[0..2], &c_B_inital[1..3]);
        let scalars_neg_one: Vec<Scalar> = vec![-Scalar::one(); 3];

        let c_minus_one = xpc_gens.commit(&scalars_neg_one, Scalar::zero());
        //Calculate openings of c_D1, c_D2, and c_D3
        //d1 = xb1

        let d_1: Vec<_> = b_2d_vec[0].iter().map(|i| i * x_exp[0]).collect();
        let d_2: Vec<_> = b_2d_vec[1].iter().map(|i| i * x_exp[1]).collect();
        //let d_3: Vec<_> = b_2d_vec[2].iter().map(|i| i * x_exp[2]).collect();
        //compute t's. t_i = s_i * x^i
        let t_1_3: Vec<_> = s_vec_product
            .iter()
            .zip(x_exp.iter())
            .map(|(s, x)| s * x)
            .collect();

        //compute d.  d_vec = sum i=1..m-1 {x^i . s_{i+1}}

        let xb2: Vec<_> = b2.iter().map(|i| i * x_exp[0]).collect();
        let x2b3: Vec<_> = bm.iter().map(|i| i * x_exp[1]).collect();
        let d: Vec<_> = xb2.iter().zip(x2b3.iter()).map(|(i, j)| i + j).collect();
        //compute t. t_vec = sum i=1..m-1 {x^i . b_{i+1}}
        //t = x.s_2 + x^2.s_3
        let t = vectorutil::vector_multiply_scalar(&x_exp[0..2], &s_vec_product[1..3]);
        //Preparing Zero Argument Input
        //create A and B matrices and r,s arrays to be used in Zero argument
        //create r and s vector for Zero Argument. r would be the same while s now will be t
        let mut s: Vec<Scalar> = vec![t_1_3[0], t_1_3[1], t];
        //create A as matrix for zero argument. A is actually a2,a3,a_{-1}

        let a_columns = vec![
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
            scalars_neg_one,
        ];
        let a_array = Array2D::from_columns(&a_columns);
        //create B as matrix for zero argument. B is actually D here
        let columns = vec![d_1, d_2, d];
        let d_array = Array2D::from_columns(&columns);
        //cA = (cA2,cA3,c-1) with openings a2,a3,-1 and r = (r2,r3,0)
        let cA: Vec<RistrettoPoint> = vec![comit_a[1], comit_a[2], c_minus_one];
        //cB = (cD1,cD2,cD) with openings d1,d2,d and s=(s1,s2,s)

        let _cB: Vec<RistrettoPoint> = vec![c_D_multihadamard[0], c_D_multihadamard[1], c_D];
        // engage in a zero argument, for the committed values satisfying 0 = a2 ⇤ d1 + a3 ⇤ d2   1 ⇤ d.

        let zero_proof = ZeroProof::create_zero_argument_proof(
            prover, &a_array, &d_array, pc_gens, xpc_gens, r, &mut s, y,
        );
        //create zero argument proof statement
        let zero_statement = ZeroStatement {
            c_A: cA.iter().map(|a| a.compress()).collect(),
        };
        (
            MultiHadamardProof {
                c_B: c_B_inital.iter().map(|a| a.compress()).collect(),
                zero_proof: zero_proof,
            },
            MultiHadamardStatement {
                c_b: cb.compress(),
                zero_statement: zero_statement,
            },
        )
    }

    pub fn verify(
        &self,
        verifier: &mut Verifier,
        statement: &MultiHadamardStatement,
        c_A: &[RistrettoPoint],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> Result<(), &'static str> {
        //Check c_B2,...,c_Bm−1 ∈ G
        //Always true if received as CompressedRistretto
        //Check  cB1 = cA1 &&  cA2 = zerostatement.CA1

        if c_A[0].compress() == self.c_B[0]
            && c_A[1].compress() == statement.zero_statement.c_A[0]
            && c_A[2].compress() == statement.zero_statement.c_A[1]
        {
            //Check  cBm = cb
            if statement.c_b == self.c_B[ROWS - 1] {
                //Create new transcript
                verifier.new_domain_sep(b"MultiHadamardProductProof");
                //Recreate x, y challenge by adding Commit C_B vector to Transcript
                for cr in self.c_B.iter() {
                    verifier.allocate_point(b"BVectorCommitment", *cr);
                }

                //redefine
                let x = verifier.get_challenge(b"XChallenge");
                let y_chal = verifier.get_challenge(b"YChallenge");
                let x_exp: Vec<_> = vectorutil::exp_iter(x).skip(1).take(ROWS).collect();
                //  lets decompress c_B to be used later
                let commitment_b = self
                    .c_B
                    .iter()
                    .map(|p| p.decompress().ok_or("Multihadamard Proof Verify: Failed"))
                    .collect::<Result<Vec<_>, _>>()?;
                //lets recreate  cD_i = (c_B_i)^(x_i)
                let c_D_multihadamard: Vec<RistrettoPoint> = commitment_b
                    .iter()
                    .zip(x_exp.iter())
                    .map(|(pt, x)| pt * x)
                    .collect();

                //c_D = c_B_2 ^ x c_B_3^x^2
                let c_D = RistrettoPoint::multiscalar_mul(&x_exp[0..2], &commitment_b[1..3]);
                //redefine c−1 = comck(−~1; 0)
                let scalar_one_inv = -Scalar::one();
                let scalars: Vec<Scalar> = (0..ROWS).map(|_| scalar_one_inv.clone()).collect();
                let c_minus_one = xpc_gens.commit(&scalars, Scalar::zero()).compress();
                //create THESE VECTORS INdependently
                let commit_D_vec = vec![c_D_multihadamard[0], c_D_multihadamard[1], c_D];
                let mut c_zero_A = vec![
                    statement.zero_statement.c_A[0],
                    statement.zero_statement.c_A[1],
                    statement.zero_statement.c_A[2],
                ];
                if c_zero_A[ROWS - 1] != c_minus_one {
                    c_zero_A[ROWS - 1] = c_minus_one;
                }
                // Accept if the zero argument is valid.
                self.zero_proof.verify(
                    verifier,
                    &c_zero_A,
                    xpc_gens,
                    pc_gens,
                    &commit_D_vec,
                    y_chal,
                )
            } else {
                Err("Multihadamard Product Proof Verify: c_B_m == c_b Failed")
            }
        } else {
            Err("Multihadamard Product Proof Verify: c_B_1 == c_A_1 Failed")
        }
    }
}
impl ZeroProof {
    ///Create Zero Argument proof
    ///
    pub fn create_zero_argument_proof(
        prover: &mut Prover,
        a_2d: &Array2D<Scalar>,
        b_2d: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        r_vec: &[Scalar],
        s_vec: &mut Vec<Scalar>,
        y: Scalar,
    ) -> ZeroProof {
        //Create new transcript
        prover.new_domain_sep(b"ZeroArgumentProof");
        //Initial message
        //pick a0, bm
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let b_m: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //pick r0, s3 randomly to commit on a0 and bm
        let r_0 = Scalar::random(&mut OsRng);
        let s_m = Scalar::random(&mut OsRng);

        //comit on a0 and bm
        let c_a_0 = xpc_gens.commit(&a_0, r_0).compress();
        let c_b_m = xpc_gens.commit(&b_m, s_m).compress();

        //Create Full A and B vector to be used in bilinearmap.
        //Add a0 to A and bm to B
        let a_orig_colums = a_2d.as_columns();
        //for creating the new matrix
        let mut a_columns = vec![a_0];
        for columns in a_orig_colums.iter() {
            a_columns.push(columns.to_vec());
        }
        let a_Array = Array2D::from_columns(&a_columns);

        let mut b_orig_colums = b_2d.as_columns();
        //for creating the new matrix
        //add b_m to the b vector
        b_orig_colums.push(b_m);
        let b_Array = Array2D::from_columns(&b_orig_colums);
        //for k = 0,...,2m : compute d_k

        //BILINEAR MAP
        let dv = bilinearmap(&a_Array, &b_Array, y);

        //pick random t for committing d
        let mut t: Vec<_> = (0..2 * ROWS + 1)
            .map(|_| Scalar::random(&mut OsRng))
            .collect();
        t[ROWS + 1] = Scalar::zero();

        //calculate regular committments to all d's
        let c_D: Vec<_> = dv
            .iter()
            .zip(t.iter())
            .map(|(i, t)| pc_gens.commit(*i, *t).compress())
            .collect();

        //Add C_A_0 and C_B_m and C_D to Transcript to generate challenge Z
        prover.allocate_point(b"A0Commitment", c_a_0);
        prover.allocate_point(b"BmCommitment", c_b_m);
        for cd in c_D.iter() {
            prover.allocate_point(b"DCommitment", *cd);
        }
        //The verifier picks a challenge x
        let x = prover.get_challenge(b"challenge");

        // set x = (x, x^2, x^3, x^4.., x^2m).
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS + 1).collect();
        let x_exp_m = &x_exp[0..ROWS + 1];
        // reverse the X^i vector
        let mut x_m_j = x_exp_m.to_vec();
        x_m_j.reverse();

        //computing third message
        //creating a_bar
        //a_bar =  a_0 + a_1.x + a_2.x^2 + ...
        //b_bar =  x^3.b_0 + b_1x^2 + b_2x + ...
        let mut ax: Vec<Vec<Scalar>> = Vec::new();
        let mut bx: Vec<Vec<Scalar>> = Vec::new();
        for i in 0..ROWS + 1 {
            ax.push(a_columns[i].iter().map(|a| a * x_exp_m[i]).collect());
            bx.push(b_orig_colums[i].iter().map(|b| b * x_m_j[i]).collect());
        }
        //convert ax abd bx to array2d for easy column access
        let ax_2d = Array2D::from_rows(&ax);
        let bx_2d = Array2D::from_rows(&bx);
        let mut a_bar_vec = Vec::<Scalar>::new();
        let mut b_bar_vec = Vec::<Scalar>::new();
        //creating a_bar and b_bar
        for i in 0..ROWS {
            let mut temp_a = Scalar::zero();
            let mut temp_b = Scalar::zero();
            for element in ax_2d.column_iter(i) {
                temp_a += element;
            }
            a_bar_vec.push(temp_a);
            for ele in bx_2d.column_iter(i) {
                temp_b += ele;
            }
            b_bar_vec.push(temp_b);
        }

        //extend r and s vectors
        // s_ext = s + s_m
        //r_ext = r_0, r[1],r[2], 0
        let mut r_ext_vec = vec![r_0];
        for i in 1..ROWS {
            r_ext_vec.push(r_vec[i]);
        }
        r_ext_vec.push(Scalar::zero());

        s_vec.push(s_m);
        //compute r_new = r_i . x^i. where i is [0....m]
        let r_new: Scalar = vectorutil::vector_multiply_scalar(&r_ext_vec, &x_exp_m);

        //compute s_new = s_j . x^{m-j}. where j is [0....m]
        let s_new: Scalar = vectorutil::vector_multiply_scalar(&s_vec, &x_m_j);
        //compute t_new = t_k . x^k. where k is [0....2m]
        let t_new: Scalar = vectorutil::vector_multiply_scalar(&t, &x_exp);

        //Proof struct

        ZeroProof {
            c_A_0: c_a_0,
            c_B_m: c_b_m,
            c_D: c_D,
            a_vec: a_bar_vec,
            b_vec: b_bar_vec,
            r: r_new,
            s: s_new,
            t: t_new,
        }
    }

    pub fn verify(
        &self,
        verifier: &mut Verifier,
        c_A: &[CompressedRistretto],
        xpc_gens: &VectorPedersenGens,
        pc_gens: &PedersenGens,
        c_B: &[RistrettoPoint],
        chal_y: Scalar,
    ) -> Result<(), &'static str> {
        //check lengths of vectors
        if self.c_D.len() == 2 * ROWS + 1
            && self.a_vec.len() == COLUMNS
            && self.b_vec.len() == COLUMNS
        {
            //Verifying c_d_m+1 = com(0,0)
            let commit_d_m_1 = self.c_D[ROWS + 1]
                .decompress()
                .ok_or("ZeroProof Verify: Decompression Failed")?;
            let commit_0_0 = pc_gens.commit(Scalar::zero(), Scalar::zero());
            if commit_0_0 == commit_d_m_1 {
                //Create new transcript
                verifier.new_domain_sep(b"ZeroArgumentProof");
                //recreate Transcript for Z challenge generation by adding C_A_0 and C_B_m and C_D
                verifier.allocate_point(b"A0Commitment", self.c_A_0);
                verifier.allocate_point(b"BmCommitment", self.c_B_m);
                for cd in self.c_D.iter() {
                    verifier.allocate_point(b"DCommitment", *cd);
                }

                // prod i=0..m (c_Ai^x^i ) = com(a_bar,r)
                //Com_A_0 ^ X^0 = com_a0
                let challenge = verifier.get_challenge(b"challenge");
                //recreate x_exp_m
                let x_exp: Vec<_> = vectorutil::exp_iter(challenge).take(2 * ROWS + 1).collect();
                let x_m_1 = &x_exp[1..ROWS + 1]; //necessary to create an iterator

                let temp_a = RistrettoPoint::optional_multiscalar_mul(
                    x_m_1.iter(),
                    c_A.iter().map(|pt| pt.decompress()),
                )
                .ok_or_else(|| "ZeroProof Verify: Failed")?;
                let commit_a_product =
                    self.c_A_0.decompress().ok_or("ZeroProof Verify: Failed")? + temp_a;

                //com(a_bar,r)
                let commit_a_bar = xpc_gens.commit(&self.a_vec, self.r);
                if commit_a_bar == commit_a_product {
                    // prod j=0..m (c_Bj^x^(m-j) ) = com(b_bar,s)
                    //Com_B_m ^ X^0 = com_b3
                    let x_exp_m = &x_exp[1..ROWS + 1]; //necessary to create an iterator

                    let mut commit_b_full =
                        RistrettoPoint::multiscalar_mul(x_exp_m.iter().rev(), c_B.into_iter());
                    commit_b_full = commit_b_full
                        + self.c_B_m.decompress().ok_or("ZeroProof Verify: Failed")?;

                    //com(b_bar,s)
                    let commit_b_bar = xpc_gens.commit(&self.b_vec, self.s);

                    if commit_b_bar == commit_b_full {
                        //  k=0..2m c_D_k ^(x ^k)  ==  com(a_bar * b_bar; t) where * is bilinear map
                        //create y^i
                        //com(a_bar * b_bar; t)
                        let y_i: Vec<_> = vectorutil::exp_iter(chal_y).skip(1).take(ROWS).collect();
                        let a_bar_b_bar = single_bilinearmap(&self.a_vec, &self.b_vec, &y_i);
                        let commit_a_bar_b_bar = pc_gens.commit(a_bar_b_bar, self.t);
                        //k=0..2m c_D_k ^(x ^k)
                        let c_D_x_k = RistrettoPoint::optional_multiscalar_mul(
                            x_exp.iter(),
                            self.c_D.iter().map(|pt| pt.decompress()),
                        )
                        .ok_or_else(|| "ZeroProof Verify: Failed")?;
                        if commit_a_bar_b_bar == c_D_x_k {
                            Ok(())
                        } else {
                            Err("Zero Argument Proof Verify: com(a_bar * b_bar, t) verification check Failed")
                        }
                    } else {
                        Err("Zero Argument Proof Verify: com(b_bar, s) verification check Failed")
                    }
                } else {
                    Err("Zero Argument Proof Verify: com(a_bar, r) verification check Failed")
                }
            } else {
                Err("Zero Argument Proof Verify: c_d_(m+1) == com(0,0) Failed")
            }
        } else {
            Err("Zero Argument Proof Verify: Size check failed")
        }
    }
}

pub fn bilinearmap(a: &Array2D<Scalar>, b: &Array2D<Scalar>, y_chal: Scalar) -> Vec<Scalar> {
    //complete bilinear map for Matrix A and B. A and B are constructed in the calling function

    //create y^i
    let y_i: Vec<_> = vectorutil::exp_iter(y_chal).skip(1).take(ROWS).collect();

    //converting Array2D to column representation. Can also use column iterator. Should look into it
    let a_as_cols = a.as_columns();
    let b_as_cols = b.as_columns();
    let mut dvec = Vec::<Scalar>::new();
    let kiter = (2 * ROWS + 1) as isize;
    let ijiter = ROWS as isize;
    let m = ijiter; //m = ROWS in paper
    for k in 0..kiter {
        let mut sum = Scalar::zero();
        for i in 0..=ijiter {
            for j in 0..=ijiter {
                if j == (m - k + i) {
                    sum = single_bilinearmap(&a_as_cols[i as usize], &b_as_cols[j as usize], &y_i)
                        + sum;
                } else {
                    continue;
                }
            }
        }
        dvec.push(sum);
    }
    dvec
}

pub fn single_bilinearmap(ai: &[Scalar], bj: &[Scalar], yi: &[Scalar]) -> Scalar {
    assert_eq!(ai.len(), bj.len());
    assert_eq!(ai.len(), yi.len());
    assert_eq!(yi.len(), bj.len());
    ai.iter()
        .zip(bj.iter())
        .zip(yi.iter())
        .map(|((i, j), k)| i * j * k)
        .sum()
}

#[cfg(test)]
mod test {
    use super::*;
    use merlin::Transcript;

    const ROWS: usize = 3; //m
    const COLUMNS: usize = 3; //n
    #[test]
    fn multi_hadamard_product_proof_test() {
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);

        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        let pc_gens = PedersenGens::default();

        let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        // Creating PI Matrix of size 9 explicitly for testing.

        let pi_scalar: Vec<_> = vec![
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

        let pi_2d = Array2D::from_row_major(&pi_scalar, ROWS, COLUMNS);
        let perm_scalar_as_cols = pi_2d.as_columns();

        let mut comit_a_vec = Vec::<RistrettoPoint>::new();

        for i in 0..COLUMNS {
            comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], r[i]));
        }

        // cb = com(product (from 1 to m) a1j, ..., product (from 1 to m)

        let mut bvec = Vec::<Scalar>::new();
        for row_iter in pi_2d.rows_iter() {
            let mut product = Scalar::one();
            for element in row_iter {
                product = product * element;
            }
            bvec.push(product);
        }

        //create challenge s for bvec comit
        let s = Scalar::random(&mut OsRng);
        let cb = xpc_gens.commit(&bvec, s);

        let (had_proof, had_arg) = MultiHadamardProof::create_multi_hadamard_product_arg(
            &mut prover,
            &pi_2d,
            &pc_gens,
            &xpc_gens,
            &bvec,
            &comit_a_vec,
            &cb,
            &r,
            s,
        );
        let verify = had_proof.verify(&mut verifier, &had_arg, &comit_a_vec, &pc_gens, &xpc_gens);
        assert!(verify.is_ok());
    }

    #[test]
    fn product_proof_test() {
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        let pc_gens = PedersenGens::default();

        // Creating PI Matrix of size 9 explicitly for testing.

        let pi_scalar: Vec<_> = vec![
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

        let pi_2d = Array2D::from_row_major(&pi_scalar, ROWS, COLUMNS);
        let pi_2d_as_cols = pi_2d.as_columns();
        let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();

        for i in 0..COLUMNS {
            comit_a_vec.push(xpc_gens.commit(&pi_2d_as_cols[i], r[i]));
        }
        // let iden = RistrettoPoint::default();
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);

        let (prod_proof, prod_state) = ProductProof::create_product_argument_proof(
            &mut prover,
            &pi_2d,
            &r,
            &pc_gens,
            &xpc_gens,
        );
        // prod_state.svp_statement.b = Scalar::zero();
        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        //comit_a_vec[2] = iden;
        let verify = prod_proof.verify(
            &mut verifier,
            &prod_state,
            &comit_a_vec,
            &pc_gens,
            &xpc_gens,
        );
        // println!("Error in commitment{:?}", verify.unwrap());
        assert!(verify.is_ok());
    }

    #[test]
    fn single_bilinear_map_test() {
        let ai: Vec<_> = vec![Scalar::from(7u64), Scalar::from(6u64), Scalar::from(1u64)];
        let bj: Vec<_> = vec![Scalar::from(5u64), Scalar::from(3u64), Scalar::from(4u64)];
        let y = Scalar::from(5u64);
        //create y^i
        let y_i: Vec<_> = vectorutil::exp_iter(y).skip(1).take(4).collect();
        let reference = Scalar::from(1125u64);
        //test vector lengths before passing it to the function
        let result = single_bilinearmap(&ai, &bj, &y_i);
        assert_eq!(reference, result);
    }
    #[test]
    fn bilinear_map_test() {
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
        let a_2d = Array2D::from_row_major(&a_scalar, ROWS, COLUMNS);
        let b_2d = Array2D::from_row_major(&b_scalar, ROWS, COLUMNS);

        let a_0: Vec<_> = vec![Scalar::from(6u64), Scalar::from(2u64), Scalar::from(5u64)];
        let b_m: Vec<_> = vec![Scalar::from(7u64), Scalar::from(1u64), Scalar::from(3u64)];

        //Create Full A and B vector to be used in bilinearmap. Add a0 to A and bm to B
        let a_orig_colums = a_2d.as_columns();
        //for creating the new matrix
        let a_columns = vec![
            a_0,
            a_orig_colums[0].clone(),
            a_orig_colums[1].clone(),
            a_orig_colums[2].clone(),
        ];
        let a_Array = Array2D::from_columns(&a_columns);

        let b_orig_colums = b_2d.as_columns();
        //for creating the new matrix
        let b_columns = vec![
            b_orig_colums[0].clone(),
            b_orig_colums[1].clone(),
            b_orig_colums[2].clone(),
            b_m,
        ];
        let b_Array = Array2D::from_columns(&b_columns);
        let y = Scalar::from(5u64);
        let reference: Vec<Scalar> = vec![
            Scalar::from_canonical_bytes([
                87, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                30, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                106, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                166, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                208, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                12, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
            Scalar::from_canonical_bytes([
                243, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ])
            .unwrap(),
        ];
        let result = bilinearmap(&a_Array, &b_Array, y);
        //println!("Result {:?} = ", result);
        assert_eq!(reference, result);
    }
}
