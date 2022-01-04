//! The `product` module contains API for producing a
//! product argument proof and verify it.

#![allow(non_snake_case)]

use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;
use crate::{
    accounts::{Account, Prover, Verifier},
    pedersen::vectorpedersen::VectorPedersenGens,
    shuffle::singlevalueproduct::{SVPArgument, SVPProof},
    shuffle::vectorutil,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;

///Product Proof argument
/// an argument that a set of committed values have a particular product
///
#[derive(Debug, Clone)]
struct ProductArgument {
    // commitments c_A to Matrix A = {a_i_j} i,j=1, to n,m
    //Vector of lenght m
    pub c_A: Vec<CompressedRistretto>,
    // b = prod of i =1 to n . prod of j=1 to m { a_ij}
    pub b: Scalar,
}
///Product argument proof
///
#[derive(Debug, Clone)]
pub struct ProductProof {
    pub multi_hadamard_argument: MultiHadamardArgument,
    pub multi_hadamard_proof: MultiHadamardProof,
    pub svp_argument: SVPArgument,
    pub svp_proof: SVPProof,
}

///MultiHadamard argument
///
#[derive(Debug, Clone)]
struct MultiHadamardArgument {
    pub c_A: Vec<CompressedRistretto>,
    pub c_b: CompressedRistretto,
}
///MultiHadamard argument proof
///
#[derive(Debug, Clone)]
struct MultiHadamardProof {
    pub c_B: Vec<CompressedRistretto>,
    pub zero_argument: ZeroArgument,
    pub zero_proof: ZeroProof,
}

///Zero argument
///
#[derive(Debug, Clone)]
struct ZeroArgument {
    pub c_A: Vec<CompressedRistretto>,
    pub c_B: Vec<CompressedRistretto>,
}
///Zero argument proof
///
#[derive(Debug, Clone)]
struct ZeroProof {
    pub c_A_0: CompressedRistretto,
    pub c_B_m: CompressedRistretto,
    pub c_D: Vec<CompressedRistretto>,
    pub a_vec: Vec<Scalar>,
    pub b_vec: Vec<Scalar>,
    pub r: Scalar,
    pub s: Scalar,
    pub t: Scalar,
}

impl ProductProof {
    pub fn create_product_argument_prove(
        prover: &mut Prover,
        b_matrix: &Array2D<Scalar>, //witness
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        x_chal: Scalar, //challenge generated in shuffle proof function
    ) -> (ProductProof, Scalar) {
        //create random number r to vector commit on witness. The commitment is on COLUMNS of A matrix
        //compute r. it is the witness in c_A
        let r: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //create statement
        //convert to column major representation
        let perm_scalar_as_cols = b_matrix.as_columns();

        //compute Xcomit on A
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], r[i]));
        }
        // cb = com(product (from 1 to m) a1j, ..., product (from 1 to m)
        //println!("{:?}",pi_2d);
        let mut bvec = Vec::<Scalar>::new();
        for row_iter in b_matrix.rows_iter() {
            let mut product = Scalar::one();
            for element in row_iter {
                product = product * element;
            }
            bvec.push(product);
        }
        // println!("{:?}",bvec);

        //create challenge s for bvec comit
        let s = Scalar::random(&mut OsRng);
        let cb = xpc_gens.commit(&bvec, s);

        //create b. i.e., product of all elements in A
        let b = bvec.iter().product::<Scalar>();

        //create multihadamard argument
        let hadamard_argument = MultiHadamardArgument {
            c_A: comit_a_vec.iter().map(|a| a.compress()).collect(),
            c_b: cb.compress(),
        };

        let svp_argument = SVPArgument {
            commitment_a: cb.compress(),
            b: b,
        };

        //create multihadamard product proof
        let (multihadamard_proof, x) = MultiHadamardProof::create_multi_hadamard_product_arg(
            prover,
            &b_matrix,
            &pc_gens,
            &xpc_gens,
            &bvec,
            &comit_a_vec,
            &cb,
            x_chal,
            r,
            s,
        );

        //create single value product proof
        let svp_proof =
            SVPProof::create_single_value_argument_proof(prover, &xpc_gens, cb, b, s, &bvec);

        //Product Proof struct
        (
            ProductProof {
                multi_hadamard_argument: hadamard_argument,
                multi_hadamard_proof: multihadamard_proof,
                svp_argument: svp_argument,
                svp_proof: svp_proof,
            },
            x,
        )
    }
    ///Product Argument proof verification
    ///
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        x: Scalar,
    ) -> bool {
        //The verifier accepts if cb ∈ G and both SHVZK arguments (Mutihadamard and SingleValue Product) are convincing.
        // cb ∈ G is always valid if cb is a CompressedRistretto

        //check Mutihadamard Proof
        self.multi_hadamard_proof.verify(
            verifier,
            &self.multi_hadamard_argument,
            &self.multi_hadamard_proof.zero_argument,
            &self.multi_hadamard_proof.zero_proof,
            pc_gens,
            xpc_gens,
            x,
        ) && self /*check Single Value Product Proof*/
            .svp_proof
            .verify(verifier, &self.svp_argument, xpc_gens)
    }
}

impl MultiHadamardProof {
    pub fn create_multi_hadamard_product_arg(
        prover: &mut Prover,
        pi_2d: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        bvec: &Vec<Scalar>,
        comit_a: &Vec<RistrettoPoint>,
        cb: &RistrettoPoint,
        x_chal: Scalar,
        r: Vec<Scalar>,
        s_3: Scalar,
    ) -> (MultiHadamardProof, Scalar) {
        //Create new transcript
        prover.new_domain_sep(b"MultiHadamardProductProof");

        // ai, b, vectors of length n
        // cA, cb, a1, ..., am, bvec, st bvec = product ai
        // (with entrywise multiplication)
        // cA = com(A;rvec); cb = com(bvec; s)
        //s1 = r[0]
        let s_1 = r[0];
        //create b1,b2....bm
        let perm_scalar_as_cols = pi_2d.as_columns();
        // b1 =a1
        let b1 = perm_scalar_as_cols[0].clone();
        // b2 = a1 * a2
        let a2 = perm_scalar_as_cols[1].clone();
        let b2: Vec<_> = b1.iter().zip(a2.iter()).map(|(i, j)| i * j).collect();
        //b3 = b
        let b3 = bvec.clone();
        let s2 = Scalar::random(&mut OsRng);
        let c_B2 = xpc_gens.commit(&b2, s2);
        let c_B1 = comit_a[0].clone();
        let c_B3 = cb.clone();

        //create C_B vector. Send C_B vector to verifier
        let c_B_inital: Vec<CompressedRistretto> =
            vec![c_B1.compress(), c_B2.compress(), c_B3.compress()];
        //
        //Commit C_B vector to Transcript for y challenge generation
        for cr in c_B_inital.iter() {
            prover.allocate_point(b"BVectorCommitment", *cr);
        }
        //CREATE CHALLENGE X AND Y
        let x = x_chal;

        let y = prover.get_challenge(b"challenge");
        //let y = Scalar::random(&mut OsRng);

        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        //let x_exp_m = &x_exp[1..4].to_vec();
        let c_D1 = c_B1 * x_exp[1];
        let c_D2 = c_B2 * x_exp[2];
        let c_D3 = c_B3 * x_exp[3];
        //c_D = c_B_2 ^ x c_B_3^x^2
        let c_D = c_B2 * x_exp[1] + c_B3 * x_exp[2];
        let scalar_one = Scalar::one();
        //println!("{:?}", scalar_one);
        let scalar_one_inv = -scalar_one;
        //println!("{:?}", scalar_one_inv);
        let mut scalars: Vec<Scalar> = vec![
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
        ];
        let c_minus_one = xpc_gens.commit(&scalars, Scalar::zero());
        //Calculate openings of c_D1, c_D2, and c_D3
        //d1 = xb1
        let d_1: Vec<_> = b1.iter().map(|i| i * x_exp[1]).collect();
        let d_2: Vec<_> = b2.iter().map(|i| i * x_exp[2]).collect();
        let d_3: Vec<_> = b3.iter().map(|i| i * x_exp[3]).collect();
        //compute t's
        let t_1 = s_1 * x_exp[1];
        let t_2 = s2 * x_exp[2];
        let t_3 = s_3 * x_exp[3];

        //compute d
        let xb2: Vec<_> = b2.iter().map(|i| i * x_exp[1]).collect();
        let x2b3: Vec<_> = b3.iter().map(|i| i * x_exp[2]).collect();
        let d: Vec<_> = xb2.iter().zip(x2b3.iter()).map(|(i, j)| i + j).collect();

        //compute t
        let xs2 = x_exp[1] * s2;
        let x2s3 = x_exp[2] * s_3;
        let t = xs2 + x2s3;
        //create A and B matrices and r,s arrays to be used in Zero argument
        //create r and s vector for Zero Argument. r would be the same while s now will be t
        let s: Vec<Scalar> = vec![t_1, t_2, t];
        //create A as matrix for zero argument. A is actually a2,a3,a-1

        let a_columns = vec![
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
            scalars,
        ];
        let a_array = Array2D::from_columns(&a_columns);
        //create B as matrix for zero argument. B is actually D here
        let columns = vec![d_1, d_2, d];
        let d_array = Array2D::from_columns(&columns);
        //cA = (cA2,cA3,c-1) with openings a2,a3,-1 and r = (r2,r3,0)
        let cA: Vec<RistrettoPoint> = vec![comit_a[1], comit_a[2], c_minus_one];
        //cB = (cD1,cD2,cD) with openings d1,d2,d and s=(s1,s2,s)

        let cB: Vec<RistrettoPoint> = vec![c_D1, c_D2, c_D];
        // engage in a zero argument, for the committed values satisfying 0 = a2 ⇤ d1 + a3 ⇤ d2   1 ⇤ d.

        let zero_proof = ZeroProof::create_zero_argument_proof(
            prover, &a_array, &d_array, pc_gens, xpc_gens, &cA, &cB, &r, &s, y,
        );
        //create zero argument
        let zero_arg = ZeroArgument {
            c_A: cA.iter().map(|a| a.compress()).collect(),
            c_B: cB.iter().map(|b| b.compress()).collect(),
        };
        (
            MultiHadamardProof {
                c_B: c_B_inital,
                zero_argument: zero_arg,
                zero_proof: zero_proof,
            },
            x,
        )
    }

    pub fn verify(
        &self,
        verifier: &mut Verifier,
        arg: &MultiHadamardArgument,
        zero_arg: &ZeroArgument,
        zero_proof: &ZeroProof,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        x_chal: Scalar,
    ) -> bool {
        //Create new transcript
        verifier.new_domain_sep(b"MultiHadamardProductProof");
        //Recreate y challenge by adding Commit C_B vector to Transcript
        for cr in self.c_B.iter() {
            verifier.allocate_point(b"BVectorCommitment", *cr);
        }
        //Check c_B2,...,c_Bm−1 ∈ G
        //Always true if received as CompressedRistretto
        //Check  cB1 = cA1
        assert_eq!(arg.c_A[0], self.c_B[0]);
        //Check  cBm = cb
        assert_eq!(arg.c_b, self.c_B[ROWS - 1]);

        //redefine cD_i = (c_B_i)^(x_i)
        let x = x_chal;
        let y_chal = verifier.get_challenge(b"challenge");
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        //let x_exp_m = &x_exp[1..4].to_vec();
        let c_D1 = self.c_B[0].decompress().unwrap() * x_exp[1];
        let c_D2 = self.c_B[1].decompress().unwrap() * x_exp[2];
        let c_D3 = self.c_B[2].decompress().unwrap() * x_exp[3];
        //c_D = c_B_2 ^ x c_B_3^x^2
        let c_D = self.c_B[1].decompress().unwrap() * x_exp[1]
            + self.c_B[2].decompress().unwrap() * x_exp[2];
        //redefine c−1 = comck(−~1; 0)
        let scalar_one = Scalar::one();
        let scalar_one_inv = -scalar_one;
        let mut scalars: Vec<Scalar> = vec![
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
            scalar_one_inv.clone(),
        ];
        let c_minus_one = xpc_gens.commit(&scalars, Scalar::zero());

        // Accept if the zero argument is valid.
        zero_proof.verify(verifier, zero_arg, xpc_gens, pc_gens, y_chal)
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
        comit_a: &Vec<RistrettoPoint>,
        comit_b: &Vec<RistrettoPoint>,
        r_vec: &Vec<Scalar>,
        s_vec: &Vec<Scalar>,
        y: Scalar,
    ) -> ZeroProof {
        //Create new transcript
        prover.new_domain_sep(b"ZeroArgumentProof");
        //Initial message
        //pick a0, bm
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let b_m: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //pick r0, s3
        let r_0 = Scalar::random(&mut OsRng);
        let s_m = Scalar::random(&mut OsRng);

        //comit on a0 and bm
        let c_a_0 = xpc_gens.commit(&a_0, r_0).compress();
        let c_b_m = xpc_gens.commit(&b_m, s_m).compress();

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
        //for k = 0,...,2m : compute d_k

        //BILINEAR MAP
        let dv = bilnearmap(&a_Array, &b_Array, y);

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
        //The verifier picks a challenge x which is z in my view
        let z_chal = prover.get_challenge(b"challenge");
        //let z_chal = Scalar::random(&mut OsRng);

        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = vectorutil::exp_iter(z_chal).take(2 * ROWS + 1).collect();
        let x_exp_m = &x_exp[0..ROWS + 1].to_vec();
        let x_k = &x_exp[0..2 * ROWS + 1].to_vec();
        //creating this explicitly for now. Shold be done in iterator
        let mut x_m_j = x_exp_m.clone();
        x_m_j.reverse();

        //creating a_bar
        //get COLUMNS of A matrix
        let a_cols = a_Array.as_columns();
        let b_cols = b_Array.as_columns();
        //calculate a0 + a1x + a2x^2 + ...
        let a1x: Vec<_> = a_cols[1].iter().map(|i| i * x_exp_m[1]).collect();
        let a2x2: Vec<_> = a_cols[2].iter().map(|i| i * x_exp_m[2]).collect();
        let a3x3: Vec<_> = a_cols[3].iter().map(|i| i * x_exp_m[3]).collect();

        //calculate x3b0 + b1x2 + b2x + ...
        let b0x3: Vec<_> = b_cols[0].iter().map(|i| i * x_m_j[0]).collect();
        let b1x2: Vec<_> = b_cols[1].iter().map(|i| i * x_m_j[1]).collect();
        let b2x: Vec<_> = b_cols[2].iter().map(|i| i * x_m_j[2]).collect();

        let mut a_bar_vec = Vec::<Scalar>::new();
        let mut b_bar_vec = Vec::<Scalar>::new();
        //creating a_bar and b_bar
        for i in 0..3 {
            a_bar_vec.push(a_cols[0][i] + a1x[i] + a2x2[i] + a3x3[i]);
            b_bar_vec.push(b0x3[i] + b1x2[i] + b2x[i] + b_cols[3][i]);
        }
        //extend r and s vectors
        let r_ext_vec = vec![r_0, r_vec[1], r_vec[2], Scalar::zero()];
        let s_ext_vec = vec![s_vec[0], s_vec[1], s_vec[2], s_m];

        //compute r_bar = r . x. x is [0....x^n]
        let r_bar: Scalar = vectorutil::vector_multiply_scalar(&r_ext_vec, &x_exp_m);

        //compute s_bar = s . x. x is [0....x^n]
        let s_bar: Scalar = vectorutil::vector_multiply_scalar(&s_ext_vec, &x_m_j);
        //compute t_bar = t . x. x is [0....x^2m+1]
        let t_bar: Scalar = vectorutil::vector_multiply_scalar(&t, &x_k);

        //Third Message. Send a_bar, b_bar, r_bar, s_bar, t_bar

        ZeroProof {
            c_A_0: c_a_0,
            c_B_m: c_b_m,
            c_D: c_D,
            a_vec: a_bar_vec,
            b_vec: b_bar_vec,
            r: r_bar,
            s: s_bar,
            t: t_bar,
        }
    }

    pub fn verify(
        &self,
        verifier: &mut Verifier,
        arg: &ZeroArgument,
        xpc_gens: &VectorPedersenGens,
        pc_gens: &PedersenGens,
        chal_y: Scalar,
    ) -> bool {
        //check lengths of vectors
        assert_eq!(self.c_D.len(), 2 * ROWS + 1);
        assert_eq!(self.a_vec.len(), COLUMNS);
        assert_eq!(self.b_vec.len(), COLUMNS);

        //Create new transcript
        verifier.new_domain_sep(b"ZeroArgumentProof");
        //recreate Transcript for Z challenge generation aby adding C_A_0 and C_B_m and C_D
        verifier.allocate_point(b"A0Commitment", self.c_A_0);
        verifier.allocate_point(b"BmCommitment", self.c_B_m);
        for cd in self.c_D.iter() {
            verifier.allocate_point(b"DCommitment", *cd);
        }

        //VERIFICATION CODE HERE.
        //Verifying c_d_m+1 = com(0,0)
        let comit_d_m_1 = self.c_D[ROWS + 1].decompress().unwrap();
        let zz = Scalar::zero();
        let zzz = Scalar::zero();
        let comit_0_0 = pc_gens.commit(zz, zzz);
        assert_eq!(comit_0_0, comit_d_m_1);
        //if comit_0_0 == comit_d_m_1{
        //  println!("Cdm+1 TRUE");
        //}

        // prod i=0..m (c_Ai^x^i ) = com(a_bar,r)
        //Com_A_0 ^ X^0 = com_a0
        let challenge = verifier.get_challenge(b"challenge");
        //recreate x_exp_m
        let x_exp: Vec<_> = vectorutil::exp_iter(challenge).take(2 * ROWS + 1).collect();
        //can use multiscalar_multiplication. should be done for all elements.
        let x_m_1 = &x_exp[1..ROWS + 1].to_vec();
        let points = arg
            .c_A
            .iter()
            .map(|p| p.decompress().unwrap())
            .collect::<Vec<RistrettoPoint>>();

        let temp_a = RistrettoPoint::multiscalar_mul(x_m_1.iter(), points.iter());
        let comit_a_product = self.c_A_0.decompress().unwrap() + temp_a;

        //com(a_bar,r)
        let comit_a_bar = xpc_gens.commit(&self.a_vec, self.r);
        // prod j=0..m (c_Bj^x^(m-j) ) = com(b_bar,s)
        //Com_B_m ^ X^0 = com_b3
        let x_exp_m = &x_exp[0..ROWS + 1].to_vec();
        let x_k = &x_exp[0..2 * ROWS + 1].to_vec();
        //creating this explicitly for now. Shold be done in iterator
        let mut x_m_j = x_exp_m.clone();
        x_m_j.reverse();
        //can use multiscalar_multiplication. should be done for all elements.
        let b_full = vec![
            arg.c_B[0].decompress().unwrap(),
            arg.c_B[1].decompress().unwrap(),
            arg.c_B[2].decompress().unwrap(),
            self.c_B_m.decompress().unwrap(),
        ];
        let comit_b_full = RistrettoPoint::multiscalar_mul(x_m_j.iter(), b_full.iter());

        //com(b_bar,s)
        let comit_b_bar = xpc_gens.commit(&self.b_vec, self.s);
        // Verify for k=0..2m c_D_k ^(x ^k)  ==  com(a_bar * b_bar; t) where * is bilinear map

        //com(a_bar * b_bar; t)
        //create y^i
        let y_i: Vec<_> = vectorutil::exp_iter(chal_y)
            .skip(1)
            .take(ROWS + 1)
            .collect();
        //let y_i = &y_exp[1..4].to_vec();
        let a_bar_b_bar = single_bilinearmap(&self.a_vec, &self.b_vec, &y_i);
        let comit_a_bar_b_bar = pc_gens.commit(a_bar_b_bar, self.t);

        //k=0..2m c_D_k ^(x ^k)
        let c_D_x_k: RistrettoPoint = self
            .c_D
            .iter()
            .zip(x_k.iter())
            .map(|(c, xk)| c.decompress().unwrap() * xk)
            .sum();

        if comit_a_bar_b_bar == c_D_x_k
            && comit_a_bar == comit_a_product
            && comit_b_bar == comit_b_full
        {
            return true;
        } else {
            return false;
        }
        // if comit_a_bar_b_bar == c_D_x_k{
        //     println!(" c_D_x_k Verifies");
        // }else{
        //     println!(" c_D_x_k Veification fails");
        // }
        // if comit_a_bar == comit_a_product{
        //     println!(" comit_a_bar Verifies");
        //     }
        //     if comit_b_bar == comit_b_full{
        //         println!(" comit_b_bar Verifies");
        //     }else{
        //         println!(" comit_b_bar Veification fails");
        //     }
    }
}

pub fn bilnearmap(a: &Array2D<Scalar>, b: &Array2D<Scalar>, y_chal: Scalar) -> Vec<Scalar> {
    //Estimate complete bilinear map for Matrix A and B. A and B are constructed in the calling function

    //create y^i
    let y_i: Vec<_> = vectorutil::exp_iter(y_chal)
        .skip(1)
        .take(ROWS + 1)
        .collect();
    //let y_i = &y_exp[1..4].to_vec();

    //converting Array2D to column representation. Can also use column iterator. Should look into it
    let a_as_cols = a.as_columns();
    let b_as_cols = b.as_columns();
    let mut dvec = Vec::<Scalar>::new();

    for k in 0isize..7 {
        //println!("K = , {:?}",k);
        let mut sum = Scalar::zero();
        for i in 0isize..=3 {
            //  println!("i = {:?}",i);
            for j in 0isize..=3 {
                //    println!("j = {:?}",j);
                //  println!("ROWS - k + i = {:?}",(3 - k + i));
                if j == (3 - k + i) {
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

pub fn single_bilinearmap(ai: &Vec<Scalar>, bj: &Vec<Scalar>, yi: &Vec<Scalar>) -> Scalar {
    ai.iter()
        .zip(bj.iter())
        .zip(yi.iter())
        .map(|((i, j), k)| i * j * k)
        .sum()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::shuffle::shuffle;
    use merlin::Transcript;
    //Matrix Size

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

        //for testing purposes only.
        let x_chal = Scalar::random(&mut OsRng);

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

        let (had_proof, x) = MultiHadamardProof::create_multi_hadamard_product_arg(
            &mut prover,
            &pi_2d,
            &pc_gens,
            &xpc_gens,
            &bvec,
            &comit_a_vec,
            &cb,
            x_chal,
            r,
            s,
        );
        //create MultiHadamard argument
        let had_arg = MultiHadamardArgument {
            c_A: comit_a_vec
                .iter()
                .map(|a| a.compress())
                .collect::<Vec<CompressedRistretto>>(),
            c_b: cb.compress(),
        };
        let verify = had_proof.verify(
            &mut verifier,
            &had_arg,
            &had_proof.zero_argument,
            &had_proof.zero_proof,
            &pc_gens,
            &xpc_gens,
            x,
        );
        assert!(verify);

        //println!("Verify Hadamard and Zero {:?}", verify)
    }

    #[test]
    fn product_proof_test() {
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);
        let pc_gens = PedersenGens::default();

        //for testing purposes only.
        let x_chal = Scalar::random(&mut OsRng);

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
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);

        let (prod_proof, x) = ProductProof::create_product_argument_prove(
            &mut prover,
            &pi_2d,
            &pc_gens,
            &xpc_gens,
            x_chal,
        );

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);

        let verify = prod_proof.verify(&mut verifier, &pc_gens, &xpc_gens, x);
        assert!(verify);

        //println!("Product Argument Verify {:?}", verify)
    }
}
