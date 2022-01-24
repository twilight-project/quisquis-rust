//! The `singlevalueproduct` module contains API for producing a 3-move argument of knowledge [Groth] of committed single
//!values having a particular product.
//!

#![allow(non_snake_case)]

use crate::{
    accounts::{Prover, Verifier},
    pedersen::vectorpedersen::VectorPedersenGens,
};

use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;

use crate::shuffle::shuffle::COLUMNS;
//use crate::shuffle::shuffle::ROWS;

///Single value Product argument
///
#[derive(Debug, Clone)]
pub struct SVPStatement {
    pub commitment_a: CompressedRistretto,
    pub b: Scalar,
}
///Single value Product Proof
///
#[derive(Debug, Clone)]
pub struct SVPProof {
    pub commitment_d: CompressedRistretto,
    pub commitment_delta_small: CompressedRistretto,
    pub commitment_delta_capital: CompressedRistretto,
    pub a_twildle: Vec<Scalar>,
    pub b_twildle: Vec<Scalar>,
    pub r_twildle: Scalar,
    pub s_twildle: Scalar,
}

impl SVPProof {
    ///Create Single Value Argument proof
    ///
    pub fn create_single_value_argument_proof(
        prover: &mut Prover,
        xpc_gens: &VectorPedersenGens,
        comit_a: RistrettoPoint,
        b: Scalar,
        r: Scalar,
        a_vec: &[Scalar],
    ) -> SVPProof {
        //Create new transcript
        prover.new_domain_sep(b"SingleValueProductProof");

        //compute the first message

        //compute b1 =a1, b2 =a1 ·a2, b3 =b2 ·b3, b4= b3 ·a4
        let mut bvec = Vec::<Scalar>::new();

        let mut prod: Scalar = Scalar::one();
        for ai in a_vec.iter() {
            prod = prod * ai;
            bvec.push(prod);
        }
        //Pick d1,...,dn, and rd randomly
        let d_vec: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let rd = Scalar::random(&mut OsRng);
        //Compute vector commitment on d_vec. send it to verifier
        let comit_d = xpc_gens.commit(&d_vec, rd);

        //compute random delta of COLUMN size and set delta_1 as d_1 and delta_n as 0
        let mut delta_vec: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        delta_vec[0] = d_vec[0];
        delta_vec[COLUMNS - 1] = Scalar::zero();
        //pick local random s_1 and s_x to comit on delta_vec and d_delta
        let s_1 = Scalar::random(&mut OsRng);
        let s_x = Scalar::random(&mut OsRng);

        //Create commitments on delta and d_delta
        // cdelta and cDelta have n-1 entries
        let mut delta_small = Vec::<Scalar>::new();
        let mut delta_cap = Vec::<Scalar>::new();

        // delta[i] = - delta_vec[i] * d_vec[i+1]
        for i in 0..COLUMNS - 1 {
            delta_small.push((-delta_vec[i]) * d_vec[i + 1]);
        }

        // d_Delta[i] = delta_vec[i+1] - a[i+1]*delta_vec[i] - bvec[i]*dvec[i+1]
        for i in 0..COLUMNS - 1 {
            delta_cap
                .push(delta_vec[i + 1] - (a_vec[i + 1] * delta_vec[i]) - (bvec[i] * d_vec[i + 1]));
        }
        //println!("{:?}", delta);
        //println!("{:?}", d_delta);

        //The msg terms are smaller than the number of commitment keys in extended commitment function.
        //create new CommitmentGens to accomodate for smaller lengths
        let xpc_gens_trun = VectorPedersenGens::new(delta_small.len() + 1);

        //Create commitment
        let comit_delta_small = xpc_gens_trun.commit(&delta_small, s_1); //send it to verifier

        let comit_delta_cap = xpc_gens_trun.commit(&delta_cap, s_x); //send it to verifier
                                                                     //println!("{:?}", comit_delta);
                                                                     //println!("{:?}", comit_d_delta);
                                                                     //SEND comit_d, comit_delta, comit_d_delta to the verifier

        //Add variables to Merlin transcript for challenge generation
        prover.allocate_point(b"DeltaSmall", comit_delta_small.compress());
        prover.allocate_point(b"DeltaCapital", comit_delta_cap.compress());
        prover.allocate_point(b"d", comit_d.compress());

        // Compute Challenge x
        let x = prover.get_challenge(b"challenge");
        //let x = Scalar::random(&mut OsRng);

        //compute a_bar = x *a_vec + d_vec

        let a_bar: Vec<_> = a_vec
            .iter()
            .zip(d_vec.iter())
            .map(|(a, d)| a * x + d)
            .collect();
        //compute b_bar = x *bvec + delta_vec

        let b_bar: Vec<_> = bvec
            .iter()
            .zip(delta_vec.iter())
            .map(|(b, d)| b * x + d)
            .collect();

        //compute rbar = xr + rd
        let r_bar = r * x + rd;

        //compute sbar = xs_x + s_1
        let s_bar = s_x * x + s_1;

        //send all this to verifier
        SVPProof {
            commitment_d: comit_d.compress(),
            commitment_delta_small: comit_delta_small.compress(),
            commitment_delta_capital: comit_delta_cap.compress(),
            a_twildle: a_bar,
            b_twildle: b_bar,
            r_twildle: r_bar,
            s_twildle: s_bar,
        }
    }

    ///This method is for verifying the single value product proof
    pub fn verify(
        &self,
        verifier: &mut Verifier,
        svparg: &SVPStatement,
        /* x: Scalar,*/ xpc_gens: &VectorPedersenGens,
    ) -> bool {
        //Verification Code
        //checking the length of a_twildle and b_twildle vectors
        assert_eq!(self.a_twildle.len(), COLUMNS);
        assert_eq!(self.b_twildle.len(), COLUMNS);

        //Create new transcript
        verifier.new_domain_sep(b"SingleValueProductProof");
        //RECREATE X FROM MERLIN HERE
        //Add variables to Merlin transcript for challenge generation
        verifier.allocate_point(b"DeltaSmall", self.commitment_delta_small);
        verifier.allocate_point(b"DeltaCapital", self.commitment_delta_capital);
        verifier.allocate_point(b"d", self.commitment_d);

        let x = verifier.get_challenge(b"challenge");
        //c_a^x * c_d == com(abar;rbar)
        //Compute vector commitment on a_twildle
        let comit_a_bar = xpc_gens.commit(&self.a_twildle, self.r_twildle);
        //compute comit_a * challenge x
        let cax = svparg.commitment_a.decompress().unwrap() * x;
        let caxcd = cax + self.commitment_d.decompress().unwrap();

        //c_∆^x . c_δ = com_ck(x ̃b2 − ̃b1 ̃a2,...,x ̃bn − ̃bn−1 ̃an;  ̃s)

        let cdelta_cap_x = self.commitment_delta_capital.decompress().unwrap() * x;
        let cdelta_cap_x_delta_small =
            cdelta_cap_x + self.commitment_delta_small.decompress().unwrap();

        let mut comvec = Vec::<Scalar>::new();
        // comvec[i] = x * b_bar[i+1] - b_bar[i]a_bar[i+1]

        for i in 0..COLUMNS - 1 {
            comvec.push((self.b_twildle[i + 1] * x) - (self.b_twildle[i] * self.a_twildle[i + 1]));
        }

        //create new CommitmentGens to accomodate for smaller lengths
        let xpc_gens_trun = VectorPedersenGens::new(comvec.len() + 1);
        let comit_verify = xpc_gens_trun.commit(&comvec, self.s_twildle);
        // b_bar_n == b * x
        let xb = svparg.b * x;

        if cdelta_cap_x_delta_small == comit_verify
            && caxcd == comit_a_bar
            && self.a_twildle[0] == self.b_twildle[0]
            && caxcd == comit_a_bar
            && xb == self.b_twildle[COLUMNS - 1]
        {
            //println!("SVP verified");
            return true;
        } else {
            //println!("SVP Failed");
            return false;
        }
        // a_bar1 == b_bar1
        //  if self.a_twildle[0][0] == self.b_twildle[0] {
        //    println!("a1 == b1");
        // }

        // if self.b_twildle[COLUMNS - 1] == xb {
        //   println!("xb == bn");
        // }
        // if caxcd == comit_a_bar {
        //   println!("caxcd == comit_a_bar");
        //}
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::shuffle::shuffle::ROWS;
    use crate::shuffle::singlevalueproduct::SVPProof;
    use array2d::Array2D;
    use merlin::Transcript;
    #[test]
    fn single_value_product_proof_test() {
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

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

        //create b. i.e., product of all elements in A
        let b = bvec.iter().product::<Scalar>();

        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"SingleValue");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);

        let proof = SVPProof::create_single_value_argument_proof(
            &mut prover,
            &xpc_gens,
            cb.clone(),
            b.clone(),
            s,
            &bvec,
        );
        let arg = SVPStatement {
            commitment_a: cb.compress(),
            b: b,
        };

        let mut transcript_v = Transcript::new(b"SingleValue");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        let verify = proof.verify(&mut verifier, &arg, &xpc_gens);
        assert!(verify);
        // println!("Verification {:?}",verify);
    }
}
