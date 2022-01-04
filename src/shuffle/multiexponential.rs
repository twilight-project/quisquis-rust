//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;
use crate::{
    accounts::{Account, Prover, Verifier},
    elgamal::ElGamalCommitment,
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    shuffle::vectorutil,
    shuffle::Shuffle,
};
use array2d::Array2D;
use bulletproofs::PedersenGens;
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;

///Multiexponential Proof Statement
/// aGiven ciphertexts C_11,...,C_mn and C we will give in this section an argument of knowledge of openings
//of commitments ~cA to A = {a_ij}i,j=1 to n,m
///~C1,..., ~Cm ∈ H^n , C ∈ H and ~cA ∈ G^m
#[derive(Debug, Clone)]
pub struct MultiexpoStatement {
    //Vector of lenght m
    pub c_A: Vec<CompressedRistretto>,
    pub C: CompressedRistretto,
    // C1,..., ~Cm Vectors.  Figure out an enum to support both commit and Pubkeys
    //pub cipher: array2d<>
}
///Multiexponential Proof
///
#[derive(Debug, Clone)]
pub struct MultiexpoProof {
    pub c_A_0: CompressedRistretto,
    pub c_B_k: Vec<CompressedRistretto>,
    pub E_k_0: Vec<CompressedRistretto>,
    pub E_k_1: Vec<CompressedRistretto>,
    pub a_vec: Vec<Scalar>,
    pub r: Scalar,
    pub b: Scalar,
    pub s: Scalar,
    pub t: Scalar,
}
impl MultiexpoProof {
    pub fn create_multiexponential_elgamal_commit_proof(
        prover: &mut Prover,
        shuf: &Shuffle,
        a_witness: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        pk: &RistrettoPublicKey,
        rho: Scalar,
    ) -> (MultiexpoProof, Vec<RistrettoPoint>) {
        //Create new transcript
        prover.new_domain_sep(b"MultiExponentialElgamalCommmitmentProof");

        //create random number s' to vector commit on witness. The commitment is on columns of A matrix
        //compute s'. it is the witness in c_A
        let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //create statement
        //compute Xcomit on A
        //convert to column major representation
        let perm_scalar_as_cols = a_witness.as_columns();
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
            comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], s_dash[i]));
        }
        //compute random a_0 vectors of length n and r_0
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let r_0 = Scalar::random(&mut OsRng);

        //compute random vectors b, s, and tau of length 2*m.
        let mut b_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut s_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut tau_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();

        //explicitly set values at index m
        b_vec[ROWS] = Scalar::zero();
        s_vec[ROWS] = Scalar::zero();
        tau_vec[ROWS] = rho;

        //compute Xcomit on a_0
        //let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
        let c_A_0 = xpc_gens.commit(&a_0, r_0).compress();

        //compute standard pedersen commitment on all items of b_vec
        let cb_k: Vec<_> = b_vec
            .iter()
            .zip(s_vec.iter())
            .map(|(b, s)| pc_gens.commit(*b, *s).compress())
            .collect();

        //create E_k
        let (ek_c, ek_d) = create_ek_comm(&shuf.outputs, &a_witness, &a_0, pk, &b_vec, &tau_vec);

        //send C_A_0, cb_k and E_k to the Verifier. 1st Message
        //add to Transcript for challenge x
        prover.allocate_point(b"A0Commitment", c_A_0);
        //add comit_A and comit_tau in Transcript
        for i in 0..cb_k.iter().count() {
            prover.allocate_point(b"BKCommitment", cb_k[i]);
            prover.allocate_point(b"EK0Commitment", ek_c[i]);
            prover.allocate_point(b"EK1Commitment", ek_d[i]);
        }
        //create challenge x for hiding a and b

        let x = prover.get_challenge(b"xchallenege");

        //create challenge x for hiding a and b
        //let x = Scalar::random(&mut OsRng);
        let x = Scalar::from(3u64);
        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        let x_exp_m = &x_exp[1..ROWS + 1].to_vec();
        let x_k = &x_exp[1..2 * ROWS].to_vec();

        //compute a_vec = a_0 + Ax
        //borrow A
        let perm_scalar_rows = a_witness.as_rows();

        let ax: Vec<Scalar> = (0..ROWS)
            .map(|i| vectorutil::vector_multiply_scalar(&perm_scalar_rows[i], &x_exp_m))
            .collect();
        let mut a_vec = Vec::<Scalar>::new();
        //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect();
        for i in 0..ax.len() {
            a_vec.push(ax[i] + a_0[i]);
        }

        //compute r_vec = r . x. r is s' in thi case
        let rx: Scalar = vectorutil::vector_multiply_scalar(&s_dash, &x_exp_m);
        let r = r_0 + rx;

        //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
        let bx = vectorutil::vector_multiply_scalar(&b_vec[1..6].to_vec(), &x_k);
        let b = b_vec[0] + bx;

        //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
        let sx = vectorutil::vector_multiply_scalar(&s_vec[1..6].to_vec(), &x_k);
        let s = s_vec[0] + sx;

        //compute t = t0 + sum from 1 to 2m-1 (tk.x^k)
        let tx = vectorutil::vector_multiply_scalar(&tau_vec[1..6].to_vec(), &x_k);
        let t = tau_vec[0] + tx;

        //Third Message. Send a_vec, r, b, s
        (
            MultiexpoProof {
                c_A_0: c_A_0,
                c_B_k: cb_k,
                E_k_0: ek_c,
                E_k_1: ek_d,
                a_vec: a_vec,
                r: r,
                b: b,
                s: s,
                t: t,
            },
            comit_a_vec,
        )
    }
    pub fn verify_multiexponential_elgamal_commit_proof(
        &self,
        verifier: &mut Verifier,
        multiexpo_statement: &MultiexpoStatement,
        shuffle: &Shuffle,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        pk: &RistrettoPublicKey,
    ) -> bool {
        //Check cA0,cB0,...,cB2m−1 ∈ G and E0,...,E2m−1 ∈ H and ~a ∈ Z_q^n
        assert_eq!(self.a_vec.len(), COLUMNS);
        //accept if cBm = comck(0; 0) and Em = C
        //let comit_b_m = self.c_B_k[ROWS];
        let comit_0_0 = pc_gens.commit(Scalar::zero(), Scalar::zero());
        assert_eq!(comit_0_0.compress(), self.c_B_k[ROWS]);

        //Create new transcript
        verifier.new_domain_sep(b"MultiExponentialElgamalCommmitmentProof");
        //recreate Challenge from Transcript
        verifier.allocate_point(b"A0Commitment", self.c_A_0);
        //add comit_A and comit_tau in Transcript
        for i in 0..self.c_B_k.iter().count() {
            verifier.allocate_point(b"BKCommitment", self.c_B_k[i]);
            verifier.allocate_point(b"EK0Commitment", self.E_k_0[i]);
            verifier.allocate_point(b"EK1Commitment", self.E_k_1[i]);
        }
        //create challenge x

        let x = verifier.get_challenge(b"xchallenege");

        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        let x_exp_m = &x_exp[1..ROWS + 1].to_vec();
        let x_k = &x_exp[1..2 * ROWS].to_vec();
        // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
        //compute C_A^x_vec
        let c_a_x_vec = RistrettoPoint::optional_multiscalar_mul(
            x_exp_m.iter(),
            multiexpo_statement.c_A.iter().map(|pt| pt.decompress()),
        );
        //let trying = extended_commit(&ax, rx, &xpc_gens);
        let c_a_0_c_a_x_vec = c_a_x_vec.unwrap() + self.c_A_0.decompress().unwrap();
        //compute comit(a_vec:r). The commitment is on the a_vec from second message.
        // let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
        let c_a_r = xpc_gens.commit(&self.a_vec, self.r);

        //Verifying Cb_0 .. == comit(b;s)
        let comit_b_s = pc_gens.commit(self.b, self.s);
        //product of (c_B_k)^(x^k)
        let len_cb = self.c_B_k.len();
        let c_b_k = &self.c_B_k[1..len_cb].to_vec();
        let c_b_k_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter().clone(),
            c_b_k.iter().map(|pt| pt.decompress()),
        );
        //c_B_0 + product of c_B_k..
        let cb_sum = self.c_B_k[0].decompress().unwrap() + c_b_k_x_k.unwrap();

        //checking E_m == C . In this case C is product of all N Pk^x^i. Which is also G, and H. Check this later
        //Creating C on the prover and checking
        // let (em_g, em_h) = create_C_comit_prover(&shuf.outputs, &a_witness, pk, rho);
        // if ek_c[ROWS] == em_g && ek_d[ROWS] == em_h {
        //     println!("Em == Cprover  TRUE");
        // } else {
        //     println!("Em ==Cprover  FALSE");
        // }

        //Big verification
        //computing the left hand side. E0 + product of Ek^x^k
        //Ek^x^k for k = 1..2m-1
        let ek_c_1_5 = &self.E_k_0[1..6].to_vec();
        let ek_d_1_5 = &self.E_k_1[1..6].to_vec();
        // println!("{:?}",x_k);
        // println!("{:?}",ek_g);
        let E_k_c_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter(),
            ek_c_1_5.iter().map(|pt| pt.decompress()),
        );
        let E_k_d_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter(),
            ek_d_1_5.iter().map(|pt| pt.decompress()),
        );
        // let E_k_g_x_k =
        //     RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_g_1_5.iter().clone());
        // let E_k_h_x_k =
        //     RistrettoPoint::multiscalar_mul(x_k.iter().clone(), ek_h_1_5.iter().clone());
        let lhs_g = self.E_k_0[0].decompress().unwrap() + E_k_c_x_k.unwrap();
        let lhs_h = self.E_k_1[0].decompress().unwrap() + E_k_d_x_k.unwrap();

        //computing the rhs.
        //extract commitments from accounts
        let comm: Vec<ElGamalCommitment> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        //convert to 2D array representation
        let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS, COLUMNS).as_rows();

        //Preparing vectors for multiscalar
        let c1 = &comm_matrix_as_rows[0];
        let c2 = &comm_matrix_as_rows[1];
        let c3 = &comm_matrix_as_rows[2];

        // gather c, d from ElgamalCommitment
        let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
        let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
        let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();

        //reencryption
        let c_bb = reencrypt_commitment(pk, self.t, self.b);
        //product of i ..m C_i^(x^m-i)a
        // for i = 1
        //computing the scalar x^3-1)a = x^2.a
        let x_2 = x_exp_m[1];
        let x_2_a: Vec<_> = self.a_vec.iter().map(|i| i * x_2).collect();

        let c1_g_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_c.clone());
        let c1_h_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_d.clone());

        // for i = 2
        //computing the scalar x^3-2)a = x.a
        let x_1 = x_exp_m[0];
        let x_1_a: Vec<_> = self.a_vec.iter().map(|i| i * x_1).collect();

        let c2_g_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_c.clone());
        let c2_h_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_d.clone());

        // for i = 3
        //computing the scalar x^3-3)a = a
        let c3_g_xa = RistrettoPoint::multiscalar_mul(self.a_vec.clone(), c3_c.clone());
        let c3_h_xa = RistrettoPoint::multiscalar_mul(self.a_vec.clone(), c3_d.clone());

        //adding all points together
        let c_g_x = c3_g_xa + c1_g_xa + c2_g_xa;
        let c_h_x = c3_h_xa + c1_h_xa + c2_h_xa;

        let rhs_g = c_g_x + c_bb.c.decompress().unwrap();
        let rhs_h = c_h_x + c_bb.d.decompress().unwrap();
        lhs_g == rhs_g && lhs_h == rhs_h && c_a_0_c_a_x_vec == c_a_r && comit_b_s == cb_sum
        // if lhs_g == rhs_g && lhs_h == rhs_h {
        //     println!("lhs == rhs TRUE");
        // } else {
        //     println!("Lhs ==rhs  FALSE");
        // }
        // if c_a_0_c_a_x_vec == c_a_r {
        //     println!("CA TRUE");
        // } else {
        //     println!("CA FALSE");
        // }
        // if comit_b_s == cb_sum {
        //     println!("CB TRUE");
        // } else {
        //     println!("CB FALSE");
        // }
    }

    //b' is the witness and trated as A in the arguent described in paper
    pub fn create_multiexponential_pubkey_proof(
        prover: &mut Prover,
        shuf: &Shuffle,
        a_witness: &Array2D<Scalar>,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        G: RistrettoPoint,
        H: RistrettoPoint,
    ) -> (MultiexpoProof, Vec<RistrettoPoint>) {
        //Create new transcript
        prover.new_domain_sep(b"MultiExponentialPubKeyProof");
        //create random number s' to vector commit on witness. The commitment is on columns of A matrix
        //compute s'. it is the witness in c_A
        let s_dash: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();

        //create statement
        //compute Xcomit on A
        //convert to column major representation
        let perm_scalar_as_cols = a_witness.as_columns();
        let mut comit_a_vec = Vec::<RistrettoPoint>::new();
        for i in 0..COLUMNS {
            //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
            comit_a_vec.push(xpc_gens.commit(&perm_scalar_as_cols[i], s_dash[i]));
        }
        //compute random a_0 vectors of length n and r_0
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(&mut OsRng)).collect();
        let r_0 = Scalar::random(&mut OsRng);

        //compute random vectors b, and s of length 2*m. No need fpr tau in this case.
        let mut b_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        let mut s_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        //explicitly set values at index m
        b_vec[ROWS] = Scalar::zero();
        s_vec[ROWS] = Scalar::zero();

        //compute Xcomit on a_0
        //let c_A_0 = extended_commit(&a_0, r_0, &xpc_gens);
        let c_A_0 = xpc_gens.commit(&a_0, r_0).compress();
        //compute standard pedersen commitment on all items of b_vec
        let cb_k: Vec<_> = b_vec
            .iter()
            .zip(s_vec.iter())
            .map(|(b, s)| pc_gens.commit(*b, *s).compress())
            .collect();

        let (ek_g, ek_h) = create_ek_pk(&shuf.outputs, &a_witness, &a_0, G, H, &b_vec);

        //send C_A_0, cb_k and E_k to the Verifier. 1st Message
        //add to Transcript for challenge x
        prover.allocate_point(b"A0Commitment", c_A_0);
        //add comit_A and comit_tau in Transcript
        for i in 0..cb_k.iter().count() {
            prover.allocate_point(b"BKCommitment", cb_k[i]);
            prover.allocate_point(b"EK0Commitment", ek_g[i]);
            prover.allocate_point(b"EK1Commitment", ek_h[i]);
        }
        //create challenge x for hiding a and b

        let x = prover.get_challenge(b"xchallenege");
        //let x = Scalar::from(3u64);
        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        let x_exp_m = &x_exp[1..ROWS + 1].to_vec();
        let x_k = &x_exp[1..2 * ROWS].to_vec();

        //compute a_vec = a_0 + Ax
        //borrow A
        let perm_scalar_rows = a_witness.as_rows();

        let ax: Vec<Scalar> = (0..ROWS)
            .map(|i| vectorutil::vector_multiply_scalar(&perm_scalar_rows[i], &x_exp_m))
            .collect();
        let mut a_vec = Vec::<Scalar>::new();
        //let a_vec: Vec<Scalar> = ax.iter().zip(a_0.iter()).map(|(i,j)| i+j).collect();
        for i in 0..ax.len() {
            a_vec.push(ax[i] + a_0[i]);
        }

        //compute r_vec = r . x. r is s' in thi case
        let rx: Scalar = vectorutil::vector_multiply_scalar(&s_dash, &x_exp_m);
        let r = r_0 + rx;

        //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
        let bx = vectorutil::vector_multiply_scalar(&b_vec[1..6].to_vec(), &x_k);
        let b = b_vec[0] + bx;

        //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
        let sx = vectorutil::vector_multiply_scalar(&s_vec[1..6].to_vec(), &x_k);
        let s = s_vec[0] + sx;

        //Third Message. Send a_vec, r, b, s
        (
            MultiexpoProof {
                c_A_0: c_A_0,
                c_B_k: cb_k,
                E_k_0: ek_g,
                E_k_1: ek_h,
                a_vec: a_vec,
                r: r,
                b: b,
                s: s,
                t: Scalar::zero(),
            },
            comit_a_vec,
        )
    }
    pub fn verify_multiexponential_pubkey_proof(
        &self,
        verifier: &mut Verifier,
        multiexpo_statement: &MultiexpoStatement,
        shuffle: &Shuffle,
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        G: RistrettoPoint,
        H: RistrettoPoint,
    ) -> bool {
        //Check cA0,cB0,...,cB2m−1 ∈ G and E0,...,E2m−1 ∈ H and ~a ∈ Z_q^n
        assert_eq!(self.a_vec.len(), COLUMNS);
        //accept if cBm = comck(0; 0) and Em = C
        //let comit_b_m = self.c_B_k[ROWS];
        let comit_0_0 = pc_gens.commit(Scalar::zero(), Scalar::zero());
        assert_eq!(comit_0_0.compress(), self.c_B_k[ROWS]);

        //checking E_m == C . In this case C is product of all N Pk^x^i. Which is also G, and H. Check this later
        // if self.E_k_0[ROWS] == G.compress() && self.E_k_1[ROWS] == H.compress() {
        //   println!("Em == C^x  TRUE");
        //} else {
        //  println!("Em == C^x  FALSE");
        // }
        assert_eq!(self.E_k_0[ROWS], G.compress());
        assert_eq!(self.E_k_1[ROWS], H.compress());

        //Create new transcript
        verifier.new_domain_sep(b"MultiExponentialPubKeyProof");
        //recreate Challenge from Transcript
        verifier.allocate_point(b"A0Commitment", self.c_A_0);
        //add comit_A and comit_tau in Transcript
        for i in 0..self.c_B_k.iter().count() {
            verifier.allocate_point(b"BKCommitment", self.c_B_k[i]);
            verifier.allocate_point(b"EK0Commitment", self.E_k_0[i]);
            verifier.allocate_point(b"EK1Commitment", self.E_k_1[i]);
        }
        //create challenge x

        let x = verifier.get_challenge(b"xchallenege");

        // set x = (x, x^2, x^3, x^4.., x^m). Thesis says length should be m but rebekkah has its length as 2m-2
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
        let x_exp_m = &x_exp[1..ROWS + 1].to_vec();
        let x_k = &x_exp[1..2 * ROWS].to_vec();

        //VERIFICATION CODE HERE.
        //Verifying c_B_m = com(0,0)
        // if comit_0_0.compress() == comit_b_m {
        //    println!("Cbm TRUE");
        // }
        // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
        //println!("{:?}",x_exp_m);
        //compute C_A^x_vec
        let c_a_x_vec = RistrettoPoint::optional_multiscalar_mul(
            x_exp_m.iter(),
            multiexpo_statement.c_A.iter().map(|pt| pt.decompress()),
        );
        //let trying = extended_commit(&ax, rx, &xpc_gens);
        let c_a_0_c_a_x_vec = c_a_x_vec.unwrap() + self.c_A_0.decompress().unwrap();
        //compute comit(a_vec:r)
        //let c_a_r = extended_commit(&a_vec, r, &xpc_gens);
        let c_a_r = xpc_gens.commit(&self.a_vec, self.r);

        //Verifying Cb_0 .. == comit(b;s)
        let comit_b_s = pc_gens.commit(self.b, self.s);
        //product of (c_B_k)^(x^k)
        let len_cb = self.c_B_k.len();
        let c_b_k = &self.c_B_k[1..len_cb].to_vec();
        let c_b_k_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter(),
            c_b_k.iter().map(|pt| pt.decompress()),
        );
        //c_B_0 + product of c_B_k..
        let cb_sum = self.c_B_k[0].decompress().unwrap() + c_b_k_x_k.unwrap();

        // //Creating C on the prover and checking
        // let (em_g, em_h) = create_C_pk_prover(&shuf.outputs, &a_witness);
        // if ek_g[ROWS] == em_g && ek_h[ROWS] == em_h {
        //     println!("Em == Cprover  TRUE");
        // } else {
        //     println!("Em ==Cprover  FALSE");
        // }

        //Big verification
        //computing the left hand side. E0 + product of Ek^x^k
        //Ek^x^k for k = 1..2m-1
        let ek_g_1_5 = &self.E_k_0[1..2 * ROWS];
        let ek_h_1_5 = &self.E_k_1[1..2 * ROWS];
        // println!("{:?}",x_k);
        // println!("{:?}",ek_g);
        let E_k_g_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter(),
            ek_g_1_5.iter().map(|pt| pt.decompress()),
        );
        let E_k_h_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_k.iter(),
            ek_h_1_5.iter().map(|pt| pt.decompress()),
        );
        let lhs_g = self.E_k_0[0].decompress().unwrap() + E_k_g_x_k.unwrap();
        let lhs_h = self.E_k_1[0].decompress().unwrap() + E_k_h_x_k.unwrap();

        //computing the rhs.
        //extract commitments from accounts
        let pk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        //convert to 2D array representation
        let pk_matrix_as_rows = Array2D::from_row_major(&pk, ROWS, COLUMNS).as_rows();

        //Preparing vectors for multiscalar
        let c1 = &pk_matrix_as_rows[0];
        let c2 = &pk_matrix_as_rows[1];
        let c3 = &pk_matrix_as_rows[2];

        // gather c, d from ElgamalCommitment
        let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        //reencryption (G,H)^b
        let g_bb = G * self.b;
        let h_bb = H * self.b;

        //product of i ..m C_i^(x^m-i)a
        // for i = 1
        //computing the scalar x^3-1)a = x^2.a
        let x_2 = x_exp_m[1];
        let x_2_a: Vec<_> = self.a_vec.iter().map(|i| i * x_2).collect();

        let c1_g_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_c.clone());
        let c1_h_xa = RistrettoPoint::multiscalar_mul(x_2_a.clone(), c1_d.clone());

        // for i = 2
        //computing the scalar x^3-2)a = x.a
        let x_1 = x_exp_m[0];
        let x_1_a: Vec<_> = self.a_vec.iter().map(|i| i * x_1).collect();

        let c2_g_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_c.clone());
        let c2_h_xa = RistrettoPoint::multiscalar_mul(x_1_a.clone(), c2_d.clone());

        // for i = 3
        //computing the scalar x^3-3)a = a
        let c3_g_xa = RistrettoPoint::multiscalar_mul(self.a_vec.clone(), c3_c.clone());
        let c3_h_xa = RistrettoPoint::multiscalar_mul(self.a_vec.clone(), c3_d.clone());

        //adding all points together
        let c_g_x = c3_g_xa + c1_g_xa + c2_g_xa;
        let c_h_x = c3_h_xa + c1_h_xa + c2_h_xa;

        let rhs_g = c_g_x + g_bb;
        let rhs_h = c_h_x + h_bb;
        lhs_g == rhs_g && lhs_h == rhs_h && c_a_0_c_a_x_vec == c_a_r && comit_b_s == cb_sum
        // if lhs_g == rhs_g && lhs_h == rhs_h {
        //     println!("lhs == rhs TRUE");
        // } else {
        //     println!("Lhs ==rhs  FALSE");
        // }
        // if c_a_0_c_a_x_vec == c_a_r {
        //     println!("CA TRUE");
        // } else {
        //     println!("CA FALSE");
        // }
        //   if comit_b_s == cb_sum {
        //     println!("CB TRUE");
        // } else {
        //     println!("CB FALSE");
        // }
    }
}
pub fn create_C_comit_prover(
    accounts: &Array2D<Account>,
    pi: &Array2D<Scalar>,
    pk: &RistrettoPublicKey,
    rho: Scalar,
) -> (RistrettoPoint, RistrettoPoint) {
    //extract commitments from accounts
    let comm: Vec<ElGamalCommitment> = accounts.as_row_major().iter().map(|acc| acc.comm).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS, COLUMNS).as_rows();

    //convert to column major representation
    let perm_scalar_as_cols = pi.as_columns();

    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes

    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    // (e3_c, e3_d) = product of all i -> m  (C_i^(a_i))
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    // reencryption
    let xero = Scalar::zero();
    let comit = reencrypt_commitment(pk, rho, xero);
    let C_c = e3_c + comit.c.decompress().unwrap();
    let C_d = e3_d + comit.d.decompress().unwrap();
    (C_c, C_d)
}

pub fn create_C_pk_prover(
    accounts: &Array2D<Account>,
    pi: &Array2D<Scalar>,
) -> (RistrettoPoint, RistrettoPoint) {
    //extract commitments from accounts
    let comm: Vec<RistrettoPublicKey> = accounts.as_row_major().iter().map(|acc| acc.pk).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS, COLUMNS).as_rows();

    //convert to column major representation
    let perm_scalar_as_cols = pi.as_columns();
    //println!("{:?}",perm_scalar_as_cols);
    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes

    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    // (e3_c, e3_d) = product of all i -> m  (C_i^(a_i))
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    // let encrypt_1_rho =
    (e3_c, e3_d)
}

pub fn create_ek_comm(
    accounts: &Array2D<Account>,
    b_mat: &Array2D<Scalar>,
    a0: &Vec<Scalar>,
    pk: &RistrettoPublicKey,
    b_random: &Vec<Scalar>,
    tau: &Vec<Scalar>,
) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
    //extract commitments from accounts
    let comm: Vec<ElGamalCommitment> = accounts.as_row_major().iter().map(|acc| acc.comm).collect();
    //convert to 2D array representation
    let comm_matrix_as_rows = Array2D::from_row_major(&comm, ROWS, COLUMNS).as_rows();

    //convert to column major representation
    let perm_scalar_as_cols = b_mat.as_columns();

    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes

    //Preparing vectors for multiscalar
    let c1 = &comm_matrix_as_rows[0];
    let c2 = &comm_matrix_as_rows[1];
    let c3 = &comm_matrix_as_rows[2];

    // gather c, d from ElgamalCommitment
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.d.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.c.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.d.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    //E_5.
    // (e5_c, e5_d) = sum of all i (c1^a3)
    let e5_c = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_c.iter().clone());
    let e5_d = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_d.iter().clone());

    //E_4.
    // (e4_c, e4_d) = sum of all i (c1^a2.c2^a3)
    let mut combined_scalars = a2.clone();
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    let e4_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e4_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_3.
    // (e3_c, e3_d) = sum of all i (c1^a1.c2^a2.c3^a3)
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_2.
    // (e2_c, e2_d) = sum of all i (c1^a0. c2^a1.c3^a2)
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a0.clone());
    let mut point_c = c2_c.clone();
    point_c.extend(c3_c.clone());
    point_c.extend(c1_c.clone());
    let mut point_d = c2_d.clone();
    point_d.extend(c3_d.clone());
    point_d.extend(c1_d.clone());
    let e2_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e2_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_1.
    // (e1_c, e1_d) = sum of all i (c2^a0 . c3^a1)
    let mut combined_scalars = a0.clone();
    combined_scalars.extend(a1.clone());
    let mut point_c = c2_c.clone();
    point_c.extend(c3_c.clone());
    let mut point_d = c2_d.clone();
    point_d.extend(c3_d.clone());
    let e1_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e1_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //E_0.
    // (e0_c, e0_d) = sum of all i (c3^a0)
    let e0_c = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_c.iter().clone());
    let e0_d = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_d.iter().clone());

    let e_c = vec![e0_c, e1_c, e2_c, e3_c, e4_c, e5_c];
    let e_d = vec![e0_d, e1_d, e2_d, e3_d, e4_d, e5_d];

    //reencryption
    //creating encrytpion for eack ek
    let encrypt_comit: Vec<_> = b_random
        .iter()
        .zip(tau.iter())
        .map(|(b, i)| reencrypt_commitment(pk, *i, *b))
        .collect();

    let c_encrypt: Vec<_> = encrypt_comit.iter().map(|com| com.c.decompress()).collect();
    let d_encrypt: Vec<_> = encrypt_comit.iter().map(|com| com.d.decompress()).collect();

    let E_c: Vec<_> = c_encrypt
        .iter()
        .zip(e_c.iter())
        .map(|(ee, e)| (ee.unwrap() + e).compress())
        .collect();

    let E_d: Vec<_> = d_encrypt
        .iter()
        .zip(e_d.iter())
        .map(|(dd, d)| (dd.unwrap() + d).compress())
        .collect();

    (E_c, E_d)
    //(e_c,e_d)
}
pub fn create_ek_pk(
    accounts: &Array2D<Account>,
    b_dash: &Array2D<Scalar>,
    a0: &Vec<Scalar>,
    G: RistrettoPoint,
    H: RistrettoPoint,
    b_random: &Vec<Scalar>,
) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
    //extract commitments from accounts
    let pk: Vec<RistrettoPublicKey> = accounts.as_row_major().iter().map(|acc| acc.pk).collect();
    //convert to 2D array representation
    let pk_matrix_as_rows = Array2D::from_row_major(&pk, ROWS, COLUMNS).as_rows();

    //convert b' to column major representation
    let perm_scalar_as_cols = b_dash.as_columns();

    //Creating ek's as individual entites. Should be refactored later. this is only done for testing purposes

    //Preparing vectors for multiscalar
    let c1 = &pk_matrix_as_rows[0];
    let c2 = &pk_matrix_as_rows[1];
    let c3 = &pk_matrix_as_rows[2];

    // gather g, h from Publickey
    let c1_c: Vec<_> = c1.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c1_d: Vec<_> = c1.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c2_c: Vec<_> = c2.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c2_d: Vec<_> = c2.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    let c3_c: Vec<_> = c3.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let c3_d: Vec<_> = c3.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();

    //Column vectors for A
    let a1 = &perm_scalar_as_cols[0];
    let a2 = &perm_scalar_as_cols[1];
    let a3 = &perm_scalar_as_cols[2];

    //E_5.
    // (e5_c, e5_d) = sum of all i (c1^a3)
    let e5_c = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_c.iter().clone());
    let e5_d = RistrettoPoint::multiscalar_mul(a3.iter().clone(), c1_d.iter().clone());
    //reencryption
    let e5_g_encrypt = G * b_random[5];
    let e5_h_encrypt = H * b_random[5];

    let e5_g = e5_c + e5_g_encrypt;
    let e5_h = e5_d + e5_h_encrypt;

    //E_4.
    // (e4_c, e4_d) = sum of all i (c1^a2.c2^a3)
    let mut combined_scalars = a2.clone();
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    let e4_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e4_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //reencryption
    let e4_g_encrypt = G * b_random[4];
    let e4_h_encrypt = H * b_random[4];

    let e4_g = e4_c + e4_g_encrypt;
    let e4_h = e4_d + e4_h_encrypt;

    //E_3.
    // (e3_c, e3_d) = sum of all i (c1^a1.c2^a2.c3^a3)
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a3.clone());
    let mut point_c = c1_c.clone();
    point_c.extend(c2_c.clone());
    point_c.extend(c3_c.clone());
    let mut point_d = c1_d.clone();
    point_d.extend(c2_d.clone());
    point_d.extend(c3_d.clone());
    let e3_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e3_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());
    //reencryption
    let e3_g_encrypt = G * b_random[3];
    let e3_h_encrypt = H * b_random[3];

    let e3_g = e3_c + e3_g_encrypt;
    let e3_h = e3_d + e3_h_encrypt;

    //E_2.
    // (e2_c, e2_d) = sum of all i (c1^a0. c2^a1.c3^a2)
    let mut combined_scalars = a1.clone();
    combined_scalars.extend(a2.clone());
    combined_scalars.extend(a0.clone());
    let mut point_c = c2_c.clone();
    point_c.extend(c3_c.clone());
    point_c.extend(c1_c.clone());
    let mut point_d = c2_d.clone();
    point_d.extend(c3_d.clone());
    point_d.extend(c1_d.clone());
    let e2_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e2_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());

    //reencryption
    let e2_g_encrypt = G * b_random[2];
    let e2_h_encrypt = H * b_random[2];

    let e2_g = e2_c + e2_g_encrypt;
    let e2_h = e2_d + e2_h_encrypt;

    //E_1.
    // (e1_c, e1_d) = sum of all i (c2^a0 . c3^a1)
    let mut combined_scalars = a0.clone();
    combined_scalars.extend(a1.clone());
    let mut point_c = c2_c.clone();
    point_c.extend(c3_c.clone());
    let mut point_d = c2_d.clone();
    point_d.extend(c3_d.clone());
    let e1_c = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_c.iter());
    let e1_d = RistrettoPoint::multiscalar_mul(combined_scalars.iter(), point_d.iter());
    //reencryption
    let e1_g_encrypt = G * b_random[1];
    let e1_h_encrypt = H * b_random[1];

    let e1_g = e1_c + e1_g_encrypt;
    let e1_h = e1_d + e1_h_encrypt;

    //E_0.
    // (e0_c, e0_d) = sum of all i (c3^a0)
    let e0_c = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_c.iter().clone());
    let e0_d = RistrettoPoint::multiscalar_mul(a0.iter().clone(), c3_d.iter().clone());

    //reencryption
    let e0_g_encrypt = G * b_random[0];
    let e0_h_encrypt = H * b_random[0];

    let e0_g = e0_c + e0_g_encrypt;
    let e0_h = e0_d + e0_h_encrypt;

    let e_c = vec![
        e0_g.compress(),
        e1_g.compress(),
        e2_g.compress(),
        e3_g.compress(),
        e4_g.compress(),
        e5_g.compress(),
    ];
    let e_d = vec![
        e0_h.compress(),
        e1_h.compress(),
        e2_h.compress(),
        e3_h.compress(),
        e4_h.compress(),
        e5_h.compress(),
    ];

    //without encryption ek
    //let e_c_W_E = vec![e0_c, e1_c, e2_c, e3_c, e4_c, e5_c];
    //let e_d_W_E = vec![e0_d, e1_d, e2_d, e3_d, e4_d, e5_d];

    (e_c, e_d)
}

pub fn reencrypt_commitment(
    p: &RistrettoPublicKey,
    rscalar: Scalar,
    bl_scalar: Scalar,
) -> ElGamalCommitment {
    // lets make c
    let c = &rscalar * &p.gr.decompress().unwrap();

    // lets multiply balance scalar with the basepoint scalar
    let gv = &bl_scalar * &RISTRETTO_BASEPOINT_POINT;

    let kh = &rscalar * &p.grsk.decompress().unwrap();

    // lets make d
    let d = &gv + &kh;

    ElGamalCommitment {
        c: c.compress(),
        d: d.compress(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::shuffle::shuffle::COLUMNS;
    use crate::shuffle::shuffle::ROWS;
    use crate::{
        accounts::Account,
        shuffle::shuffle,
        shuffle::vectorutil,
        shuffle::{Permutation, Shuffle},
    };
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use array2d::Array2D;
    use merlin::Transcript;
    use rand::rngs::OsRng;
    const N: usize = 9; //N - Length of vector
    #[test]
    fn multiexpo_pk_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (_, b_dash) =
            shuffle::create_b_b_dash(x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
        // gather g, h from Public key
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);

        let (proof, argCommitment) = MultiexpoProof::create_multiexponential_pubkey_proof(
            &mut prover,
            &shuffle,
            &b_dash,
            &pc_gens,
            &xpc_gens,
            G,
            H,
        );
        let multiexpo_arg = MultiexpoStatement {
            c_A: argCommitment.iter().map(|a| a.compress()).collect(),
            C: CompressedRistretto::default(),
        };

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);

        let verify = proof.verify_multiexponential_pubkey_proof(
            &mut verifier,
            &multiexpo_arg,
            &shuffle,
            &pc_gens,
            &xpc_gens,
            G,
            H,
        );
        println! {"Verify PubKey Multiexpo{:?} ", verify}
        assert_eq!(true, true);
    }
    #[test]
    fn multiexpo_comm_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_mat, _) =
            shuffle::create_b_b_dash(x, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
        // gather g, h from Public key
        // gather g, h from Public key
        let pk: Vec<RistrettoPublicKey> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());
        let pk = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };

        //create vector of -rho of length N
        let neg_rho = -shuffle.rho;
        let rho_vec: Vec<Scalar> = vec![
            neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho,
        ];

        //create rho = -rho . b
        let rho_b = vectorutil::vector_multiply_scalar(&rho_vec, &b_mat.as_row_major());

        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        let (proof, argCommitment) = MultiexpoProof::create_multiexponential_elgamal_commit_proof(
            &mut prover,
            &shuffle,
            &b_mat,
            &pc_gens,
            &xpc_gens,
            &pk,
            rho_b,
        );
        // multiexp_commit_prove(&shuffle, &b_mat, &pc_gens, &xpc_gens, &pk, rho_b);
        let multiexpo_arg = MultiexpoStatement {
            c_A: argCommitment.iter().map(|a| a.compress()).collect(),
            C: CompressedRistretto::default(),
        };

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);

        let verify = proof.verify_multiexponential_elgamal_commit_proof(
            &mut verifier,
            &multiexpo_arg,
            &shuffle,
            &pc_gens,
            &xpc_gens,
            &pk,
        );
        println! {"Verify PubKey Multiexpo{:?} ", verify}
        assert_eq!(true, true);
    }

    #[test]
    fn ek_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let accounts = Array2D::from_row_major(&account_vector, ROWS, COLUMNS);
        let perm = Permutation::new(&mut OsRng, N);
        //println!("{:?}",perm.perm_matrix);
        //println!("{:?}",perm.perm_matrix.as_columns());

        //create_ek_comm(&accounts,&perm);
    }
}
