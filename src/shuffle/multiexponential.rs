//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::accounts::transcript;
use crate::shuffle::shuffle::COLUMNS;
use crate::shuffle::shuffle::ROWS;
use crate::{
    accounts::{Account, Prover, Verifier},
    elgamal::ElGamalCommitment,
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    shuffle::vectorutil,
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
// use serde::{Deserialize, Serialize};
use serde_derive::{Deserialize, Serialize};
use std::iter;
///Multiexponential Proof
///
#[derive(Debug, Clone, Serialize, Deserialize)]
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
    fn multiexpo_proof_inital_message_common(
        xpc_gens: &VectorPedersenGens,
        pc_gens: &PedersenGens,
        rng: &mut merlin::TranscriptRng,
    ) -> (
        Vec<Scalar>,
        Vec<Scalar>,
        Vec<Scalar>,
        CompressedRistretto,
        Vec<CompressedRistretto>,
        Scalar,
    ) {
        //compute random a_0 vectors of length n and r_0
        let a_0: Vec<_> = (0..COLUMNS).map(|_| Scalar::random(rng)).collect();
        let r_0 = Scalar::random(rng);

        //compute random vectors b, and s of length 2*m. No need fpr tau in this case.
        let mut b_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(rng)).collect();
        let mut s_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(rng)).collect();
        //explicitly set values at index m
        b_vec[ROWS] = Scalar::zero();
        s_vec[ROWS] = Scalar::zero();

        //compute Xtendedcomit on a_0
        let c_A_0 = xpc_gens.commit(&a_0, r_0).compress();
        //compute standard pedersen commitment on all items of b_vec
        let cb_k: Vec<_> = b_vec
            .iter()
            .zip(s_vec.iter())
            .map(|(b, s)| pc_gens.commit(*b, *s).compress())
            .collect();
        (a_0, b_vec, s_vec, c_A_0, cb_k, r_0)
    }
    fn multiexpo_proof_challenge_response_common(
        a_witness: &Array2D<Scalar>,
        x_exp: &[Scalar],
        a_0: &[Scalar],
        s_dash: &[Scalar],
        b_vec: &[Scalar],
        s_vec: &[Scalar],
        r_0: Scalar,
    ) -> (Vec<Scalar>, Scalar, Scalar, Scalar) {
        //compute a_vec = a_0 + Ax
        let perm_scalar_rows = a_witness.as_columns();

        let ax: Vec<Scalar> = (0..ROWS)
            .map(|i| vectorutil::vector_multiply_scalar(&perm_scalar_rows[i], &x_exp[1..ROWS + 1]))
            .collect();
        let mut a_vec = Vec::<Scalar>::new();
        for i in 0..ax.len() {
            a_vec.push(ax[i] + a_0[i]);
        }

        //compute r_vec = r . x. r is s' in thi case
        let rx: Scalar = vectorutil::vector_multiply_scalar(&s_dash, &x_exp[1..ROWS + 1]);
        let r = r_0 + rx;

        //compute b = b0 + sum from 1 to 2m-1 (bk.x^k)
        let bx = vectorutil::vector_multiply_scalar(&b_vec, &x_exp);

        //compute s = s0 + sum from 1 to 2m-1 (sk.x^k)
        let sx = vectorutil::vector_multiply_scalar(&s_vec, &x_exp);
        (a_vec, r, bx, sx)
    }
    pub fn create_multiexponential_elgamal_commit_proof(
       // prover: &mut Prover,
        commit: &[ElGamalCommitment],
        a_witness: &Array2D<Scalar>,
        s_dash: &[Scalar],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        base_pk: &RistrettoPublicKey,
        rho: Scalar,
    ) -> MultiexpoProof {
        //Create new transcript and prover instance
        let mut transcript = merlin::Transcript::new(b"MultiExponentialElgamalCommmitmentProof");
        let mut prover = Prover::new(b"ShuffleProof", &mut transcript);
        //prover.new_domain_sep(b"MultiExponentialElgamalCommmitmentProof");

        let witness_as_rows = a_witness.as_rows();
        // transcriptRng using public transcript data + secret for proof + external source
        let mut rng = prover.prove_rekey_witness_transcript_rng(&a_witness.as_row_major());
        //Compute initial message
        let (a_0, b_vec, s_vec, c_A_0, cb_k, r_0) =
            Self::multiexpo_proof_inital_message_common(&xpc_gens, &pc_gens, &mut rng);

        //compute tau of length 2*m.
        let mut tau_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut rng)).collect();

        //explicitly set values at index m
        tau_vec[ROWS] = rho;

        //create E_k
        let c: Vec<_> = commit.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let d: Vec<_> = commit.iter().map(|pt| pt.d.decompress().unwrap()).collect();
        //convert to 2D array representation
        let comm_matrix_c_rows = Array2D::from_row_major(&c, ROWS, COLUMNS);
        let comm_matrix_d_rows = Array2D::from_row_major(&d, ROWS, COLUMNS);
        //add a0 as the first column
        let a = vec![
            a_0.clone(),
            witness_as_rows[0].clone(),
            witness_as_rows[1].clone(),
            witness_as_rows[2].clone(),
        ];
        let a_2d = Array2D::from_rows(&a);
        //create e_k for c and d components of elgamal commitment
        let e_k_c = create_ek_common(&comm_matrix_c_rows, &a_2d);
        let e_k_d = create_ek_common(&comm_matrix_d_rows, &a_2d);
        let (E_K_c, E_K_d) = reencrypt_commitment_ek(&e_k_c, &e_k_d, &base_pk, &b_vec, &tau_vec);

        //add to Transcript for challenge x
        prover.allocate_point(b"A0Commitment", &c_A_0);
        //add comit_A and comit_tau in Transcript
        for ((cbk, ekc), ekd) in cb_k.iter().zip(E_K_c.iter()).zip(E_K_d.iter()) {
            prover.allocate_point(b"BKCommitment", cbk);
            prover.allocate_point(b"EK0Commitment", ekc);
            prover.allocate_point(b"EK1Commitment", ekd);
        }
        //create challenge x for hiding a and b
        let x = prover.get_challenge(b"xchallenege");
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();

        //Compute response to challenge x
        //Third Message. Send a_vec, r, b, s
        let (a_vec, r, bx, sx) = Self::multiexpo_proof_challenge_response_common(
            &a_witness, &x_exp, &a_0, s_dash, &b_vec, &s_vec, r_0,
        );

        //compute t = t0 + sum from 1 to 2m-1 (tk.x^k)
        let tx = vectorutil::vector_multiply_scalar(&tau_vec, &x_exp);

        //Third Message. Send a_vec, r, b, s
        //(
        MultiexpoProof {
            c_A_0: c_A_0,
            c_B_k: cb_k,
            E_k_0: E_K_c,
            E_k_1: E_K_d,
            a_vec: a_vec,
            r: r,
            b: bx,
            s: sx,
            t: tx,
        }
    }
    //b' is the witness and trated as A in the arguent described in paper
    pub fn create_multiexponential_pubkey_proof(
       // prover: &mut Prover,
        pks: &[RistrettoPublicKey],
        a_witness: &Array2D<Scalar>,
        s_dash: &[Scalar],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        base_pk: &RistrettoPublicKey,
    ) -> MultiexpoProof {
        //Create new transcript and prover instance
        let mut transcript = merlin::Transcript::new(b"MultiExponentialPubKeyProof");
        let mut prover = Prover::new(b"ShuffleProof", &mut transcript);
        //prover.new_domain_sep(b"MultiExponentialPubKeyProof");
        let witness_as_rows = a_witness.as_rows();
        // transcriptRng using public transcript data + secret for proof + external source
        let mut rng = prover.prove_rekey_witness_transcript_rng(&a_witness.as_row_major());
        //Compute initial message
        let (a_0, b_vec, s_vec, c_A_0, cb_k, r_0) =
            Self::multiexpo_proof_inital_message_common(&xpc_gens, &pc_gens, &mut rng);

        //create E_k
        let g: Vec<_> = pks.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h: Vec<_> = pks.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        //convert to 2D array representation
        let pk_matrix_g_rows = Array2D::from_row_major(&g, ROWS, COLUMNS);
        let pk_matrix_h_rows = Array2D::from_row_major(&h, ROWS, COLUMNS);
        //add a0 as the first column
        let a = vec![
            a_0.clone(),
            witness_as_rows[0].clone(),
            witness_as_rows[1].clone(),
            witness_as_rows[2].clone(),
        ];
        let a_2d = Array2D::from_rows(&a);
        let e_k_g = create_ek_common(&pk_matrix_g_rows, &a_2d);
        let e_k_h = create_ek_common(&pk_matrix_h_rows, &a_2d);
        //reencryption
        let (ek_g, ek_h) = reencrypt_publickey_ek(&e_k_g, &e_k_h, &base_pk, &b_vec);

        //send C_A_0, cb_k and E_k to the Verifier. 1st Message
        //add to Transcript for challenge x
        prover.allocate_point(b"A0Commitment", &c_A_0);
        //add comit_A and comit_tau in Transcript
        for ((cbk, ekg), ekh) in cb_k.iter().zip(ek_g.iter()).zip(ek_h.iter()) {
            prover.allocate_point(b"BKCommitment", cbk);
            prover.allocate_point(b"EK0Commitment", ekg);
            prover.allocate_point(b"EK1Commitment", ekh);
        }
        //create challenge x for hiding a and b

        let x = prover.get_challenge(b"xchallenege");
        // set x = (x, x^2, x^3, x^4.., x^N).
        let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();

        //Compute response to challenge x
        //Third Message. Send a_vec, r, b, s
        let (a_vec, r, bx, sx) = Self::multiexpo_proof_challenge_response_common(
            &a_witness, &x_exp, &a_0, &s_dash, &b_vec, &s_vec, r_0,
        );
        //(
        MultiexpoProof {
            c_A_0: c_A_0,
            c_B_k: cb_k,
            E_k_0: ek_g,
            E_k_1: ek_h,
            a_vec: a_vec,
            r: r,
            b: bx,
            s: sx,
            t: Scalar::zero(),
        }
    }
    fn verify_multiexpo_scalars(
        &self,
        c_A: &[CompressedRistretto],
        x_exp: &[Scalar],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
    ) -> Result<(), &'static str> {
        // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
        //compute C_A^x_vec
        let c_a_0_c_a_x_vec = RistrettoPoint::optional_multiscalar_mul(
            &x_exp[1..ROWS + 1],
            c_A.iter().map(|pt| pt.decompress()),
        )
        .ok_or_else(|| "MultiexponentialProof Verify: Failed")?
            + self
                .c_A_0
                .decompress()
                .ok_or("MultiexponentialProof Verify: Decompression Failed")?;

        //compute comit(a_vec:r). The commitment is on the a_vec from second message.
        let c_a_r = xpc_gens.commit(&self.a_vec, self.r);
        if c_a_0_c_a_x_vec == c_a_r {
            //Verifying Cb_0 .. == comit(b;s)
            let comit_b_s = pc_gens.commit(self.b, self.s);
            //product of (c_B_k)^(x^k)
            let c_b_k_x_k = RistrettoPoint::optional_multiscalar_mul(
                x_exp.iter(),
                self.c_B_k.iter().map(|pt| pt.decompress()),
            )
            .ok_or_else(|| "MultiexponentialProof Verify: Failed")?;
            if comit_b_s == c_b_k_x_k {
                Ok(())
            } else {
                Err("Multi-exponentiation Argument: Scalar b Verification Failed")
            }
        } else {
            Err("Multi-exponentiation Argument: a Scalar vector Verification Failed")
        }
    }
    ///verify the E_k equation. Option<T> are handled in calling function
    fn verify_multiexpo_ek(
        &self,
        x_exp: &[Scalar],
        c: &[RistrettoPoint],
        d: &[RistrettoPoint],
    ) -> (
        Option<RistrettoPoint>,
        Option<RistrettoPoint>,
        RistrettoPoint,
        RistrettoPoint,
    ) {
        //computing the left hand side. E0 + product of Ek^x^k
        //Ek^x^k for k = 1..2m-1
        let E_k_c_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_exp.iter(),
            self.E_k_0.iter().map(|pt| pt.decompress()),
        );
        let E_k_d_x_k = RistrettoPoint::optional_multiscalar_mul(
            x_exp.iter(),
            self.E_k_1.iter().map(|pt| pt.decompress()),
        );
        //convert to 2D array representation
        let c_2d_rows = Array2D::from_row_major(&c, ROWS, COLUMNS).as_rows();
        let d_2d_rows = Array2D::from_row_major(&d, ROWS, COLUMNS).as_rows();
        //computing the scalar x^3-1)a = x^2.a
        let x_1_a: Vec<_> = self.a_vec.iter().map(|i| i * x_exp[1]).collect();
        let x_2_a: Vec<_> = self.a_vec.iter().map(|i| i * x_exp[2]).collect();

        let c_c_x = RistrettoPoint::multiscalar_mul(
            x_2_a.iter().chain(x_1_a.iter()).chain(self.a_vec.iter()),
            c_2d_rows[0]
                .iter()
                .chain(c_2d_rows[1].iter())
                .chain(c_2d_rows[2].iter()),
        );

        let c_d_x = RistrettoPoint::multiscalar_mul(
            x_2_a.iter().chain(x_1_a.iter()).chain(self.a_vec.iter()),
            d_2d_rows[0]
                .iter()
                .chain(d_2d_rows[1].iter())
                .chain(d_2d_rows[2].iter()),
        );
        (E_k_c_x_k, E_k_d_x_k, c_c_x, c_d_x)
    }
    pub fn verify_multiexponential_elgamal_commit_proof(
        &self,
        //verifier: &mut Verifier,
        c_A: &[CompressedRistretto],
        updated_accounts: &[Account],
        accounts: &[Account],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        base_pk: &RistrettoPublicKey,
        exp_x: &[Scalar], //used for creating C on the verifier
    ) -> Result<(), &'static str> {
        //Check cA0,cB0,...,cB2m−1 ∈ G and E0,...,E2m−1 ∈ H and ~a ∈ Z_q^n
        //accept if cBm = comck(0; 0) and Em = C
        let comit_0_0 = pc_gens.commit(Scalar::zero(), Scalar::zero());
        //assert_eq!(comit_0_0.compress(), self.c_B_k[ROWS]);

        if self.a_vec.len() == COLUMNS && comit_0_0.compress() == self.c_B_k[ROWS] {
            //checking E_m == C
            //recreate C on Verifier as C = prod of i..n {comit_i{x^i}}
            //extract commitments from accounts
            let comitments: Vec<ElGamalCommitment> = accounts.iter().map(|acc| acc.comm).collect();
            let c_i = comitments
                .iter()
                .map(|c| {
                    c.c.decompress()
                        .ok_or("MultiexponentialProof Verify: Decompression Failed")
                })
                .collect::<Result<Vec<_>, _>>()?;
            let d_i = comitments
                .iter()
                .map(|d| {
                    d.d.decompress()
                        .ok_or("MultiexponentialProof Verify: Decompression Failed")
                })
                .collect::<Result<Vec<_>, _>>()?;
            let C_c = RistrettoPoint::multiscalar_mul(exp_x.iter(), c_i.iter());
            let C_d = RistrettoPoint::multiscalar_mul(exp_x.iter(), d_i.iter());
            //checking E_m == C
            if C_c.compress() == self.E_k_0[ROWS] && C_d.compress() == self.E_k_1[ROWS] {
                //Create new transcript and verifier instance
                let mut transcript =
                    merlin::Transcript::new(b"MultiExponentialElgamalCommmitmentProof");
                let mut verifier = Verifier::new(b"ShuffleProof", &mut transcript);
                //verifier.new_domain_sep(b"MultiExponentialElgamalCommmitmentProof");
                //recreate Challenge from Transcript
                verifier.allocate_point(b"A0Commitment", &self.c_A_0);
                for ((cbk, ek0), ek1) in self
                    .c_B_k
                    .iter()
                    .zip(self.E_k_0.iter())
                    .zip(self.E_k_1.iter())
                {
                    verifier.allocate_point(b"BKCommitment", cbk);
                    verifier.allocate_point(b"EK0Commitment", ek0);
                    verifier.allocate_point(b"EK1Commitment", ek1);
                }
                //create challenge x

                let x = verifier.get_challenge(b"xchallenege");

                // set x = (x, x^2, x^3, x^4.., x^N).
                let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();
                // Verify c_A_0 . c_A_vec^(x_vec) = com (a_vec,r)
                //Verifying Cb_0 .. == comit(b;s)
                self.verify_multiexpo_scalars(c_A, &x_exp, &pc_gens, &xpc_gens)?;

                //E_0 . prod of k =1 -> 2m-1 {E_k ^ {x^k}} = reencryption * prod of i =1 -> m {C_i ^ {x ^ m-i}a}
                //computing the rhs.
                //extract commitments from accounts
                let updated_comitments: Vec<ElGamalCommitment> =
                    updated_accounts.iter().map(|acc| acc.comm).collect();

                //extract c,d from commitments
                let c = updated_comitments
                    .iter()
                    .map(|pt| {
                        pt.c.decompress()
                            .ok_or("MultiexponentialProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let d = updated_comitments
                    .iter()
                    .map(|pt| {
                        pt.d.decompress()
                            .ok_or("MultiexponentialProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                //reencryption
                let c_bb = reencrypt_commitment(base_pk, self.t, self.b);
                //product of i ..m C_i^(x^m-i)a
                // for i = 1
                //computing the scalar x^(3-1)a = x^2.a
                //computing the left hand side. E0 + product of Ek^x^k
                //Ek^x^k for k = 1..2m-1
                let (E_k_c_x_k, E_k_d_x_k, c_c_x, c_d_x) = self.verify_multiexpo_ek(&x_exp, &c, &d);
                let rhs_c = c_c_x
                    + c_bb
                        .c
                        .decompress()
                        .ok_or("MultiexponentialProof Verify: Decompression Failed")?;
                let rhs_d = c_d_x
                    + c_bb
                        .d
                        .decompress()
                        .ok_or("MultiexponentialProof Verify: Decompression Failed")?;
                if E_k_c_x_k.ok_or("MultiexponentialProof Verify: Failed")? == rhs_c
                    && E_k_d_x_k.ok_or("MultiexponentialProof Verify:Failed")? == rhs_d
                {
                    Ok(())
                } else {
                    Err("Multi-exponentiation Commitment Argument: E_K Verification Failed")
                }
            } else {
                Err("Multi-exponentiation Commitment Argument: Verify C == Em Failed")
            }
        } else {
            Err("Multi-exponentiation Commitment Argument: Verify com(0,0) == c_B_m Failed")
        }
    }
    pub fn verify_multiexponential_pubkey_proof(
        &self,
       // verifier: &mut Verifier,
        c_A: &[CompressedRistretto],
        updated_accounts: &[Account],
        pc_gens: &PedersenGens,
        xpc_gens: &VectorPedersenGens,
        base_pk: &RistrettoPublicKey,
        pk_GH: &RistrettoPublicKey,
    ) -> Result<(), &'static str> {
        //accept if cBm = comck(0; 0) and Em = C
        let comit_0_0 = pc_gens.commit(Scalar::zero(), Scalar::zero());
        if self.a_vec.len() == COLUMNS && comit_0_0.compress() == self.c_B_k[ROWS] {
            //checking E_m == C
            //recreate C on Verifier as C = prod of i..n {comit_i{x^i}}
            //extract pubkeys from accounts

            //checking E_m == C, where C is (G,H) i.e, prod i..N {pk_i{x^i}}
            let e_m = RistrettoPublicKey {
                gr: self.E_k_0[ROWS],
                grsk: self.E_k_1[ROWS],
            };
            if *pk_GH == e_m {
                //Create new transcript and verifier instance
                let mut transcript = merlin::Transcript::new(b"MultiExponentialPubKeyProof");
                let mut verifier = Verifier::new(b"ShuffleProof", &mut transcript);
                //verifier.new_domain_sep(b"MultiExponentialPubKeyProof");
                //recreate Challenge from Transcript
                verifier.allocate_point(b"A0Commitment", &self.c_A_0);
                for ((cbk, ek0), ek1) in self
                    .c_B_k
                    .iter()
                    .zip(self.E_k_0.iter())
                    .zip(self.E_k_1.iter())
                {
                    verifier.allocate_point(b"BKCommitment", cbk);
                    verifier.allocate_point(b"EK0Commitment", ek0);
                    verifier.allocate_point(b"EK1Commitment", ek1);
                }
                //create challenge x

                let x = verifier.get_challenge(b"xchallenege");

                // set x = (x, x^2, x^3, x^4.., x^2m).
                let x_exp: Vec<_> = vectorutil::exp_iter(x).take(2 * ROWS).collect();

                //compute C_A^x_vec, //Verifying Cb_0 .. == comit(b;s), //product of (c_B_k)^(x^k)

                self.verify_multiexpo_scalars(c_A, &x_exp, &pc_gens, &xpc_gens)?;

                let upks: Vec<RistrettoPublicKey> =
                    updated_accounts.iter().map(|acc| acc.pk).collect();

                //extract g,h from RistrettoPublicKey
                let g = upks
                    .iter()
                    .map(|pt| {
                        pt.gr
                            .decompress()
                            .ok_or("MultiexponentialProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let h = upks
                    .iter()
                    .map(|pt| {
                        pt.grsk
                            .decompress()
                            .ok_or("MultiexponentialProof Verify: Decompression Failed")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                //reencryption (G,H)^b
                let g_bb = base_pk
                    .gr
                    .decompress()
                    .ok_or("MultiexponentialProof Verify: Decompression Failed")?
                    * self.b;
                let h_bb = base_pk
                    .grsk
                    .decompress()
                    .ok_or("MultiexponentialProof Verify: Decompression Failed")?
                    * self.b;
                //product of i ..m C_i^(x^m-i)a, Ek^x^k for k = 1..2m-1
                let (E_k_g_x_k, E_k_h_x_k, c_g_x, c_h_x) = self.verify_multiexpo_ek(&x_exp, &g, &h);

                let rhs_g = c_g_x + g_bb;
                let rhs_h = c_h_x + h_bb;
                if E_k_g_x_k.ok_or("MultiexponentialProof Verify: Failed")? == rhs_g
                    && E_k_h_x_k.ok_or("MultiexponentialProof Verify: Failed")? == rhs_h
                {
                    Ok(())
                } else {
                    Err("Multi-exponentiation Pubkey Argument: E_K Verification Failed")
                }
            } else {
                Err("Multi-exponentiation Pubkey Argument: Verify Em == C Failed")
            }
        } else {
            Err("Multi-exponentiation Pubkey Argument: Verify com(0,0) == c_B_m Failed")
        }
    }
}

//Explicit generation of e_k for 3x3 matrix
fn create_ek_common(
    cipher_mat: &Array2D<RistrettoPoint>, // c point -> Commitment,  OR g point -> Pk
    a_mat: &Array2D<Scalar>,
) -> Vec<RistrettoPoint> {
    //Row-wise arrangement of ciphertexts
    let cipher_mat_1_as_rows = cipher_mat.as_rows();
    //convert to column major representation
    let perm_scalar_as_rows = a_mat.as_rows();

    //Creating explicit e_k for 3x3 matrix

    //E_0.
    // (e0_c, e0_d) = sum of all i (c3^a0)
    let e0 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[0].iter(),
        cipher_mat_1_as_rows[2].iter(),
    );
    //println!("E_0 {:?}", e0_1);
    let e1 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[0]
            .iter()
            .chain(perm_scalar_as_rows[1].iter()),
        cipher_mat_1_as_rows[1]
            .iter()
            .chain(cipher_mat_1_as_rows[2].iter()),
    );

    //E_2.
    // (e2_c, e2_d) = sum of all i (c1^a0. c2^a1.c3^a2)
    let e2 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[0]
            .iter()
            .chain(perm_scalar_as_rows[1].iter())
            .chain(perm_scalar_as_rows[2].iter()),
        cipher_mat_1_as_rows[0]
            .iter()
            .chain(cipher_mat_1_as_rows[1].iter())
            .chain(cipher_mat_1_as_rows[2].iter()),
    );
    //E_3.
    // (e3_c, e3_d) = sum of all i (c1^a1.c2^a2.c3^a3)
    let e3 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[1]
            .iter()
            .chain(perm_scalar_as_rows[2].iter())
            .chain(perm_scalar_as_rows[3].iter()),
        cipher_mat_1_as_rows[0]
            .iter()
            .chain(cipher_mat_1_as_rows[1].iter())
            .chain(cipher_mat_1_as_rows[2].iter()),
    );

    //E_4.
    // (e4_c, e4_d) = sum of all i (c1^a2.c2^a3)
    let e4 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[2]
            .iter()
            .chain(perm_scalar_as_rows[3].iter()),
        cipher_mat_1_as_rows[0]
            .iter()
            .chain(cipher_mat_1_as_rows[1].iter()),
    );

    //E_5.
    // (e5_c, e5_d) = sum of all i (c1^a3)
    let e5 = RistrettoPoint::multiscalar_mul(
        perm_scalar_as_rows[3].iter(),
        cipher_mat_1_as_rows[0].iter(),
    );
    vec![e0, e1, e2, e3, e4, e5]
}
#[allow(dead_code)]
// General function for creating ek for Matrix size
fn create_ek_common_loop(
    cipher_mat: &Array2D<RistrettoPoint>,
    b_mat: &Array2D<Scalar>,
) -> Vec<RistrettoPoint> {
    //Row-wise arrangement of ciphertexts
    let cipher_mat_rows = cipher_mat.as_rows();

    //convert to column major representation
    let perm_scalar_cols = b_mat.as_columns();

    let mut e_k = Vec::with_capacity(2 * ROWS);

    let kiter = (2 * ROWS) as isize;
    let iiter = ROWS as isize;
    let jiiter = (ROWS + 1) as isize;
    let m = ROWS as isize; //m = ROWS in paper
    let mut j;
    for k in 0..kiter {
        let mut combined_scalars: Vec<&Scalar> = Vec::new();
        let mut point_c: Vec<&RistrettoPoint> = Vec::new();
        //let mut sum = Scalar::zero();
        for i in 1..=iiter {
            j = k - m + i;
            if j >= 0 && j < jiiter {
                //create a chain of iterators to run multiscalar_mul
                combined_scalars.extend(&perm_scalar_cols[j as usize]);
                point_c.extend(&cipher_mat_rows[i as usize - 1])
            }
        }
        e_k.push(RistrettoPoint::multiscalar_mul(
            combined_scalars.into_iter(),
            point_c.into_iter(),
        ));
    }
    e_k
}
//reencrypt e_k for commitment to produce E_k on the prover

fn reencrypt_commitment_ek(
    e_k_c: &Vec<RistrettoPoint>,
    e_k_d: &Vec<RistrettoPoint>,
    base_pk: &RistrettoPublicKey,
    b_random: &Vec<Scalar>,
    tau: &Vec<Scalar>,
) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
    let encrypt_comit: Vec<_> = b_random
        .iter()
        .zip(tau.iter())
        .map(|(b, i)| reencrypt_commitment(base_pk, *i, *b))
        .collect();

    let c_encrypt: Vec<_> = encrypt_comit.iter().map(|com| com.c.decompress()).collect();
    let d_encrypt: Vec<_> = encrypt_comit.iter().map(|com| com.d.decompress()).collect();

    let E_c: Vec<_> = c_encrypt
        .iter()
        .zip(e_k_c.iter())
        .map(|(ee, e)| (ee.unwrap() + e).compress())
        .collect();

    let E_d: Vec<_> = d_encrypt
        .iter()
        .zip(e_k_d.iter())
        .map(|(dd, d)| (dd.unwrap() + d).compress())
        .collect();

    (E_c, E_d)
}
//reencrypt e_k for public key to produce E_k on the prover
fn reencrypt_publickey_ek(
    e_k_g: &Vec<RistrettoPoint>,
    e_k_h: &Vec<RistrettoPoint>,
    base_pk: &RistrettoPublicKey,
    b_random: &Vec<Scalar>,
) -> (Vec<CompressedRistretto>, Vec<CompressedRistretto>) {
    //get base_pk
    let G = base_pk.gr.decompress().unwrap();
    let H = base_pk.grsk.decompress().unwrap();
    let g_reencrypt = iter::once(G)
        .chain(iter::once(G))
        .chain(iter::once(G))
        .chain(iter::once(G))
        .chain(iter::once(G))
        .chain(iter::once(G))
        .zip(b_random.iter())
        .zip(e_k_g.iter())
        .map(|((a, b), c)| ((a * b) + c).compress())
        .collect();

    let h_reencrypt = iter::once(H)
        .chain(iter::once(H))
        .chain(iter::once(H))
        .chain(iter::once(H))
        .chain(iter::once(H))
        .chain(iter::once(H))
        .zip(b_random.iter())
        .zip(e_k_h.iter())
        .map(|((a, b), c)| ((a * b) + c).compress())
        .collect();
    (g_reencrypt, h_reencrypt)
}

fn reencrypt_commitment(
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
        accounts::Account, shuffle::ddh::DDHProof, shuffle::shuffle, shuffle::vectorutil,
        shuffle::Shuffle,
    };
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    use array2d::Array2D;
    use merlin::Transcript;
    use rand::rngs::OsRng;
    //const N: usize = 9; //N - Length of vector
    #[test]
    fn multiexpo_pk_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (_, b_dash) =
            shuffle::create_b_b_dash(&exp_xx, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.0o0
        // x^i
        //println!("x^i {:?}", exp_xx);

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

        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_xx.iter(), h_i.iter());

        let pk_GH = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        //TESTING pk^b' == pk^ xi
        let pk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let g_outs_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_outs_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i ^ x_i)
        let G_out = RistrettoPoint::multiscalar_mul(b_dash.as_row_major().iter(), g_outs_i.iter());
        let h_out = RistrettoPoint::multiscalar_mul(b_dash.as_row_major().iter(), h_outs_i.iter());
        if G == G_out && H == h_out {
            println!("G out = pk^x_i = {:?}", true);
            println!("G = {:?} ", G.compress());
            println!("H = {:?} ", H.compress());
        } else {
            println!("G out = pk^x_i = {:?}", false);
        }
        let base_pk = RistrettoPublicKey::generate_base_pk();

        //create Prover and verifier
        //let mut transcript_p = Transcript::new(b"ShuffleProof");
        //let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        //commit on b'
        let s_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut OsRng)).collect();

        //create the ciphertext vector
        let rpk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let proof = MultiexpoProof::create_multiexponential_pubkey_proof(
          //  &mut prover,
            &rpk,
            &b_dash,
            &s_dash,
            &pc_gens,
            &xpc_gens,
            &base_pk,
        );

        //let mut transcript_v = Transcript::new(b"ShuffleProof");
       // let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);
        //let v = multiexpo_arg.C.compare(pk_x.gr, pk_x.grsk);
        //println!("Verify C = pk^x_i = {:?}", v);
        //println!("Pk_x_g = {:?} && Pk_x_h = {:?}", pk_x.gr, pk_x.grsk);
        // println!("Em_g = {:?} ", proof.E_k_0[3]);

        // println!("Em_h = {:?} ", proof.E_k_1[3]);
        // multiexpo_arg.C.print();
        let witness_as_rows = b_dash.as_rows();
        let mut comit_a_vec = Vec::<CompressedRistretto>::new();
        // //for i in 0..COLUMNS {
        for i in 0..ROWS {
            //     //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
            comit_a_vec.push(xpc_gens.commit(&witness_as_rows[i], s_dash[i]).compress());
        }
        let verify = proof.verify_multiexponential_pubkey_proof(
           // &mut verifier,
            &comit_a_vec,
            &shuffle.outputs.as_row_major(),
            &pc_gens,
            &xpc_gens,
            &base_pk,
            &pk_GH,
        );
        // println! {"Verify PubKey Multiexpo{:?} ", verify}
        assert!(verify.is_ok());
    }
    #[test]
    fn multiexpo_comm_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_mat, _) =
            shuffle::create_b_b_dash(&exp_xx, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
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
        let G = RistrettoPoint::multiscalar_mul(exp_xx.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_xx.iter(), h_i.iter());
        // let base_pk = RistrettoPublicKey::generate_base_pk();
        let base_pk = RistrettoPublicKey {
            gr: G.compress(),
            grsk: H.compress(),
        };
        //create vector of -rho of length N
        let neg_rho = -shuffle.rho;
        // let rho_vec: Vec<Scalar> = vec![
        //     neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho, neg_rho,
        // ];

        //create rho = -rho . b
        //let rho_b = vectorutil::vector_multiply_scalar(&rho_vec, &b_mat.as_row_major());
        //create Prover and verifier
       // let mut transcript_p = Transcript::new(b"ShuffleProof");
       // let mut prover = Prover::new(b"Shuffle", &mut transcript_p);
        //commit on b'
        let s_dash: Vec<_> = (0..ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        let witness_as_rows = b_mat.as_rows();
        let mut comit_a_vec = Vec::<CompressedRistretto>::new();
        // //for i in 0..COLUMNS {
        for i in 0..ROWS {
            //     //comit_a_vec.push(extended_commit(&perm_scalar_as_cols[i], s_dash[i], &xpc_gens));
            comit_a_vec.push(xpc_gens.commit(&witness_as_rows[i], s_dash[i]).compress());
        }
        //create the ciphertext vector
        let comm: Vec<ElGamalCommitment> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        let proof = MultiexpoProof::create_multiexponential_elgamal_commit_proof(
            //&mut prover,
            &comm,
            &b_mat,
            &s_dash,
            &pc_gens,
            &xpc_gens,
            &base_pk,
            neg_rho,
        );
        //testing Quisquis verification check
        //create DDH Proof
        let (_ddh_proof, _ddh_statement) = DDHProof::create_verify_update_ddh_prove(
            
            &g_i,
            &h_i,
            &exp_xx,
            G,
            H,
            shuffle.rho,
        );
        //checking C = Em where C is Commit ^ x . (G',H')
        let comm_in: Vec<ElGamalCommitment> = shuffle
            .inputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        let c_i: Vec<_> = comm_in.iter().map(|c| c.c.decompress().unwrap()).collect();
        let d_i: Vec<_> = comm_in.iter().map(|d| d.d.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let C_c = RistrettoPoint::multiscalar_mul(exp_xx.iter(), c_i.iter());
        // + ddh_statement.G_dash.decompress().unwrap();
        let C_d = RistrettoPoint::multiscalar_mul(exp_xx.iter(), d_i.iter());
        // + ddh_statement.H_dash.decompress().unwrap();

        if C_c.compress() == proof.E_k_0[3] && C_d.compress() == proof.E_k_1[3] {
            println!("true");
        } else {
            println!("false");
        }
       // let mut transcript_v = Transcript::new(b"ShuffleProof");
       // let mut verifier = Verifier::new(b"Shuffle", &mut transcript_v);

        let verify = proof.verify_multiexponential_elgamal_commit_proof(
            //&mut verifier,
            &comit_a_vec,
            &shuffle.outputs.as_row_major(),
            &shuffle.inputs.as_row_major(),
            &pc_gens,
            &xpc_gens,
            &base_pk,
            &exp_xx,
        );
        // println! {"Verify Commit Multiexpo{:?} ", verify}
        assert!(verify.is_ok());
    }
    #[test]
    fn ek_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (b_mat, b_dash) =
            shuffle::create_b_b_dash(&exp_xx, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
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
        let _G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let _H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());

        let a_0: Vec<Scalar> = vec![Scalar::from(3u64), Scalar::from(2u64), Scalar::from(1u64)];

        let comm: Vec<ElGamalCommitment> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        let c: Vec<_> = comm.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let d: Vec<_> = comm.iter().map(|pt| pt.d.decompress().unwrap()).collect();
        //convert to 2D array representation
        let comm_matrix_c_as_rows = Array2D::from_row_major(&c, ROWS, COLUMNS);
        let comm_matrix_d_as_rows = Array2D::from_row_major(&d, ROWS, COLUMNS);
        let perm_scalar_as_cols = b_mat.as_columns();
        let perm_scalar_as = vec![
            a_0.clone(),
            perm_scalar_as_cols[0].clone(),
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
        ];
        let input_b = Array2D::from_columns(&perm_scalar_as);

        let pkk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let gr: Vec<_> = pkk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let grsk: Vec<_> = pkk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        //convert to 2D array representation
        let gr_matrix_as_rows = Array2D::from_row_major(&gr, ROWS, COLUMNS);
        let grsk_matrix_as_rows = Array2D::from_row_major(&grsk, ROWS, COLUMNS);
        let perm_scalar_as_cols = b_dash.as_columns();
        let perm_scalar_dash = vec![
            a_0,
            perm_scalar_as_cols[0].clone(),
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
        ];
        let input_b_dash = Array2D::from_columns(&perm_scalar_dash);

        create_ek_common(&gr_matrix_as_rows, &input_b_dash);
        create_ek_common(&grsk_matrix_as_rows, &input_b_dash);
        let ekc = create_ek_common(&comm_matrix_d_as_rows, &input_b);
        create_ek_common(&comm_matrix_c_as_rows, &input_b);

        let e_k_c = create_ek_common_loop(&comm_matrix_c_as_rows, &input_b);
        // let e_k_c_compress: Vec<_> = e_k_c.iter().map(|pt| pt.compress()).collect();
        //println!("{:?}", e_k_c_compress);
        assert_eq!(e_k_c, ekc);
    }
    #[test]
    fn E_k_commit_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let _pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let _xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        // x^i
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();
        let (b_mat, _) =
            shuffle::create_b_b_dash(&exp_xx, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
        //Create Pk^x^ for testing purposes here. Should be refactored later.
        // gather g, h from Public key
        // gather g, h from Public key
        let base_pk = RistrettoPublicKey::generate_base_pk();

        let a_0: Vec<Scalar> = vec![Scalar::from(3u64), Scalar::from(2u64), Scalar::from(1u64)];

        //Calling create ek_comm function directly
        let b_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        let tau_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();
        //create 2DArrays
        let comm: Vec<ElGamalCommitment> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.comm)
            .collect();
        let c: Vec<_> = comm.iter().map(|pt| pt.c.decompress().unwrap()).collect();
        let d: Vec<_> = comm.iter().map(|pt| pt.d.decompress().unwrap()).collect();
        //convert to 2D array representation
        let comm_matrix_c_as_rows = Array2D::from_row_major(&c, ROWS, COLUMNS);
        let comm_matrix_d_as_rows = Array2D::from_row_major(&d, ROWS, COLUMNS);
        let perm_scalar_as_cols = b_mat.as_columns();
        let perm_scalar_as = vec![
            a_0.clone(),
            perm_scalar_as_cols[0].clone(),
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
        ];
        let input = Array2D::from_columns(&perm_scalar_as);

        let e_k_c = create_ek_common(&comm_matrix_c_as_rows, &input);
        let e_k_d = create_ek_common(&comm_matrix_d_as_rows, &input);
        let (_e_K_c, _e_K_d) = reencrypt_commitment_ek(&e_k_c, &e_k_d, &base_pk, &b_vec, &tau_vec);
        // assert_eq!(E_K_C, e_K_c);
        // assert_eq!(E_K_D, e_K_d);
    }
    #[test]
    fn E_k_pubkey_creation_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let (acc, _) = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let result = Shuffle::output_shuffle(&account_vector);
        let shuffle = result.unwrap();
        let _pc_gens = PedersenGens::default();
        //generate Xcomit generator points of length m+1
        let _xpc_gens = VectorPedersenGens::new(ROWS + 1);

        //create challenge x for b and b' vectors
        let x = Scalar::random(&mut OsRng);
        let exp_xx: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();

        //create b and b' vectors to be used for Multiexponentiationa and hadamard proof later
        let (_, b_dash) =
            shuffle::create_b_b_dash(&exp_xx, &shuffle.shuffled_tau.as_row_major(), &shuffle.pi);
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
        let _G = RistrettoPoint::multiscalar_mul(exp_xx.iter().clone(), g_i.iter().clone());
        let _H = RistrettoPoint::multiscalar_mul(&exp_xx, h_i.iter().clone());

        let a_0: Vec<Scalar> = vec![Scalar::from(3u64), Scalar::from(2u64), Scalar::from(1u64)];

        //Calling create ek_comm function directly
        let b_vec: Vec<_> = (0..2 * ROWS).map(|_| Scalar::random(&mut OsRng)).collect();

        //  let (E_K_G, E_K_H) = (&shuffle.outputs, &b_dash, &a_0.clone(), G, H, &b_vec);
        //     &tau_vec,)
        //create 2DArrays
        let pkk: Vec<RistrettoPublicKey> = shuffle
            .outputs
            .as_row_major()
            .iter()
            .map(|acc| acc.pk)
            .collect();
        let gr: Vec<_> = pkk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let grsk: Vec<_> = pkk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        //convert to 2D array representation
        let gr_matrix_as_rows = Array2D::from_row_major(&gr, ROWS, COLUMNS);
        let grsk_matrix_as_rows = Array2D::from_row_major(&grsk, ROWS, COLUMNS);
        let perm_scalar_as_cols = b_dash.as_columns();
        let perm_scalar_dash = vec![
            a_0,
            perm_scalar_as_cols[0].clone(),
            perm_scalar_as_cols[1].clone(),
            perm_scalar_as_cols[2].clone(),
        ];
        let input = Array2D::from_columns(&perm_scalar_dash);
        let base_pk = RistrettoPublicKey::generate_base_pk();
        let e_k_g = create_ek_common(&gr_matrix_as_rows, &input);
        let e_k_h = create_ek_common(&grsk_matrix_as_rows, &input);
        let (_e_K_g, _e_K_h) = reencrypt_publickey_ek(&e_k_g, &e_k_h, &base_pk, &b_vec);
        // assert_eq!(E_K_G, e_K_g);
        // assert_eq!(E_K_H, e_K_h);
    }
    #[test]
    fn just_test() {
        let ec: Vec<CompressedRistretto> = vec![
            CompressedRistretto([
                18, 240, 187, 189, 87, 214, 194, 118, 206, 129, 165, 129, 119, 71, 33, 7, 207, 247,
                191, 111, 85, 53, 211, 128, 128, 71, 129, 142, 191, 155, 220, 55,
            ]),
            CompressedRistretto([
                78, 7, 22, 46, 166, 217, 2, 147, 47, 42, 196, 103, 57, 233, 12, 188, 111, 148, 100,
                139, 90, 219, 68, 82, 29, 100, 195, 1, 101, 188, 233, 84,
            ]),
            CompressedRistretto([
                108, 42, 217, 98, 195, 149, 28, 83, 76, 121, 24, 252, 2, 193, 164, 120, 53, 31, 73,
                48, 124, 78, 185, 167, 24, 133, 116, 236, 81, 184, 83, 57,
            ]),
            CompressedRistretto([
                14, 118, 0, 66, 53, 118, 71, 12, 53, 13, 14, 77, 112, 126, 92, 201, 69, 105, 111,
                228, 59, 126, 19, 200, 111, 247, 16, 218, 175, 240, 199, 104,
            ]),
            CompressedRistretto([
                106, 16, 97, 2, 117, 128, 7, 191, 114, 41, 198, 21, 148, 136, 25, 58, 111, 2, 7,
                84, 38, 185, 146, 8, 63, 22, 115, 11, 112, 197, 26, 108,
            ]),
            CompressedRistretto([
                248, 84, 213, 159, 228, 248, 67, 55, 47, 153, 155, 221, 107, 127, 234, 60, 180,
                220, 247, 37, 214, 196, 8, 167, 33, 160, 217, 146, 22, 27, 150, 56,
            ]),
        ];
        let E_c: Vec<CompressedRistretto> = vec![
            CompressedRistretto([
                18, 240, 187, 189, 87, 214, 194, 118, 206, 129, 165, 129, 119, 71, 33, 7, 207, 247,
                191, 111, 85, 53, 211, 128, 128, 71, 129, 142, 191, 155, 220, 55,
            ]),
            CompressedRistretto([
                78, 7, 22, 46, 166, 217, 2, 147, 47, 42, 196, 103, 57, 233, 12, 188, 111, 148, 100,
                139, 90, 219, 68, 82, 29, 100, 195, 1, 101, 188, 233, 84,
            ]),
            CompressedRistretto([
                108, 42, 217, 98, 195, 149, 28, 83, 76, 121, 24, 252, 2, 193, 164, 120, 53, 31, 73,
                48, 124, 78, 185, 167, 24, 133, 116, 236, 81, 184, 83, 57,
            ]),
            CompressedRistretto([
                14, 118, 0, 66, 53, 118, 71, 12, 53, 13, 14, 77, 112, 126, 92, 201, 69, 105, 111,
                228, 59, 126, 19, 200, 111, 247, 16, 218, 175, 240, 199, 104,
            ]),
            CompressedRistretto([
                106, 16, 97, 2, 117, 128, 7, 191, 114, 41, 198, 21, 148, 136, 25, 58, 111, 2, 7,
                84, 38, 185, 146, 8, 63, 22, 115, 11, 112, 197, 26, 108,
            ]),
            CompressedRistretto([
                248, 84, 213, 159, 228, 248, 67, 55, 47, 153, 155, 221, 107, 127, 234, 60, 180,
                220, 247, 37, 214, 196, 8, 167, 33, 160, 217, 146, 22, 27, 150, 56,
            ]),
        ];
        assert_eq!(ec, E_c);
    }
}
