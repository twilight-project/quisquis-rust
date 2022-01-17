//! The `vectorpedersen` module contains API for producing a
//! vector commitment.

#![allow(non_snake_case)]

use crate::{
    accounts::{Prover, Verifier},
    ristretto::RistrettoPublicKey,
    shuffle::vectorutil,
};
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};

/*
pub fn hadamard_product_proof_prover(tau: Array2D<Scalar>, pi: Permutation)->(Vec<RistrettoPoint>,Vec<RistrettoPoint>,Vec<RistrettoPoint>){
//create pedersen generators for Xtended commitment
let pc_gens = PedersenGens::default();
    //generate Xcomit generator points of length m+1
let gens = extended_pedersen_gen(ROWS+1, pc_gens.B, pc_gens.B_blinding);

//Store Xtended commitments for tau, b and b'
let mut c_tau : Vec<RistrettoPoint> = Vec::new();
let mut c_b : Vec<RistrettoPoint> = Vec::new();
let mut c_b_dash : Vec<RistrettoPoint> = Vec::new();

// X challenge from the verifier
let x = Scalar::random(&mut OsRng);

let (b, b_dash) = create_b_b_dash(x, &tau.as_row_major(), &pi.perm_matrix.as_row_major());

//process matrices as columns
let tau_cols = tau.as_rows();
let b_cols = b.as_rows();
let b_dash_cols = b_dash.as_rows();

//rscalar blindings for Xtended commits
let rscalar_tau = Scalar::random(&mut OsRng);
let rscalar_b = Scalar::random(&mut OsRng);
let rscalar_b_dash = Scalar::random(&mut OsRng);

//Create Xtended commitment on tau, b and b'
for i in 0..3{
    c_tau.push(extended_commit(&tau_cols[i], rscalar_tau, &gens));
    c_b.push(extended_commit(&b_cols[i], rscalar_b, &gens));
    c_b_dash.push(extended_commit(&b_dash_cols[i], rscalar_b_dash, &gens));
}
(c_tau, c_b, c_b_dash)
}

*/
pub fn verify_update_ddh_prove(
    x: Scalar,
    pk: &Vec<RistrettoPublicKey>,
    rho: Scalar,
) -> (Scalar, Scalar, CompressedRistretto, CompressedRistretto) {
    // x^i
    let exp_x: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
    // gather g, h from Public key
    let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    // (G, H) = sum of all i (pk_i * x^i)
    let G = RistrettoPoint::multiscalar_mul(exp_x.iter().clone(), g_i.iter().clone());
    let H = RistrettoPoint::multiscalar_mul(&exp_x, h_i.iter().clone());
    // x^i * rho
    let exp_x_rho: Vec<_> = exp_x.iter().map(|x| x * rho).collect();
    // (G', H')
    let G_dash = RistrettoPoint::multiscalar_mul(exp_x_rho.iter().clone(), g_i.iter().clone());
    let H_dash = RistrettoPoint::multiscalar_mul(&exp_x_rho, h_i.iter().clone());

    //create the ddh prove
    let (z, chal) = Prover::verify_update_ddh_prover(G, H, G_dash, H_dash, rho);
    (z, chal, G_dash.compress(), H_dash.compress())
}

pub fn verify_update_ddh_verify(
    x: Scalar,
    pk: &Vec<RistrettoPublicKey>,
    g_dash: CompressedRistretto,
    h_dash: CompressedRistretto,
    z: Scalar,
    chal: Scalar,
) -> bool {
    // x^i
    let exp_x: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
    // gather g, h from Public key
    let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
    let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
    // (G, H) = sum of all i (pk_i * x^i)
    let G = RistrettoPoint::multiscalar_mul(exp_x.iter().clone(), g_i.iter().clone());
    let H = RistrettoPoint::multiscalar_mul(&exp_x, h_i.iter().clone());

    //verify the ddh prove
    Verifier::verify_update_ddh_verifier(G.compress(), H.compress(), g_dash, h_dash, z, chal)
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::accounts::Account;
    use crate::{
        keys::{PublicKey, SecretKey},
        ristretto::{RistrettoPublicKey, RistrettoSecretKey},
    };
    //use array2d::Array2D;
    use rand::rngs::OsRng;
    //use crate::shuffle::shuffle::COLUMNS;
    //use crate::shuffle::shuffle::ROWS;
    //const N: usize = 9;   //N - Length of vector
    #[test]
    fn ddh_prove_test() {
        let mut account_vector: Vec<Account> = Vec::new();
        // lets create these accounts and associated keypairs
        for _ in 0..9 {
            let mut rng = rand::thread_rng();
            let sk: RistrettoSecretKey = SecretKey::random(&mut rng);
            let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
            let acc = Account::generate_account(pk);
            account_vector.push(acc);
        }
        let pk: Vec<RistrettoPublicKey> = account_vector.iter().map(|acc| acc.pk).collect();
        let x = Scalar::random(&mut OsRng);
        let rho = Scalar::random(&mut OsRng);
        let (z, chal, G_dash, H_dash) = verify_update_ddh_prove(x, &pk, rho);
        let verify = verify_update_ddh_verify(x, &pk, G_dash, H_dash, z, chal);
        assert_eq!(verify, true);
    }

    // #[test]
    // fn x_psi_test() {
    //     //let x = Scalar::random(&mut OsRng);
    //     let x = Scalar::from(2u64);
    //     let exp_x: Vec<_> = vectorutil::exp_iter(x).take(9).collect();
    //     let perm = Permutation::new(&mut OsRng, N);
    //     let perm_vec = perm.perm_matrix.as_row_major();
    //     let mut x_psi: Vec<Scalar> = Vec::with_capacity(9);
    //     for i in 0..9{
    //         x_psi.push(exp_x[perm_vec[i]])
    //     }
    //     println!("{:?}",exp_x);
    //     println!("{:?}",perm_vec);
    //     println!("{:?}",x_psi);
    //     //assert_eq!(exp_2[0], Scalar::from(1u64));
    // }
    // #[test]
    // fn hadamard_product_test() {
    //     let tau: Vec<_> = (0..9).map(|_| Scalar::random(&mut OsRng)).collect();
    //     let tau_2d = Array2D::from_row_major(&tau, 3, 3);
    //     let perm = Permutation::new(&mut OsRng, N);
    //     //let (t, b, bd) = hadamard_product_proof_prover(tau_2d, perm);
    //     //let b_dash_tau : Vec<RistrettoPoint> = bd.iter().zip(t.iter()).map(|(b, t)| b+t).collect();
    //    // assert_eq!(b_dash_tau, b);

    //    // println!("{:?}",x);
    //    // println!("{:?}",exp_2);
    //     //assert_eq!(exp_2[0], Scalar::from(1u64));
    // }
}
