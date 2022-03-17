//! The `ddh` module contains API for producing a
//! DDH proof and its verification.

#![allow(non_snake_case)]

use crate::accounts::{Prover, Verifier};
use curve25519_dalek::traits::MultiscalarMul;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use rand::rngs::OsRng;
///DDH Statement
///
#[derive(Debug, Clone)]
pub struct DDHStatement {
    // G' = G ^ rho, H' = H ^ rho
    pub G_dash: CompressedRistretto,
    pub H_dash: CompressedRistretto,
}
///DDH Proof
///
#[derive(Debug, Clone)]
pub struct DDHProof {
    challenge: Scalar,
    z: Scalar,
}
impl DDHProof {
    /// create sigma protocol based ddh proof over (G, H , G', H') tuple
    /// proof that (G',H')  = (G^rho , H^rho)
    /// (G,H) ← prod of all i->N  pk_i ^ x_i
    pub fn create_verify_update_ddh_prove(
        prover: &mut Prover,
        g_i: &[RistrettoPoint],
        h_i: &[RistrettoPoint],
        exp_x: &[Scalar],
        G: RistrettoPoint,
        H: RistrettoPoint,
        rho: Scalar,
    ) -> (DDHProof, DDHStatement) {
        //Create new transcript
        prover.new_domain_sep(b"DDHTupleProof");

        // x^i * rho
        let exp_x_rho: Vec<_> = exp_x.iter().map(|x| x * rho).collect();
        // (G', H') = prod of all i->N  pk_i ^ (x_i . rho)
        let G_dash = RistrettoPoint::multiscalar_mul(exp_x_rho.iter(), g_i.iter()).compress();
        let H_dash = RistrettoPoint::multiscalar_mul(exp_x_rho.iter(), h_i.iter()).compress();

        // Generate a single blinding factor
        let r_scalar = Scalar::random(&mut OsRng);
        // first messasge
        let g_r = (G * r_scalar).compress();
        let h_r = (H * r_scalar).compress();

        //allocates points to Transcript
        prover.allocate_point(b"g", G.compress());
        prover.allocate_point(b"g_dash", G_dash);
        prover.allocate_point(b"h", H.compress());
        prover.allocate_point(b"h_dash", H_dash);
        prover.allocate_point(b"gr", g_r);
        prover.allocate_point(b"hr", h_r);

        // obtain a scalar challenge
        let challenge = prover.get_challenge(b"Challenge");

        //compact proof
        let x_rho = challenge * rho;
        let z = r_scalar - x_rho;
        (
            DDHProof {
                challenge: challenge,
                z: z,
            },
            DDHStatement {
                G_dash: G_dash,
                H_dash: H_dash,
            },
        )
    }
    /// Verify the ddh proof over (G, H , G', H') tuple
    pub fn verify_ddh_proof(
        &self,
        verifier: &mut Verifier,
        statement: &DDHStatement,
        G: CompressedRistretto,
        H: CompressedRistretto,
    ) -> Result<(), &'static str> {
        // Initiate the verification transcript
        verifier.new_domain_sep(b"DDHTupleProof");
        //allocates statement points to Transcript
        verifier.allocate_point(b"g", G);
        verifier.allocate_point(b"g_dash", statement.G_dash);
        verifier.allocate_point(b"h", H);
        verifier.allocate_point(b"h_dash", statement.H_dash);
        //lets recreate g_r & h_r from x and z
        let combined_scalars = vec![self.z, self.challenge];
        let g_point = vec![G, statement.G_dash];
        let g_r = Verifier::multiscalar_multiplication(&combined_scalars, &g_point)
            .ok_or("DDH Proof Verify: Failed")?;
        let h_point = vec![H, statement.H_dash];
        let h_r = Verifier::multiscalar_multiplication(&combined_scalars, &h_point)
            .ok_or("DDH Proof Verify: Failed")?;
        //add g_r and h_r to transcript
        verifier.allocate_point(b"gr", g_r.compress());
        verifier.allocate_point(b"hr", h_r.compress());
        // obtain a scalar challenge
        let c = verifier.get_challenge(b"Challenge");
        //verify the ddh prove
        if self.challenge == c {
            Ok(())
        } else {
            Err("DDH Proof Verify: Failed")
        }
    }
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
        shuffle::vectorutil,
    };
    use merlin::Transcript;
    use rand::rngs::OsRng;

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
        //create Prover and verifier
        let mut transcript_p = Transcript::new(b"ShuffleProof");
        let mut prover = Prover::new(b"DDHTuple", &mut transcript_p);
        // create x^i
        let exp_x: Vec<_> = vectorutil::exp_iter(x).skip(1).take(9).collect();
        // gather g, h from Public key
        let g_i: Vec<_> = pk.iter().map(|pt| pt.gr.decompress().unwrap()).collect();
        let h_i: Vec<_> = pk.iter().map(|pt| pt.grsk.decompress().unwrap()).collect();
        // (G, H) = sum of all i (pk_i * x^i)
        let G = RistrettoPoint::multiscalar_mul(exp_x.iter(), g_i.iter());
        let H = RistrettoPoint::multiscalar_mul(exp_x.iter(), h_i.iter());
        let (proof, statement) =
            DDHProof::create_verify_update_ddh_prove(&mut prover, &g_i, &h_i, &exp_x, G, H, rho);

        let mut transcript_v = Transcript::new(b"ShuffleProof");
        let mut verifier = Verifier::new(b"DDHTuple", &mut transcript_v);

        let verify = proof.verify_ddh_proof(&mut verifier, &statement, G.compress(), H.compress());
        assert!(verify.is_ok());
    }
}
