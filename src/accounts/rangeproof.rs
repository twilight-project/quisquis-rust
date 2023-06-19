use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use core::borrow::BorrowMut;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// Range Proof gadget
/// RangeProof struct to hold the R1CS range proof

pub struct RangeProofProver<'g, T: BorrowMut<Transcript>> {
    /// Common R1CS Prover for multiple rangeproofs
    pub(crate) prover: bulletproofs::r1cs::Prover<'g, T>,
}

impl<'g, T: BorrowMut<Transcript>> RangeProofProver<'g, T> {
    // R1CS constraint system building
    pub fn range_proof_prover(
        &mut self,
        val: u64,
        epsilon_blinding: Scalar,
    ) -> Result<CompressedRistretto, R1CSError> {
        // Commit to the val as variable
        let (com, var) = self.prover.commit(val.into(), epsilon_blinding);
        //Update range proof R1CS constraint system
        range_proof(&mut self.prover, var.into(), Some(val), 64 as usize)?;
        Ok(com)
    }
    pub fn build_proof(self) -> Result<R1CSProof, R1CSError> {
        let bp_gens = BulletproofGens::new(512, 1);
        self.prover.prove(&bp_gens)
    }

    // pub fn hadamard_product_prover(&mut self, val: u64, epsilon_blinding: Scalar) -> Result<CompressedRistretto, R1CSError>{

    // }
}

pub struct RangeProofVerifier<T: BorrowMut<Transcript>> {
    /// Common R1CS Verifier for multiple rangeproofs
    pub(crate) verifier: bulletproofs::r1cs::Verifier<T>,
}

impl<T: BorrowMut<Transcript>> RangeProofVerifier<T> {
    // R1CS constraint system building
    pub fn range_proof_verifier(&mut self, com: CompressedRistretto) -> Result<(), R1CSError> {
        // Commit to the val as variable
        let var = self.verifier.commit(com);
        //Update range proof R1CS constraint system
        range_proof(&mut self.verifier, var.into(), None, 64 as usize)
    }
    pub fn verify_proof(self, proof: &R1CSProof, pc_gens: &PedersenGens) -> Result<(), R1CSError> {
        let bp_gens = BulletproofGens::new(512, 1);
        self.verifier.verify(proof, pc_gens, &bp_gens)
    }
}
/// Enforces that the quantity of v is in the range [0, 2^n).
pub fn range_proof<CS: ConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_assignment: Option<u64>,
    n: usize,
) -> Result<(), R1CSError> {
    let mut exp_2 = Scalar::one();
    for i in 0..n {
        // Create low-level variables and add them to constraints
        let (a, b, o) = cs.allocate_multiplier(v_assignment.map(|q| {
            let bit: u64 = (q >> i) & 1;
            ((1 - bit).into(), bit.into())
        }))?;

        // Enforce a * b = 0, so one of (a,b) is zero
        cs.constrain(o.into());

        // Enforce that a = 1 - b, so they both are 1 or 0.
        cs.constrain(a + (b - 1u64));

        // Add `-b_i*2^i` to the linear combination
        // in order to form the following constraint by the end of the loop:
        // v = Sum(b_i * 2^i, i = 0..n-1)
        v = v - b * exp_2;

        exp_2 = exp_2 + exp_2;
    }

    // Enforce that v = Sum(b_i * 2^i, i = 0..n-1)
    cs.constrain(v);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use bulletproofs::r1cs::{Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
    use merlin::Transcript;
    use rand::rngs::OsRng;
    #[test]
    fn range_proof_test() {
        //assuing the bitrange is always 64
        // Common
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let v_val = 156774839u64;
        let b_val = 3564435674839u64;
        let c_val = 674839u64;
        let d_val = 67442545356456839u64;
        // Prover's scope
        // Prover makes a `ConstraintSystem` instance representing a range proof gadget
        let mut prover_transcript = Transcript::new(b"RangeProofTest");
        let mut rng = rand::thread_rng();
        //let v_val = 156774839u64;
        let prover = Prover::new(&pc_gens, &mut prover_transcript);
        let mut range_prover = RangeProofProver { prover: prover };

        let com_1 = range_prover
            .range_proof_prover(v_val, Scalar::random(&mut rng))
            .unwrap();
        let com_2 = range_prover
            .range_proof_prover(b_val, Scalar::random(&mut rng))
            .unwrap();
        let com_3 = range_prover
            .range_proof_prover(c_val, Scalar::random(&mut rng))
            .unwrap();
        let com_4 = range_prover
            .range_proof_prover(d_val, Scalar::random(&mut rng))
            .unwrap();

        // let (com, var) = range_prover
        //   .prover
        // .commit(v_val.into(), Scalar::random(&mut rng));
        // assert!(range_proof(&mut range_prover.prover, var.into(), Some(v_val), 64).is_ok());

        let proof = range_prover.build_proof().unwrap();
        let length = proof.serialized_size();
        println!("Size : {:?}", length);

        // Verifier makes a `ConstraintSystem` instance representing a merge gadget
        let mut verifier_transcript = Transcript::new(b"RangeProofTest");
        let verifier = Verifier::new(&mut verifier_transcript);
        let mut range_verifier = RangeProofVerifier { verifier: verifier };
        assert!(range_verifier.range_proof_verifier(com_1).is_ok());
        assert!(range_verifier.range_proof_verifier(com_2).is_ok());
        assert!(range_verifier.range_proof_verifier(com_3).is_ok());
        assert!(range_verifier.range_proof_verifier(com_4).is_ok());
        // let var = range_verifier.verifier.commit(commitment);
        let check = range_verifier.verify_proof(&proof, &pc_gens).is_ok();
        // Verifier adds constraints to the constraint system
        // assert!(range_proof(&mut range_verifier.verifier, var.into(), None, 64).is_ok());

        // Verifier verifies proof
        //let result = range_verifier
        //  .verifier
        //.verify(&proof, &pc_gens, &bp_gens)
        // .is_ok();
        assert!(check);

        //create range proof directly
        let mut prover_transcript_direct = Transcript::new(b"doctest example");

        // Create a 32-bit rangeproof.
        let (proof_direct, committed_value) = RangeProof::prove_single(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript_direct,
            v_val,
            &Scalar::random(&mut OsRng),
            64,
        )
        .expect("A real program could handle errors");
        //let length_direct = proof_direct.to_bytes().len();
        //println!("Size_direct : {:?}", length_direct);
        // Verification requires a transcript with identical initial state:
        let mut verifier_transcript_direct = Transcript::new(b"doctest example");
        assert!(proof_direct
            .verify_single(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript_direct,
                &committed_value,
                64
            )
            .is_ok());
    }
    #[test]
    fn aggregate_range_proof_test() {
        // Generators for Pedersen commitments.  These can be selected
        // independently of the Bulletproofs generators.
        let pc_gens = PedersenGens::default();

        // Generators for Bulletproofs, valid for proofs up to bitsize 64
        // and aggregation size up to 16.
        let bp_gens = BulletproofGens::new(64, 16);

        // Four secret values we want to prove lie in the range [0, 2^64)
        let secrets = [
            156774839u64,
            3564435674839u64,
            674839u64,
            67442545356456839u64,
        ];

        // The API takes blinding factors for the commitments.
        let blindings: Vec<_> = (0..4).map(|_| Scalar::random(&mut OsRng)).collect();

        // The proof can be chained to an existing transcript.
        // Here we create a transcript with a doctest domain separator.
        let mut prover_transcript = Transcript::new(b"doctest example");

        // Create an aggregated 32-bit rangeproof and corresponding commitments.
        let (proof, commitments) = RangeProof::prove_multiple(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            &secrets,
            &blindings,
            64,
        )
        .expect("A real program could handle errors");
        let length_direct = proof.to_bytes().len();
        println!("Size_direct : {:?}", length_direct);
        // Verification requires a transcript with identical initial state:
        let mut verifier_transcript = Transcript::new(b"doctest example");
        assert!(proof
            .verify_multiple(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &commitments,
                64
            )
            .is_ok());
    }
}
