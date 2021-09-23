use bulletproofs::r1cs::*;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::ristretto::CompressedRistretto;
use merlin::Transcript;

// Range Proof gadget
/// RangeProof struct to hold the R1CS range proof 
pub struct RangeProofProver<'g> {
    /// Common R1CS Prover for multiple rangeproofs
    pub prover: bulletproofs::r1cs::Prover<'g, Transcript>,
}

impl<'g> RangeProofProver<'g> {
    // Private constructor
  /*pub fn new(cs: Prover) -> RangeProofProver<'g> {
        
        RangeProofProver {
            proof: proof,
            com: com,
        }
    }*/
    pub fn range_proof_prover(self, val: u64, epsilon_blinding: Scalar, n: usize) -> Result<CompressedRistretto, R1CSError> {
    
        // Commit to the val as variable 
        let (com, var) = self.prover.commit(val.into(), epsilon_blinding);
        //Update range proof R1CS constraint system       
        RangeProofProver::range_proof(& mut self.prover, var.into(), Some(val), n)?;
        Ok(com)
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
}
