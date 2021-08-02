
use curve25519_dalek::{
    ristretto::CompressedRistretto,
    constants::RISTRETTO_BASEPOINT_TABLE,
    scalar::Scalar
};
use crate::{
    ristretto::RistrettoPublicKey,
    elgamal::{
        signed_integer::SignedInteger
    }
};



#[derive(Debug, Copy, Clone)]
pub struct ElGamalCommitment {
    pub(crate) c: CompressedRistretto,
    pub(crate) d: CompressedRistretto,
}

impl ElGamalCommitment {
    // Private constructor
    fn set_commitment(c: CompressedRistretto, d: CompressedRistretto) -> ElGamalCommitment {
        ElGamalCommitment {
            c: c,
            d: d,
        }
    }

    // generate_commitment creates commitment over balance
    // c = k*g (where k is a random scalar)
    // d = vG + kh (where v is balance, G is base point, k is random scalar and h is grsk generated in pk)
	pub fn generate_commitment(p: &RistrettoPublicKey, rscalar: Scalar, bl: i64) -> ElGamalCommitment  {

		// lets make c
		let c = &rscalar * &p.gr.decompress().unwrap();

        let signed_int = SignedInteger::from(bl as u64);
        let bl_scalar : Scalar = SignedInteger::into(signed_int);

        // lets multiply balance scalar with the basepoint scalar
        let gv = &bl_scalar * &RISTRETTO_BASEPOINT_TABLE;

        let kh = &rscalar * &p.grsk.decompress().unwrap();

        // lets make d
        let d = &gv + &kh;

        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

    // add_commitments adds two commitments and return a commitment
    pub fn add_commitments(a: &ElGamalCommitment, b: &ElGamalCommitment) -> ElGamalCommitment  {

        //Add c of first commitment with the c of second commitment
        let c = &a.c.decompress().unwrap() + &b.c.decompress().unwrap();
        
        //Add d of first commitment with the d of second commitment
        let d = &a.d.decompress().unwrap() + &b.d.decompress().unwrap();

        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

}

// ------- ElGamalCommitment Partial Eq, Eq ------- //

impl PartialEq for ElGamalCommitment{
    fn eq(&self, other: &Self) -> bool {
        self.c == other.c && self.d == other.d
    }
}

impl Eq for ElGamalCommitment {}