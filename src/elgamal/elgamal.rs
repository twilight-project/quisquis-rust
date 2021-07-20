
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



#[derive(Debug)]
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

	pub fn generate_commitment(p: &RistrettoPublicKey, rscalar: Scalar, bl: i64) -> ElGamalCommitment  {

		// lets make c
		let c = &rscalar * &p.gr.decompress().unwrap();

        let signed_int = SignedInteger::from(bl as u64);
        let bl_scalar : Scalar = SignedInteger::into(signed_int);

        //lets multiply balance scalar with the basepoint scalar
        let gv = &bl_scalar * &RISTRETTO_BASEPOINT_TABLE;

        let kh = &rscalar * &p.grsk.decompress().unwrap();

        // lets make d
        let d = &gv + & kh;

        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }
}