
use curve25519_dalek::{
    ristretto::CompressedRistretto,
    scalar::Scalar
};
use crate::ristretto::RistrettoPublicKey;



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

	pub fn generate_commitment(p: &RistrettoPublicKey, rscalar: Scalar, bl: u64)  {

        println!("hello");
        

		// lets make c
		// let c = &rscalar * &p.gr.decompress().unwrap();
        // let grrsk = &rscalar * &p.grsk.decompress().unwrap();
        // RistrettoPublicKey::new_from_pk(grr.compress(), grrsk.compress())
    }
}