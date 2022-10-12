use crate::ristretto::{RistrettoPublicKey, RistrettoSecretKey};
use core::ops::{Mul, Sub};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE, ristretto::CompressedRistretto, scalar::Scalar,
};

#[derive(Debug, Copy, Clone)]
pub struct ElGamalCommitment {
    pub(crate) c: CompressedRistretto,
    pub(crate) d: CompressedRistretto,
}

impl ElGamalCommitment {
    // Private constructor
    fn set_commitment(c: CompressedRistretto, d: CompressedRistretto) -> ElGamalCommitment {
        ElGamalCommitment { c: c, d: d }
    }

    // generate_commitment creates commitment over balance
    // c = k*g (where k is a random scalar)
    // d = vG + kh (where v is balance, G is base point, k is random scalar and h is grsk generated in pk)
    pub fn generate_commitment(
        p: &RistrettoPublicKey,
        rscalar: Scalar,
        bl_scalar: Scalar,
    ) -> ElGamalCommitment {
        // lets make c
        let c = &rscalar * &p.gr.decompress().unwrap();

        //let signed_int = SignedInteger::from(bl as u64);
        //let bl_scalar: Scalar = SignedInteger::into(signed_int);

        // lets multiply balance scalar with the basepoint scalar
        let gv = &bl_scalar * &RISTRETTO_BASEPOINT_TABLE;
        let kh = &rscalar * &p.grsk.decompress().unwrap();

        // lets make d
        let d = &gv + &kh;

        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

    // add_commitments adds two commitments and return a commitment
    pub fn add_commitments(a: &ElGamalCommitment, b: &ElGamalCommitment) -> ElGamalCommitment {
        //Add c of first commitment with the c of second commitment
        let c = &a.c.decompress().unwrap() + &b.c.decompress().unwrap();
        //Add d of first commitment with the d of second commitment
        let d = &a.d.decompress().unwrap() + &b.d.decompress().unwrap();

        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

    /// verifies the commitment of balance for specific SecretKey
    pub fn verify_commitment(
        self: &Self,
        pr: &RistrettoSecretKey,
        bl_scalar: Scalar,
    ) -> Result<(), &'static str> {
        if self.d
            == (&(&bl_scalar * &RISTRETTO_BASEPOINT_TABLE)
                + &(&pr.0 * &self.c.decompress().ok_or("Error::Decompression Failed")?))
                .compress()
        {
            Ok(())
        } else {
            Err("Invalid Account::Commitment Verification Failed")
        }
    }

    /// Decrypts commitment in the form G*v
    pub fn decommit(self: &Self, pr: &RistrettoSecretKey) -> CompressedRistretto {
        (&self.d.decompress().unwrap() - &(&pr.0 * &self.c.decompress().unwrap())).compress()
    }
}

// ------- ElGamalCommitment Partial Eq, Eq, Sub, Mul ------- //

impl PartialEq for ElGamalCommitment {
    fn eq(&self, other: &Self) -> bool {
        self.c == other.c && self.d == other.d
    }
}

impl Sub<ElGamalCommitment> for ElGamalCommitment {
    type Output = ElGamalCommitment;

    fn sub(self, other: ElGamalCommitment) -> ElGamalCommitment {
        let c = &self.c.decompress().unwrap() - &other.c.decompress().unwrap();
        let d = &self.d.decompress().unwrap() - &other.d.decompress().unwrap();
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a ElGamalCommitment {
    type Output = ElGamalCommitment;
    /// Scalar multiplication: compute `scalar * self`.
    fn mul(self, scalar: &'b Scalar) -> ElGamalCommitment {
        let c = scalar * &self.c.decompress().unwrap();
        let d = scalar * &self.d.decompress().unwrap();
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use crate::keys::{PublicKey, SecretKey};
    #[test]
    fn verify_commitment_test() {
        use rand::rngs::OsRng;
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        let comm_scalar = Scalar::random(&mut OsRng);
        let comm =
            ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::from(16 as u64));
        assert!(
            comm.verify_commitment(&sk, Scalar::from(16 as u64)).is_ok(),
            "Invalid Commitment"
        );
    }
}
