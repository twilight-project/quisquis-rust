use crate::ristretto::{RistrettoPublicKey, RistrettoSecretKey};
use core::ops::{Mul, Sub};
use std::convert::TryInto;
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
    
    /// Get c of the commitment
    /// 
    pub fn c(self: &Self) -> CompressedRistretto {
        self.c
    }

    /// Get d of the commitment
    /// 
    pub fn d(self: &Self) -> CompressedRistretto {
        self.d
    }

    /// Serializes the Commitment into a byte array of 64-byte elements.
    pub fn to_bytes(&self) -> [u8;64] {
        let mut buf = Vec::with_capacity(64);
        buf.extend_from_slice(self.c.as_bytes());
        buf.extend_from_slice(self.d.as_bytes());
        buf.try_into().unwrap_or_else(|v: Vec<u8>| panic!("Expected a Vec of length {} but it was {}", 64, v.len()))
    }

    /// Deserializes the Commitment from a byte array of 64-byte elements.
    pub fn from_bytes(data: &[u8]) -> Result<Self, &'static str> {
        if data.len() != 64 {
            return Err("Invalid Encryption Length");
        }
        let c: CompressedRistretto = slice_to_point(&data[0..32])?;
        let d: CompressedRistretto = slice_to_point(&data[32..64])?;
        Ok(ElGamalCommitment{
            c , d
        })
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

// Deserialize a compressed ristretto point from a slice. The input slice is 32 bytes
/// Utility Function
fn slice_to_point(data: &[u8]) -> Result<CompressedRistretto, &'static str> {
    if data.len() != 32 {
        return Err("Invalid Length");
    }
    let pt = CompressedRistretto::from_slice(&data);
    match pt.decompress() {
        Some(_) => (),
        None => {
            return Err("InvalidPoint");
        }
    };
    Ok(pt)
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

    #[test]
    fn verify_bytes_test() {
        use rand::rngs::OsRng;
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        let comm_scalar = Scalar::random(&mut OsRng);
        let comm =
            ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::from(16 as u64));
        
        let comit_bytes = comm.to_bytes();
        println!("Bytes {:?}", comit_bytes);
        let comit = ElGamalCommitment::from_bytes(&comit_bytes).unwrap();
        assert_eq!(comm, comit);
    }
}
