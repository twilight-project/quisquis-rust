//! ElGamal commitment implementation for the Quisquis protocol.
//!
//! Provides the [`ElGamalCommitment`] type and associated operations for
//! homomorphic commitments using the Ristretto group.

use crate::ristretto::{RistrettoPublicKey, RistrettoSecretKey};
use core::ops::{Mul, Sub};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE, ristretto::CompressedRistretto,
    ristretto::RistrettoPoint, scalar::Scalar,
};
use serde::{Deserialize, Serialize};
use std::convert::TryInto;

/// Represents an ElGamal commitment in the Ristretto group.
///
/// An ElGamal commitment consists of two compressed Ristretto points, `c` and `d`.
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct ElGamalCommitment {
    pub(crate) c: CompressedRistretto,
    pub(crate) d: CompressedRistretto,
}

impl ElGamalCommitment {
    /// Private constructor for an ElGamal commitment from two compressed points.
    fn set_commitment(c: CompressedRistretto, d: CompressedRistretto) -> ElGamalCommitment {
        ElGamalCommitment { c, d }
    }

    /// Generates an ElGamal commitment over a value.
    ///
    /// # Arguments
    ///
    /// * `p` - The recipient's public key.
    /// * `rscalar` - A random scalar (blinding factor).
    /// * `bl_scalar` - The value to commit to, as a scalar.
    ///
    /// # Returns
    ///
    /// An `ElGamalCommitment` to the value.
    pub fn generate_commitment(
        p: &RistrettoPublicKey,
        rscalar: Scalar,
        bl_scalar: Scalar,
    ) -> ElGamalCommitment {
        // c = k * g
        let c = &rscalar * &p.gr.decompress().unwrap();
        // d = vG + kh
        let gv = &bl_scalar * &RISTRETTO_BASEPOINT_TABLE;
        let kh = &rscalar * &p.grsk.decompress().unwrap();
        let d = &gv + &kh;
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

    /// Adds two ElGamal commitments homomorphically.
    ///
    /// # Arguments
    ///
    /// * `a` - The first commitment.
    /// * `b` - The second commitment.
    ///
    /// # Returns
    ///
    /// The sum of the two commitments.
    pub fn add_commitments(a: &ElGamalCommitment, b: &ElGamalCommitment) -> ElGamalCommitment {
        let c = &a.c.decompress().unwrap() + &b.c.decompress().unwrap();
        let d = &a.d.decompress().unwrap() + &b.d.decompress().unwrap();
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }

    /// Verifies the commitment of a value for a specific secret key.
    ///
    /// # Arguments
    ///
    /// * `pr` - The secret key.
    /// * `bl_scalar` - The value to verify, as a scalar.
    ///
    /// # Errors
    ///
    /// Returns an error if the commitment is invalid.
    pub fn verify_commitment(
        &self,
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

    /// Decrypts the commitment to obtain the point `G*v`.
    ///
    /// # Arguments
    ///
    /// * `pr` - The secret key.
    ///
    /// # Returns
    ///
    /// The compressed Ristretto point corresponding to `G*v`.
    pub fn decommit(&self, pr: &RistrettoSecretKey) -> CompressedRistretto {
        (&self.d.decompress().unwrap() - &(&pr.0 * &self.c.decompress().unwrap())).compress()
    }

    /// Attempts to decrypt the commitment to recover the committed scalar value.
    ///
    /// # Arguments
    ///
    /// * `pr` - The secret key.
    ///
    /// # Returns
    ///
    /// The committed scalar value, if found (brute-force search).
    pub fn decommit_value(&self, pr: &RistrettoSecretKey) -> Option<Scalar> {
        let point: CompressedRistretto = self.decommit(pr);
        brute_force_decrypt(point.decompress().unwrap())
    }

    /// Returns the `c` component of the commitment.
    pub fn c(&self) -> CompressedRistretto {
        self.c
    }

    /// Returns the `d` component of the commitment.
    pub fn d(&self) -> CompressedRistretto {
        self.d
    }

    /// Serializes the commitment into a 64-byte array.
    pub fn to_bytes(&self) -> [u8; 64] {
        let mut buf = Vec::with_capacity(64);
        buf.extend_from_slice(self.c.as_bytes());
        buf.extend_from_slice(self.d.as_bytes());
        buf.try_into().unwrap_or_else(|v: Vec<u8>| {
            panic!("Expected a Vec of length {} but it was {}", 64, v.len())
        })
    }

    /// Deserializes the commitment from a 64-byte array.
    ///
    /// # Errors
    ///
    /// Returns an error if the input is not 64 bytes or the points are invalid.
    pub fn from_bytes(data: &[u8]) -> Result<Self, &'static str> {
        if data.len() != 64 {
            return Err("Invalid Encryption Length");
        }
        let c: CompressedRistretto = slice_to_point(&data[0..32])?;
        let d: CompressedRistretto = slice_to_point(&data[32..64])?;
        Ok(ElGamalCommitment { c, d })
    }
}

/// Attempts to brute-force decrypt the encrypted key by searching for a scalar `bl`
/// such that `G * bl == encrypted_key`.
///
/// # Arguments
///
/// * `encrypted_key` - The Ristretto point to decrypt.
///
/// # Returns
///
/// The scalar value if found, or `None` if not found.
fn brute_force_decrypt(encrypted_key: RistrettoPoint) -> Option<Scalar> {
    let basepoint = RISTRETTO_BASEPOINT_TABLE;
    let u64_max = u64::MAX;
    let mut scalar: Scalar;
    for val in 0..u64_max {
        scalar = Scalar::from(val);
        let decrypted_point = &basepoint * &scalar;

        if decrypted_point == encrypted_key {
            return Some(scalar);
        }
    }
    None
}

// ------- ElGamalCommitment Partial Eq, Eq, Sub, Mul ------- //

impl PartialEq for ElGamalCommitment {
    /// Checks if two ElGamal commitments are equal.
    ///
    /// # Arguments
    ///
    /// * `other` - The other ElGamal commitment to compare with.
    ///
    /// # Returns
    ///
    /// `true` if the commitments are equal, `false` otherwise.
    fn eq(&self, other: &Self) -> bool {
        self.c == other.c && self.d == other.d
    }
}

impl Sub<ElGamalCommitment> for ElGamalCommitment {
    type Output = ElGamalCommitment;

    /// Subtracts one ElGamal commitment from another.
    ///
    /// # Arguments
    ///
    /// * `other` - The ElGamal commitment to subtract.
    ///
    /// # Returns
    ///
    /// The difference between the two commitments.
    fn sub(self, other: ElGamalCommitment) -> ElGamalCommitment {
        let c = &self.c.decompress().unwrap() - &other.c.decompress().unwrap();
        let d = &self.d.decompress().unwrap() - &other.d.decompress().unwrap();
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a ElGamalCommitment {
    type Output = ElGamalCommitment;
    /// Multiplies the ElGamal commitment by a scalar.
    ///
    /// # Arguments
    ///
    /// * `scalar` - The scalar to multiply by.
    ///
    /// # Returns
    ///
    /// The resulting ElGamal commitment.
    fn mul(self, scalar: &'b Scalar) -> ElGamalCommitment {
        let c = scalar * &self.c.decompress().unwrap();
        let d = scalar * &self.d.decompress().unwrap();
        ElGamalCommitment::set_commitment(c.compress(), d.compress())
    }
}

/// Deserializes a compressed Ristretto point from a 32-byte slice.
///
/// # Errors
///
/// Returns an error if the input is not 32 bytes or the point is invalid.
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
    #[test]
    fn verify_decommit_value() {
        use rand::rngs::OsRng;
        let sk: RistrettoSecretKey = SecretKey::random(&mut OsRng);
        let pk = RistrettoPublicKey::from_secret_key(&sk, &mut OsRng);
        let comm_scalar = Scalar::random(&mut OsRng);
        let comm =
            ElGamalCommitment::generate_commitment(&pk, comm_scalar, Scalar::from(160000 as u64));
        let decrypted_scalar = comm.decommit_value(&sk).unwrap();
        assert_eq!(decrypted_scalar, Scalar::from(160000 as u64));
    }
}
