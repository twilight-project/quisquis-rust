use core::ops::Neg;
use curve25519_dalek::scalar::Scalar;
/// Represents a signed integer with absolute value in the 64-bit range.
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd)]
pub struct SignedInteger(i64);

impl SignedInteger {
    /// Returns Some(x) if self is non-negative
    /// Otherwise returns None.
    pub fn to_u64(&self) -> Option<u64> {
        if self.0 < 0 {
            None
        } else {
            Some(self.0 as u64)
        }
    }

    /// Converts the integer to Scalar.
    pub fn to_scalar(self) -> Scalar {
        self.into()
    }
}

impl From<u64> for SignedInteger {
    fn from(u: u64) -> SignedInteger {
        SignedInteger(u as i64)
    }
}

impl Into<Scalar> for SignedInteger {
    fn into(self) -> Scalar {
        if self.0 < 0 {
            Scalar::zero() - Scalar::from((-self.0) as u64)
        } else {
            Scalar::from(self.0 as u64)
        }
    }
}

impl Neg for SignedInteger {
    type Output = SignedInteger;

    fn neg(self) -> SignedInteger {
        SignedInteger(-self.0)
    }
}
