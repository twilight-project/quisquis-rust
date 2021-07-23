use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};

// This is a temporary solution for declaring assets. It should be moved to a governance module
// byte codes of static points on the curve are hard-coded as here - these were imported from rust - pedersengens function of bulletproofs
pub const BASE_PAIR_BTC_COMPRESSED : [CompressedRistretto; 2] = [
    CompressedRistretto([
        226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227, 11, 106, 165, 130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118
    ]),
    CompressedRistretto([
        140, 146, 64, 180, 86, 169, 230, 220, 101, 195, 119, 161, 4, 141, 116, 95, 148, 160, 140, 219, 127, 68, 203, 205, 123, 70, 243, 64, 72, 135, 17, 52
    ])
];