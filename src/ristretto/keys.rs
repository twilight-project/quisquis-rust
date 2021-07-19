use crate::keys::{SecretKey, PublicKey};
use rand::{CryptoRng, Rng};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE,
    ristretto::CompressedRistretto,
    scalar::Scalar
};

const SCALAR_LENGTH: usize = 32;
const PUBLIC_KEY_LENGTH: usize = 32;

// ------- SecretKey ------- //

#[derive(Debug)]
pub struct RistrettoSecretKey(pub(crate) Scalar);

impl SecretKey for RistrettoSecretKey {

    fn key_length() -> usize {
        SCALAR_LENGTH
    }

    fn random<R: Rng + CryptoRng>(rng: &mut R) -> Self {
        RistrettoSecretKey(Scalar::random(rng))
    }
}

// ------- PublicKey ------- //
#[derive(Debug)]
pub struct RistrettoPublicKey {
    pub(crate) gr: CompressedRistretto,
    pub(crate) grsk: CompressedRistretto,
}

impl RistrettoPublicKey {
    // Private constructor
    fn new_from_pk(gr: CompressedRistretto, grsk: CompressedRistretto) -> RistrettoPublicKey {
        RistrettoPublicKey {
            gr: gr,
            grsk: grsk,
        }
    }
}

impl PublicKey for RistrettoPublicKey {
    type K = RistrettoSecretKey;

    /// Generates a new Public key from the given secret key
    fn from_secret_key<R: Rng + CryptoRng>(k: &Self::K, rng: &mut R) -> RistrettoPublicKey {
        // Lets generate a new random scalar because in quisquis we need basepoint * randomScalar 
        // and then we multiply it with sk 
        let random_scalar = Scalar::random(rng);
        let gr = &random_scalar * &RISTRETTO_BASEPOINT_TABLE;
        let grsk = &k.0 * &gr;
        RistrettoPublicKey::new_from_pk(gr.compress(), grsk.compress())
    }

    fn key_length() -> usize {
        PUBLIC_KEY_LENGTH
    }

    // UpdateKeys multiplies pk with a random scalar r
    // returns UpdatedPublicKey and random scalar used
    fn update_public_key(p: &RistrettoPublicKey, rscalar: Scalar) -> RistrettoPublicKey {
        let grr = &rscalar * &p.gr.decompress().unwrap();
        let grrsk = &rscalar * &p.grsk.decompress().unwrap();
        RistrettoPublicKey::new_from_pk(grr.compress(), grrsk.compress())
    }

    // VerifyKeysUpdate verifies if keypair is generated correctly g^r * sk = g^r^sk = h
    // returns boolean
    fn verify_public_key_update(u: &RistrettoPublicKey, p: &RistrettoPublicKey, rscalar: Scalar) -> bool {

        let grr = &rscalar * &p.gr.decompress().unwrap();
        let grrsk = &rscalar * &p.grsk.decompress().unwrap();
        if grr == u.gr.decompress().unwrap() && grrsk == u.grsk.decompress().unwrap(){
            return true
        }else{
            return false
        }
    }
}

