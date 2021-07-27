use rand::{CryptoRng, Rng};
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_TABLE,
    ristretto::CompressedRistretto,
    scalar::Scalar
};

use crate::{
    ristretto::constants::BASE_PK_BTC_COMPRESSED,
    keys::{SecretKey, PublicKey}
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

    // update_public_key multiplies pk with a random scalar r
    // returns UpdatedPublicKey and random scalar used
    fn update_public_key(p: &RistrettoPublicKey, rscalar: Scalar) -> RistrettoPublicKey {
        let grr = &rscalar * &p.gr.decompress().unwrap();
        let grrsk = &rscalar * &p.grsk.decompress().unwrap();
        RistrettoPublicKey::new_from_pk(grr.compress(), grrsk.compress())
    }

    // verify_public_key_update verifies if keypair is generated correctly g^r * sk = g^r^sk = h
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

    // generate_base_ppk returns a base pk of ristretto
    // it is a temp fix and is using constants.rs to retrieve fixed asset representation
    // however, it is assumed logic of multi-asset base pks can be extended here later
    fn generate_base_pk() -> RistrettoPublicKey{
        RistrettoPublicKey::new_from_pk(BASE_PK_BTC_COMPRESSED[0], BASE_PK_BTC_COMPRESSED[1])
    }
}


