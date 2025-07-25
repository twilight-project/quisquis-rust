//! Schnorr signature implementation used for transaction authentication.
//!
//! The signing key is a scalar while the verification key is a pair of
//! compressed Ristretto points derived from the secret scalar.  Signatures
//! are generated and verified over Merlin transcripts.
//! 
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use std::fmt;

use merlin::Transcript;
use crate::accounts::TranscriptProtocol;


//Genarating Signing Key(Private key) and VerificationKey(Public key) for dual point elgamal encryption

/// Signing key (aka "privkey") is a type alias for the scalar in Ristretto255 group.
pub type SigningKey = Scalar;

/// Verification key (aka "pubkey") is a wrapper type around two Ristretto points
/// that lets the verifier to check the signature.
#[derive(Copy, Clone, PartialEq, Eq, Default, Debug)]//, Serialize, Deserialize)]
//#[serde(from = "CompressedRistretto", into = "CompressedRistretto")]
pub struct VerificationKey {
    /// Randomized generator `G * r`.
    pub(crate) g: CompressedRistretto,
    /// Public key computed as `(G * r) * sk`.
    pub(crate) h: CompressedRistretto,
}

impl VerificationKey {
    /// Constructs a VerificationKey from a private key and some randomness.
    pub fn from_secret(privkey: &Scalar, r: &Scalar) -> Self {
        let g = Self::from_secret_decompressed(r);
        let h = privkey * &g;
        Self::from_compressed(g.compress(),h.compress())
    }

    /// Constructs first point of VerificationKey from randomness.
    pub fn from_secret_decompressed(r: &Scalar) -> RistrettoPoint {
        r * RISTRETTO_BASEPOINT_POINT
    }

    /// Creates new key from a compressed form, remembers the compressed point.
    pub fn from_compressed(p: CompressedRistretto, q: CompressedRistretto) -> Self {
        VerificationKey { 
            g: p,
            h: q
        }
    }

    /// Converts the Verification key to compressed points
    pub fn into_point(self) -> (CompressedRistretto, CompressedRistretto) {
        (self.g, self.h)
    }

    /// Returns a reference to the compressed ristretto points
    pub fn as_point(&self) -> (&CompressedRistretto, &CompressedRistretto) {
        (&self.g, &self.h)
    }

    /// Returns the byte representation of the verification key
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes: Vec<u8> = Vec::with_capacity(64);
        bytes.extend_from_slice(self.g.as_bytes());
        bytes.extend_from_slice(self.h.as_bytes());
        bytes
    }
}


#[allow(non_snake_case)]
/// A Schnorr signature.
#[derive(Copy, Clone)]
pub struct Signature {
    /// Signature using nonce, message, and private key
    pub s: Scalar,
    /// Nonce commitment
    pub R: CompressedRistretto,
}
#[allow(non_snake_case)]
impl Signature {
    /// Signs the given transcript using the Schnorr scheme.
    pub fn sign(transcript: &mut Transcript, pubkey: VerificationKey, privkey: Scalar) -> Signature {
     //   let X = VerificationKey::from_secret(&privkey); // pubkey

        let mut rng = transcript
            .build_rng()
            .rekey_with_witness_bytes(b"x", &privkey.to_bytes())
            .finalize(&mut rand::thread_rng());

        // Generate ephemeral keypair (r, R). r is a random nonce.
        let r = Scalar::random(&mut rng);
        // R = generator * r
        let R = (&pubkey.g.decompress().unwrap() * &r).compress();

        let c = {
            transcript.domain_sep(b"zkschnorr");
            transcript.append_point_var(b"G", &pubkey.g);
            transcript.append_point_var(b"H", &pubkey.h);
            transcript.append_point_var(b"R", &R);
            transcript.get_challenge(b"c")
        };

        let s = r + c * privkey;

        Signature { s, R }
    }

/// Verifies this signature against a transcript and verification key.
    /// The transcript must be in the same state it was during [`sign`].
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        pubkey: VerificationKey,
    ) -> Result<(), &'static str> {
        // Make c = H(pubkey, R, m)
        // The message has already been fed into the transcript
        let c = {
            transcript.domain_sep(b"zkschnorr");
            transcript.append_point_var(b"G", &pubkey.g);
            transcript.append_point_var(b"H", &pubkey.h);
            transcript.append_point_var(b"R", &self.R);
            transcript.get_challenge(b"c")
        };
        // Form the final linear combination:
        // `s * pubkey_g = R + c * pubkey_h`
        let lhs = &self.s * &pubkey.g.decompress().unwrap();
        let rhs = &self.R.decompress() .unwrap()+ &(&c * &pubkey.h.decompress().unwrap());
        if lhs == rhs {
            Ok(())
        }
        else{
            Err("Error::InvalidSignature")
        }   
    }
}

// Message-oriented API
impl Signature {
    /// Signs a message with a domain-separation label.
    ///
    /// This is a byte-oriented wrapper over [`sign`]. Internally it creates a
    /// `Transcript` labelled `"ZkSchnorr.sign_message"` and appends the provided
    /// message bytes under `label`.
    pub fn sign_message(label: &'static [u8], message: &[u8], pubkey: VerificationKey, privkey: Scalar) -> Signature {
        Self::sign(&mut Self::transcript_for_message(label, message),pubkey, privkey)
    }

    /// Verifies a message signature using the provided verification key.
    ///
    /// Internally it creates a `Transcript` labelled `"ZkSchnorr.sign_message"`
    /// and appends the message bytes with the given `label`.
    pub fn verify_message(
        &self,
        label: &'static [u8],
        message: &[u8],
        pubkey: VerificationKey,
    ) -> Result<(), &'static str> {
        self.verify(&mut Self::transcript_for_message(label, message), pubkey)
    }

    fn transcript_for_message(label: &'static [u8], message: &[u8]) -> Transcript {
        let mut t = Transcript::new(b"ZkSchnorr.sign_message");
        t.append_message(label, message);
        t
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Signature({}{})",
            hex::encode(&self.s.as_bytes()),
            hex::encode(&self.R.as_bytes())
        )
        // Without hex crate we'd do this, but it outputs comma-separated numbers: [aa, 11, 5a, ...]
        // write!(f, "{:x?}", &self.0)
    }
}

//Signature Tests
#[allow(non_snake_case)]
#[test]
fn sign_and_verify_single() {
    let privkey = Scalar::from(1u64);
    let r = Scalar::from(10987u64);

    let X = VerificationKey::from_secret(&privkey, &r);

    let sig = Signature::sign(&mut Transcript::new(b"example transcript"), X, privkey);

    
    assert!(sig
        .verify(&mut Transcript::new(b"example transcript"), X)
        .is_ok());

    let priv_bad = Scalar::from(2u64);

    let X_bad = VerificationKey::from_secret(&priv_bad, &r);
    assert!(sig
        .verify(&mut Transcript::new(b"example transcript"), X_bad)
        .is_err());
    assert!(sig
        .verify(&mut Transcript::new(b"invalid transcript"), X)
        .is_err());
}
#[allow(non_snake_case)]
#[test]
fn sign_and_verify_single_msg() {
    let privkey = Scalar::from(1u64);
    let r = Scalar::from(10987u64);

    let X = VerificationKey::from_secret(&privkey, &r);

    let sig = Signature::sign_message(("transcript label").as_bytes(), ("account").as_bytes(), X, privkey);

    
    assert!(sig
        .verify_message(("transcript label").as_bytes(), ("account").as_bytes(), X)
        .is_ok());

    let priv_bad = Scalar::from(2u64);

    let X_bad = VerificationKey::from_secret(&priv_bad, &r);
    assert!(sig
        .verify_message(("transcript label").as_bytes(), ("account").as_bytes(), X_bad)
        .is_err());
    assert!(sig
        .verify_message(("transcript label").as_bytes(), ("Invalid Message").as_bytes(), X)
        .is_err());
}