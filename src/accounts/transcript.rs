use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// Extension trait to the Merlin transcript API that allows committing scalars and points and
/// generating challenges as scalars.
pub trait TranscriptProtocol {
    /// Appends `label` to the transcript as a domain separator.
    fn domain_sep(&mut self, label: &'static [u8]);

    /// Append the `label` for a scalar variable to the transcript.
    fn append_scalar_var(&mut self, label: &'static [u8], scalar: &Scalar);

    /// Append a point variable to the transcript, for use by a prover.
    fn append_point_var(&mut self, label: &'static [u8], point: &CompressedRistretto);

    /// Get a scalar challenge from the transcript.
    fn get_challenge(&mut self, label: &'static [u8]) -> Scalar;
}

impl TranscriptProtocol for Transcript {
    fn domain_sep(&mut self, label: &'static [u8]) {
        self.append_message(b"dom-sep", label);
    }

    fn append_scalar_var(&mut self, label: &'static [u8], scalar: &Scalar) {
        self.append_message(label, scalar.as_bytes());
    }

    fn append_point_var(&mut self, label: &'static [u8], point: &CompressedRistretto) {
        self.append_message(b"ptvar", label);
        self.append_message(b"val", point.as_bytes());
    }

    fn get_challenge(&mut self, label: &'static [u8]) -> Scalar {
        let mut bytes = [0; 64];
        self.challenge_bytes(label, &mut bytes);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }
}