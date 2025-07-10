//! Transcript extension utilities for the Quisquis protocol.
//!
//! This module provides the [`TranscriptProtocol`] trait, which extends the Merlin transcript API
//! with methods for committing scalars, points, and accounts, and for generating Fiat-Shamir
//! challenges as scalars.

use crate::accounts::Account;
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;

/// Extension trait to the Merlin transcript API for Quisquis-specific operations.
///
/// This trait allows committing scalars, points, and account structures to the transcript,
/// and generating Fiat-Shamir challenges as scalars.
pub trait TranscriptProtocol {
    /// Appends `label` to the transcript as a domain separator.
    ///
    /// This is used to separate different protocol domains and prevent transcript collisions.
    fn domain_sep(&mut self, label: &'static [u8]);

    /// Appends a scalar variable to the transcript with the given `label`.
    ///
    /// # Arguments
    /// * `label` - The label for the scalar variable.
    /// * `scalar` - The scalar value to append.
    fn append_scalar_var(&mut self, label: &'static [u8], scalar: &Scalar);

    /// Appends a compressed Ristretto point variable to the transcript with the given `label`.
    ///
    /// # Arguments
    /// * `label` - The label for the point variable.
    /// * `point` - The compressed Ristretto point to append.
    fn append_point_var(&mut self, label: &'static [u8], point: &CompressedRistretto);

    /// Appends an account variable to the transcript with the given `label`.
    ///
    /// This is Quisquis-specific and commits all components of the account (public key and commitment).
    ///
    /// # Arguments
    /// * `label` - The label for the account variable.
    /// * `account` - The account to append.
    fn append_account_var(&mut self, label: &'static [u8], account: &Account);

    /// Generates a scalar challenge from the transcript using the given `label`.
    ///
    /// # Arguments
    /// * `label` - The label for the challenge.
    ///
    /// # Returns
    /// A scalar derived from the transcript state.
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

    fn append_account_var(&mut self, label: &'static [u8], account: &Account) {
        self.append_message(b"acvar", label);
        self.append_message(b"gr", account.pk.gr.as_bytes());
        self.append_message(b"grsk", account.pk.grsk.as_bytes());
        self.append_message(b"commc", account.comm.c.as_bytes());
        self.append_message(b"commd", account.comm.d.as_bytes());
    }

    fn get_challenge(&mut self, label: &'static [u8]) -> Scalar {
        let mut bytes = [0; 64];
        self.challenge_bytes(label, &mut bytes);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }
}
