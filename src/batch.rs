// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

//! Batch signature verification.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::vec::Vec;

use core::iter::once;

use curve25519_dalek::constants;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use curve25519_dalek::traits::VartimeMultiscalarMul;

pub use curve25519_dalek::digest::Digest;

use merlin::Transcript;

use rand::Rng;
#[cfg(all(feature = "batch", not(feature = "batch_deterministic")))]
use rand::thread_rng;
#[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
use rand_core;

use sha2::Sha512;

use crate::errors::InternalError;
use crate::errors::SignatureError;
use crate::public::PublicKey;
use crate::signature::Signature;

trait BatchTranscript {
    fn append_hrams(&mut self, hrams: &Vec<Scalar>);
    fn append_message_lengths(&mut self, message_lengths: &Vec<usize>);
}

impl BatchTranscript for Transcript {
    /// Add all the computed `H(R||A||M)`s to the protocol transcript.
    ///
    /// Each is also prefixed with their index in the vector.
    fn append_hrams(&mut self, hrams: &Vec<Scalar>) {
        for (i, hram) in hrams.iter().enumerate() {
            // XXX add message length into transcript
            self.append_u64(b"", i as u64);
            self.append_message(b"hram", hram.as_bytes());
        }
    }

    fn append_message_lengths(&mut self, message_lengths: &Vec<usize>) {
        for (i, len) in message_lengths.iter().enumerate() {
            self.append_u64(b"", i as u64);
            self.append_u64(b"mlen", *len as u64);
        }
    }
}

/// An implementation of `rand_core::RngCore` which does nothing, to provide
/// purely deterministic transcript-based nonces, rather than synthetically
/// random nonces.
#[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
struct ZeroRng {}

#[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
impl rand_core::RngCore for ZeroRng {
    fn next_u32(&mut self) -> u32 {
        rand_core::impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        rand_core::impls::next_u64_via_fill(self)
    }

    /// A no-op function which leaves the destination bytes for randomness unchanged.
    ///
    /// In this case, the internal merlin code is initialising the destination
    /// by doing `[0u8; …]`, which means that when we call
    /// `merlin::TranscriptRngBuilder.finalize()`, rather than rekeying the
    /// STROBE state based on external randomness, we're doing an
    /// `ENC_{state}(00000000000000000000000000000000)` operation, which is
    /// identical to the STROBE `MAC` operation.
    fn fill_bytes(&mut self, _dest: &mut [u8]) { }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

#[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
impl rand_core::CryptoRng for ZeroRng {}

#[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
fn zero_rng() -> ZeroRng {
    ZeroRng {}
}

/// Verify a batch of `signatures` on `messages` with their respective `public_keys`.
///
/// # Inputs
///
/// * `messages` is a slice of byte slices, one per signed message.
/// * `signatures` is a slice of `Signature`s.
/// * `public_keys` is a slice of `PublicKey`s.
/// * `csprng` is an implementation of `Rng + CryptoRng`.
///
/// # Returns
///
/// * A `Result` whose `Ok` value is an emtpy tuple and whose `Err` value is a
///   `SignatureError` containing a description of the internal error which
///   occured.
///
/// # Examples
///
/// ```
/// extern crate ed25519_dalek;
/// extern crate rand;
///
/// use ed25519_dalek::verify_batch;
/// use ed25519_dalek::Keypair;
/// use ed25519_dalek::PublicKey;
/// use ed25519_dalek::Signature;
/// use rand::rngs::OsRng;
///
/// # fn main() {
/// let mut csprng = OsRng{};
/// let keypairs: Vec<Keypair> = (0..64).map(|_| Keypair::generate(&mut csprng)).collect();
/// let msg: &[u8] = b"They're good dogs Brant";
/// let messages: Vec<&[u8]> = (0..64).map(|_| msg).collect();
/// let signatures:  Vec<Signature> = keypairs.iter().map(|key| key.sign(&msg)).collect();
/// let public_keys: Vec<PublicKey> = keypairs.iter().map(|key| key.public).collect();
///
/// let result = verify_batch(&messages[..], &signatures[..], &public_keys[..]);
/// assert!(result.is_ok());
/// # }
/// ```
#[cfg(all(any(feature = "batch", feature = "batch_deterministic"),
          any(feature = "alloc", feature = "std")))]
#[allow(non_snake_case)]
pub fn verify_batch(
    messages: &[&[u8]],
    signatures: &[Signature],
    public_keys: &[PublicKey],
) -> Result<(), SignatureError>
{
    // Return an Error if any of the vectors were not the same size as the others.
    if signatures.len() != messages.len() ||
        signatures.len() != public_keys.len() ||
        public_keys.len() != messages.len() {
        return Err(SignatureError(InternalError::ArrayLengthError{
            name_a: "signatures", length_a: signatures.len(),
            name_b: "messages", length_b: messages.len(),
            name_c: "public_keys", length_c: public_keys.len(),
        }));
    }

    // Compute H(R || A || M) for each (signature, public_key, message) triplet
    let hrams: Vec<Scalar> = (0..signatures.len()).map(|i| {
        let mut h: Sha512 = Sha512::default();
        h.input(signatures[i].R.as_bytes());
        h.input(public_keys[i].as_bytes());
        h.input(&messages[i]);
        Scalar::from_hash(h)
    }).collect();

    // Collect the message lengths to add into the transcript.
    let message_lengths: Vec<usize> = messages.iter().map(|i| i.len()).collect();

    // Build a PRNG based on a transcript of the H(R || A || M)s seen thus far.
    // This provides synthethic randomness in the default configuration, and
    // purely deterministic in the case of compiling with the
    // "batch_deterministic" feature.
    let mut transcript: Transcript = Transcript::new(b"ed25519 batch verification");

    transcript.append_hrams(&hrams);
    transcript.append_message_lengths(&message_lengths);

    #[cfg(all(feature = "batch", not(feature = "batch_deterministic")))]
    let mut prng = transcript.build_rng().finalize(&mut thread_rng());
    #[cfg(all(not(feature = "batch"), feature = "batch_deterministic"))]
    let mut prng = transcript.build_rng().finalize(&mut zero_rng());

    // Select a random 128-bit scalar for each signature.
    let zs: Vec<Scalar> = signatures
        .iter()
        .map(|_| Scalar::from(prng.gen::<u128>()))
        .collect();


    // Compute the basepoint coefficient, ∑ s[i]z[i] (mod l)
    let B_coefficient: Scalar = signatures
        .iter()
        .map(|sig| sig.s)
        .zip(zs.iter())
        .map(|(s, z)| z * s)
        .sum();

    // Multiply each H(R || A || M) by the random value
    let zhrams = hrams.iter().zip(zs.iter()).map(|(hram, z)| hram * z);

    let Rs = signatures.iter().map(|sig| sig.R.decompress());
    let As = public_keys.iter().map(|pk| Some(pk.1));
    let B = once(Some(constants::ED25519_BASEPOINT_POINT));

    // Compute (-∑ z[i]s[i] (mod l)) B + ∑ z[i]R[i] + ∑ (z[i]H(R||A||M)[i] (mod l)) A[i] = 0
    let id = EdwardsPoint::optional_multiscalar_mul(
        once(-B_coefficient).chain(zs.iter().cloned()).chain(zhrams),
        B.chain(Rs).chain(As),
    ).ok_or_else(|| SignatureError(InternalError::VerifyError))?;

    if id.is_identity() {
        Ok(())
    } else {
        Err(SignatureError(InternalError::VerifyError))
    }
}
