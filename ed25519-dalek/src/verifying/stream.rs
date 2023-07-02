use curve25519_dalek::{edwards::EdwardsPoint, scalar::Scalar};
use sha2::{Digest, Sha512};

use crate::{signature::InternalSignature, InternalError, SignatureError, VerifyingKey};

/// An IUF verifier for ed25519.
///
/// Created with [`VerifyingKey::verify_stream()`] or [`SigningKey::verify_stream()`].
///
/// [`SigningKey::verify_stream()`]: super::SigningKey::verify_stream()
#[derive(Debug)]
pub struct StreamVerifier {
    /// Public key to verify with.
    pub(crate) public_key: VerifyingKey,

    /// Candidate signature to verify against.
    pub(crate) signature: InternalSignature,

    /// Hash state.
    pub(crate) hasher: Sha512,
}

impl StreamVerifier {
    /// Constructs new stream verifier.
    ///
    /// Seeds hash state with public key and signature components.
    pub(crate) fn new(public_key: VerifyingKey, signature: InternalSignature) -> Self {
        let mut hasher = Sha512::new();
        hasher.update(signature.R.as_bytes());
        hasher.update(public_key.as_bytes());

        Self {
            public_key,
            hasher,
            signature,
        }
    }

    /// Digest message chunk.
    pub fn update(&mut self, chunk: impl AsRef<[u8]>) {
        self.hasher.update(&chunk);
    }

    /// Finalize verifier and check against candidate signature.
    #[allow(non_snake_case)]
    pub fn finalize_and_verify(self) -> Result<(), SignatureError> {
        let minus_A: EdwardsPoint = -self.public_key.point;
        let k = Scalar::from_hash(self.hasher);
        let R =
            EdwardsPoint::vartime_double_scalar_mul_basepoint(&k, &(minus_A), &self.signature.s);

        if R.compress() == self.signature.R {
            Ok(())
        } else {
            Err(InternalError::Verify.into())
        }
    }
}
