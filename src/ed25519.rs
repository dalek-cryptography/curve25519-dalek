// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

//! ed25519 keypairs and batch verification.

use core::default::Default;

use rand::CryptoRng;
use rand::Rng;

#[cfg(feature = "serde")]
use serde::de::Error as SerdeError;
#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "serde")]
use serde::{Deserializer, Serializer};

pub use sha2::Sha512;

use curve25519_dalek::digest::generic_array::typenum::U64;
pub use curve25519_dalek::digest::Digest;

use curve25519_dalek::constants;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;

pub use crate::constants::*;
pub use crate::errors::*;
pub use crate::public::*;
pub use crate::secret::*;
pub use crate::signature::*;

/// Verify a batch of `signatures` on `messages` with their respective `public_keys`.
///
/// # Inputs
///
/// * `messages` is a slice of byte slices, one per signed message.
/// * `signatures` is a slice of `Signature`s.
/// * `public_keys` is a slice of `PublicKey`s.
/// * `csprng` is an implementation of `Rng + CryptoRng`, such as
///   `rand::rngs::ThreadRng`.
///
/// # Panics
///
/// This function will panic if the `messages, `signatures`, and `public_keys`
/// slices are not equal length.
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
/// use rand::thread_rng;
/// use rand::rngs::ThreadRng;
///
/// # fn main() {
/// let mut csprng: ThreadRng = thread_rng();
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
#[cfg(any(feature = "alloc", feature = "std"))]
#[allow(non_snake_case)]
pub fn verify_batch(
    messages: &[&[u8]],
    signatures: &[Signature],
    public_keys: &[PublicKey],
) -> Result<(), SignatureError>
{
    const ASSERT_MESSAGE: &'static [u8] = b"The number of messages, signatures, and public keys must be equal.";
    assert!(signatures.len()  == messages.len(),    ASSERT_MESSAGE);
    assert!(signatures.len()  == public_keys.len(), ASSERT_MESSAGE);
    assert!(public_keys.len() == messages.len(),    ASSERT_MESSAGE);
 
    #[cfg(feature = "alloc")]
    use alloc::vec::Vec;
    #[cfg(feature = "std")]
    use std::vec::Vec;

    use core::iter::once;
    use rand::thread_rng;

    use curve25519_dalek::traits::IsIdentity;
    use curve25519_dalek::traits::VartimeMultiscalarMul;

    // Select a random 128-bit scalar for each signature.
    let zs: Vec<Scalar> = signatures
        .iter()
        .map(|_| Scalar::from(thread_rng().gen::<u128>()))
        .collect();

    // Compute the basepoint coefficient, ∑ s[i]z[i] (mod l)
    let B_coefficient: Scalar = signatures
        .iter()
        .map(|sig| sig.s)
        .zip(zs.iter())
        .map(|(s, z)| z * s)
        .sum();

    // Compute H(R || A || M) for each (signature, public_key, message) triplet
    let hrams = (0..signatures.len()).map(|i| {
        let mut h: Sha512 = Sha512::default();
        h.input(signatures[i].R.as_bytes());
        h.input(public_keys[i].as_bytes());
        h.input(&messages[i]);
        Scalar::from_hash(h)
    });

    // Multiply each H(R || A || M) by the random value
    let zhrams = hrams.zip(zs.iter()).map(|(hram, z)| hram * z);

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

/// An ed25519 keypair.
#[derive(Debug, Default)] // we derive Default in order to use the clear() method in Drop
pub struct Keypair {
    /// The secret half of this keypair.
    pub secret: SecretKey,
    /// The public half of this keypair.
    pub public: PublicKey,
}

impl Keypair {
    /// Convert this keypair to bytes.
    ///
    /// # Returns
    ///
    /// An array of bytes, `[u8; KEYPAIR_LENGTH]`.  The first
    /// `SECRET_KEY_LENGTH` of bytes is the `SecretKey`, and the next
    /// `PUBLIC_KEY_LENGTH` bytes is the `PublicKey` (the same as other
    /// libraries, such as [Adam Langley's ed25519 Golang
    /// implementation](https://github.com/agl/ed25519/)).
    pub fn to_bytes(&self) -> [u8; KEYPAIR_LENGTH] {
        let mut bytes: [u8; KEYPAIR_LENGTH] = [0u8; KEYPAIR_LENGTH];

        bytes[..SECRET_KEY_LENGTH].copy_from_slice(self.secret.as_bytes());
        bytes[SECRET_KEY_LENGTH..].copy_from_slice(self.public.as_bytes());
        bytes
    }

    /// Construct a `Keypair` from the bytes of a `PublicKey` and `SecretKey`.
    ///
    /// # Inputs
    ///
    /// * `bytes`: an `&[u8]` representing the scalar for the secret key, and a
    ///   compressed Edwards-Y coordinate of a point on curve25519, both as bytes.
    ///   (As obtained from `Keypair::to_bytes()`.)
    ///
    /// # Warning
    ///
    /// Absolutely no validation is done on the key.  If you give this function
    /// bytes which do not represent a valid point, or which do not represent
    /// corresponding parts of the key, then your `Keypair` will be broken and
    /// it will be your fault.
    ///
    /// # Returns
    ///
    /// A `Result` whose okay value is an EdDSA `Keypair` or whose error value
    /// is an `SignatureError` describing the error that occurred.
    pub fn from_bytes<'a>(bytes: &'a [u8]) -> Result<Keypair, SignatureError> {
        if bytes.len() != KEYPAIR_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError {
                name: "Keypair",
                length: KEYPAIR_LENGTH,
            }));
        }
        let secret = SecretKey::from_bytes(&bytes[..SECRET_KEY_LENGTH])?;
        let public = PublicKey::from_bytes(&bytes[SECRET_KEY_LENGTH..])?;

        Ok(Keypair{ secret: secret, public: public })
    }

    /// Generate an ed25519 keypair.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate rand;
    /// extern crate ed25519_dalek;
    ///
    /// # #[cfg(feature = "std")]
    /// # fn main() {
    ///
    /// use rand::Rng;
    /// use rand::rngs::OsRng;
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let keypair: Keypair = Keypair::generate(&mut csprng);
    ///
    /// # }
    /// #
    /// # #[cfg(not(feature = "std"))]
    /// # fn main() { }
    /// ```
    ///
    /// # Input
    ///
    /// A CSPRNG with a `fill_bytes()` method, e.g. `rand_chacha::ChaChaRng`.
    ///
    /// The caller must also supply a hash function which implements the
    /// `Digest` and `Default` traits, and which returns 512 bits of output.
    /// The standard hash function used for most ed25519 libraries is SHA-512,
    /// which is available with `use sha2::Sha512` as in the example above.
    /// Other suitable hash functions include Keccak-512 and Blake2b-512.
    pub fn generate<R>(csprng: &mut R) -> Keypair
    where
        R: CryptoRng + Rng,
    {
        let sk: SecretKey = SecretKey::generate(csprng);
        let pk: PublicKey = (&sk).into();

        Keypair{ public: pk, secret: sk }
    }

    /// Sign a message with this keypair's secret key.
    pub fn sign(&self, message: &[u8]) -> Signature {
        let expanded: ExpandedSecretKey = (&self.secret).into();

        expanded.sign(&message, &self.public)
    }

    /// Sign a `prehashed_message` with this `Keypair` using the
    /// Ed25519ph algorithm defined in [RFC8032 §5.1][rfc8032].
    ///
    /// # Inputs
    ///
    /// * `prehashed_message` is an instantiated hash digest with 512-bits of
    ///   output which has had the message to be signed previously fed into its
    ///   state.
    /// * `context` is an optional context string, up to 255 bytes inclusive,
    ///   which may be used to provide additional domain separation.  If not
    ///   set, this will default to an empty string.
    ///
    /// # Returns
    ///
    /// An Ed25519ph [`Signature`] on the `prehashed_message`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate ed25519_dalek;
    /// extern crate rand;
    ///
    /// use ed25519_dalek::Digest;
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Sha512;
    /// use ed25519_dalek::Signature;
    /// use rand::thread_rng;
    ///
    /// # #[cfg(feature = "std")]
    /// # fn main() {
    /// let mut csprng = thread_rng();
    /// let keypair: Keypair = Keypair::generate(&mut csprng);
    /// let message: &[u8] = b"All I want is to pet all of the dogs.";
    ///
    /// // Create a hash digest object which we'll feed the message into:
    /// let mut prehashed: Sha512 = Sha512::new();
    ///
    /// prehashed.input(message);
    /// # }
    /// #
    /// # #[cfg(not(feature = "std"))]
    /// # fn main() { }
    /// ```
    ///
    /// If you want, you can optionally pass a "context".  It is generally a
    /// good idea to choose a context and try to make it unique to your project
    /// and this specific usage of signatures.
    ///
    /// For example, without this, if you were to [convert your OpenPGP key
    /// to a Bitcoin key][terrible_idea] (just as an example, and also Don't
    /// Ever Do That) and someone tricked you into signing an "email" which was
    /// actually a Bitcoin transaction moving all your magic internet money to
    /// their address, it'd be a valid transaction.
    ///
    /// By adding a context, this trick becomes impossible, because the context
    /// is concatenated into the hash, which is then signed.  So, going with the
    /// previous example, if your bitcoin wallet used a context of
    /// "BitcoinWalletAppTxnSigning" and OpenPGP used a context (this is likely
    /// the least of their safety problems) of "GPGsCryptoIsntConstantTimeLol",
    /// then the signatures produced by both could never match the other, even
    /// if they signed the exact same message with the same key.
    ///
    /// Let's add a context for good measure (remember, you'll want to choose
    /// your own!):
    ///
    /// ```
    /// # extern crate ed25519_dalek;
    /// # extern crate rand;
    /// #
    /// # use ed25519_dalek::Digest;
    /// # use ed25519_dalek::Keypair;
    /// # use ed25519_dalek::Signature;
    /// # use ed25519_dalek::Sha512;
    /// # use rand::thread_rng;
    /// #
    /// # #[cfg(feature = "std")]
    /// # fn main() {
    /// # let mut csprng = thread_rng();
    /// # let keypair: Keypair = Keypair::generate(&mut csprng);
    /// # let message: &[u8] = b"All I want is to pet all of the dogs.";
    /// # let mut prehashed: Sha512 = Sha512::new();
    /// # prehashed.input(message);
    /// #
    /// let context: &[u8] = b"Ed25519DalekSignPrehashedDoctest";
    ///
    /// let sig: Signature = keypair.sign_prehashed(prehashed, Some(context));
    /// # }
    /// #
    /// # #[cfg(not(feature = "std"))]
    /// # fn main() { }
    /// ```
    ///
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    /// [terrible_idea]: https://github.com/isislovecruft/scripts/blob/master/gpgkey2bc.py
    pub fn sign_prehashed<D>(
        &self,
        prehashed_message: D,
        context: Option<&'static [u8]>,
    ) -> Signature
    where
        D: Digest<OutputSize = U64>,
    {
        let expanded: ExpandedSecretKey = (&self.secret).into(); // xxx thanks i hate this

        expanded.sign_prehashed(prehashed_message, &self.public, context)
    }

    /// Verify a signature on a message with this keypair's public key.
    pub fn verify(
        &self,
        message: &[u8],
        signature: &Signature
    ) -> Result<(), SignatureError>
    {
        self.public.verify(message, signature)
    }

    /// Verify a `signature` on a `prehashed_message` using the Ed25519ph algorithm.
    ///
    /// # Inputs
    ///
    /// * `prehashed_message` is an instantiated hash digest with 512-bits of
    ///   output which has had the message to be signed previously fed into its
    ///   state.
    /// * `context` is an optional context string, up to 255 bytes inclusive,
    ///   which may be used to provide additional domain separation.  If not
    ///   set, this will default to an empty string.
    /// * `signature` is a purported Ed25519ph [`Signature`] on the `prehashed_message`.
    ///
    /// # Returns
    ///
    /// Returns `true` if the `signature` was a valid signature created by this
    /// `Keypair` on the `prehashed_message`.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate ed25519_dalek;
    /// extern crate rand;
    ///
    /// use ed25519_dalek::Digest;
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    /// use ed25519_dalek::Sha512;
    /// use rand::thread_rng;
    ///
    /// # #[cfg(feature = "std")]
    /// # fn main() {
    /// let mut csprng = thread_rng();
    /// let keypair: Keypair = Keypair::generate(&mut csprng);
    /// let message: &[u8] = b"All I want is to pet all of the dogs.";
    ///
    /// let mut prehashed: Sha512 = Sha512::default();
    /// prehashed.input(message);
    ///
    /// let context: &[u8] = b"Ed25519DalekSignPrehashedDoctest";
    ///
    /// let sig: Signature = keypair.sign_prehashed(prehashed, Some(context));
    ///
    /// // The sha2::Sha512 struct doesn't implement Copy, so we'll have to create a new one:
    /// let mut prehashed_again: Sha512 = Sha512::default();
    /// prehashed_again.input(message);
    ///
    /// let verified = keypair.public.verify_prehashed(prehashed_again, Some(context), &sig);
    ///
    /// assert!(verified.is_ok());
    /// # }
    /// #
    /// # #[cfg(not(feature = "std"))]
    /// # fn main() { }
    /// ```
    ///
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    pub fn verify_prehashed<D>(
        &self,
        prehashed_message: D,
        context: Option<&[u8]>,
        signature: &Signature,
    ) -> Result<(), SignatureError>
    where
        D: Digest<OutputSize = U64>,
    {
        self.public.verify_prehashed(prehashed_message, context, signature)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Keypair {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for Keypair {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'d>,
    {
        struct KeypairVisitor;

        impl<'d> Visitor<'d> for KeypairVisitor {
            type Value = Keypair;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 keypair, 64 bytes in total where the secret key is \
                                     the first 32 bytes and is in unexpanded form, and the second \
                                     32 bytes is a compressed point for a public key.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Keypair, E>
            where
                E: SerdeError,
            {
                let secret_key = SecretKey::from_bytes(&bytes[..SECRET_KEY_LENGTH]);
                let public_key = PublicKey::from_bytes(&bytes[SECRET_KEY_LENGTH..]);

                if secret_key.is_ok() && public_key.is_ok() {
                    Ok(Keypair{ secret: secret_key.unwrap(), public: public_key.unwrap() })
                } else {
                    Err(SerdeError::invalid_length(bytes.len(), &self))
                }
            }
        }
        deserializer.deserialize_bytes(KeypairVisitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use clear_on_drop::clear::Clear;

    #[test]
    fn keypair_clear_on_drop() {
        let mut keypair: Keypair = Keypair::from_bytes(&[1u8; KEYPAIR_LENGTH][..]).unwrap();

        keypair.clear();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use std::mem;
            use std::slice;

            unsafe { slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x)) }
        }

        assert!(!as_bytes(&keypair).contains(&0x15));
    }
}
