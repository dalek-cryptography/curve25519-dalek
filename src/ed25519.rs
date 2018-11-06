// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2018 Isis Lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! A Rust implementation of ed25519 EdDSA key generation, signing, and
//! verification.

use core::default::Default;
use core::fmt::{Debug};

use rand::CryptoRng;
use rand::Rng;

#[cfg(feature = "serde")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "serde")]
use serde::{Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Error as SerdeError;
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "sha2")]
use sha2::Sha512;

use clear_on_drop::clear::Clear;

use curve25519_dalek::digest::Digest;
use curve25519_dalek::digest::generic_array::typenum::U64;

use curve25519_dalek::constants;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;

use errors::SignatureError;
use errors::InternalError;

/// The length of a curve25519 EdDSA `Signature`, in bytes.
pub const SIGNATURE_LENGTH: usize = 64;

/// The length of a curve25519 EdDSA `SecretKey`, in bytes.
pub const SECRET_KEY_LENGTH: usize = 32;

/// The length of an ed25519 EdDSA `PublicKey`, in bytes.
pub const PUBLIC_KEY_LENGTH: usize = 32;

/// The length of an ed25519 EdDSA `Keypair`, in bytes.
pub const KEYPAIR_LENGTH: usize = SECRET_KEY_LENGTH + PUBLIC_KEY_LENGTH;

/// The length of the "key" portion of an "expanded" curve25519 EdDSA secret key, in bytes.
const EXPANDED_SECRET_KEY_KEY_LENGTH: usize = 32;

/// The length of the "nonce" portion of an "expanded" curve25519 EdDSA secret key, in bytes.
const EXPANDED_SECRET_KEY_NONCE_LENGTH: usize = 32;

/// The length of an "expanded" curve25519 EdDSA key, `ExpandedSecretKey`, in bytes.
pub const EXPANDED_SECRET_KEY_LENGTH: usize = EXPANDED_SECRET_KEY_KEY_LENGTH + EXPANDED_SECRET_KEY_NONCE_LENGTH;

/// An EdDSA signature.
///
/// # Note
///
/// These signatures, unlike the ed25519 signature reference implementation, are
/// "detached"—that is, they do **not** include a copy of the message which has
/// been signed.
#[allow(non_snake_case)]
#[derive(Copy, Eq, PartialEq)]
#[repr(C)]
pub struct Signature {
    /// `R` is an `EdwardsPoint`, formed by using an hash function with
    /// 512-bits output to produce the digest of:
    ///
    /// - the nonce half of the `ExpandedSecretKey`, and
    /// - the message to be signed.
    ///
    /// This digest is then interpreted as a `Scalar` and reduced into an
    /// element in ℤ/lℤ.  The scalar is then multiplied by the distinguished
    /// basepoint to produce `R`, and `EdwardsPoint`.
    pub (crate) R: CompressedEdwardsY,

    /// `s` is a `Scalar`, formed by using an hash function with 512-bits output
    /// to produce the digest of:
    ///
    /// - the `r` portion of this `Signature`,
    /// - the `PublicKey` which should be used to verify this `Signature`, and
    /// - the message to be signed.
    ///
    /// This digest is then interpreted as a `Scalar` and reduced into an
    /// element in ℤ/lℤ.
    pub (crate) s: Scalar,
}

impl Clone for Signature {
    fn clone(&self) -> Self { *self }
}

impl Debug for Signature {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "Signature( R: {:?}, s: {:?} )", &self.R, &self.s)
    }
}

impl Signature {
    /// Convert this `Signature` to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SIGNATURE_LENGTH] {
        let mut signature_bytes: [u8; SIGNATURE_LENGTH] = [0u8; SIGNATURE_LENGTH];

        signature_bytes[..32].copy_from_slice(&self.R.as_bytes()[..]);
        signature_bytes[32..].copy_from_slice(&self.s.as_bytes()[..]);
        signature_bytes
    }

    /// Construct a `Signature` from a slice of bytes.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Signature, SignatureError> {
        if bytes.len() != SIGNATURE_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError{
                name: "Signature", length: SIGNATURE_LENGTH }));
        }
        let mut lower: [u8; 32] = [0u8; 32];
        let mut upper: [u8; 32] = [0u8; 32];

        lower.copy_from_slice(&bytes[..32]);
        upper.copy_from_slice(&bytes[32..]);

        if upper[31] & 224 != 0 {
            return Err(SignatureError(InternalError::ScalarFormatError));
        }

        Ok(Signature{ R: CompressedEdwardsY(lower), s: Scalar::from_bits(upper) })
    }
}

#[cfg(feature = "serde")]
impl Serialize for Signature {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for Signature {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'d> {
        struct SignatureVisitor;

        impl<'d> Visitor<'d> for SignatureVisitor {
            type Value = Signature;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 signature as 64 bytes, as specified in RFC8032.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Signature, E> where E: SerdeError{
                Signature::from_bytes(bytes).or(Err(SerdeError::invalid_length(bytes.len(), &self)))
            }
        }
        deserializer.deserialize_bytes(SignatureVisitor)
    }
}

/// An EdDSA secret key.
#[repr(C)]
#[derive(Default)] // we derive Default in order to use the clear() method in Drop
pub struct SecretKey(pub (crate) [u8; SECRET_KEY_LENGTH]);

impl Debug for SecretKey {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "SecretKey: {:?}", &self.0[..])
    }
}

/// Overwrite secret key material with null bytes when it goes out of scope.
impl Drop for SecretKey {
    fn drop(&mut self) {
        self.0.clear();
    }
}

impl SecretKey {
    /// Expand this `SecretKey` into an `ExpandedSecretKey`.
    pub fn expand<D>(&self) -> ExpandedSecretKey
        where D: Digest<OutputSize = U64> + Default
    {
        ExpandedSecretKey::from_secret_key::<D>(&self)
    }

    /// Convert this secret key to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_LENGTH] {
        self.0
    }

    /// View this secret key as a byte array.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; SECRET_KEY_LENGTH] {
        &self.0
    }

    /// Construct a `SecretKey` from a slice of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate ed25519_dalek;
    /// #
    /// use ed25519_dalek::SecretKey;
    /// use ed25519_dalek::SECRET_KEY_LENGTH;
    /// use ed25519_dalek::SignatureError;
    ///
    /// # fn doctest() -> Result<SecretKey, SignatureError> {
    /// let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = [
    ///    157, 097, 177, 157, 239, 253, 090, 096,
    ///    186, 132, 074, 244, 146, 236, 044, 196,
    ///    068, 073, 197, 105, 123, 050, 105, 025,
    ///    112, 059, 172, 003, 028, 174, 127, 096, ];
    ///
    /// let secret_key: SecretKey = SecretKey::from_bytes(&secret_key_bytes)?;
    /// #
    /// # Ok(secret_key)
    /// # }
    /// #
    /// # fn main() {
    /// #     let result = doctest();
    /// #     assert!(result.is_ok());
    /// # }
    /// ```
    ///
    /// # Returns
    ///
    /// A `Result` whose okay value is an EdDSA `SecretKey` or whose error value
    /// is an `SignatureError` wrapping the internal error that occurred.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<SecretKey, SignatureError> {
        if bytes.len() != SECRET_KEY_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError{
                name: "SecretKey", length: SECRET_KEY_LENGTH }));
        }
        let mut bits: [u8; 32] = [0u8; 32];
        bits.copy_from_slice(&bytes[..32]);

        Ok(SecretKey(bits))
    }

    /// Generate a `SecretKey` from a `csprng`.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate rand;
    /// extern crate sha2;
    /// extern crate ed25519_dalek;
    ///
    /// # #[cfg(feature = "std")]
    /// # fn main() {
    /// #
    /// use rand::Rng;
    /// use rand::OsRng;
    /// use sha2::Sha512;
    /// use ed25519_dalek::PublicKey;
    /// use ed25519_dalek::SecretKey;
    /// use ed25519_dalek::Signature;
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    /// # }
    /// #
    /// # #[cfg(not(feature = "std"))]
    /// # fn main() { }
    /// ```
    ///
    /// Afterwards, you can generate the corresponding public—provided you also
    /// supply a hash function which implements the `Digest` and `Default`
    /// traits, and which returns 512 bits of output—via:
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # fn main() {
    /// #
    /// # use rand::Rng;
    /// # use rand::ChaChaRng;
    /// # use rand::SeedableRng;
    /// # use sha2::Sha512;
    /// # use ed25519_dalek::PublicKey;
    /// # use ed25519_dalek::SecretKey;
    /// # use ed25519_dalek::Signature;
    /// #
    /// # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
    /// # let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    ///
    /// let public_key: PublicKey = PublicKey::from_secret::<Sha512>(&secret_key);
    /// # }
    /// ```
    ///
    /// The standard hash function used for most ed25519 libraries is SHA-512,
    /// which is available with `use sha2::Sha512` as in the example above.
    /// Other suitable hash functions include Keccak-512 and Blake2b-512.
    ///
    /// # Input
    ///
    /// A CSPRNG with a `fill_bytes()` method, e.g. `rand::ChaChaRng`
    pub fn generate<T>(csprng: &mut T) -> SecretKey
        where T: CryptoRng + Rng,
    {
        let mut sk: SecretKey = SecretKey([0u8; 32]);

        csprng.fill_bytes(&mut sk.0);

        sk
    }
}

#[cfg(feature = "serde")]
impl Serialize for SecretKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_bytes(self.as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for SecretKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'d> {
        struct SecretKeyVisitor;

        impl<'d> Visitor<'d> for SecretKeyVisitor {
            type Value = SecretKey;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 secret key as 32 bytes, as specified in RFC8032.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<SecretKey, E> where E: SerdeError {
                SecretKey::from_bytes(bytes).or(Err(SerdeError::invalid_length(bytes.len(), &self)))
            }
        }
        deserializer.deserialize_bytes(SecretKeyVisitor)
    }
}

/// An "expanded" secret key.
///
/// This is produced by using an hash function with 512-bits output to digest a
/// `SecretKey`.  The output digest is then split in half, the lower half being
/// the actual `key` used to sign messages, after twiddling with some bits.¹ The
/// upper half is used a sort of half-baked, ill-designed² pseudo-domain-separation
/// "nonce"-like thing, which is used during signature production by
/// concatenating it with the message to be signed before the message is hashed.
//
// ¹ This results in a slight bias towards non-uniformity at one spectrum of
// the range of valid keys.  Oh well: not my idea; not my problem.
//
// ² It is the author's view (specifically, isis agora lovecruft, in the event
// you'd like to complain about me, again) that this is "ill-designed" because
// this doesn't actually provide true hash domain separation, in that in many
// real-world applications a user wishes to have one key which is used in
// several contexts (such as within tor, which does does domain separation
// manually by pre-concatenating static strings to messages to achieve more
// robust domain separation).  In other real-world applications, such as
// bitcoind, a user might wish to have one master keypair from which others are
// derived (à la BIP32) and different domain separators between keys derived at
// different levels (and similarly for tree-based key derivation constructions,
// such as hash-based signatures).  Leaving the domain separation to
// application designers, who thus far have produced incompatible,
// slightly-differing, ad hoc domain separation (at least those application
// designers who knew enough cryptographic theory to do so!), is therefore a
// bad design choice on the part of the cryptographer designing primitives
// which should be simple and as foolproof as possible to use for
// non-cryptographers.  Further, later in the ed25519 signature scheme, as
// specified in RFC8032, the public key is added into *another* hash digest
// (along with the message, again); it is unclear to this author why there's
// not only one but two poorly-thought-out attempts at domain separation in the
// same signature scheme, and which both fail in exactly the same way.  For a
// better-designed, Schnorr-based signature scheme, see Trevor Perrin's work on
// "generalised EdDSA" and "VXEdDSA".
#[repr(C)]
#[derive(Default)] // we derive Default in order to use the clear() method in Drop
pub struct ExpandedSecretKey {
    pub (crate) key: Scalar,
    pub (crate) nonce: [u8; 32],
}

/// Overwrite secret key material with null bytes when it goes out of scope.
impl Drop for ExpandedSecretKey {
    fn drop(&mut self) {
        self.key.clear();
        self.nonce.clear();
    }
}

#[cfg(feature = "sha2")]
impl<'a> From<&'a SecretKey> for ExpandedSecretKey {
    /// Construct an `ExpandedSecretKey` from a `SecretKey`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    /// #
    /// use rand::{Rng, OsRng};
    /// use sha2::Sha512;
    /// use ed25519_dalek::{SecretKey, ExpandedSecretKey};
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    /// let expanded_secret_key: ExpandedSecretKey = ExpandedSecretKey::from(&secret_key);
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "std"), not(feature = "sha2")))]
    /// # fn main() {}
    /// ```
    fn from(secret_key: &'a SecretKey) -> ExpandedSecretKey {
        ExpandedSecretKey::from_secret_key::<Sha512>(&secret_key)
    }
}

impl ExpandedSecretKey {
    /// Convert this `ExpandedSecretKey` into an array of 64 bytes.
    ///
    /// # Returns
    ///
    /// An array of 64 bytes.  The first 32 bytes represent the "expanded"
    /// secret key, and the last 32 bytes represent the "domain-separation"
    /// "nonce".
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # #[cfg(all(feature = "sha2", feature = "std"))]
    /// # fn main() {
    /// #
    /// use rand::{Rng, OsRng};
    /// use sha2::Sha512;
    /// use ed25519_dalek::{SecretKey, ExpandedSecretKey};
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    /// let expanded_secret_key: ExpandedSecretKey = ExpandedSecretKey::from(&secret_key);
    /// let expanded_secret_key_bytes: [u8; 64] = expanded_secret_key.to_bytes();
    ///
    /// assert!(&expanded_secret_key_bytes[..] != &[0u8; 64][..]);
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    #[inline]
    pub fn to_bytes(&self) -> [u8; EXPANDED_SECRET_KEY_LENGTH] {
        let mut bytes: [u8; 64] = [0u8; 64];

        bytes[..32].copy_from_slice(self.key.as_bytes());
        bytes[32..].copy_from_slice(&self.nonce[..]);
        bytes
    }

    /// Construct an `ExpandedSecretKey` from a slice of bytes.
    ///
    /// # Returns
    ///
    /// A `Result` whose okay value is an EdDSA `ExpandedSecretKey` or whose
    /// error value is an `SignatureError` describing the error that occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # #[cfg(all(feature = "sha2", feature = "std"))]
    /// # fn do_test() -> Result<ExpandedSecretKey, SignatureError> {
    /// #
    /// use rand::{Rng, OsRng};
    /// use ed25519_dalek::{SecretKey, ExpandedSecretKey};
    /// use ed25519_dalek::SignatureError;
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    /// let expanded_secret_key: ExpandedSecretKey = ExpandedSecretKey::from(&secret_key);
    /// let bytes: [u8; 64] = expanded_secret_key.to_bytes();
    /// let expanded_secret_key_again = ExpandedSecretKey::from_bytes(&bytes)?;
    /// #
    /// # Ok(expanded_secret_key_again)
    /// # }
    /// #
    /// # #[cfg(all(feature = "sha2", feature = "std"))]
    /// # fn main() {
    /// #     let result = do_test();
    /// #     assert!(result.is_ok());
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<ExpandedSecretKey, SignatureError> {
        if bytes.len() != EXPANDED_SECRET_KEY_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError{
                name: "ExpandedSecretKey", length: EXPANDED_SECRET_KEY_LENGTH }));
        }
        let mut lower: [u8; 32] = [0u8; 32];
        let mut upper: [u8; 32] = [0u8; 32];

        lower.copy_from_slice(&bytes[00..32]);
        upper.copy_from_slice(&bytes[32..64]);

        Ok(ExpandedSecretKey{ key:   Scalar::from_bits(lower),
                              nonce:                   upper  })
    }

    /// Construct an `ExpandedSecretKey` from a `SecretKey`, using hash function `D`.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate rand;
    /// # extern crate sha2;
    /// # extern crate ed25519_dalek;
    /// #
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    /// #
    /// use rand::{Rng, OsRng};
    /// use sha2::Sha512;
    /// use ed25519_dalek::{SecretKey, ExpandedSecretKey};
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let secret_key: SecretKey = SecretKey::generate(&mut csprng);
    /// let expanded_secret_key: ExpandedSecretKey = ExpandedSecretKey::from_secret_key::<Sha512>(&secret_key);
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    pub fn from_secret_key<D>(secret_key: &SecretKey) -> ExpandedSecretKey
            where D: Digest<OutputSize = U64> + Default {
        let mut h: D = D::default();
        let mut hash:  [u8; 64] = [0u8; 64];
        let mut lower: [u8; 32] = [0u8; 32];
        let mut upper: [u8; 32] = [0u8; 32];

        h.input(secret_key.as_bytes());
        hash.copy_from_slice(h.result().as_slice());

        lower.copy_from_slice(&hash[00..32]);
        upper.copy_from_slice(&hash[32..64]);

        lower[0]  &= 248;
        lower[31] &=  63;
        lower[31] |=  64;

        ExpandedSecretKey{ key: Scalar::from_bits(lower), nonce: upper, }
    }

    /// Sign a message with this `ExpandedSecretKey`.
    #[allow(non_snake_case)]
    pub fn sign<D>(&self, message: &[u8], public_key: &PublicKey) -> Signature
            where D: Digest<OutputSize = U64> + Default {
        let mut h: D = D::default();
        let R: CompressedEdwardsY;
        let r: Scalar;
        let s: Scalar;
        let k: Scalar;

        h.input(&self.nonce);
        h.input(&message);

        r = Scalar::from_hash(h);
        R = (&r * &constants::ED25519_BASEPOINT_TABLE).compress();

        h = D::default();
        h.input(R.as_bytes());
        h.input(public_key.as_bytes());
        h.input(&message);

        k = Scalar::from_hash(h);
        s = &(&k * &self.key) + &r;

        Signature{ R, s }
    }

    /// Sign a `prehashed_message` with this `ExpandedSecretKey` using the
    /// Ed25519ph algorithm defined in [RFC8032 §5.1][rfc8032].
    ///
    /// # Inputs
    ///
    /// * `prehashed_message` is an instantiated hash digest with 512-bits of
    ///   output which has had the message to be signed previously fed into its
    ///   state.
    /// * `public_key` is a [`PublicKey`] which corresponds to this secret key.
    /// * `context` is an optional context string, up to 255 bytes inclusive,
    ///   which may be used to provide additional domain separation.  If not
    ///   set, this will default to an empty string.
    ///
    /// # Returns
    ///
    /// An Ed25519ph [`Signature`] on the `prehashed_message`.
    ///
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    #[allow(non_snake_case)]
    pub fn sign_prehashed<D>(&self,
                             prehashed_message: D,
                             public_key: &PublicKey,
                             context: Option<&'static [u8]>) -> Signature
        where D: Digest<OutputSize = U64> + Default
    {
        let mut h: D;
        let mut prehash: [u8; 64] = [0u8; 64];
        let R: CompressedEdwardsY;
        let r: Scalar;
        let s: Scalar;
        let k: Scalar;

        let ctx: &[u8] = context.unwrap_or(b""); // By default, the context is an empty string.

        debug_assert!(ctx.len() <= 255, "The context must not be longer than 255 octets.");

        let ctx_len: u8 = ctx.len() as u8;

        // Get the result of the pre-hashed message.
        prehash.copy_from_slice(prehashed_message.result().as_slice());

        // This is the dumbest, ten-years-late, non-admission of fucking up the
        // domain separation I have ever seen.  Why am I still required to put
        // the upper half "prefix" of the hashed "secret key" in here?  Why
        // can't the user just supply their own nonce and decide for themselves
        // whether or not they want a deterministic signature scheme?  Why does
        // the message go into what's ostensibly the signature domain separation
        // hash?  Why wasn't there always a way to provide a context string?
        //
        // ...
        //
        // This is a really fucking stupid bandaid, and the damned scheme is
        // still bleeding from malleability, for fuck's sake.
        h = D::default()
            .chain(b"SigEd25519 no Ed25519 collisions")
            .chain(&[1]) // Ed25519ph
            .chain(&[ctx_len])
            .chain(ctx)
            .chain(&self.nonce)
            .chain(&prehash[..]);

        r = Scalar::from_hash(h);
        R = (&r * &constants::ED25519_BASEPOINT_TABLE).compress();

        h = D::default()
            .chain(b"SigEd25519 no Ed25519 collisions")
            .chain(&[1]) // Ed25519ph
            .chain(&[ctx_len])
            .chain(ctx)
            .chain(R.as_bytes())
            .chain(public_key.as_bytes())
            .chain(&prehash[..]);

        k = Scalar::from_hash(h);
        s = &(&k * &self.key) + &r;

        Signature{ R, s }
    }

}

#[cfg(feature = "serde")]
impl Serialize for ExpandedSecretKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for ExpandedSecretKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'d> {
        struct ExpandedSecretKeyVisitor;

        impl<'d> Visitor<'d> for ExpandedSecretKeyVisitor {
            type Value = ExpandedSecretKey;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 expanded secret key as 64 bytes, as specified in RFC8032.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<ExpandedSecretKey, E> where E: SerdeError {
                ExpandedSecretKey::from_bytes(bytes).or(Err(SerdeError::invalid_length(bytes.len(), &self)))
            }
        }
        deserializer.deserialize_bytes(ExpandedSecretKeyVisitor)
    }
}

/// An ed25519 public key.
#[derive(Copy, Clone, Default, Eq, PartialEq)]
#[repr(C)]
pub struct PublicKey(pub (crate) CompressedEdwardsY);

impl Debug for PublicKey {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "PublicKey( CompressedEdwardsY( {:?} ))", self.0)
    }
}

impl PublicKey {
    /// Convert this public key to a byte array.
    #[inline]
    pub fn to_bytes(&self) -> [u8; PUBLIC_KEY_LENGTH] {
        self.0.to_bytes()
    }

    /// View this public key as a byte array.
    #[inline]
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; PUBLIC_KEY_LENGTH] {
        &(self.0).0
    }

    /// Construct a `PublicKey` from a slice of bytes.
    ///
    /// # Warning
    ///
    /// The caller is responsible for ensuring that the bytes passed into this
    /// method actually represent a `curve25519_dalek::curve::CompressedEdwardsY`
    /// and that said compressed point is actually a point on the curve.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate ed25519_dalek;
    /// #
    /// use ed25519_dalek::PublicKey;
    /// use ed25519_dalek::PUBLIC_KEY_LENGTH;
    /// use ed25519_dalek::SignatureError;
    ///
    /// # fn doctest() -> Result<PublicKey, SignatureError> {
    /// let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = [
    ///    215,  90, 152,   1, 130, 177,  10, 183, 213,  75, 254, 211, 201, 100,   7,  58,
    ///     14, 225, 114, 243, 218, 166,  35,  37, 175,   2,  26, 104, 247,   7,   81, 26];
    ///
    /// let public_key = PublicKey::from_bytes(&public_key_bytes)?;
    /// #
    /// # Ok(public_key)
    /// # }
    /// #
    /// # fn main() {
    /// #     doctest();
    /// # }
    /// ```
    ///
    /// # Returns
    ///
    /// A `Result` whose okay value is an EdDSA `PublicKey` or whose error value
    /// is an `SignatureError` describing the error that occurred.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<PublicKey, SignatureError> {
        if bytes.len() != PUBLIC_KEY_LENGTH {
            return Err(SignatureError(InternalError::BytesLengthError{
                name: "PublicKey", length: PUBLIC_KEY_LENGTH }));
        }
        let mut bits: [u8; 32] = [0u8; 32];
        bits.copy_from_slice(&bytes[..32]);

        Ok(PublicKey(CompressedEdwardsY(bits)))
    }

    /// Derive this public key from its corresponding `SecretKey`.
    #[allow(unused_assignments)]
    pub fn from_secret<D>(secret_key: &SecretKey) -> PublicKey
        where D: Digest<OutputSize = U64> + Default
    {
        let mut h:    D = D::default();
        let mut hash:   [u8; 64] = [0u8; 64];
        let mut digest: [u8; 32] = [0u8; 32];

        h.input(secret_key.as_bytes());
        hash.copy_from_slice(h.result().as_slice());

        digest.copy_from_slice(&hash[..32]);

        PublicKey::mangle_scalar_bits_and_multiply_by_basepoint_to_produce_public_key(&mut digest)
    }

    /// Derive this public key from its corresponding `ExpandedSecretKey`.
    pub fn from_expanded_secret(expanded_secret_key: &ExpandedSecretKey) -> PublicKey {
        let mut bits: [u8; 32] = expanded_secret_key.key.to_bytes();

        PublicKey::mangle_scalar_bits_and_multiply_by_basepoint_to_produce_public_key(&mut bits)
    }

    /// Internal utility function for mangling the bits of a (formerly
    /// mathematically well-defined) "scalar" and multiplying it to produce a
    /// public key.
    fn mangle_scalar_bits_and_multiply_by_basepoint_to_produce_public_key(bits: &mut [u8; 32]) -> PublicKey {
        bits[0]  &= 248;
        bits[31] &= 127;
        bits[31] |= 64;

        let pk = (&Scalar::from_bits(*bits) * &constants::ED25519_BASEPOINT_TABLE).compress().to_bytes();

        PublicKey(CompressedEdwardsY(pk))
    }

    /// Verify a signature on a message with this keypair's public key.
    ///
    /// # Return
    ///
    /// Returns `Ok(())` if the signature is valid, and `Err` otherwise.
    #[allow(non_snake_case)]
    pub fn verify<D>(&self, message: &[u8], signature: &Signature) -> Result<(), SignatureError>
            where D: Digest<OutputSize = U64> + Default
    {
        let mut h: D = D::default();
        let R: EdwardsPoint;
        let k: Scalar;

        let A: EdwardsPoint = match self.0.decompress() {
            Some(x) => x,
            None    => return Err(SignatureError(InternalError::PointDecompressionError)),
        };

        h.input(signature.R.as_bytes());
        h.input(self.as_bytes());
        h.input(&message);

        k = Scalar::from_hash(h);
        R = EdwardsPoint::vartime_double_scalar_mul_basepoint(&k, &(-A), &signature.s);

        if R.compress() == signature.R {
            Ok(())
        } else {
            Err(SignatureError(InternalError::VerifyError))
        }
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
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    #[allow(non_snake_case)]
    pub fn verify_prehashed<D>(&self,
                               prehashed_message: D,
                               context: Option<&[u8]>,
                               signature: &Signature) -> Result<(), SignatureError>
        where D: Digest<OutputSize = U64> + Default
    {
        let mut h: D = D::default();
        let R: EdwardsPoint;
        let k: Scalar;

        let ctx: &[u8] = context.unwrap_or(b"");
        debug_assert!(ctx.len() <= 255, "The context must not be longer than 255 octets.");

        let A: EdwardsPoint = match self.0.decompress() {
            Some(x) => x,
            None    => return Err(SignatureError(InternalError::PointDecompressionError)),
        };

        h.input(b"SigEd25519 no Ed25519 collisions");
        h.input(&[1]); // Ed25519ph
        h.input(&[ctx.len() as u8]);
        h.input(ctx);
        h.input(signature.R.as_bytes());
        h.input(self.as_bytes());
        h.input(prehashed_message.result().as_slice());

        k = Scalar::from_hash(h);
        R = EdwardsPoint::vartime_double_scalar_mul_basepoint(&k, &(-A), &signature.s);

        if R.compress() == signature.R {
            Ok(())
        } else {
            Err(SignatureError(InternalError::VerifyError))
        }
    }
}

impl From<ExpandedSecretKey> for PublicKey {
    fn from(source: ExpandedSecretKey) -> PublicKey {
        PublicKey::from_expanded_secret(&source)
    }
}

/// Verify a batch of `signatures` on `messages` with their respective `public_keys`.
///
/// # Inputs
///
/// * `messages` is a slice of byte slices, one per signed message.
/// * `signatures` is a slice of `Signature`s.
/// * `public_keys` is a slice of `PublicKey`s.
/// * `csprng` is an implementation of `Rng + CryptoRng`, such as `rand::ThreadRng`.
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
/// extern crate sha2;
///
/// use ed25519_dalek::verify_batch;
/// use ed25519_dalek::Keypair;
/// use ed25519_dalek::PublicKey;
/// use ed25519_dalek::Signature;
/// use rand::thread_rng;
/// use rand::ThreadRng;
/// use sha2::Sha512;
///
/// # fn main() {
/// let mut csprng: ThreadRng = thread_rng();
/// let keypairs: Vec<Keypair> = (0..64).map(|_| Keypair::generate::<Sha512, _>(&mut csprng)).collect();
/// let msg: &[u8] = b"They're good dogs Brant";
/// let messages: Vec<&[u8]> = (0..64).map(|_| msg).collect();
/// let signatures:  Vec<Signature> = keypairs.iter().map(|key| key.sign::<Sha512>(&msg)).collect();
/// let public_keys: Vec<PublicKey> = keypairs.iter().map(|key| key.public).collect();
///
/// let result = verify_batch::<Sha512>(&messages[..], &signatures[..], &public_keys[..]);
/// assert!(result.is_ok());
/// # }
/// ```
#[cfg(any(feature = "alloc", feature = "std"))]
#[allow(non_snake_case)]
pub fn verify_batch<D>(messages: &[&[u8]],
                       signatures: &[Signature],
                       public_keys: &[PublicKey]) -> Result<(), SignatureError>
    where D: Digest<OutputSize = U64> + Default
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
        let mut h: D = D::default();
        h.input(signatures[i].R.as_bytes());
        h.input(public_keys[i].as_bytes());
        h.input(&messages[i]);
        Scalar::from_hash(h)
    });

    // Multiply each H(R || A || M) by the random value
    let zhrams = hrams.zip(zs.iter()).map(|(hram, z)| hram * z);

    let Rs = signatures.iter().map(|sig| sig.R.decompress());
    let As = public_keys.iter().map(|pk| pk.0.decompress());
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

#[cfg(feature = "serde")]
impl Serialize for PublicKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_bytes(self.as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for PublicKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'d> {

        struct PublicKeyVisitor;

        impl<'d> Visitor<'d> for PublicKeyVisitor {
            type Value = PublicKey;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 public key as a 32-byte compressed point, as specified in RFC8032")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<PublicKey, E> where E: SerdeError {
                PublicKey::from_bytes(bytes).or(Err(SerdeError::invalid_length(bytes.len(), &self)))
            }
        }
        deserializer.deserialize_bytes(PublicKeyVisitor)
    }
}

/// An ed25519 keypair.
#[derive(Debug, Default)] // we derive Default in order to use the clear() method in Drop
#[repr(C)]
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
            return Err(SignatureError(InternalError::BytesLengthError{
                name: "Keypair", length: KEYPAIR_LENGTH}));
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
    /// extern crate sha2;
    /// extern crate ed25519_dalek;
    ///
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    ///
    /// use rand::Rng;
    /// use rand::OsRng;
    /// use sha2::Sha512;
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    ///
    /// let mut csprng: OsRng = OsRng::new().unwrap();
    /// let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
    ///
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    ///
    /// # Input
    ///
    /// A CSPRNG with a `fill_bytes()` method, e.g. `rand::ChaChaRng`.
    ///
    /// The caller must also supply a hash function which implements the
    /// `Digest` and `Default` traits, and which returns 512 bits of output.
    /// The standard hash function used for most ed25519 libraries is SHA-512,
    /// which is available with `use sha2::Sha512` as in the example above.
    /// Other suitable hash functions include Keccak-512 and Blake2b-512.
    pub fn generate<D, R>(csprng: &mut R) -> Keypair
        where D: Digest<OutputSize = U64> + Default,
              R: CryptoRng + Rng,
    {
        let sk: SecretKey = SecretKey::generate(csprng);
        let pk: PublicKey = PublicKey::from_secret::<D>(&sk);

        Keypair{ public: pk, secret: sk }
    }

    /// Sign a message with this keypair's secret key.
    pub fn sign<D>(&self, message: &[u8]) -> Signature
            where D: Digest<OutputSize = U64> + Default {
        self.secret.expand::<D>().sign::<D>(&message, &self.public)
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
    /// extern crate sha2;
    ///
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    /// use rand::thread_rng;
    /// use rand::ThreadRng;
    /// use sha2::Sha512;
    ///
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    /// let mut csprng: ThreadRng = thread_rng();
    /// let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
    /// let message: &[u8] = b"All I want is to pet all of the dogs.";
    ///
    /// // Create a hash digest object which we'll feed the message into:
    /// let prehashed: Sha512 = Sha512::default();
    ///
    /// prehashed.input(message);
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
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
    /// # extern crate sha2;
    /// #
    /// # use ed25519_dalek::Keypair;
    /// # use ed25519_dalek::Signature;
    /// # use rand::thread_rng;
    /// # use rand::ThreadRng;
    /// # use sha2::Sha512;
    /// #
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    /// # let mut csprng: ThreadRng = thread_rng();
    /// # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
    /// # let message: &[u8] = b"All I want is to pet all of the dogs.";
    /// # let prehashed: Sha512 = Sha512::default();
    /// # prehashed.input(message);
    /// #
    /// let context: &[u8] = b"Ed25519DalekSignPrehashedDoctest";
    ///
    /// let sig: Signature = keypair.sign_prehashed(prehashed, Some(context));
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    ///
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    /// [terrible_idea]: https://github.com/isislovecruft/scripts/blob/master/gpgkey2bc.py
    pub fn sign_prehashed<D>(&self,
                             prehashed_message: D,
                             context: Option<&'static [u8]>) -> Signature
        where D: Digest<OutputSize = U64> + Default
    {
        self.secret.expand::<D>().sign_prehashed::<D>(prehashed_message, &self.public, context)
    }

    /// Verify a signature on a message with this keypair's public key.
    pub fn verify<D>(&self, message: &[u8], signature: &Signature) -> Result<(), SignatureError>
            where D: Digest<OutputSize = U64> + Default {
        self.public.verify::<D>(message, signature)
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
    /// extern crate sha2;
    ///
    /// use ed25519_dalek::Keypair;
    /// use ed25519_dalek::Signature;
    /// use rand::thread_rng;
    /// use rand::ThreadRng;
    /// use sha2::Sha512;
    ///
    /// # #[cfg(all(feature = "std", feature = "sha2"))]
    /// # fn main() {
    /// let mut csprng: ThreadRng = thread_rng();
    /// let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
    /// let message: &[u8] = b"All I want is to pet all of the dogs.";
    ///
    /// let prehashed: Sha512 = Sha512::default();
    /// prehashed.input(message);
    ///
    /// let context: &[u8] = b"Ed25519DalekSignPrehashedDoctest";
    ///
    /// let sig: Signature = keypair.sign_prehashed(prehashed, Some(context));
    ///
    /// // The sha2::Sha512 struct doesn't implement Copy, so we'll have to create a new one:
    /// let prehashed_again: Sha512 = Sha512::default();
    /// prehashed_again.input(message);
    ///
    /// let valid: bool = keypair.public.verify_prehashed(prehashed_again, context, sig);
    ///
    /// assert!(valid);
    /// # }
    /// #
    /// # #[cfg(any(not(feature = "sha2"), not(feature = "std")))]
    /// # fn main() { }
    /// ```
    ///
    /// [rfc8032]: https://tools.ietf.org/html/rfc8032#section-5.1
    pub fn verify_prehashed<D>(&self,
                               prehashed_message: D,
                               context: Option<&[u8]>,
                               signature: &Signature) -> Result<(), SignatureError>
        where D: Digest<OutputSize = U64> + Default
    {
        self.public.verify_prehashed::<D>(prehashed_message, context, signature)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Keypair {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

#[cfg(feature = "serde")]
impl<'d> Deserialize<'d> for Keypair {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'d> {

        struct KeypairVisitor;

        impl<'d> Visitor<'d> for KeypairVisitor {
            type Value = Keypair;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("An ed25519 keypair, 64 bytes in total where the secret key is \
                                     the first 32 bytes and is in unexpanded form, and the second \
                                     32 bytes is a compressed point for a public key.")
            }

            fn visit_bytes<E>(self, bytes: &[u8]) -> Result<Keypair, E> where E: SerdeError {
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
    use std::io::BufReader;
    use std::io::BufRead;
    use std::fs::File;
    use std::string::String;
    use std::vec::Vec;
    use rand::thread_rng;
    use rand::ChaChaRng;
    use rand::SeedableRng;
    use rand::ThreadRng;
    use hex::FromHex;
    use sha2::Sha512;
    use super::*;

    #[cfg(all(test, feature = "serde"))]
    static PUBLIC_KEY: PublicKey = PublicKey(CompressedEdwardsY([
        130, 039, 155, 015, 062, 076, 188, 063,
        124, 122, 026, 251, 233, 253, 225, 220,
        014, 041, 166, 120, 108, 035, 254, 077,
        160, 083, 172, 058, 219, 042, 086, 120, ]));

    #[cfg(all(test, feature = "serde"))]
    static SECRET_KEY: SecretKey = SecretKey([
        062, 070, 027, 163, 092, 182, 011, 003,
        077, 234, 098, 004, 011, 127, 079, 228,
        243, 187, 150, 073, 201, 137, 076, 022,
        085, 251, 152, 002, 241, 042, 072, 054, ]);

    /// Signature with the above keypair of a blank message.
    #[cfg(all(test, feature = "serde"))]
    static SIGNATURE_BYTES: [u8; SIGNATURE_LENGTH] = [
        010, 126, 151, 143, 157, 064, 047, 001,
        196, 140, 179, 058, 226, 152, 018, 102,
        160, 123, 080, 016, 210, 086, 196, 028,
        053, 231, 012, 157, 169, 019, 158, 063,
        045, 154, 238, 007, 053, 185, 227, 229,
        079, 108, 213, 080, 124, 252, 084, 167,
        216, 085, 134, 144, 129, 149, 041, 081,
        063, 120, 126, 100, 092, 059, 050, 011, ];

    #[test]
    fn sign_verify() {  // TestSignVerify
        let mut csprng: ChaChaRng;
        let keypair: Keypair;
        let good_sig: Signature;
        let bad_sig:  Signature;

        let good: &[u8] = "test message".as_bytes();
        let bad:  &[u8] = "wrong message".as_bytes();

        csprng  = ChaChaRng::from_seed([0u8; 32]);
        keypair  = Keypair::generate::<Sha512, _>(&mut csprng);
        good_sig = keypair.sign::<Sha512>(&good);
        bad_sig  = keypair.sign::<Sha512>(&bad);

        assert!(keypair.verify::<Sha512>(&good, &good_sig).is_ok(),
                "Verification of a valid signature failed!");
        assert!(keypair.verify::<Sha512>(&good, &bad_sig).is_err(),
                "Verification of a signature on a different message passed!");
        assert!(keypair.verify::<Sha512>(&bad,  &good_sig).is_err(),
                "Verification of a signature on a different message passed!");
    }

    // TESTVECTORS is taken from sign.input.gz in agl's ed25519 Golang
    // package. It is a selection of test cases from
    // http://ed25519.cr.yp.to/python/sign.input
    #[cfg(test)]
    #[cfg(not(release))]
    #[test]
    fn golden() { // TestGolden
        let mut line: String;
        let mut lineno: usize = 0;

        let f = File::open("TESTVECTORS");
        if f.is_err() {
            println!("This test is only available when the code has been cloned \
                      from the git repository, since the TESTVECTORS file is large \
                      and is therefore not included within the distributed crate.");
            panic!();
        }
        let file = BufReader::new(f.unwrap());

        for l in file.lines() {
            lineno += 1;
            line = l.unwrap();

            let parts: Vec<&str> = line.split(':').collect();
            assert_eq!(parts.len(), 5, "wrong number of fields in line {}", lineno);

            let sec_bytes: Vec<u8> = FromHex::from_hex(&parts[0]).unwrap();
            let pub_bytes: Vec<u8> = FromHex::from_hex(&parts[1]).unwrap();
            let msg_bytes: Vec<u8> = FromHex::from_hex(&parts[2]).unwrap();
            let sig_bytes: Vec<u8> = FromHex::from_hex(&parts[3]).unwrap();

            let secret: SecretKey = SecretKey::from_bytes(&sec_bytes[..SECRET_KEY_LENGTH]).unwrap();
            let public: PublicKey = PublicKey::from_bytes(&pub_bytes[..PUBLIC_KEY_LENGTH]).unwrap();
            let keypair: Keypair  = Keypair{ secret: secret, public: public };

		    // The signatures in the test vectors also include the message
		    // at the end, but we just want R and S.
            let sig1: Signature = Signature::from_bytes(&sig_bytes[..64]).unwrap();
            let sig2: Signature = keypair.sign::<Sha512>(&msg_bytes);

            assert!(sig1 == sig2, "Signature bytes not equal on line {}", lineno);
            assert!(keypair.verify::<Sha512>(&msg_bytes, &sig2).is_ok(),
                    "Signature verification failed on line {}", lineno);
        }
    }

    // From https://tools.ietf.org/html/rfc8032#section-7.3
    #[test]
    fn ed25519ph_rf8032_test_vector() {
        let secret_key: &[u8] = b"833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42";
        let public_key: &[u8] = b"ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf";
        let message: &[u8] = b"616263";
        let signature: &[u8] = b"98a70222f0b8121aa9d30f813d683f809e462b469c7ff87639499bb94e6dae4131f85042463c2a355a2003d062adf5aaa10b8c61e636062aaad11c2a26083406";

        let sec_bytes: Vec<u8> = FromHex::from_hex(secret_key).unwrap();
        let pub_bytes: Vec<u8> = FromHex::from_hex(public_key).unwrap();
        let msg_bytes: Vec<u8> = FromHex::from_hex(message).unwrap();
        let sig_bytes: Vec<u8> = FromHex::from_hex(signature).unwrap();

        let secret: SecretKey = SecretKey::from_bytes(&sec_bytes[..SECRET_KEY_LENGTH]).unwrap();
        let public: PublicKey = PublicKey::from_bytes(&pub_bytes[..PUBLIC_KEY_LENGTH]).unwrap();
        let keypair: Keypair  = Keypair{ secret: secret, public: public };
        let sig1: Signature = Signature::from_bytes(&sig_bytes[..]).unwrap();

        let mut prehash_for_signing: Sha512 = Sha512::default();
        let mut prehash_for_verifying: Sha512 = Sha512::default();

        prehash_for_signing.input(&msg_bytes[..]);
        prehash_for_verifying.input(&msg_bytes[..]);

        let sig2: Signature = keypair.sign_prehashed(prehash_for_signing, None);

        assert!(sig1 == sig2,
                "Original signature from test vectors doesn't equal signature produced:\
                \noriginal:\n{:?}\nproduced:\n{:?}", sig1, sig2);
        assert!(keypair.verify_prehashed(prehash_for_verifying, None, &sig2).is_ok(),
                "Could not verify ed25519ph signature!");
    }

    #[test]
    fn ed25519ph_sign_verify() {
        let mut csprng: ChaChaRng;
        let keypair: Keypair;
        let good_sig: Signature;
        let bad_sig:  Signature;

        let good: &[u8] = b"test message";
        let bad:  &[u8] = b"wrong message";

        // ugh… there's no `impl Copy for Sha512`… i hope we can all agree these are the same hashes
        let mut prehashed_good1: Sha512 = Sha512::default();
        prehashed_good1.input(good);
        let mut prehashed_good2: Sha512 = Sha512::default();
        prehashed_good2.input(good);
        let mut prehashed_good3: Sha512 = Sha512::default();
        prehashed_good3.input(good);

        let mut prehashed_bad1: Sha512 = Sha512::default();
        prehashed_bad1.input(bad);
        let mut prehashed_bad2: Sha512 = Sha512::default();
        prehashed_bad2.input(bad);

        let context: &[u8] = b"testing testing 1 2 3";

        csprng   = ChaChaRng::from_seed([0u8; 32]);
        keypair  = Keypair::generate::<Sha512, _>(&mut csprng);
        good_sig = keypair.sign_prehashed::<Sha512>(prehashed_good1, Some(context));
        bad_sig  = keypair.sign_prehashed::<Sha512>(prehashed_bad1,  Some(context));

        assert!(keypair.verify_prehashed::<Sha512>(prehashed_good2, Some(context), &good_sig).is_ok(),
                "Verification of a valid signature failed!");
        assert!(keypair.verify_prehashed::<Sha512>(prehashed_good3, Some(context), &bad_sig).is_err(),
                "Verification of a signature on a different message passed!");
        assert!(keypair.verify_prehashed::<Sha512>(prehashed_bad2,  Some(context), &good_sig).is_err(),
                "Verification of a signature on a different message passed!");
    }

    #[test]
    fn verify_batch_seven_signatures() {
        let messages: [&[u8]; 7] = [
            b"Watch closely everyone, I'm going to show you how to kill a god.",
            b"I'm not a cryptographer I just encrypt a lot.",
            b"Still not a cryptographer.",
            b"This is a test of the tsunami alert system. This is only a test.",
            b"Fuck dumbin' it down, spit ice, skip jewellery: Molotov cocktails on me like accessories.",
            b"Hey, I never cared about your bucks, so if I run up with a mask on, probably got a gas can too.",
            b"And I'm not here to fill 'er up. Nope, we came to riot, here to incite, we don't want any of your stuff.", ];
        let mut csprng: ThreadRng = thread_rng();
        let mut keypairs: Vec<Keypair> = Vec::new();
        let mut signatures: Vec<Signature> = Vec::new();

        for i in 0..messages.len() {
            let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
            signatures.push(keypair.sign::<Sha512>(&messages[i]));
            keypairs.push(keypair);
        }
        let public_keys: Vec<PublicKey> = keypairs.iter().map(|key| key.public).collect();

        let result = verify_batch::<Sha512>(&messages, &signatures[..], &public_keys[..]);

        assert!(result.is_ok());
    }

    #[test]
    fn public_key_from_bytes() {
        // Make another function so that we can test the ? operator.
        fn do_the_test() -> Result<PublicKey, SignatureError> {
            let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = [
                215, 090, 152, 001, 130, 177, 010, 183,
                213, 075, 254, 211, 201, 100, 007, 058,
                014, 225, 114, 243, 218, 166, 035, 037,
                175, 002, 026, 104, 247, 007, 081, 026, ];
            let public_key = PublicKey::from_bytes(&public_key_bytes)?;

            Ok(public_key)
        }
        assert_eq!(do_the_test(), Ok(PublicKey(CompressedEdwardsY([
            215, 090, 152, 001, 130, 177, 010, 183,
            213, 075, 254, 211, 201, 100, 007, 058,
            014, 225, 114, 243, 218, 166, 035, 037,
            175, 002, 026, 104, 247, 007, 081, 026, ]))))
    }

    #[test]
    fn keypair_clear_on_drop() {
        let mut keypair: Keypair = Keypair::from_bytes(&[15u8; KEYPAIR_LENGTH][..]).unwrap();

        keypair.clear();

        fn as_bytes<T>(x: &T) -> &[u8] {
            use core::mem;
            use core::slice;

            unsafe {
                slice::from_raw_parts(x as *const T as *const u8, mem::size_of_val(x))
            }
        }

        assert!(!as_bytes(&keypair).contains(&0x15));
    }

    #[test]
    fn pubkey_from_secret_and_expanded_secret() {
        let mut csprng = thread_rng();
        let secret: SecretKey = SecretKey::generate::<_>(&mut csprng);
        let expanded_secret: ExpandedSecretKey = ExpandedSecretKey::from_secret_key::<Sha512>(&secret);
        let public_from_secret: PublicKey = PublicKey::from_secret::<Sha512>(&secret);
        let public_from_expanded_secret: PublicKey = PublicKey::from_expanded_secret(&expanded_secret);

        assert!(public_from_secret == public_from_expanded_secret);
    }

    #[cfg(all(test, feature = "serde"))]
    use bincode::{serialize, deserialize, Infinite};

    #[cfg(all(test, feature = "serde"))]
    #[test]
    fn serialize_deserialize_signature() {
        let signature: Signature = Signature::from_bytes(&SIGNATURE_BYTES).unwrap();
        let encoded_signature: Vec<u8> = serialize(&signature, Infinite).unwrap();
        let decoded_signature: Signature = deserialize(&encoded_signature).unwrap();

        assert_eq!(signature, decoded_signature);
    }

    #[cfg(all(test, feature = "serde"))]
    #[test]
    fn serialize_deserialize_public_key() {
        let encoded_public_key: Vec<u8> = serialize(&PUBLIC_KEY, Infinite).unwrap();
        let decoded_public_key: PublicKey = deserialize(&encoded_public_key).unwrap();

        assert_eq!(PUBLIC_KEY, decoded_public_key);
    }

    #[cfg(all(test, feature = "serde"))]
    #[test]
    fn serialize_deserialize_secret_key() {
        let encoded_secret_key: Vec<u8> = serialize(&SECRET_KEY, Infinite).unwrap();
        let decoded_secret_key: SecretKey = deserialize(&encoded_secret_key).unwrap();

        for i in 0..32 {
            assert_eq!(SECRET_KEY.0[i], decoded_secret_key.0[i]);
        }
    }
}
