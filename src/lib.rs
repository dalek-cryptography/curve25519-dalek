// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

//! A Rust implementation of ed25519 key generation, signing, and verification.
//!
//! # Example
//!
//! Creating an ed25519 signature on a message is simple.
//!
//! First, we need to generate a `Keypair`, which includes both public and
//! secret halves of an asymmetric key.  To do so, we need a cryptographically
//! secure pseudorandom number generator (CSPRNG). For this example, we'll use
//! the operating system's builtin PRNG:
//!
//! ```
//! # #[cfg(feature = "std")]
//! # fn main() {
//! use rand::rngs::OsRng;
//! use ed25519_dalek::Keypair;
//! use ed25519_dalek::Signature;
//!
//! let mut csprng = OsRng{};
//! let keypair: Keypair = Keypair::generate(&mut csprng);
//! # }
//! #
//! # #[cfg(not(feature = "std"))]
//! # fn main() { }
//! ```
//!
//! We can now use this `keypair` to sign a message:
//!
//! ```
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::Keypair;
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! use ed25519_dalek::{Signature, Signer};
//! let message: &[u8] = b"This is a test of the tsunami alert system.";
//! let signature: Signature = keypair.sign(message);
//! # }
//! ```
//!
//! As well as to verify that this is, indeed, a valid signature on
//! that `message`:
//!
//! ```
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::{Keypair, Signature, Signer};
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! # let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature: Signature = keypair.sign(message);
//! use ed25519_dalek::Verifier;
//! assert!(keypair.verify(message, &signature).is_ok());
//! # }
//! ```
//!
//! Anyone else, given the `public` half of the `keypair` can also easily
//! verify this signature:
//!
//! ```
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! # use ed25519_dalek::Signer;
//! use ed25519_dalek::{PublicKey, Verifier};
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! # let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature: Signature = keypair.sign(message);
//!
//! let public_key: PublicKey = keypair.public_key();
//! assert!(public_key.verify(message, &signature).is_ok());
//! # }
//! ```
//!
//! ## Serialisation
//!
//! `PublicKey`s, `SecretKey`s, `Keypair`s, and `Signature`s can be serialised
//! into byte-arrays by calling `.to_bytes()`.  It's perfectly acceptible and
//! safe to transfer and/or store those bytes.  (Of course, never transfer your
//! secret key to anyone else, since they will only need the public key to
//! verify your signatures!)
//!
//! ```
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::{Keypair, Signature, Signer, PublicKey};
//! use ed25519_dalek::{PUBLIC_KEY_LENGTH, SECRET_KEY_LENGTH, KEYPAIR_LENGTH, SIGNATURE_LENGTH};
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! # let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature: Signature = keypair.sign(message);
//!
//! let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = keypair.public_key().to_bytes();
//! let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = keypair.secret_key().to_bytes();
//! let keypair_bytes:    [u8; KEYPAIR_LENGTH]    = keypair.to_bytes();
//! let signature_bytes:  [u8; SIGNATURE_LENGTH]  = signature.to_bytes();
//! # }
//! ```
//!
//! And similarly, decoded from bytes with `::from_bytes()`:
//!
//! ```
//! # use std::convert::TryFrom;
//! # use rand::rngs::OsRng;
//! # use std::convert::TryInto;
//! # use ed25519_dalek::{Keypair, Signature, Signer, PublicKey, SecretKey, SignatureError};
//! # use ed25519_dalek::{PUBLIC_KEY_LENGTH, SECRET_KEY_LENGTH, KEYPAIR_LENGTH, SIGNATURE_LENGTH};
//! # fn do_test() -> Result<(SecretKey, PublicKey, Keypair, Signature), SignatureError> {
//! # let mut csprng = OsRng{};
//! # let keypair_orig: Keypair = Keypair::generate(&mut csprng);
//! # let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature_orig: Signature = keypair_orig.sign(message);
//! # let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = keypair_orig.public_key().to_bytes();
//! # let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = keypair_orig.secret_key().to_bytes();
//! # let keypair_bytes:    [u8; KEYPAIR_LENGTH]    = keypair_orig.to_bytes();
//! # let signature_bytes:  [u8; SIGNATURE_LENGTH]  = signature_orig.to_bytes();
//! #
//! let public_key: PublicKey = PublicKey::from_bytes(&public_key_bytes)?;
//! let secret_key: SecretKey = SecretKey::from_bytes(&secret_key_bytes)?;
//! let keypair:    Keypair   = Keypair::from_bytes(&keypair_bytes)?;
//! let signature:  Signature = Signature::try_from(&signature_bytes[..])?;
//! #
//! # Ok((secret_key, public_key, keypair, signature))
//! # }
//! # fn main() {
//! #     do_test();
//! # }
//! ```
//!
//! ### PKCS#8 Key Encoding
//!
//! PKCS#8 is a private key format with support for multiple algorithms.
//! It can be encoded as binary (DER) or text (PEM).
//!
//! You can recognize PEM-encoded PKCS#8 keys by the following:
//!
//! ```text
//! -----BEGIN PRIVATE KEY-----
//! ```
//!
//! To use PKCS#8, you need to enable the `pkcs8` crate feature.
//!
//! The following traits can be used to decode/encode [`Keypair`] and
//! [`PublicKey`] as PKCS#8. Note that [`pkcs8`] is re-exported from the
//! toplevel of the crate:
//!
//! - [`pkcs8::DecodePrivateKey`]: decode private keys from PKCS#8
//! - [`pkcs8::EncodePrivateKey`]: encode private keys to PKCS#8
//! - [`pkcs8::DecodePublicKey`]: decode public keys from PKCS#8
//! - [`pkcs8::EncodePublicKey`]: encode public keys to PKCS#8
//!
//! #### Example
//!
//! NOTE: this requires the `pem` crate feature.
//!
#![cfg_attr(feature = "pem", doc = "```")]
#![cfg_attr(not(feature = "pem"), doc = "```ignore")]
//! use ed25519_dalek::{PublicKey, pkcs8::DecodePublicKey};
//!
//! let pem = "-----BEGIN PUBLIC KEY-----
//! MCowBQYDK2VwAyEAGb9ECWmEzf6FQbrBZ9w7lshQhqowtrbLDFw4rXAxZuE=
//! -----END PUBLIC KEY-----";
//!
//! let public_key = PublicKey::from_public_key_pem(pem)
//!     .expect("invalid public key PEM");
//! ```
//!
//! ### Using Serde
//!
//! If you prefer the bytes to be wrapped in another serialisation format, all
//! types additionally come with built-in [serde](https://serde.rs) support by
//! building `ed25519-dalek` via:
//!
//! ```bash
//! $ cargo build --features="serde"
//! ```
//!
//! They can be then serialised into any of the wire formats which serde supports.
//! For example, using [bincode](https://github.com/TyOverby/bincode):
//!
//! ```
//! # #[cfg(feature = "serde")]
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::{Keypair, Signature, Signer, Verifier, PublicKey};
//! use bincode::serialize;
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! # let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature: Signature = keypair.sign(message);
//! # let public_key: PublicKey = keypair.public_key();
//! # let verified: bool = public_key.verify(message, &signature).is_ok();
//!
//! let encoded_public_key: Vec<u8> = serialize(&public_key).unwrap();
//! let encoded_signature: Vec<u8> = serialize(&signature).unwrap();
//! # }
//! # #[cfg(not(feature = "serde"))]
//! # fn main() {}
//! ```
//!
//! After sending the `encoded_public_key` and `encoded_signature`, the
//! recipient may deserialise them and verify:
//!
//! ```
//! # #[cfg(feature = "serde")]
//! # fn main() {
//! # use rand::rngs::OsRng;
//! # use ed25519_dalek::{Keypair, Signature, Signer, Verifier, PublicKey};
//! # use bincode::serialize;
//! use bincode::deserialize;
//!
//! # let mut csprng = OsRng{};
//! # let keypair: Keypair = Keypair::generate(&mut csprng);
//! let message: &[u8] = b"This is a test of the tsunami alert system.";
//! # let signature: Signature = keypair.sign(message);
//! # let public_key: PublicKey = keypair.public_key();
//! # let verified: bool = public_key.verify(message, &signature).is_ok();
//! # let encoded_public_key: Vec<u8> = serialize(&public_key).unwrap();
//! # let encoded_signature: Vec<u8> = serialize(&signature).unwrap();
//! let decoded_public_key: PublicKey = deserialize(&encoded_public_key).unwrap();
//! let decoded_signature: Signature = deserialize(&encoded_signature).unwrap();
//!
//! # assert_eq!(public_key, decoded_public_key);
//! # assert_eq!(signature, decoded_signature);
//! #
//! let verified: bool = decoded_public_key.verify(&message, &decoded_signature).is_ok();
//!
//! assert!(verified);
//! # }
//! # #[cfg(not(feature = "serde"))]
//! # fn main() {}
//! ```

#![no_std]
#![warn(future_incompatible, rust_2018_idioms)]
#![deny(missing_docs)] // refuse to compile if documentation is missing
#![cfg_attr(not(test), forbid(unsafe_code))]
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(docsrs)))]

#[cfg(any(feature = "batch", feature = "batch_deterministic"))]
extern crate alloc;

#[cfg(any(feature = "std", test))]
#[macro_use]
extern crate std;

#[cfg(feature = "serde")]
extern crate serde_crate as serde;

pub use ed25519;

#[cfg(any(feature = "batch", feature = "batch_deterministic"))]
mod batch;
mod constants;
mod errors;
mod keypair;
mod public;
mod secret;
mod signature;

pub use curve25519_dalek::digest::Digest;

#[cfg(any(feature = "batch", feature = "batch_deterministic"))]
pub use crate::batch::*;
pub use crate::constants::*;
pub use crate::errors::*;
pub use crate::keypair::*;
pub use crate::public::*;
pub use crate::secret::*;

// Re-export the `Signer` and `Verifier` traits from the `signature` crate
pub use ed25519::signature::{Signer, Verifier};
pub use ed25519::Signature;

#[cfg(feature = "pkcs8")]
pub use ed25519::pkcs8;
