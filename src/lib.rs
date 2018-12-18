// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2018 Isis Lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! ed25519 signatures and verification
//!
//! # Example
//!
//! Creating an ed25519 signature on a message is simple.
//!
//! First, we need to generate a `Keypair`, which includes both public and
//! secret halves of an asymmetric key.  To do so, we need a cryptographically
//! secure pseudorandom number generator (CSPRNG), and a hash function which
//! has 512 bits of output.  For this example, we'll use the operating
//! system's builtin PRNG and SHA-512 to generate a keypair:
//!
//! ```
//! extern crate rand;
//! extern crate sha2;
//! extern crate ed25519_dalek;
//!
//! # #[cfg(all(feature = "std", feature = "sha2"))]
//! # fn main() {
//! use rand::Rng;
//! use rand::OsRng;
//! use sha2::Sha512;
//! use ed25519_dalek::Keypair;
//! use ed25519_dalek::Signature;
//!
//! let mut csprng: OsRng = OsRng::new().unwrap();
//! let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # }
//! #
//! # #[cfg(any(not(feature = "std"), not(feature = "sha2")))]
//! # fn main() { }
//! ```
//!
//! We can now use this `keypair` to sign a message:
//!
//! ```
//! # extern crate rand;
//! # extern crate rand_chacha;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # fn main() {
//! # use rand::Rng;
//! # use rand_chacha::ChaChaRng;
//! # use rand::SeedableRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! let signature: Signature = keypair.sign::<Sha512>(message);
//! # }
//! ```
//!
//! As well as to verify that this is, indeed, a valid signature on
//! that `message`:
//!
//! ```
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # extern crate rand_chacha;
//! # fn main() {
//! # use rand::Rng;
//! # use rand_chacha::ChaChaRng;
//! # use rand::SeedableRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! assert!(keypair.verify::<Sha512>(message, &signature).is_ok());
//! # }
//! ```
//!
//! Anyone else, given the `public` half of the `keypair` can also easily
//! verify this signature:
//!
//! ```
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # extern crate rand_chacha;
//! # fn main() {
//! # use rand::Rng;
//! # use rand_chacha::ChaChaRng;
//! # use rand::SeedableRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! use ed25519_dalek::PublicKey;
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//!
//! let public_key: PublicKey = keypair.public;
//! assert!(public_key.verify::<Sha512>(message, &signature).is_ok());
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
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # extern crate rand_chacha;
//! # fn main() {
//! # use rand::{Rng, SeedableRng};
//! # use rand_chacha::ChaChaRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::{Keypair, Signature, PublicKey};
//! use ed25519_dalek::{PUBLIC_KEY_LENGTH, SECRET_KEY_LENGTH, KEYPAIR_LENGTH, SIGNATURE_LENGTH};
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! # let public_key: PublicKey = keypair.public;
//!
//! let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = public_key.to_bytes();
//! let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = keypair.secret.to_bytes();
//! let keypair_bytes:    [u8; KEYPAIR_LENGTH]    = keypair.to_bytes();
//! let signature_bytes:  [u8; SIGNATURE_LENGTH]  = signature.to_bytes();
//! # }
//! ```
//!
//! And similarly, decoded from bytes with `::from_bytes()`:
//!
//! ```
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate rand_chacha;
//! # extern crate ed25519_dalek;
//! # use rand::{Rng, SeedableRng};
//! # use rand_chacha::ChaChaRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::{Keypair, Signature, PublicKey, SecretKey, SignatureError};
//! # use ed25519_dalek::{PUBLIC_KEY_LENGTH, SECRET_KEY_LENGTH, KEYPAIR_LENGTH, SIGNATURE_LENGTH};
//! # fn do_test() -> Result<(SecretKey, PublicKey, Keypair, Signature), SignatureError> {
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair_orig: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature_orig: Signature = keypair_orig.sign::<Sha512>(message);
//! # let public_key_bytes: [u8; PUBLIC_KEY_LENGTH] = keypair_orig.public.to_bytes();
//! # let secret_key_bytes: [u8; SECRET_KEY_LENGTH] = keypair_orig.secret.to_bytes();
//! # let keypair_bytes:    [u8; KEYPAIR_LENGTH]    = keypair_orig.to_bytes();
//! # let signature_bytes:  [u8; SIGNATURE_LENGTH]  = signature_orig.to_bytes();
//! #
//! let public_key: PublicKey = PublicKey::from_bytes(&public_key_bytes)?;
//! let secret_key: SecretKey = SecretKey::from_bytes(&secret_key_bytes)?;
//! let keypair:    Keypair   = Keypair::from_bytes(&keypair_bytes)?;
//! let signature:  Signature = Signature::from_bytes(&signature_bytes)?;
//! #
//! # Ok((secret_key, public_key, keypair, signature))
//! # }
//! # fn main() {
//! #     do_test();
//! # }
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
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # extern crate rand_chacha;
//! # #[cfg(feature = "serde")]
//! extern crate serde;
//! # #[cfg(feature = "serde")]
//! extern crate bincode;
//!
//! # #[cfg(feature = "serde")]
//! # fn main() {
//! # use rand::{Rng, SeedableRng};
//! # use rand_chacha::ChaChaRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::{Keypair, Signature, PublicKey};
//! use bincode::{serialize, Infinite};
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! # let public_key: PublicKey = keypair.public;
//! # let verified: bool = public_key.verify::<Sha512>(message, &signature).is_ok();
//!
//! let encoded_public_key: Vec<u8> = serialize(&public_key, Infinite).unwrap();
//! let encoded_signature: Vec<u8> = serialize(&signature, Infinite).unwrap();
//! # }
//! # #[cfg(not(feature = "serde"))]
//! # fn main() {}
//! ```
//!
//! After sending the `encoded_public_key` and `encoded_signature`, the
//! recipient may deserialise them and verify:
//!
//! ```
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # extern crate rand_chacha;
//! # #[cfg(feature = "serde")]
//! # extern crate serde;
//! # #[cfg(feature = "serde")]
//! # extern crate bincode;
//! #
//! # #[cfg(feature = "serde")]
//! # fn main() {
//! # use rand::{Rng, SeedableRng};
//! # use rand_chacha::ChaChaRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::{Keypair, Signature, PublicKey};
//! # use bincode::{serialize, Infinite};
//! use bincode::{deserialize};
//!
//! # let mut csprng: ChaChaRng = ChaChaRng::from_seed([0u8; 32]);
//! # let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
//! let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! # let public_key: PublicKey = keypair.public;
//! # let verified: bool = public_key.verify::<Sha512>(message, &signature).is_ok();
//! # let encoded_public_key: Vec<u8> = serialize(&public_key, Infinite).unwrap();
//! # let encoded_signature: Vec<u8> = serialize(&signature, Infinite).unwrap();
//! let decoded_public_key: PublicKey = deserialize(&encoded_public_key).unwrap();
//! let decoded_signature: Signature = deserialize(&encoded_signature).unwrap();
//!
//! # assert_eq!(public_key, decoded_public_key);
//! # assert_eq!(signature, decoded_signature);
//! #
//! let verified: bool = decoded_public_key.verify::<Sha512>(&message, &decoded_signature).is_ok();
//!
//! assert!(verified);
//! # }
//! # #[cfg(not(feature = "serde"))]
//! # fn main() {}
//! ```

#![no_std]
#![allow(unused_features)]
#![deny(missing_docs)] // refuse to compile if documentation is missing

extern crate clear_on_drop;
extern crate curve25519_dalek;
extern crate failure;
extern crate rand;

#[cfg(any(feature = "std", test))]
#[macro_use]
extern crate std;

#[cfg(any(test, feature = "sha2"))]
extern crate sha2;

#[cfg(test)]
extern crate hex;

#[cfg(test)]
extern crate rand_chacha;

#[cfg(feature = "serde")]
extern crate serde;

#[cfg(all(test, feature = "serde"))]
extern crate bincode;

mod ed25519;

pub mod errors;

// Export everything public in ed25519.
pub use ed25519::*;
pub use errors::*;
