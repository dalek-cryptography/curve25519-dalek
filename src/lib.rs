// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
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
//! secure pseudorandom number generator (CSPRING), and a hash function which
//! has 512 bits of output.  For this example, we'll use the operating
//! system's builtin PRNG and SHA-512 to generate a keypair:
//!
//! ```
//! extern crate rand;
//! extern crate sha2;
//! extern crate ed25519_dalek;
//!
//! # fn main() {
//! use rand::Rng;
//! use rand::OsRng;
//! use sha2::Sha512;
//! use ed25519_dalek::Keypair;
//! use ed25519_dalek::Signature;
//!
//! let mut cspring: OsRng = OsRng::new().unwrap();
//! let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
//! # }
//! ```
//!
//! We can now use this `keypair` to sign a message:
//!
//! ```
//! # extern crate rand;
//! # extern crate sha2;
//! # extern crate ed25519_dalek;
//! # fn main() {
//! # use rand::Rng;
//! # use rand::OsRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! # let mut cspring: OsRng = OsRng::new().unwrap();
//! # let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
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
//! # fn main() {
//! # use rand::Rng;
//! # use rand::OsRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! # let mut cspring: OsRng = OsRng::new().unwrap();
//! # let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! let verified: bool = keypair.verify::<Sha512>(message, &signature);
//!
//! assert!(verified);
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
//! # fn main() {
//! # use rand::Rng;
//! # use rand::OsRng;
//! # use sha2::Sha512;
//! # use ed25519_dalek::Keypair;
//! # use ed25519_dalek::Signature;
//! use ed25519_dalek::PublicKey;
//! # let mut cspring: OsRng = OsRng::new().unwrap();
//! # let keypair: Keypair = Keypair::generate::<Sha512>(&mut cspring);
//! # let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! # let signature: Signature = keypair.sign::<Sha512>(message);
//! let public_key: PublicKey = keypair.public;
//! let verified: bool = public_key.verify::<Sha512>(message, &signature);
//!
//! assert!(verified);
//! # }
//! ```

#![no_std]
#![cfg_attr(feature = "nightly", feature(rand))]
#![allow(unused_features)]
#![cfg_attr(feature = "bench", feature(test))]
#![deny(missing_docs)] // refuse to compile if documentation is missing

#[macro_use]
extern crate arrayref;
extern crate curve25519_dalek;
extern crate generic_array;
extern crate digest;

#[cfg(feature = "std")]
extern crate rand;

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
extern crate sha2;

#[cfg(test)]
extern crate rustc_serialize;

#[cfg(all(test, feature = "bench"))]
extern crate test;


mod ed25519;

// Export everything public in ed25519.
pub use ed25519::*;
