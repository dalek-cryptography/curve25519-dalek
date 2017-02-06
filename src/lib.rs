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
//! First, we need to generate a `Keypair`, which includes both public
//! and secret halves of an asymmetric key.  To do so, we need a
//! cryptographically secure random number generator (CSPRING).  For
//! this example, we'll use the operating system's builtin PRNG to
//! generate a keypair:
//!
//! ```ignore
//! extern crate rand;
//! extern crate ed25519;
//!
//! use rand::Rng;
//! use rand::OsRng;
//! use ed25519::Keypair;
//!
//! let mut cspring: OsRng = OsRng::new().unwrap();
//! let keypair: Keypair = Keypair::generate(&mut cspring);
//! ```
//!
//! We can now use this `keypair` to sign a message:
//!
//! ```ignore
//! let message: &[u8] = "This is a test of the tsunami alert system.".as_bytes();
//! let signature: Signature = keypair.sign(message);
//! ```
//!
//! As well as to verify that this is, indeed, a valid signature on
//! that `message`:
//!
//! ```ignore
//! let verified: bool = keypair.verify(message, &signature);
//!
//! assert!(verified);
//! ```
//!
//! Anyone else, given the `public` half of the `keypair` can also easily
//! verify this signature:
//!
//! ```ignore
//! let public_key: PublicKey = keypair.public;
//! let verified: bool = public_key.verify(message, &signature);
//!
//! assert!(verified);
//! ```

#![no_std]
#![feature(rand)]
#![allow(unused_features)]
#![feature(test)]

#[macro_use]
extern crate arrayref;
extern crate sha2;
extern crate curve25519_dalek;

#[cfg(feature = "std")]
extern crate rand;

#[cfg(test)]
#[macro_use]
extern crate std;
#[cfg(test)]
extern crate test;
#[cfg(test)]
extern crate rustc_serialize;

mod ed25519;

// Export everything public in ed25519.
pub use ed25519::*;
