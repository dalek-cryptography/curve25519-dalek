// scalar_verus.rs
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
// use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

// use the shared verus definitions
use super::common_verus::*;

verus! {

// ## Constants
// 
// - Prime order of the Ristretto group and the Ed25519 basepoint:
//   ℓ = 2^{252} + 27742317777372353535851937790883648493
//
// - Cofactor of curve25519:
//   h = 8
//
// In all cases the 32 byte value is interpreted as an integer in little endian format (`as_nat_32_u8`)

// ## Specification for:
// `curve25519_dalek::scalar::Scalar`
// `pub fn from_bytes_mod_order(bytes: [u8; 32]) -> Scalar`
//
// 1. Result is equal to the input mod ℓ

// ## Specification for:
// `curve25519_dalek::scalar::Scalar`
// `pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> Scalar`
//
// 1. Result is equal to the input mod ℓ

// ## Specification for:
// `curve25519_dalek::scalar::Scalar`
// `pub fn from_canonical_bytes(bytes: [u8; 32]) -> CtOption<Scalar>``
//
// 1. Outputs none if input represents an integer which is greater than of equal to ℓ
// 2. Otherwise outputs the input

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub const ZERO
//
// 1. Equal to 0

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub const ONE
//
// 1. Equal to 1

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub fn random<R>(rng: &mut R) -> Self
//
// 1. Returns a valid scalar (i.e., corresponds to an integer in {0, 1,..., ℓ - 1})
// 2. Uniformly random in {0, 1,..., ℓ - 1}

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub fn hash_from_bytes<D>(input: &[u8]) -> Scalar
//
// 1. Output is a valid scalar, i.e. an integer less than ℓ
// 2. Function is deterministic, same input always gives the same output
// 3. Uniform distribution in {0, 1,..., ℓ - 1}

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub fn from_hash<D>(hash: D) -> Scalar
//
// 1. Output is a valid scalar, i.e. an integer less than ℓ
// 2. Function is deterministic, same input always gives the same output
// 3. Uniform distribution in {0, 1,..., ℓ - 1}

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub const fn to_bytes(&self) -> [u8; 32]
//
// 1. Output equal to self

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub const fn as_bytes(&self) -> [u8; 32]
//
// 1. Output equal to self (same as above but pointer version)

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub fn invert(&self) -> Scalar
//
// 1. If self ≠ 0, self * result = 1 (mod ℓ)

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub fn batch_invert(inputs: &mut [Scalar]) -> Scalar
//
// 1. Same as above but for a batch of scalars

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_
//
// 1. Output is equal to self

// ## Specification for:
// curve25519_dalek::scalar::Scalar
// pub(crate) fn non_adjacent_form(&self, w: usize) -> [i8; 256]
// Permitted in source only for (2 <= w <= 8)
// Called "w-Non-Adjacent Form"
// 
// let n_i denote the output
//
// 1. k = \sum_i n_i 2^i,
// 2. each nonzero coefficient n_i is odd
// 3. each nonzero coefficient is bounded |n_i| < 2^{w-1}
// 4. n_{m-1} is nonzero
// 5. at most one of any w consecutive coefficients is nonzero

// ## Specification for:


// ## Specification for:


// ## Specification for:


// ## Specification for:


// ## Specification for:


// ## Specification for:


// ## Specification for:


// ## Specification for:
// `curve25519_dalek::scalar``
// `pub const fn clamp_integer(mut bytes: [u8; 32]) -> [u8; 32]`
// 
// Let n denote the 32 byte output interpreted as an integer in little endian format (`as_nat_32_u8`)
//
// 1. 2^254 ≤ n
// 2. n < 2^255
// 3. n is divisible by 8 (the cofactor of curve25519)
// 4. If the input is uniformly random then the output is uniformly random
//
// [Further info](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/)


}
