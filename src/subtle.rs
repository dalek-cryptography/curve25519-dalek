// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to curve25519-dalek, using the Creative
// Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Constant-time traits and utility functions.

use core::ops::Neg;

/// Trait for items which can be conditionally assigned in constant time.
pub trait CTAssignable {
    /// If `choice == 1u8`, assign `other` to `self`.
    /// Otherwise, leave `self` unchanged.
    /// Executes in constant time.
    fn conditional_assign(&mut self, other: &Self, choice: u8);
}

/// Trait for items whose equality to another item may be tested in constant time.
pub trait CTEq {
    /// Determine if two items are equal in constant time.
    ///
    /// # Returns
    ///
    /// `1u8` if the two items are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &Self) -> u8;
}

/// Trait for items which can be conditionally negated in constant time.
///
/// Note: it is not necessary to implement this trait, as a generic
/// implementation is provided.
pub trait CTNegatable
{
    /// Conditionally negate an element if `choice == 1u8`.
    fn conditional_negate(&mut self, choice: u8);
}

impl<T> CTNegatable for T
    where T: CTAssignable, for<'a> &'a T: Neg<Output=T>
{
    fn conditional_negate(&mut self, choice: u8) {
        // Need to cast to eliminate mutability
        let self_neg: T = -(self as &T);
        self.conditional_assign(&self_neg, choice);
    }
}

/// Check equality of two bytes in constant time.
///
/// # Return
///
/// Returns `1u8` if `a == b` and `0u8` otherwise.
#[inline(always)]
pub fn bytes_equal_ct(a: u8, b: u8) -> u8 {
    let mut x: u8;

    x  = !(a ^ b);
    x &= x >> 4;
    x &= x >> 2;
    x &= x >> 1;
    x
}

/// Test if a byte is non-zero in constant time.
///
/// ```
/// # extern crate curve25519_dalek;
/// # use curve25519_dalek::subtle::byte_is_nonzero;
/// # fn main() {
/// let mut x: u8;
/// x = 0;
/// assert!(byte_is_nonzero(x) == 0);
/// x = 3;
/// assert!(byte_is_nonzero(x) == 1);
/// # }
/// ```
///
/// # Return
///
/// * If b != 0, returns 1u8.
/// * If b == 0, returns 0u8.
#[inline(always)]
pub fn byte_is_nonzero(b: u8) -> u8 {
    let mut x = b;
    x |= x >> 4;
    x |= x >> 2;
    x |= x >> 1;
    (x & 1)
}

/// Check equality of two 32-byte arrays in constant time.
///
/// If the contents of the arrays do *not* match,
/// `0u8` will be returned:
///
/// ```
/// # extern crate curve25519_dalek;
/// # use curve25519_dalek::subtle::arrays_equal;
/// # fn main() {
/// let a: [u8; 3] = [0, 1, 2];
/// let b: [u8; 3] = [1, 2, 3];
///
/// assert!(arrays_equal(&a, &b) == 0);
/// # }
/// ```
///
/// If the contents *do* match, `1u8` is returned:
///
/// ```
/// # extern crate curve25519_dalek;
/// # use curve25519_dalek::subtle::arrays_equal;
/// # fn main() {
/// let a: [u8; 3] = [0, 1, 2];
/// let b: [u8; 3] = [0, 1, 2];
///
/// assert!(arrays_equal(&a, &b) == 1);
/// # }
/// ```
///
/// This function is commonly used in various cryptographic applications, such
/// as [signature verification](https://github.com/isislovecruft/ed25519-dalek/blob/0.3.2/src/ed25519.rs#L280),
/// among many other applications.
///
/// # Return
///
/// Returns `1u8` if `a == b` and `0u8` otherwise.
#[inline(always)]
pub fn arrays_equal(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    let mut x: u8 = 0;

    for i in 0..32 {
        x |= a[i] ^ b[i];
    }
    bytes_equal_ct(x, 0)
}
