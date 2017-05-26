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

#[cfg(feature = "std")]
use core::ops::BitAnd;
#[cfg(feature = "std")]
use core::ops::BitOr;
#[cfg(feature = "std")]
use core::ops::Not;
#[cfg(feature = "std")]
use core::ops::Sub;

use core::ops::Neg;

#[cfg(feature = "std")]
use num_traits::One;
#[cfg(feature = "std")]
use num_traits::Signed;


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
pub trait CTNegatable {
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

/// Select `a` if `choice == 1` or select `b` if `choice == 0`, in constant time.
///
/// # Inputs
///
/// * `a`, `b`, and `choice` must be types for which bitwise-AND, and
///   bitwise-OR, bitwise-complement, subtraction, multiplicative identity,
///   copying, partial equality, and partial order comparison are defined.
/// * `choice`: If `choice` is equal to the multiplicative identity of the type
///   (i.e. `1u8` for `u8`, etc.), then `a` is returned.  If `choice` is equal
///   to the additive identity (i.e. `0u8` for `u8`, etc.) then `b` is returned.
///
/// # Warning
///
/// The behaviour of this function is undefined if `choice` is something other
/// than a multiplicative identity or additive identity (i.e. `1u8` or `0u8`).
///
/// If you somehow manage to design a type which is not a signed integer, and
/// yet implements all the requisite trait bounds for this generic, it's your
/// problem if something breaks.
///
/// # Examples
///
/// This function should work for signed integer types:
///
/// ```
/// # extern crate curve25519_dalek;
/// # use curve25519_dalek::subtle::conditional_select;
/// # fn main() {
/// let a: i32 = 5;
/// let b: i32 = 13;
///
/// assert!(conditional_select(a, b, 0) == 13);
/// assert!(conditional_select(a, b, 1) == 5);
///
/// let c: i64 = 2343249123;
/// let d: i64 = 8723884895;
///
/// assert!(conditional_select(c, d, 0) == d);
/// assert!(conditional_select(c, d, 1) == c);
/// # }
/// ```
///
/// It does not work with `i128`s, however, because the `num` crate doesn't
/// implement `num::traits::Signed` for `i128`.
///
/// # TODO
///
/// Once `#[feature(specialization)]` is finished, we should rewrite this.  Or
/// find some other way to only implement it for types which we know work
/// correctly.
#[inline(always)]
#[cfg(feature = "std")]
pub fn conditional_select<T>(a: T, b: T, choice: T) -> T
    where T: PartialEq +
             PartialOrd +
             One +
             Copy +
             Signed +
             Sub<T, Output = T> +
          BitAnd<T, Output = T> +
           BitOr<T, Output = T> +
             Not<Output = T>
{
    (!(choice - T::one()) & a) | ((choice - T::one()) & b)
}

/// Check equality of two bytes in constant time.
///
/// # Return
///
/// Returns `1u8` if `a == b` and `0u8` otherwise.
#[inline(always)]
pub fn bytes_equal(a: u8, b: u8) -> u8 {
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

/// Check equality of two arrays, `a` and `b`, in constant time.
///
/// There is an `assert!` that the two arrays are of equal length.  For
/// example, the following code will panic:
///
/// ```rust,ignore
/// let a: [u8; 3] = [0, 0, 0];
/// let b: [u8; 4] = [0, 0, 0, 0];
///
/// assert!(arrays_equal(&a, &b) == 1);
/// ```
///
/// However, if the arrays are equal length, but their contents do *not* match,
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
/// And finally, if the contents *do* match, `1u8` is returned:
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
pub fn arrays_equal(a: &[u8], b: &[u8]) -> u8 {
    assert_eq!(a.len(), b.len());

    let mut x: u8 = 0;

    for i in 0 .. a.len() {
        x |= a[i] ^ b[i];
    }
    bytes_equal(x, 0)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn arrays_equal_different_lengths() {
        let a: [u8; 3] = [0, 0, 0];
        let b: [u8; 4] = [0, 0, 0, 0];

        assert!(arrays_equal(&a, &b) == 1);
    }

    #[test]
    #[cfg(feature = "std")]
    fn conditional_select_i32() {
        let a: i32 = 5;
        let b: i32 = 13;

        assert_eq!(conditional_select(a, b, 0), 13);
        assert_eq!(conditional_select(a, b, 1), 5);
    }

    #[test]
    #[cfg(feature = "std")]
    fn conditional_select_i64() {
        let c: i64 = 2343249123;
        let d: i64 = 8723884895;

        assert_eq!(conditional_select(c, d, 0), d);
        assert_eq!(conditional_select(c, d, 1), c);
    }
}
