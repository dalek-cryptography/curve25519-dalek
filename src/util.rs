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

//! Utility functions and tools for constant-time comparisons.

/// Check equality of two bytes in constant time.
///
/// # Return
///
/// Returns 1 if `a == b` and 0 otherwise.
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
/// ```rust,ignore
/// let mut x: u8;
/// x = 0;
/// assert!(byte_is_nonzero(x));
/// x = 3;
/// assert!(byte_is_nonzero(x) == 1);
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
/// # Return
///
/// Returns 1 if `a == b` and 0 otherwise.
#[inline(always)]
// We don't use this in curve25519-dalek, but it's useful for e.g. an ed25519 implementation.
#[allow(dead_code)]
pub fn arrays_equal_ct(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    let mut x: u8 = 0;

    for i in 0..32 {
        x |= a[i] ^ b[i];
    }
    bytes_equal_ct(x, 0)
}
