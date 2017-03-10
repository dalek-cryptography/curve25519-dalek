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

//! Miscellaneous common utility functions.

/// Convert an array of (at least) three bytes into an i64.
#[inline]
//#[allow(dead_code)]
pub fn load3(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
}

/// Convert an array of (at least) four bytes into an i64.
#[inline]
//#[allow(dead_code)]
pub fn load4(input: &[u8]) -> i64 {
       (input[0] as i64)
    | ((input[1] as i64) << 8)
    | ((input[2] as i64) << 16)
    | ((input[3] as i64) << 24)
}
