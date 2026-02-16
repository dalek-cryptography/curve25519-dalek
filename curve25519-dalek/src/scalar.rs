// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// Portions Copyright 2017 Brian Smith
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
// - Brian Smith <brian@briansmith.org>
//! Arithmetic on scalars (integers mod the group order).
//!
//! Both the Ristretto group and the Ed25519 basepoint have prime order
//! \\( \ell = 2\^{252} + 27742317777372353535851937790883648493 \\).
//!
//! This code is intended to be useful with both the Ristretto group
//! (where everything is done modulo \\( \ell \\)), and the X/Ed25519
//! setting, which mandates specific bit-twiddles that are not
//! well-defined modulo \\( \ell \\).
//!
//! All arithmetic on `Scalars` is done modulo \\( \ell \\).
//!
//! # Constructing a scalar
//!
//! To create a [`Scalar`](struct.Scalar.html) from a supposedly canonical encoding, use
//! [`Scalar::from_canonical_bytes`](struct.Scalar.html#method.from_canonical_bytes).
//!
//! This function does input validation, ensuring that the input bytes
//! are the canonical encoding of a `Scalar`.
//! If they are, we'll get
//! `Some(Scalar)` in return:
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let one_as_bytes: [u8; 32] = Scalar::ONE.to_bytes();
//! let a: Option<Scalar> = Scalar::from_canonical_bytes(one_as_bytes).into();
//!
//! assert!(a.is_some());
//! ```
//!
//! However, if we give it bytes representing a scalar larger than \\( \ell \\)
//! (in this case, \\( \ell + 2 \\)), we'll get `None` back:
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let l_plus_two_bytes: [u8; 32] = [
//!    0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
//!    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
//! ];
//! let a: Option<Scalar> = Scalar::from_canonical_bytes(l_plus_two_bytes).into();
//!
//! assert!(a.is_none());
//! ```
//!
//! Another way to create a `Scalar` is by reducing a \\(256\\)-bit integer mod
//! \\( \ell \\), for which one may use the
//! [`Scalar::from_bytes_mod_order`](struct.Scalar.html#method.from_bytes_mod_order)
//! method.  In the case of the second example above, this would reduce the
//! resultant scalar \\( \mod \ell \\), producing \\( 2 \\):
//!
//! ```
//! use curve25519_dalek::scalar::Scalar;
//!
//! let l_plus_two_bytes: [u8; 32] = [
//!    0xef, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
//!    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//!    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
//! ];
//! let a: Scalar = Scalar::from_bytes_mod_order(l_plus_two_bytes);
//!
//! let two: Scalar = Scalar::ONE + Scalar::ONE;
//!
//! assert!(a == two);
//! ```
//!
//! There is also a constructor that reduces a \\(512\\)-bit integer,
//! [`Scalar::from_bytes_mod_order_wide`].
//!
//! To construct a `Scalar` as the hash of some input data, use
//! [`Scalar::hash_from_bytes`], which takes a buffer, or
//! [`Scalar::from_hash`], which allows an IUF API.
//!
#![cfg_attr(feature = "digest", doc = "```")]
#![cfg_attr(not(feature = "digest"), doc = "```ignore")]
//! # fn main() {
//! use sha2::{Digest, Sha512};
//! use curve25519_dalek::scalar::Scalar;
//!
//! // Hashing a single byte slice
//! let a = Scalar::hash_from_bytes::<Sha512>(b"Abolish ICE");
//!
//! // Streaming data into a hash object
//! let mut hasher = Sha512::default();
//! hasher.update(b"Abolish ");
//! hasher.update(b"ICE");
//! let a2 = Scalar::from_hash(hasher);
//!
//! assert_eq!(a, a2);
//! # }
//! ```
//!
//! See also `Scalar::hash_from_bytes` and `Scalar::from_hash` that
//! reduces a \\(512\\)-bit integer, if the optional `digest` feature
//! has been enabled.

use crate::lemmas::common_lemmas::bits_as_nat_lemmas::*;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mask_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::common_lemmas::shift_lemmas::*;
use crate::lemmas::common_lemmas::sum_lemmas::*;
use crate::lemmas::common_lemmas::to_nat_lemmas::*;
use crate::scalar_helpers::*;
#[cfg(feature = "alloc")]
use crate::specs::iterator_specs::collect_scalars_from_iter;
#[cfg(all(feature = "alloc", verus_keep_ghost))]
use crate::specs::iterator_specs::spec_scalars_from_iter;
use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::Index;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::calc;
use vstd::prelude::*;

#[cfg(feature = "group")]
use group::ff::{Field, FromUniformBytes, PrimeField};
#[cfg(feature = "group-bits")]
use group::ff::{FieldBits, PrimeFieldBits};

#[cfg(any(test, feature = "group"))]
use rand_core::RngCore;

#[cfg(any(test, feature = "rand_core"))]
use rand_core::CryptoRngCore;
// From a conflict:
//use rand_core::{CryptoRng, RngCore};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;
use subtle::CtOption;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::backend;
use crate::constants;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs_u64::spec_as_bytes;

#[allow(unused_imports)]
use crate::specs::core_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar52_specs::*;

#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas::*;

#[allow(unused_imports)]
use crate::lemmas::scalar_batch_invert_lemmas::*;

#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::montgomery_reduce_lemmas::*;

#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::naf_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::scalar_lemmas_::radix16_lemmas::*;
use crate::lemmas::scalar_lemmas_::radix_2w_lemmas::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;

#[allow(unused_imports)]
use crate::core_assumes::*;

#[allow(unused_imports)]
use crate::specs::scalar_specs::*;

#[allow(unused_imports)]
use crate::specs::proba_specs::*;

#[cfg(feature = "digest")]
#[allow(unused_imports)]
use digest::Digest;

verus! {

/*** <VERIFICATION NOTE> Focus on u64; removed all other backend types </VERIFICATION NOTE> ***/
type UnpackedScalar = backend::serial::u64::scalar::Scalar52;

/// The `Scalar` struct holds an element of \\(\mathbb Z / \ell\mathbb Z \\).
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Copy, Clone, Hash)]
pub struct Scalar {
    /// `bytes` is a little-endian byte encoding of an integer representing a scalar modulo the
    /// group order.
    ///
    /// # Invariant #1
    ///
    /// The integer representing this scalar is less than \\(2\^{255}\\). That is, the most
    /// significant bit of `bytes[31]` is 0.
    ///
    /// This is required for `EdwardsPoint` variable- and fixed-base multiplication, because most
    /// integers above 2^255 are unrepresentable in our radix-16 NAF (see [`Self::as_radix_16`]).
    /// The invariant is also required because our `MontgomeryPoint` multiplication assumes the MSB
    /// is 0 (see `MontgomeryPoint::mul`).
    ///
    /// # Invariant #2 (weak)
    ///
    /// The integer representing this scalar is less than \\(2\^{255} - 19 \\), i.e., it represents
    /// a canonical representative of an element of \\( \mathbb Z / \ell\mathbb Z \\). This is
    /// stronger than invariant #1. It also sometimes has to be broken.
    ///
    /// This invariant is deliberately broken in the implementation of `EdwardsPoint::{mul_clamped,
    /// mul_base_clamped}`, `MontgomeryPoint::{mul_clamped, mul_base_clamped}`, and
    /// `BasepointTable::mul_base_clamped`. This is not an issue though. As mentioned above,
    /// scalar-point multiplication is defined for any choice of `bytes` that satisfies invariant
    /// #1. Since clamping guarantees invariant #1 is satisfied, these operations are well defined.
    ///
    /// Note: Scalar-point mult is the _only_ thing you can do safely with an unreduced scalar.
    /// Scalar-scalar addition and subtraction are NOT correct when using unreduced scalars.
    /// Multiplication is correct, but this is only due to a quirk of our implementation, and not
    /// guaranteed to hold in general in the future.
    ///
    /// Note: It is not possible to construct an unreduced `Scalar` from the public API unless the
    /// `legacy_compatibility` is enabled (thus making `Scalar::from_bits` public). Thus, for all
    /// public non-legacy uses, invariant #2
    /// always holds.
    ///
    /* <VERIFICATION NOTE>
    Changed from pub(crate) to pub
    </VERIFICATION NOTE> */
    pub bytes: [u8; 32],/* <ORIGINAL CODE>
    pub(crate) bytes: [u8; 32],
    </ORIGINAL CODE> */
}

// This is a dummy function that we call from signal
// to test that verus functions in libsignal know
// about verus functions in curve-dalek
pub open spec fn is_a_scalar(s: Scalar) -> bool {
    true
}

impl Scalar {
    /// Construct a `Scalar` by reducing a 256-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    // VERIFICATION NOTE: VERIFIED
    pub fn from_bytes_mod_order(bytes: [u8; 32]) -> (result: Scalar)
        ensures
    // Result is equivalent to input modulo the group order

            u8_32_as_nat(&result.bytes) % group_order() == u8_32_as_nat(&bytes) % group_order(),
            // Result satisfies Scalar invariants #1 and #2
            is_canonical_scalar(&result),
    {
        // Temporarily allow s_unreduced.bytes > 2^255 ...
        let s_unreduced = Scalar { bytes };

        // Then reduce mod the group order and return the reduced representative.
        let s = s_unreduced.reduce();
        /*** <VERIFICATION NOTE> We omit debug asserts from verification  </VERIFICATION NOTE> ***/
        #[cfg(not(verus_keep_ghost))]
        debug_assert_eq!(0u8, s[31] >> 7);

        s
    }

    /// Construct a `Scalar` by reducing a 512-bit little-endian integer
    /// modulo the group order \\( \ell \\).
    /*
    <VERIFICATION NOTE>
      VERIFIED
      - Split single expression into two statements to allow proof block
      - Added proof block to connect postconditions from from_bytes_wide and pack()
    </VERIFICATION NOTE>
    */
    pub fn from_bytes_mod_order_wide(input: &[u8; 64]) -> (result: Scalar)
        ensures
            u8_32_as_nat(&result.bytes) % group_order() == bytes_seq_as_nat(input@) % group_order(),
            // Result satisfies Scalar invariants #1 and #2
            is_canonical_scalar(&result),
            // Uniformity: reducing 512 uniform bits mod L (≈2^253) produces nearly uniform scalar.
            // Bias: at most L/2^512 ≈ 2^-259 statistical distance from uniform (cryptographically negligible).
            is_uniform_bytes(input) ==> is_uniform_scalar(&result),
    {
        /* <ORIGINAL CODE>
        UnpackedScalar::from_bytes_wide(input).pack()
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        // The proof chain:
        // 1. from_bytes_wide ensures: scalar52_to_nat(&s) < group_order() AND limbs_bounded(&s)
        // 2. pack() requires limbs_bounded, ensures: scalar52_to_nat(self) < group_order() ==> is_canonical_scalar(&result)
        // 3. is_canonical_scalar includes bytes[31] <= 127
        let unpacked = UnpackedScalar::from_bytes_wide(input);
        let result = unpacked.pack();

        proof {
            // from_bytes_wide postconditions:
            // - limbs_bounded(&unpacked)
            // - scalar52_to_nat(&unpacked) == bytes_seq_as_nat(input@) % group_order()
            // - scalar52_to_nat(&unpacked) < group_order()
            // pack() postconditions:
            // - u8_32_as_nat(&result.bytes) == scalar52_to_nat(&unpacked) % pow2(256)
            // - scalar52_to_nat(&unpacked) < group_order() ==> is_canonical_scalar(&result)
            // Since scalar52_to_nat(&unpacked) < group_order() < pow2(256),
            // we have scalar52_to_nat(&unpacked) % pow2(256) == scalar52_to_nat(&unpacked)
            lemma_group_order_smaller_than_pow256();
            lemma_small_mod(scalar52_to_nat(&unpacked), pow2(256));

            // Therefore u8_32_as_nat(&result.bytes) == scalar52_to_nat(&unpacked)
            //                                        == bytes_seq_as_nat(input@) % group_order()
            // Since bytes_seq_as_nat(input@) % group_order() < group_order(),
            // u8_32_as_nat(&result.bytes) % group_order() == u8_32_as_nat(&result.bytes)
            //                                              == bytes_seq_as_nat(input@) % group_order()
            lemma_mod_bound(bytes_seq_as_nat(input@) as int, group_order() as int);
            lemma_small_mod(u8_32_as_nat(&result.bytes), group_order());

            // Uniformity: reducing 512 uniform bits mod L (≈2^253) produces nearly uniform scalar.
            // Bias: at most L/2^512 ≈ 2^-259 statistical distance (cryptographically negligible).
            axiom_uniform_mod_reduction(input, &result);
        }

        result  /* </MODIFIED CODE> */

    }

    /// Attempt to construct a `Scalar` from a canonical byte representation.
    ///
    /// # Return
    ///
    /// - `Some(s)`, where `s` is the `Scalar` corresponding to `bytes`,
    ///   if `bytes` is a canonical byte representation modulo the group order \\( \ell \\);
    /// - `None` if `bytes` is not a canonical byte representation.
    /*
    <VERIFICATION NOTE>
      - Refactored to use wrapper functions instead of trait functions for ct_eq and ct_option_new
      - Has proof bypass
    </VERIFICATION NOTE> */
    pub fn from_canonical_bytes(bytes: [u8; 32]) -> (result: CtOption<Scalar>)
        ensures
            u8_32_as_nat(&bytes) < group_order() ==> ct_option_has_value(result),
            u8_32_as_nat(&bytes) >= group_order() ==> !ct_option_has_value(result),
            ct_option_has_value(result) ==> u8_32_as_nat(&ct_option_value(result).bytes)
                % group_order() == u8_32_as_nat(&bytes) % group_order(),
    {
        /* <ORIGINAL CODE>
          let high_bit_unset = (bytes[31] >> 7).ct_eq(&0);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let high_byte_shifted = bytes[31] >> 7;
        let high_bit_unset = ct_eq_u8(&high_byte_shifted, &0);
        /* </MODIFIED CODE> */

        let candidate = Scalar { bytes };
        let is_canonical = candidate.is_canonical();

        /* <ORIGINAL CODE>
          CtOption::new(candidate, high_bit_unset & candidate.is_canonical())
          </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let condition = choice_and(high_bit_unset, is_canonical);
        let result = ct_option_new(candidate, condition);
        /* </MODIFIED CODE> */

        // Capture the high byte value for proof (avoids Verus interpreter issues)
        let ghost high_byte: u8 = bytes[31];

        proof {
            if u8_32_as_nat(&bytes) < group_order() {
                lemma_canonical_bytes_high_bit_clear(&candidate.bytes);
                assert(high_byte >> 7 == 0) by (bit_vector)
                    requires
                        high_byte <= 127,
                ;
            }
            // ct_option_value(result) == candidate and candidate.bytes == bytes

            assert(ct_option_value(result).bytes == bytes);
        }

        result
    }

    /// Construct a `Scalar` from the low 255 bits of a 256-bit integer. This breaks the invariant
    /// that scalars are always reduced. Scalar-scalar arithmetic, i.e., addition, subtraction,
    /// multiplication, **does not work** on scalars produced from this function. You may only use
    /// the output of this function for `EdwardsPoint::mul`, `MontgomeryPoint::mul`, and
    /// `EdwardsPoint::vartime_double_scalar_mul_basepoint`. **Do not use this function** unless
    /// you absolutely have to.
    /* <VERIFICATION NOTE>
        -This is not in default features and not in our current target list ==> spec omitted for now
    </VERIFICATION NOTE> */
    #[cfg(feature = "legacy_compatibility")]
    #[deprecated(
        since = "4.0.0",
        note = "This constructor outputs scalars with undefined scalar-scalar arithmetic. See docs."
    )]
    pub const fn from_bits(bytes: [u8; 32]) -> Scalar {
        let mut s = Scalar { bytes };
        // Ensure invariant #1 holds. That is, make s < 2^255 by masking the high bit.
        s.bytes[31] &= 0b0111_1111;

        s
    }
}

impl Eq for Scalar {

}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::cmp::PartialEqSpecImpl for Scalar {
    open spec fn obeys_eq_spec() -> bool {
        true  // Scalar equality is straightforward byte comparison

    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl PartialEq for Scalar {
    // VERIFICATION NOTE: PartialEqSpecImpl trait provides the external specification
    fn eq(&self, other: &Self) -> (result: bool)
        ensures
            result == (self.bytes == other.bytes),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Choice::into
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         let result = self.ct_eq(other).into();
         </ORIGINAL CODE> */
        let choice = self.ct_eq(other);
        assert(choice_is_true(choice) == (self.bytes == other.bytes));
        let result = choice_into(choice);
        assert(result == choice_is_true(choice));
        assert(result == (self.bytes == other.bytes));

        result
    }
}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> (result: Choice)
        ensures
            choice_is_true(result) == (self.bytes == other.bytes),
    {
        /* <VERIFICATION NOTE>
         Use wrapper function for Verus compatibility instead of direct subtle call
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         self.bytes.ct_eq(&other.bytes)
         </ORIGINAL CODE> */
        ct_eq_bytes32(&self.bytes, &other.bytes)
    }
}

impl Index<usize> for Scalar {
    type Output = u8;

    /// Index the bytes of the representative for this `Scalar`.  Mutation is not permitted.
    fn index(&self, _index: usize) -> (result: &u8)
        requires
            _index < 32,
        ensures
            result == &self.bytes[_index as int],
    {
        &(self.bytes[_index])
    }
}

impl Debug for Scalar {
    /* VERIFICATION NOTE: we don't cover debugging */
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Scalar{{\n\tbytes: {:?},\n}}", &self.bytes)
    }
}

impl<'a> MulAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: VERIFIED
    fn mul_assign(&mut self, _rhs: &'a Scalar)
        requires
            is_canonical_scalar(old(self)),
            is_canonical_scalar(_rhs),
        ensures
            u8_32_as_nat(&self.bytes) % group_order() == (u8_32_as_nat(&old(self).bytes)
                * u8_32_as_nat(&_rhs.bytes)) % group_order(),
            is_canonical_scalar(self),
    {
        /* <ORIGINAL CODE>
         *self = UnpackedScalar::mul(&self.unpack(), &_rhs.unpack()).pack();
         </ORIGINAL CODE> */
        /* <VERIFICATION NOTE>
         In the modified code, we store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(scalar52_to_nat(&self_unpacked) == u8_32_as_nat(&old(self).bytes));
            assert(scalar52_to_nat(&rhs_unpacked) == u8_32_as_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
            lemma_limbs_bounded_implies_prod_bounded(&self_unpacked, &rhs_unpacked);
        }

        let result_unpacked = UnpackedScalar::mul(&self_unpacked, &rhs_unpacked);
        proof {
            assert(scalar52_to_nat(&result_unpacked) % group_order() == (scalar52_to_nat(
                &self_unpacked,
            ) * scalar52_to_nat(&rhs_unpacked)) % group_order());
            assert(limbs_bounded(&result_unpacked));
        }

        *self = result_unpacked.pack();
        proof {
            assert(scalar52_to_nat(&result_unpacked) == scalar52_to_nat(&result_unpacked) % pow2(
                256,
            )) by {
                assert(group_order() < pow2(256)) by {
                    lemma_group_order_bound();
                    lemma_pow2_strictly_increases(255, 256);
                }
                lemma_small_mod(scalar52_to_nat(&result_unpacked), pow2(256));
            }
            assert(u8_32_as_nat(&self.bytes) % group_order() == scalar52_to_nat(&result_unpacked)
                % group_order());
            assert(u8_32_as_nat(&self.bytes) % group_order() == (u8_32_as_nat(&old(self).bytes)
                * u8_32_as_nat(&_rhs.bytes)) % group_order());
        }
        /* </MODIFIED CODE> */

    }
}

define_mul_assign_variants!(LHS = Scalar, RHS = Scalar);

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::MulSpecImpl<&Scalar> for &Scalar {
    open spec fn obeys_mul_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn mul_req(self, rhs: &Scalar) -> bool {
        is_canonical_scalar(self) && is_canonical_scalar(rhs)
    }

    open spec fn mul_spec(self, rhs: &Scalar) -> Scalar {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl<'b> Mul<&'b Scalar> for &Scalar {
    type Output = Scalar;

    // VERIFICATION NOTE: VERIFIED
    // NOTE: MulSpecImpl::mul_req requires is_canonical_scalar for both inputs
    fn mul(self, _rhs: &'b Scalar) -> (result: Scalar)
        ensures
            u8_32_as_nat(&result.bytes) % group_order() == (u8_32_as_nat(&self.bytes)
                * u8_32_as_nat(&_rhs.bytes)) % group_order(),
            is_canonical_scalar(&result),
    {
        /* <VERIFICATION NOTE>
         Store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        proof {
            assert(scalar52_to_nat(&self_unpacked) == u8_32_as_nat(&self.bytes));
            assert(scalar52_to_nat(&rhs_unpacked) == u8_32_as_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
            lemma_limbs_bounded_implies_prod_bounded(&self_unpacked, &rhs_unpacked);
        }
        let result_unpacked = UnpackedScalar::mul(&self_unpacked, &rhs_unpacked);
        proof {
            assert(scalar52_to_nat(&result_unpacked) == scalar52_to_nat(&result_unpacked) % pow2(
                256,
            )) by {
                assert(group_order() < pow2(256)) by {
                    lemma_group_order_bound();
                    lemma_pow2_strictly_increases(255, 256);
                }
                lemma_small_mod(scalar52_to_nat(&result_unpacked), pow2(256));
            }
            assert(scalar52_to_nat(&result_unpacked) % group_order() == (scalar52_to_nat(
                &self_unpacked,
            ) * scalar52_to_nat(&rhs_unpacked)) % group_order());
            assert(limbs_bounded(&result_unpacked));
        }
        // UnpackedScalar::mul ensures scalar52_to_nat(&result_unpacked) < group_order()
        // pack() ensures: scalar52_to_nat(self) < group_order() ==> is_canonical_scalar(&result)
        let result = result_unpacked.pack();
        proof {
            assert(u8_32_as_nat(&result.bytes) % group_order() == scalar52_to_nat(&result_unpacked)
                % group_order());
            assert(u8_32_as_nat(&result.bytes) % group_order() == (u8_32_as_nat(&self.bytes)
                * u8_32_as_nat(&_rhs.bytes)) % group_order());
            // Trigger pack()'s conditional postcondition for is_canonical_scalar
            assert(scalar52_to_nat(&result_unpacked) < group_order());
            assert(is_canonical_scalar(&result));
        }
        /* </MODIFIED CODE> */
        /* <ORIGINAL CODE>
         let result = UnpackedScalar::mul(&self.unpack(), &_rhs.unpack()).pack();
         </ORIGINAL CODE> */

        result
    }
}

define_mul_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&Scalar> for &Scalar {
    open spec fn obeys_add_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn add_req(self, rhs: &Scalar) -> bool {
        is_canonical_scalar(self) && is_canonical_scalar(rhs)
    }

    open spec fn add_spec(self, rhs: &Scalar) -> Scalar {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl<'a> Add<&'a Scalar> for &Scalar {
    type Output = Scalar;

    // VERIFICATION NOTE: VERIFIED
    // PRECONDITION is_canonical_scalar(self) && is_canonical_scalar(_rhs)
    #[allow(non_snake_case)]
    fn add(self, _rhs: &'a Scalar) -> (result: Scalar)
        ensures
            u8_32_as_nat(&result.bytes) == (u8_32_as_nat(&self.bytes) + u8_32_as_nat(&_rhs.bytes))
                % group_order(),
            is_canonical_scalar(&result),
    {
        // The UnpackedScalar::add function produces reduced outputs if the inputs are reduced. By
        // Scalar invariant #1, this is always the case.
        /* <VERIFICATION NOTE>
         Store unpacked values explicitly for asserts
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         UnpackedScalar::add(&self.unpack(), &_rhs.unpack()).pack()
         </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();
        let result_unpacked = UnpackedScalar::add(&self_unpacked, &rhs_unpacked);

        let result = result_unpacked.pack();
        proof {
            lemma_group_order_smaller_than_pow256();
            lemma_small_mod(scalar52_to_nat(&result_unpacked), pow2(256));
        }
        /* </MODIFIED CODE> */

        result
    }
}

define_add_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

impl<'a> AddAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: VERIFIED
    #[allow(clippy::op_ref)]
    fn add_assign(&mut self, _rhs: &'a Scalar)
        requires
            is_canonical_scalar(old(self)),
            is_canonical_scalar(_rhs),
        ensures
            u8_32_as_nat(&self.bytes) == (u8_32_as_nat(&old(self).bytes) + u8_32_as_nat(
                &_rhs.bytes,
            )) % group_order(),
    {
        *self = &*self + _rhs;
    }
}

define_add_assign_variants!(LHS = Scalar, RHS = Scalar);

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::SubSpecImpl<&Scalar> for &Scalar {
    open spec fn obeys_sub_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn sub_req(self, rhs: &Scalar) -> bool {
        is_canonical_scalar(self) && is_canonical_scalar(rhs)
    }

    open spec fn sub_spec(self, rhs: &Scalar) -> Scalar {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl<'b> Sub<&'b Scalar> for &Scalar {
    type Output = Scalar;

    // VERIFICATION NOTE: VERIFIED
    // PRECONDITION is_canonical_scalar(self) && is_canonical_scalar(_rhs)
    #[allow(non_snake_case)]
    fn sub(self, _rhs: &'b Scalar) -> (result:
        Scalar)/* VERIFICATION NOTE: preconditions are added to the SpecImpl above
        requires
            is_canonical_scalar(self),
            is_canonical_scalar(rhs)
        */

        ensures
            u8_32_as_nat(&result.bytes) % group_order() == (u8_32_as_nat(&self.bytes)
                - u8_32_as_nat(&_rhs.bytes)) % (group_order() as int),
    {
        /* <ORIGINAL CODE>
         UnpackedScalar::sub(&self.unpack(), &_rhs.unpack()).pack()
         </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        let self_unpacked = self.unpack();
        let rhs_unpacked = _rhs.unpack();

        proof {
            // unpack() ensures these properties:
            assert(scalar52_to_nat(&self_unpacked) == u8_32_as_nat(&self.bytes));
            assert(scalar52_to_nat(&rhs_unpacked) == u8_32_as_nat(&_rhs.bytes));
            assert(limbs_bounded(&self_unpacked));
            assert(limbs_bounded(&rhs_unpacked));
        }

        // UnpackedScalar::sub requires: -group_order() <= scalar52_to_nat(&a) - scalar52_to_nat(&b) < group_order()
        proof {
            // -group_order() < scalar52_to_nat(&self_unpacked) - scalar52_to_nat(&rhs_unpacked) < grour_order()
            lemma_sub_symmetric_bound(
                scalar52_to_nat(&self_unpacked),
                scalar52_to_nat(&rhs_unpacked),
                group_order(),
            );
        }

        let result_unpacked = UnpackedScalar::sub(&self_unpacked, &rhs_unpacked);

        proof {
            // Postconditions from sub - need to strengthen, review connections
            assert(scalar52_to_nat(&result_unpacked) == (scalar52_to_nat(&self_unpacked)
                - scalar52_to_nat(&rhs_unpacked)) % (group_order() as int));
            assert(limbs_bounded(&result_unpacked));
            assert(scalar52_to_nat(&result_unpacked) < group_order());

            // Since result < group_order(), taking mod again gives the same value
            lemma_small_mod(scalar52_to_nat(&result_unpacked), group_order());
            assert(scalar52_to_nat(&result_unpacked) % group_order() == scalar52_to_nat(
                &result_unpacked,
            ));
        }

        let result = result_unpacked.pack();

        proof {
            // Goal: u8_32_as_nat(&result.bytes) == scalar52_to_nat(&result_unpacked)
            // pack postcondition gives: u8_32_as_nat(...) == scalar52_to_nat(...) % pow2(256)
            assert(u8_32_as_nat(&result.bytes) == scalar52_to_nat(&result_unpacked)) by {
                assert(scalar52_to_nat(&result_unpacked) % pow2(256) == scalar52_to_nat(
                    &result_unpacked,
                )) by {
                    assert(scalar52_to_nat(&result_unpacked) < pow2(256)) by {
                        // sub postcondition: scalar52_to_nat(...) < group_order()
                        // and group_order() < pow2(256)
                        lemma_group_order_smaller_than_pow256();
                        lemma_scalar52_lt_pow2_256_if_canonical(&result_unpacked);
                    }
                    lemma_small_mod(scalar52_to_nat(&result_unpacked), pow2(256));
                }
            }

            assert(u8_32_as_nat(&result.bytes) % group_order() == (u8_32_as_nat(&self.bytes)
                - u8_32_as_nat(&_rhs.bytes)) % (group_order() as int));
        }
        /* </MODIFIED CODE> */

        result
    }
}

define_sub_variants!(LHS = Scalar, RHS = Scalar, Output = Scalar);

impl<'a> SubAssign<&'a Scalar> for Scalar {
    // VERIFICATION NOTE: VERIFIED
    #[allow(clippy::op_ref)]
    fn sub_assign(&mut self, _rhs: &'a Scalar)
        requires
            is_canonical_scalar(old(self)),
            is_canonical_scalar(_rhs),
        ensures
            u8_32_as_nat(&self.bytes) % group_order() == (u8_32_as_nat(&old(self).bytes)
                - u8_32_as_nat(&_rhs.bytes)) % (group_order() as int),
    {
        *self = &*self - _rhs;
    }
}

define_sub_assign_variants!(LHS = Scalar, RHS = Scalar);

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for &Scalar {
    open spec fn obeys_neg_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn neg_req(self) -> bool {
        true  // No preconditions - scalars are canonical by invariant

    }

    open spec fn neg_spec(self) -> Scalar {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl Neg for &Scalar {
    type Output = Scalar;

    #[allow(non_snake_case)]
    fn neg(self) -> (result: Scalar)
        ensures
            (scalar_as_nat(self) + scalar_as_nat(&result)) % group_order() == 0,
    {
        /* <ORIGINAL CODE>
        let self_R = UnpackedScalar::mul_internal(&self.unpack(), &constants::R);
        let self_mod_l = UnpackedScalar::montgomery_reduce(&self_R);
        UnpackedScalar::sub(&UnpackedScalar::ZERO, &self_mod_l).pack()

        let self_R = UnpackedScalar::mul_internal(&self.unpack(), &constants::R);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> */
        proof {
            // Establish preconditions
            lemma_r_bounded(constants::R);
            lemma_zero_bounded(UnpackedScalar::ZERO);
            lemma_r_equals_spec(constants::R);
        }

        // Execute the actual computation
        let self_unpacked = self.unpack();

        proof {
            lemma_limbs_bounded_implies_prod_bounded(&self_unpacked, &constants::R);
        }

        let self_R = UnpackedScalar::mul_internal(&self_unpacked, &constants::R);

        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&self_unpacked, &constants::R, &self_R);
            // R is canonical (< L), so product satisfies canonical_bound
            lemma_r_equals_spec(constants::R);
            lemma_canonical_product_satisfies_canonical_bound(
                &self_unpacked,
                &constants::R,
                &self_R,
            );
        }
        /* </MODIFIED CODE> */
        let self_mod_l = UnpackedScalar::montgomery_reduce(&self_R);
        // is_canonical_scalar52(&self_mod_l) follows from montgomery_reduce postcondition

        /* <ORIGINAL CODE>
        let result = UnpackedScalar::sub(&UnpackedScalar::ZERO, &self_mod_l).pack();
        </ORIGINAL CODE> */

        /* <MODIFIED CODE> */
        let sub_result = UnpackedScalar::sub(&UnpackedScalar::ZERO, &self_mod_l);
        let result = sub_result.pack();
        /* </MODIFIED CODE> */

        proof {
            // Prove congruence: scalar52_to_nat(&self_mod_l) % L == scalar_as_nat(self) % L
            lemma_mul_factors_congruent_implies_products_congruent(
                scalar52_to_nat(&self_unpacked) as int,
                montgomery_radix() as int,
                scalar52_to_nat(&constants::R) as int,
                group_order() as int,
            );
            lemma_cancel_mul_pow2_mod(
                scalar52_to_nat(&self_mod_l),
                scalar52_to_nat(&self_unpacked),
                montgomery_radix(),
            );

            // Prove result is in canonical form
            lemma_group_order_smaller_than_pow256();
            lemma_small_mod(scalar52_to_nat(&sub_result), pow2(256));

            // Prove the negation property
            lemma_negation_sums_to_zero(
                scalar_as_nat(self),
                scalar52_to_nat(&self_mod_l),
                scalar_as_nat(&result),
                group_order(),
            );
        }

        result
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::NegSpecImpl for Scalar {
    open spec fn obeys_neg_spec() -> bool {
        false  // Set to false since we use ensures clause instead of concrete spec

    }

    open spec fn neg_req(self) -> bool {
        true  // No specific preconditions - scalars are canonical by invariant

    }

    open spec fn neg_spec(self) -> Scalar {
        arbitrary()  // Placeholder - actual spec is in ensures clause

    }
}

impl Neg for Scalar {
    type Output = Scalar;

    fn neg(self) -> (result: Scalar)
        ensures
            (scalar_as_nat(&self) + scalar_as_nat(&result)) % group_order() == 0,
    {
        let result = (&self).neg();
        result
    }/* <ORIGINAL CODE>
    fn neg(self) -> Scalar {
        -&self
    }
    </ORIGINAL CODE> */

}

impl ConditionallySelectable for Scalar {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> (Self) {
        let mut bytes = [0u8;32];
        #[allow(clippy::needless_range_loop)]
        for i in 0..32 {
            /* <VERIFICATION NOTE>
            Use wrapper function for Verus compatibility instead of direct subtle call
            </VERIFICATION NOTE> */
            /* <ORIGINAL CODE>
            bytes[i] = u8::conditional_select(&a.bytes[i], &b.bytes[i], choice);
            </ORIGINAL CODE> */
            /* <MODIFIED CODE> */
            bytes[i] = select_u8(&a.bytes[i], &b.bytes[i], choice);
            /* </MODIFIED CODE> */
        }
        Scalar { bytes }
    }
}

/* <VERIFICATION NOTE>
 Trait implementations for Product and Sum use iterators which are not directly supported by Verus.
 Both use external_body helpers (collect_scalars_from_iter from iterator_specs) to collect
 the iterator into Vec<Scalar>, then call verified product_of_slice/sum_of_slice functions.
</VERIFICATION NOTE> */

impl<T> Product<T> for Scalar where T: Borrow<Scalar> {
    /* <ORIGINAL CODE>
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Scalar::ONE, |acc, item| acc * item.borrow())
    }
    </ORIGINAL CODE> */
    /* <VERIFICATION NOTE>
    Iterator operations and Borrow trait are not supported by Verus.
    We use an external_body helper to collect the iterator into Vec<Scalar>,
    then call the verified product_of_slice function for the actual computation.
    </VERIFICATION NOTE> */
    fn product<I>(iter: I) -> (result: Self) where I: Iterator<Item = T>
        ensures
            scalar_as_nat(&result) < group_order(),
            scalar_congruent_nat(&result, product_of_scalars(spec_scalars_from_iter::<T, I>(iter))),
    {
        let scalars = collect_scalars_from_iter(iter);
        // Use verified product_of_slice for the actual computation
        Scalar::product_of_slice(&scalars)
    }
}

/* <ORIGINAL CODE>
impl<T> Sum<T> for Scalar
where
    T: Borrow<Scalar>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Scalar::ZERO, |acc, item| acc + item.borrow())
    }
</ORIGINAL CODE> */

/* <VERIFICATION NOTE>
Iterator operations and Borrow trait are not supported by Verus.
We use an external_body helper to collect the iterator into Vec<Scalar>,
then call the verified sum_of_slice function for the actual computation.
</VERIFICATION NOTE> */

impl<T> Sum<T> for Scalar where T: Borrow<Scalar> {
    fn sum<I>(iter: I) -> (result: Self) where I: Iterator<Item = T>
        ensures
            scalar_as_nat(&result) < group_order(),
            scalar_congruent_nat(&result, sum_of_scalars(spec_scalars_from_iter::<T, I>(iter))),
    {
        let scalars = collect_scalars_from_iter(iter);
        // Use verified sum_of_slice for the actual computation
        Scalar::sum_of_slice(&scalars)
    }
}

impl Default for Scalar {
    fn default() -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == 0 as nat,
    {
        let result = Scalar::ZERO;
        proof {
            lemma_scalar_zero_properties();
        }
        result
    }
}

// vstd FromSpecImpl implementations for Scalar
#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<u8> for Scalar {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(x: u8) -> Scalar {
        arbitrary()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<u16> for Scalar {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(x: u16) -> Scalar {
        arbitrary()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<u32> for Scalar {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(x: u32) -> Scalar {
        arbitrary()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<u64> for Scalar {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(x: u64) -> Scalar {
        arbitrary()
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::convert::FromSpecImpl<u128> for Scalar {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(x: u128) -> Scalar {
        arbitrary()
    }
}

impl From<u8> for Scalar {
    fn from(x: u8) -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == x as nat,
    {
        let mut s_bytes = [0u8;32];
        s_bytes[0] = x;

        let result = Scalar { bytes: s_bytes };
        proof {
            assert(scalar_as_nat(&result) == x as nat) by {
                assert forall|i: int| 1 <= i < 32 implies result.bytes[i] == 0 by {}
                lemma_u8_32_as_nat_first_byte_only(&result.bytes);
            }
        }
        result
    }
}

impl From<u16> for Scalar {
    #[allow(clippy::manual_memcpy)]
    fn from(x: u16) -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8;32];
        let x_bytes = u16_to_le_bytes(x);

        // Copy the 2 bytes from x_bytes to s_bytes
        // (x_bytes.len() is always 2 because u16_to_le_bytes returns [u8; 2])
        for i in 0..2
            invariant
        // Copied bytes match

                forall|j: int| 0 <= j < i ==> s_bytes[j] == x_bytes[j],
                // Remaining bytes are still zero
                forall|j: int| i <= j < 32 ==> s_bytes[j] == 0,
        {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */

        let result = Scalar { bytes: s_bytes };
        proof {
            lemma_from_le_bytes(x_bytes@, &result.bytes, 2);
        }
        result
    }
}

impl From<u32> for Scalar {
    #[allow(clippy::manual_memcpy)]
    fn from(x: u32) -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8;32];
        let x_bytes = u32_to_le_bytes(x);

        // Copy the 4 bytes from x_bytes to s_bytes
        // (x_bytes.len() is always 4 because u32_to_le_bytes returns [u8; 4])
        for i in 0..4
            invariant
                forall|j: int| 0 <= j < i ==> s_bytes[j] == x_bytes[j],
                forall|j: int| i <= j < 32 ==> s_bytes[j] == 0,
        {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */

        let result = Scalar { bytes: s_bytes };
        proof {
            lemma_from_le_bytes(x_bytes@, &result.bytes, 4);
        }
        result
    }
}

impl From<u64> for Scalar {
    /// Construct a scalar from the given `u64`.
    ///
    /// # Inputs
    ///
    /// An `u64` to convert to a `Scalar`.
    ///
    /// # Returns
    ///
    /// A `Scalar` corresponding to the input `u64`.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let fourtytwo = Scalar::from(42u64);
    /// let six = Scalar::from(6u64);
    /// let seven = Scalar::from(7u64);
    ///
    /// assert!(fourtytwo == six * seven);
    /// ```
    #[allow(clippy::manual_memcpy)]
    fn from(x: u64) -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8;32];
        let x_bytes = u64_to_le_bytes(x);

        // Copy the 8 bytes from x_bytes to s_bytes
        // (x_bytes.len() is always 8 because u64_to_le_bytes returns [u8; 8])
        for i in 0..8
            invariant
                forall|j: int| 0 <= j < i ==> s_bytes[j] == x_bytes[j],
                forall|j: int| i <= j < 32 ==> s_bytes[j] == 0,
        {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */
        let result = Scalar { bytes: s_bytes };
        proof {
            lemma_from_le_bytes(x_bytes@, &result.bytes, 8);
        }
        result
    }
}

impl From<u128> for Scalar {
    #[allow(clippy::manual_memcpy)]
    fn from(x: u128) -> (result: Scalar)
        ensures
            scalar_as_nat(&result) == x as nat,
    {
        /* <ORIGINAL CODE>
        let x_bytes = x.to_le_bytes();
        s_bytes[0..x_bytes.len()].copy_from_slice(&x_bytes);
        </ORIGINAL CODE> */
        /* <MODIFIED CODE> Verus doesn't support copy_from_slice and to_le_bytes */
        let mut s_bytes = [0u8;32];
        let x_bytes = u128_to_le_bytes(x);

        // Copy the 16 bytes from x_bytes to s_bytes
        // (x_bytes.len() is always 16 because u128_to_le_bytes returns [u8; 16])
        for i in 0..16
            invariant
                forall|j: int| 0 <= j < i ==> s_bytes[j] == x_bytes[j],
                forall|j: int| i <= j < 32 ==> s_bytes[j] == 0,
        {
            s_bytes[i] = x_bytes[i];
        }
        /* </MODIFIED CODE> */

        let result = Scalar { bytes: s_bytes };
        proof {
            lemma_from_le_bytes(x_bytes@, &result.bytes, 16);
        }
        result
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for Scalar {
    /* <VERIFICATION NOTE>
    Using wrapper function for verus compatibility instead of direct subtle call
    </VERIFICATION NOTE> */
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 32 ==> #[trigger] self.bytes[i] == 0u8,
    {
        /* ORIGINAL CODE: self.bytes.zeroize(); */
        crate::core_assumes::zeroize_bytes32(&mut self.bytes);
    }
}

impl Scalar {
    /// The scalar \\( 0 \\).
    // pub const ZERO: Self = Self { bytes: [0u8; 32] };
    /* <VERIFICATION NOTE>
    Changed to explicit initialization
    </VERIFICATION NOTE> */
    /* <ORIGINAL CODE>
    pub const ZERO: Self = Self { bytes: [0u8; 32] };
    </ORIGINAL CODE> */
    pub const ZERO: Scalar = Scalar {
        bytes: [
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ],
    };

    /// The scalar \\( 1 \\).
    pub const ONE: Self = Self {
        bytes: [
            1,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ],
    };

    /* <VERIFICATION NOTE>
     Verification of random method postponed - requires rand_core feature to be enabled.
    </VERIFICATION NOTE> */
    #[cfg(any(test, feature = "rand_core"))]
    /// Return a `Scalar` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements `CryptoRngCore`
    ///   (i.e. `CryptoRng` + `RngCore`) interface.
    ///
    /// # Returns
    ///
    /// A random scalar within \\(\mathbb{Z} / \ell\mathbb{Z}\\).
    ///
    /// # Example
    ///
    /// ```
    /// # fn main() {
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// use rand_core::OsRng;
    ///
    /// let mut csprng = OsRng;
    /// let a: Scalar = Scalar::random(&mut csprng);
    /// # }
    /* <VERIFICATION NOTE>
     Uses fill_bytes wrapper from core_assumes to establish is_uniform_bytes,
     then from_bytes_mod_order_wide propagates uniformity to is_uniform_scalar.
    </VERIFICATION NOTE> */
    pub fn random<R: CryptoRngCore + ?Sized>(rng: &mut R) -> (result: Self)
        ensures
            is_uniform_scalar(&result),
            is_canonical_scalar(&result),
    {
        let mut scalar_bytes = [0u8;64];
        #[cfg(verus_keep_ghost)]
        crate::core_assumes::fill_bytes(rng, &mut scalar_bytes);
        #[cfg(not(verus_keep_ghost))]
        rng.fill_bytes(&mut scalar_bytes);
        Scalar::from_bytes_mod_order_wide(&scalar_bytes)
    }

    #[cfg(feature = "digest")]
    /// Hash a slice of bytes into a scalar using a specified hash function.
    ///
    /// This function hashes the input using the specified `Digest` type and then reduces
    /// the result modulo the group order to produce a scalar.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Example
    ///
    #[cfg_attr(feature = "digest", doc = "```")]
    #[cfg_attr(not(feature = "digest"), doc = "```ignore")]
    /// # use curve25519_dalek::scalar::Scalar;
    /// use sha2::Sha512;
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let s = Scalar::hash_from_bytes::<Sha512>(msg.as_bytes());
    /// # }
    /// ```
    /* <VERIFICATION NOTE>
     Marked as external_body due to complexity of Digest trait.
     For Verus verification, use hash_from_bytes_verus instead.
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    pub fn hash_from_bytes<D>(input: &[u8]) -> (result: Scalar) where
        D: digest::Digest<OutputSize = digest::generic_array::typenum::U64> + Default,

        ensures
    // Result satisfies Scalar invariants #1 and #2

            is_canonical_scalar(&result),
    {
        let mut hash = D::default();
        hash.update(input);
        Scalar::from_hash(hash)
    }

    /// Verus-compatible version of hash_from_bytes that uses SHA-512.
    ///
    /// This function is designed for Verus verification and directly computes
    /// a SHA-512 hash. For regular code with generic hash functions, use `hash_from_bytes` instead.
    ///
    /// # Inputs
    ///
    /// * `input`: a byte slice to hash
    ///
    /// # Returns
    ///
    /// A scalar reduced modulo the group order
    #[cfg(feature = "digest")]
    pub fn hash_from_bytes_verus(input: &[u8]) -> (result: Scalar)
        ensures
            is_uniform_bytes(input) ==> is_uniform_scalar(&result),
            // Result satisfies Scalar invariants #1 and #2
            is_canonical_scalar(&result),
    {
        let hash_bytes: [u8; 64] = sha512_hash_bytes(input);
        Scalar::from_hash_verus(hash_bytes)
    }

    #[cfg(feature = "digest")]
    /// Construct a scalar from a 64-byte (512-bit) hash output.
    ///
    /// This reduces the hash output modulo the group order.
    /// Typically used after calling `finalize()` on a SHA-512 hasher.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// use sha2::{Digest, Sha512};
    ///
    /// # fn main() {
    /// let mut h = Sha512::new();
    /// h.update(b"To really appreciate architecture, you may even need to commit a murder.");
    /// h.update(b"While the programs used for The Manhattan Transcripts are of the most extreme");
    /// h.update(b"nature, they also parallel the most common formula plot: the archetype of");
    /// h.update(b"murder. Other phantasms were occasionally used to underline the fact that");
    /// h.update(b"perhaps all architecture, rather than being about functional standards, is");
    /// h.update(b"about love and death.");
    ///
    /// let s = Scalar::from_hash(h);
    ///
    /// println!("{:?}", s.to_bytes());
    /// assert_eq!(
    ///     s.to_bytes(),
    ///     [  21,  88, 208, 252,  63, 122, 210, 152,
    ///       154,  38,  15,  23,  16, 167,  80, 150,
    ///       192, 221,  77, 226,  62,  25, 224, 148,
    ///       239,  48, 176,  10, 185,  69, 168,  11, ],
    /// );
    /// # }
    /// ```
    /* <VERIFICATION NOTE>
     Marked as external_body due to GenericArray having private fields.
     For Verus verification, see from_hash_verus below.
    </VERIFICATION NOTE> */
    #[cfg(feature = "digest")]
    #[verifier::external_body]
    pub fn from_hash<D>(hash: D) -> (result: Scalar) where
        D: digest::Digest<OutputSize = digest::generic_array::typenum::U64>,

        ensures
    // is_uniform_digest(&hash) ==> is_uniform_scalar(&result),
    // Result satisfies Scalar invariants #1 and #2

            is_canonical_scalar(&result),
    {
        let mut output = [0u8;64];
        output.copy_from_slice(hash.finalize().as_slice());
        Scalar::from_bytes_mod_order_wide(&output)
    }

    /// Verus-compatible version of from_hash that takes pre-finalized hash bytes.
    ///
    /// This function is designed for Verus verification and takes a byte array directly
    /// instead of a generic Digest type. For regular code, use `from_hash` instead.
    ///
    /// # Inputs
    ///
    /// * `hash_bytes`: a 64-byte array representing the output of a hash function
    ///
    /// # Returns
    ///
    /// A scalar reduced modulo the group order
    pub fn from_hash_verus(hash_bytes: [u8; 64]) -> (result: Scalar)
        ensures
            is_uniform_bytes(&hash_bytes) ==> is_uniform_scalar(&result),
            // Result satisfies Scalar invariants #1 and #2
            is_canonical_scalar(&result),
    {
        let result = Scalar::from_bytes_mod_order_wide(&hash_bytes);
        result
    }

    /// Convert this `Scalar` to its underlying sequence of bytes.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let s: Scalar = Scalar::ZERO;
    ///
    /// assert!(s.to_bytes() == [0u8; 32]);
    /// ```
    pub const fn to_bytes(&self) -> (result: [u8; 32])
        ensures
            result == self.bytes,
            scalar_as_nat(self) == u8_32_as_nat(&result),
    {
        self.bytes
    }

    /// View the little-endian byte encoding of the integer representing this Scalar.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// let s: Scalar = Scalar::ZERO;
    ///
    /// assert!(s.as_bytes() == &[0u8; 32]);
    /// ```
    pub const fn as_bytes(&self) -> (result: &[u8; 32])
        ensures
            result == &self.bytes,
            scalar_as_nat(self) == u8_32_as_nat(&result),
    {
        &self.bytes
    }
}

impl Scalar {
    /// Given a nonzero `Scalar`, compute its multiplicative inverse.
    ///
    /// # Warning
    ///
    /// `self` **MUST** be nonzero.  If you cannot
    /// *prove* that this is the case, you **SHOULD NOT USE THIS
    /// FUNCTION**.
    ///
    /// # Returns
    ///
    /// The multiplicative inverse of the this `Scalar`.
    ///
    /// # Example
    ///
    /// ```
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
    /// let X: Scalar = Scalar::from_bytes_mod_order([
    ///         0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
    ///         0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
    ///         0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
    ///         0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04,
    ///     ]);
    /// // 1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
    /// let XINV: Scalar = Scalar::from_bytes_mod_order([
    ///         0x1c, 0xdc, 0x17, 0xfc, 0xe0, 0xe9, 0xa5, 0xbb,
    ///         0xd9, 0x24, 0x7e, 0x56, 0xbb, 0x01, 0x63, 0x47,
    ///         0xbb, 0xba, 0x31, 0xed, 0xd5, 0xa9, 0xbb, 0x96,
    ///         0xd5, 0x0b, 0xcd, 0x7a, 0x3f, 0x96, 0x2a, 0x0f,
    ///     ]);
    ///
    /// let inv_X: Scalar = X.invert();
    /// assert!(XINV == inv_X);
    /// let should_be_one: Scalar = &inv_X * &X;
    /// assert!(should_be_one == Scalar::ONE);
    /// ```
    // VERIFICATION NOTE: VERIFIED
    pub fn invert(&self) -> (result: Scalar)
        requires
            is_canonical_scalar(self),
        ensures
    // Result is the multiplicative inverse: result * self ≡ 1 (mod group_order)

            (scalar_as_nat(&result) * scalar_as_nat(self)) % group_order() == 1,
            is_canonical_scalar(&result),
    {
        let unpacked = self.unpack();
        let inv_unpacked = unpacked.invert();
        let result = inv_unpacked.pack();

        proof {
            // Step 1: invert ensures scalar52_to_nat(inv_unpacked) < group_order < pow2(256)
            lemma_group_order_smaller_than_pow256();
            assert(scalar52_to_nat(&inv_unpacked) < pow2(256));

            // Step 2: Since inv_unpacked < pow2(256), pack preserves the value (no modular reduction)
            lemma_small_mod(scalar52_to_nat(&inv_unpacked), pow2(256));
            assert(u8_32_as_nat(&result.bytes) == scalar52_to_nat(&inv_unpacked));

            // Step 3: The inverse property follows from invert's postcondition
            assert((u8_32_as_nat(&result.bytes) * u8_32_as_nat(&self.bytes)) % group_order() == 1);
        }

        result
    }

    /// Given a slice of nonzero (possibly secret) `Scalar`s,
    /// compute their inverses in a batch.
    ///
    /// # Return
    ///
    /// Each element of `inputs` is replaced by its inverse.
    ///
    /// The product of all inverses is returned.
    ///
    /// # Warning
    ///
    /// All input `Scalars` **MUST** be nonzero.  If you cannot
    /// *prove* that this is the case, you **SHOULD NOT USE THIS
    /// FUNCTION**.
    ///
    /// # Example
    ///
    /// ```
    /// # use curve25519_dalek::scalar::Scalar;
    /// # fn main() {
    /// let mut scalars = [
    ///     Scalar::from(3u64),
    ///     Scalar::from(5u64),
    ///     Scalar::from(7u64),
    ///     Scalar::from(11u64),
    /// ];
    ///
    /// let allinv = Scalar::batch_invert(&mut scalars);
    ///
    /// assert_eq!(allinv, Scalar::from(3*5*7*11u64).invert());
    /// assert_eq!(scalars[0], Scalar::from(3u64).invert());
    /// assert_eq!(scalars[1], Scalar::from(5u64).invert());
    /// assert_eq!(scalars[2], Scalar::from(7u64).invert());
    /// assert_eq!(scalars[3], Scalar::from(11u64).invert());
    /// # }
    /// ```
    #[cfg(feature = "alloc")]
    // Theo: Verus doesn't like the zeroize in this function. I think the long-term
    // solution is to use assume_specification to tell Verus what zeroize does.
    // In the short-term, I've just told verus to ignore the body.
    // (SB update: alternative is to exclude just the zeroize call, as below)
    #[verifier::rlimit(50)]  // The backward loop has many invariants that need more solver time
    pub fn batch_invert(inputs: &mut [Scalar]) -> (result:
        Scalar)/* <VERIFICATION NOTE>
     Refactored for Verus: Index loops instead of iterators, manual Vec construction, ..
    </VERIFICATION NOTE> */

        ensures
    // Result is the modular inverse of the product of all original inputs

            is_inverse_of_nat(&result, product_of_scalars(old(inputs)@)),
            // Each input is replaced with its inverse
            forall|i: int|
                0 <= i < inputs.len() ==> #[trigger] is_inverse(
                    &(#[trigger] old(inputs)[i]),
                    &(#[trigger] inputs[i]),
                ),
    {
        // This code is essentially identical to the FieldElement
        // implementation, and is documented there.  Unfortunately,
        // it's not easy to write it generically, since here we want
        // to use `UnpackedScalar`s internally, and `Scalar`s
        // externally, but there's no corresponding distinction for
        // field elements.
        let n = inputs.len();
        let one_unpacked = Scalar::ONE.unpack();

        let one: UnpackedScalar = one_unpacked.as_montgomery();

        /* <VERIFICATION NOTE>
         Build vec manually instead of vec![one; n] for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         let mut scratch = vec![one; n];
         </ORIGINAL CODE> */
        let mut scratch = Vec::new();
        for j in 0..n
            invariant
                scratch.len() == j,
        {
            scratch.push(one);
        }

        // Keep an accumulator of all of the previous products
        let acc_unpacked = Scalar::ONE.unpack();

        // scratch.len() == n follows from the loop above
        let mut acc = acc_unpacked.as_montgomery();

        let ghost original_inputs: Seq<Scalar> = inputs@;

        proof {
            lemma_scalar_one_properties();
            assert(scalar52_to_nat(&acc_unpacked) == 1);
            assert(scalar52_to_nat(&acc) % group_order() == (1 * montgomery_radix())
                % group_order());
            assert((montgomery_radix() * 1) % group_order() == montgomery_radix() % group_order());
            assert(partial_product(original_inputs, 0) == 1nat);
        }

        // First loop: build prefix products
        /* <VERIFICATION NOTE>
         Rewritten with index loop instead of .zip() for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
         for (input, scratch) in inputs.iter_mut().zip(scratch.iter_mut()) {
             *scratch = acc;
             // Avoid unnecessary Montgomery multiplication in second pass by
             // keeping inputs in Montgomery form
             let tmp = input.unpack().as_montgomery();
             *input = tmp.pack();
             acc = UnpackedScalar::montgomery_mul(&acc, &tmp);
         }
        </ORIGINAL CODE> */
        for i in 0..n
            invariant
                scratch.len() == n,
                n == inputs.len(),
                // acc is canonical (needed for montgomery_mul and montgomery_invert)
                is_canonical_scalar52(&acc),
                forall|j: int| 0 <= j < i ==> #[trigger] limbs_bounded(&scratch[j]),
                // SEMANTIC INVARIANT: acc represents R * partial_product(original_inputs, i) in Montgomery form
                scalar52_to_nat(&acc) % group_order() == (montgomery_radix() * partial_product(
                    original_inputs,
                    i as int,
                )) % group_order(),
                // Track original inputs sequence
                original_inputs == old(inputs)@,
                original_inputs.len() == n,
                // inputs[i..n] are still unmodified (equal to original_inputs[i..n])
                forall|j: int| i <= j < n ==> #[trigger] inputs[j] == #[trigger] original_inputs[j],
                // SEMANTIC INVARIANT: scratch[j] contains R * partial_product(original_inputs, j)
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> scalar52_to_nat(&scratch[j]) % group_order() == (
                    montgomery_radix() * partial_product(original_inputs, j)) % group_order(),
                // SEMANTIC INVARIANT: inputs[j] for j < i contains scalar[j] in Montgomery form
                // i.e., u8_32_as_nat(&inputs[j].bytes) % L == (u8_32_as_nat(&original_inputs[j].bytes) * R) % L
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> u8_32_as_nat(&inputs[j].bytes) % group_order() == (u8_32_as_nat(
                        &original_inputs[j].bytes,
                    ) * montgomery_radix()) % group_order(),
        {
            scratch[i] = acc;

            // Avoid unnecessary Montgomery multiplication in second pass by
            // keeping inputs in Montgomery form
            // At this point: inputs[i] == original_inputs[i]
            let input_unpacked = inputs[i].unpack();

            let tmp = input_unpacked.as_montgomery();

            proof {
                use vstd::arithmetic::power2::lemma_pow2_strictly_increases;
                use vstd::arithmetic::div_mod::lemma_small_mod;

                let L = group_order();
                let R = montgomery_radix();
                let scalar_i = u8_32_as_nat(&original_inputs[i as int].bytes);

                assert(scalar52_to_nat(&input_unpacked) == scalar_i);
                assert(scalar52_to_nat(&tmp) % L == (scalar_i * R) % L);
                // tmp is canonical (< L) from as_montgomery's postcondition

                lemma_group_order_bound();
                lemma_pow2_strictly_increases(255, 256);
                lemma_small_mod(scalar52_to_nat(&tmp), pow2(256));
            }

            inputs[i] = tmp.pack();

            // Save acc before the multiplication for the proof
            let ghost acc_before = acc;

            assert(limb_prod_bounded_u128(acc.limbs, tmp.limbs, 5)) by {
                lemma_limbs_bounded_implies_prod_bounded(&acc, &tmp);
            }
            acc = UnpackedScalar::montgomery_mul(&acc, &tmp);

            proof {
                let acc_val = scalar52_to_nat(&acc);
                let acc_before_val = scalar52_to_nat(&acc_before);
                let tmp_val = scalar52_to_nat(&tmp);

                lemma_montgomery_mul_partial_product(
                    acc_before_val,
                    tmp_val,
                    acc_val,
                    original_inputs,
                    i as int,
                );
            }
        }
        // After the loop: forall|j| 0 <= j < n ==> limbs_bounded(&scratch[j])

        // After the first loop:
        // - acc represents R * product_of_scalars(original_inputs) in Montgomery form
        // - scratch[j] contains R * partial_product(original_inputs, j)

        proof {
            lemma_partial_product_full(original_inputs);
        }

        // acc is nonzero iff all inputs are nonzero
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(acc.pack() != Scalar::ZERO);

        // Compute the inverse of all products
        let ghost acc_before_invert = acc;

        /* <ORIGINAL CODE>
         acc = acc.montgomery_invert().from_montgomery();
        </ORIGINAL CODE> */

        assert(limb_prod_bounded_u128(acc.limbs, acc.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&acc, &acc);
        }

        acc = acc.montgomery_invert();
        let ghost acc_after_invert = acc;
        acc = acc.from_montgomery();

        proof {
            use vstd::arithmetic::div_mod::lemma_small_mod;
            use vstd::arithmetic::power2::lemma_pow2_strictly_increases;

            let L = group_order();
            let R = montgomery_radix();
            let P = product_of_scalars(original_inputs);
            let acc_before_val = scalar52_to_nat(&acc_before_invert);
            let acc_after_val = scalar52_to_nat(&acc_after_invert);
            let final_acc_val = scalar52_to_nat(&acc);

            lemma_invert_chain(acc_before_val, acc_after_val, final_acc_val, P);
            lemma_small_mod(1nat, L);

            lemma_group_order_bound();
            lemma_pow2_strictly_increases(255, 256);
            lemma_small_mod(final_acc_val, pow2(256));
        }

        // We need to return the product of all inverses later
        let ret = acc.pack();
        // Second loop: compute inverses in place
        let ghost ret_val = scalar52_to_nat(&acc);

        // Pass through the vector backwards to compute the inverses in place
        /* <VERIFICATION NOTE>
         Manual reverse loop instead of .rev() for Verus compatibility
        </VERIFICATION NOTE> */
        /* <ORIGINAL CODE>
        for (input, scratch) in inputs.iter_mut().rev().zip(scratch.iter().rev()) {
             let tmp = UnpackedScalar::montgomery_mul(&acc, &input.unpack());
             *input = UnpackedScalar::montgomery_mul(&acc, scratch).pack();
             acc = tmp;
         }
        </ORIGINAL CODE> */
        let mut i: usize = n;
        while i > 0
            invariant
                scratch.len() == n,
                n == inputs.len(),
                i <= n,
                // acc is canonical (needed for montgomery_mul)
                is_canonical_scalar52(&acc),
                forall|j: int| 0 <= j < scratch.len() ==> #[trigger] limbs_bounded(&scratch[j]),
                original_inputs == old(inputs)@,
                n == original_inputs.len(),
                forall|j: int| #![auto] i <= j < n ==> is_inverse(&original_inputs[j], &inputs[j]),
                // Track that ret is still inverse of product_of_all
                is_inverse_of_nat(&ret, product_of_scalars(original_inputs)),
                // SEMANTIC INVARIANT: scratch[j] still contains R * partial_product(original_inputs, j)
                forall|j: int|
                    #![auto]
                    0 <= j < n ==> scalar52_to_nat(&scratch[j]) % group_order() == (
                    montgomery_radix() * partial_product(original_inputs, j)) % group_order(),
                // SEMANTIC INVARIANT: inputs[j] for unprocessed j < i contains scalar[j] in Montgomery form
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> u8_32_as_nat(&inputs[j].bytes) % group_order() == (u8_32_as_nat(
                        &original_inputs[j].bytes,
                    ) * montgomery_radix()) % group_order(),
                // SEMANTIC INVARIANT: acc represents the inverse of partial_product(original_inputs, i)
                // i.e., (scalar52_to_nat(&acc) * partial_product(original_inputs, i)) % L == 1
                (scalar52_to_nat(&acc) * partial_product(original_inputs, i as int)) % group_order()
                    == 1nat,
            decreases i,
        {
            i -= 1;
            let input_unpacked = inputs[i].unpack();
            let ghost acc_before = acc;

            assert(limb_prod_bounded_u128(acc.limbs, input_unpacked.limbs, 5)) by {
                lemma_limbs_bounded_implies_prod_bounded(&acc, &input_unpacked);
            }

            let tmp = UnpackedScalar::montgomery_mul(&acc, &input_unpacked);

            assert(limb_prod_bounded_u128(acc.limbs, scratch[i as int].limbs, 5)) by {
                lemma_limbs_bounded_implies_prod_bounded(&acc, &scratch[i as int]);
            }

            let new_input_unpacked = UnpackedScalar::montgomery_mul(&acc, &scratch[i]);
            inputs[i] = new_input_unpacked.pack();
            acc = tmp;

            proof {
                use vstd::arithmetic::power2::lemma_pow2_strictly_increases;
                use vstd::arithmetic::div_mod::lemma_small_mod;

                let L = group_order();
                let R = montgomery_radix();
                let acc_before_val = scalar52_to_nat(&acc_before);
                let scratch_val = scalar52_to_nat(&scratch[i as int]);
                let result_m = scalar52_to_nat(&new_input_unpacked);
                let result = u8_32_as_nat(&inputs[i as int].bytes);
                let scalar_i = u8_32_as_nat(&original_inputs[i as int].bytes);

                // acc and new_input_unpacked are canonical from montgomery_mul's postcondition
                // because acc_before is canonical (loop invariant)

                // Prove result == result_m via canonicity
                lemma_group_order_bound();
                lemma_pow2_strictly_increases(255, 256);
                lemma_small_mod(result_m, pow2(256));

                // Prove inputs[i] is inverse of original_inputs[i]
                lemma_backward_loop_is_inverse(
                    acc_before_val,
                    scratch_val,
                    result_m,
                    result,
                    original_inputs,
                    i as int,
                );
                assert((scalar_i * result) % L == (result * scalar_i) % L) by {
                    lemma_mul_is_commutative(scalar_i as int, result as int);
                };

                // Prove acc invariant is maintained
                let input_val = scalar52_to_nat(&input_unpacked);
                let acc_after_val = scalar52_to_nat(&acc);
                lemma_backward_loop_acc_invariant(
                    acc_before_val,
                    input_val,
                    acc_after_val,
                    original_inputs,
                    i as int,
                );
            }
            /* ORIGINAL CODE (inlined before proof block):
               inputs[i] = UnpackedScalar::montgomery_mul(&acc, &scratch[i]).pack();
               acc = tmp;
            */
        }

        #[cfg(feature = "zeroize")]
        #[cfg(not(verus_keep_ghost))]
        Zeroize::zeroize(&mut scratch);

        ret
    }
}

#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "serde")]
/// Visitor for deserializing a Scalar from a sequence of 32 bytes.
///
/* VERIFICATION NOTE:
- We don't cover serde feature yet
- The ScalarVisitor struct is defined at module level rather than inside the
`Deserialize::deserialize` since Verus doesn't support nested types
</VERIFICATION NOTE> */
struct ScalarVisitor;

#[cfg(feature = "serde")]
impl<'de> Visitor<'de> for ScalarVisitor {
    type Value = Scalar;

    #[verifier::external_body]
    fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        {
            formatter.write_str(
                "a sequence of 32 bytes whose little-endian interpretation is less than the \
                        basepoint order ℓ",
            )
        }
    }

    #[verifier::external_body]
    fn visit_seq<A>(self, mut seq: A) -> Result<Scalar, A::Error> where
        A: serde::de::SeqAccess<'de>,
     {
        let mut bytes = [0u8;32];
        #[allow(clippy::needless_range_loop)]
        for i in 0..32 {
            bytes[i] = seq.next_element()?.ok_or_else(
                || serde::de::Error::invalid_length(i, &"expected 32 bytes"),
            )?;
        }
        Option::from(Scalar::from_canonical_bytes(bytes)).ok_or_else(
            || serde::de::Error::custom("scalar was not canonically encoded"),
        )
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl Serialize for Scalar {
    #[verifier::external_body]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> Deserialize<'de> for Scalar {
    #[verifier::external_body]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
        /* VERIFICATION NOTE:
        Originally struct ScalarVisitor defined here, but moved up to the top of the file
        </VERIFICATION NOTE> */
        deserializer.deserialize_tuple(32, ScalarVisitor)
    }
}

} // verus!
verus! {

/* <VERIFICATION NOTE>
Helper inline functions for as_radix_16, moved outside impl Scalar for Verus compatibility
</VERIFICATION NOTE> */
#[allow(clippy::identity_op)]
#[inline(always)]
fn bot_half(x: u8) -> (result:
    u8)/* <VERIFICATION NOTE>
- Adjust the spec as needed for the proof of as_radix_16
</VERIFICATION NOTE> */

    ensures
// Result is the lower 4 bits (lower nibble) of x

        result == x % 16,
        // Result is in range [0, 15]
        result <= 15,
{
    let result = (x >> 0) & 15;
    proof {
        assert((x >> 0) & 15 == x % 16) by (bit_vector);
    }
    result
}

#[inline(always)]
fn top_half(x: u8) -> (result:
    u8)/* <VERIFICATION NOTE>
- Adjust the spec as needed for the proof of as_radix_16
</VERIFICATION NOTE> */

    ensures
// Result is the upper 4 bits (upper nibble) of x

        result == x / 16,
        // Result is in range [0, 15]
        result <= 15,
{
    let result = (x >> 4) & 15;
    proof {
        assert((x >> 4) & 15 == x / 16) by (bit_vector);
    }
    result
}

impl Scalar {
    /// Get the bits of the scalar, in little-endian order
    /* VERIFICATION NOTE: original code followed by refactored version without using Iterator - unsupported by Verus)*/
    /* <ORIGINAL CODE>
    pub(crate) fn bits_le(&self) -> impl DoubleEndedIterator<Item = bool> + '_ {
        /* <VERIFICATION NOTE>
        - Opaque types like Iterator not supported in Verus yet
        - see bits_le_verus below for a Verus-compatible version
        </VERIFICATION NOTE> */
        (0..256).map(|i| {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this iterator is
            // little-endian on the bit level
            ((self.bytes[i >> 3] >> (i & 7)) & 1u8) == 1
        })
    }
    </ORIGINAL CODE> */
    /// Get the bits of the scalar as an array, in little-endian order
    /* <VERIFICATION NOTE>
         This is a Verus-compatible version of bits_le from above that returns an array instead of an iterator
        </VERIFICATION NOTE> */
    #[allow(dead_code)]
    pub(crate) fn bits_le(&self) -> (result: [bool; 256])
        ensures
            bits_as_nat(result) == u8_32_as_nat(&self.bytes),
    {
        let mut bits = [false;256];
        let mut i: usize = 0;

        while i < 256
            invariant
                i <= 256,
                bits.len() == 256,
                self.bytes.len() == 32,
                forall|j: int|
                    0 <= j < i as int ==> bits[j] == (((self.bytes[(j / 8) as int] >> ((j
                        % 8) as u8)) & 1u8) == 1u8),
            decreases 256 - i,
        {
            // As i runs from 0..256, the bottom 3 bits index the bit, while the upper bits index
            // the byte. Since self.bytes is little-endian at the byte level, this is
            // little-endian on the bit level
            let byte_idx = i >> 3;  // Divide by 8 to get byte index
            let bit_idx = (i & 7) as u8;  // Modulo 8 to get bit position within byte

            // Prove bounds and index equalities using shift and mask lemmas
            proof {
                assert(i < 256);

                // Prove i >> 3 = i / 8 using shift lemma
                lemma_u64_shr_is_div(i as u64, 3);
                // pow2(3) = 8
                lemma2_to64();
                assert(byte_idx < 32);
                assert(byte_idx == i / 8);

                // Prove i & 7 = i % 8 using mask lemma
                lemma_u64_low_bits_mask_is_mod(i as u64, 3);
                // low_bits_mask(3) = 7 and pow2(3) = 8
                lemma2_to64();
                assert(bit_idx < 8);
                assert(bit_idx == (i % 8) as u8);
            }

            bits[i] = ((self.bytes[byte_idx] >> bit_idx) & 1u8) == 1;
            i += 1;
        }

        proof {
            lemma_bits_from_bytes_eq_u8_32_as_nat(bits, self.bytes);
        }

        bits
    }

    /// Compute a width-\\(w\\) "Non-Adjacent Form" of this scalar.
    ///
    /// A width-\\(w\\) NAF of a positive integer \\(k\\) is an expression
    /// $$
    /// k = \sum_{i=0}\^m n\_i 2\^i,
    /// $$
    /// where each nonzero
    /// coefficient \\(n\_i\\) is odd and bounded by \\(|n\_i| < 2\^{w-1}\\),
    /// \\(n\_{m-1}\\) is nonzero, and at most one of any \\(w\\) consecutive
    /// coefficients is nonzero.  (Hankerson, Menezes, Vanstone; def 3.32).
    ///
    /// The length of the NAF is at most one more than the length of
    /// the binary representation of \\(k\\).  This is why the
    /// `Scalar` type maintains an invariant (invariant #1) that the top bit is
    /// \\(0\\), so that the NAF of a scalar has at most 256 digits.
    ///
    /// Intuitively, this is like a binary expansion, except that we
    /// allow some coefficients to grow in magnitude up to
    /// \\(2\^{w-1}\\) so that the nonzero coefficients are as sparse
    /// as possible.
    ///
    /// When doing scalar multiplication, we can then use a lookup
    /// table of precomputed multiples of a point to add the nonzero
    /// terms \\( k_i P \\).  Using signed digits cuts the table size
    /// in half, and using odd digits cuts the table size in half
    /// again.
    ///
    /// To compute a \\(w\\)-NAF, we use a modification of Algorithm 3.35 of HMV:
    ///
    /// 1. \\( i \gets 0 \\)
    /// 2. While \\( k \ge 1 \\):
    ///     1. If \\(k\\) is odd, \\( n_i \gets k \operatorname{mods} 2^w \\), \\( k \gets k - n_i \\).
    ///     2. If \\(k\\) is even, \\( n_i \gets 0 \\).
    ///     3. \\( k \gets k / 2 \\), \\( i \gets i + 1 \\).
    /// 3. Return \\( n_0, n_1, ... , \\)
    ///
    /// Here \\( \bar x = x \operatorname{mods} 2^w \\) means the
    /// \\( \bar x \\) with \\( \bar x \equiv x \pmod{2^w} \\) and
    /// \\( -2^{w-1} \leq \bar x < 2^{w-1} \\).
    ///
    /// We implement this by scanning across the bits of \\(k\\) from
    /// least-significant bit to most-significant-bit.
    /// Write the bits of \\(k\\) as
    /// $$
    /// k = \sum\_{i=0}\^m k\_i 2^i,
    /// $$
    /// and split the sum as
    /// $$
    /// k = \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \sum\_{i=0} k\_{i+w} 2^i
    /// $$
    /// where the first part is \\( k \mod 2^w \\).
    ///
    /// If \\( k \mod 2^w\\) is odd, and \\( k \mod 2^w < 2^{w-1} \\), then we emit
    /// \\( n_0 = k \mod 2^w \\).  Instead of computing
    /// \\( k - n_0 \\), we just advance \\(w\\) bits and reindex.
    ///
    /// If \\( k \mod 2^w\\) is odd, and \\( k \mod 2^w \ge 2^{w-1} \\), then
    /// \\( n_0 = k \operatorname{mods} 2^w = k \mod 2^w - 2^w \\).
    /// The quantity \\( k - n_0 \\) is
    /// $$
    /// \begin{aligned}
    /// k - n_0 &= \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \sum\_{i=0} k\_{i+w} 2^i
    ///          - \sum\_{i=0}^{w-1} k\_i 2^i + 2^w \\\\
    /// &= 2^w + 2^w \sum\_{i=0} k\_{i+w} 2^i
    /// \end{aligned}
    /// $$
    /// so instead of computing the subtraction, we can set a carry
    /// bit, advance \\(w\\) bits, and reindex.
    ///
    /// If \\( k \mod 2^w\\) is even, we emit \\(0\\), advance 1 bit
    /// and reindex.  In fact, by setting all digits to \\(0\\)
    /// initially, we don't need to emit anything.
    #[verifier::loop_isolation(false)]
    pub(crate) fn non_adjacent_form(&self, w: usize) -> (result: [i8; 256])
        requires
            2 <= w <= 8,
            // Scalar must fit in 255 bits (satisfied by canonical scalars since l < 2^253).
            // Note: we use this weaker bound rather than is_canonical_scalar(self) because
            // the proof only needs the 255-bit bound, not full reduction mod l.
            scalar_as_nat(self) < pow2(255),
        ensures
    // result encodes the same integer

            reconstruct(result@) == scalar_as_nat(self) as int,
            // result digits follow NAF rules
            is_valid_naf(result@, w as nat),
    {
        // VERIFICATION NOTE: we tell verus not to verify debug assertions
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(w >= 2);
        // required so that the NAF digits fit in i8
        // VERIFICATION NOTE: we tell verus not to verify debug assertions
        #[cfg(not(verus_keep_ghost))]
            debug_assert!(w <= 8);

        let mut naf = [0i8;256];

        // VERIFICATION NOTE: Inline the read_le_u64_into logic to avoid Verus unsupported features
        /* <ORIGINAL CODE>
            let mut x_u64 = [0u64; 5];
            read_le_u64_into(&self.bytes, &mut x_u64[0..4]);
             <ORIGINAL CODE> */
        // Read 4 u64s from the 32-byte array (self.bytes)
        let ghost scalar_val: nat = scalar_as_nat(self);
        let mut x_u64 = [0u64;5];
        // Named byte chunks for lemma_u64x4_from_le_bytes (same pattern as as_radix_2w)
        let chunk0: [u8; 8] = [
            self.bytes[0],
            self.bytes[1],
            self.bytes[2],
            self.bytes[3],
            self.bytes[4],
            self.bytes[5],
            self.bytes[6],
            self.bytes[7],
        ];
        let chunk1: [u8; 8] = [
            self.bytes[8],
            self.bytes[9],
            self.bytes[10],
            self.bytes[11],
            self.bytes[12],
            self.bytes[13],
            self.bytes[14],
            self.bytes[15],
        ];
        let chunk2: [u8; 8] = [
            self.bytes[16],
            self.bytes[17],
            self.bytes[18],
            self.bytes[19],
            self.bytes[20],
            self.bytes[21],
            self.bytes[22],
            self.bytes[23],
        ];
        let chunk3: [u8; 8] = [
            self.bytes[24],
            self.bytes[25],
            self.bytes[26],
            self.bytes[27],
            self.bytes[28],
            self.bytes[29],
            self.bytes[30],
            self.bytes[31],
        ];
        x_u64[0] = u64_from_le_bytes(chunk0);
        x_u64[1] = u64_from_le_bytes(chunk1);
        x_u64[2] = u64_from_le_bytes(chunk2);
        x_u64[3] = u64_from_le_bytes(chunk3);
        // x_u64[4] remains 0

        // Setup proof: bridge scalar_as_nat(self) to u64_4_as_nat
        proof {
            assert(bytes_as_nat_prefix(chunk0@, 8) + bytes_as_nat_prefix(chunk1@, 8) * pow2(64)
                + bytes_as_nat_prefix(chunk2@, 8) * pow2(128) + bytes_as_nat_prefix(chunk3@, 8)
                * pow2(192) == u8_32_as_nat(&self.bytes)) by {
                lemma_u64x4_from_le_bytes(self.bytes, chunk0, chunk1, chunk2, chunk3);
            }
            let words4: [u64; 4] = [x_u64[0], x_u64[1], x_u64[2], x_u64[3]];
            assert(u64_4_as_nat(&words4) == scalar_val);
        }

        /* ORIGINAL CODE
        let width = 1 << w;
        let window_mask = width - 1;
         */
        let width: u64 = 1u64 << (w as u64);
        proof {
            assert(width as nat == pow2(w as nat) && width >= 4u64) by {
                lemma_naf_width_properties(w);
            };
        }
        let window_mask: u64 = width - 1;

        // Establish base case for loop invariant:
        // reconstruct(naf.take(0)) + 0 * pow2(0) == scalar_val % pow2(0)
        proof {
            assert(reconstruct(naf@.take(0)) == 0) by {
                assert(naf@.take(0).len() == 0);
            };
            assert(pow2(0nat) == 1nat) by {
                lemma2_to64();
            };
            assert((scalar_val as int) % pow2(0nat) as int == 0int) by {
                lemma_small_mod(0nat, 1nat);
            };
        }

        let mut pos: usize = 0;
        let mut carry: u64 = 0;
        while pos < 256
            invariant
        // --- Mutable state bounds ---

                carry <= 1,
                pos <= 256 + w - 1,
                // --- Core invariant: reconstruction matches scalar mod pow2(pos) ---
                // (cap take length at 256 since naf has 256 elements)
                ({
                    let p: int = if pos <= 256 {
                        pos as int
                    } else {
                        256int
                    };
                    reconstruct(naf@.take(p)) + (carry as int) * pow2(pos as nat) as int == (
                    scalar_val as int) % pow2(pos as nat) as int
                }),
                // Unassigned digits are zero
                forall|j: int| pos <= j < 256 ==> naf@[j] == 0i8,
                // Terminal carry: once pos >= 256, carry must be 0
                pos >= 256 ==> carry == 0,
                // NAF digit validity: finalized digits satisfy bounds
                ({
                    let p: int = if pos <= 256 {
                        pos as int
                    } else {
                        256int
                    };
                    forall|i: int|
                        #![trigger naf@[i]]
                        0 <= i < p ==> {
                            let d = naf@[i] as int;
                            d == 0 || (d % 2 != 0 && -pow2((w - 1) as nat) < d && d < pow2(
                                (w - 1) as nat,
                            ))
                        }
                }),
                // NAF spacing: nonzero digits at least w behind pos
                ({
                    let p: int = if pos <= 256 {
                        pos as int
                    } else {
                        256int
                    };
                    forall|i: int|
                        #![trigger naf@[i]]
                        0 <= i < p && naf@[i] as int != 0 ==> i + (w as int) <= pos as int
                }),
                // NAF non-adjacency: nonzero digit implies next w-1 are zero
                ({
                    let p: int = if pos <= 256 {
                        pos as int
                    } else {
                        256int
                    };
                    forall|i: int|
                        #![trigger naf@[i]]
                        0 <= i < p && naf@[i] as int != 0 ==> (forall|j: int|
                            1 <= j < (w as int) && i + j < 256 ==> (#[trigger] naf@[i + j]) == 0i8)
                }),
            decreases 264 - pos,
        {
            // Construct a buffer of bits of the scalar, starting at bit `pos`
            let u64_idx = pos / 64;
            let bit_idx = pos % 64;

            proof {
                assert(u64_idx <= 3 && bit_idx < 64) by {
                    lemma_fundamental_div_mod(pos as int, 64);
                };
            }

            let bit_buf: u64 = if bit_idx < 64 - w {
                // This window's bits are contained in a single u64
                x_u64[u64_idx] >> bit_idx
            } else {
                // Combine the current u64's bits with the bits from the next u64
                (x_u64[u64_idx] >> bit_idx) | (x_u64[1 + u64_idx] << (64 - bit_idx))
            };

            // Prove bit extraction correctness: (bit_buf & window_mask) extracts
            // the w-bit window of scalar_val starting at bit position pos
            proof {
                let words4: [u64; 4] = [x_u64[0], x_u64[1], x_u64[2], x_u64[3]];
                // Fold OR with x_u64[4]=0 for the u64_idx==3 cross-word case
                if u64_idx == 3 && !(bit_idx < 64 - w) {
                    let w3 = words4[3];
                    assert(bit_buf == w3 >> (bit_idx as u64)) by {
                        assert((w3 >> (bit_idx as u64)) | (0u64 << ((64 - bit_idx) as u64)) == w3
                            >> (bit_idx as u64)) by (bit_vector)
                            requires
                                (bit_idx as u64) < 64u64,
                        ;
                    };
                }
                assert((bit_buf & window_mask) as nat == (u64_4_as_nat(&words4) / pow2(pos as nat))
                    % pow2(w as nat)) by {
                    lemma_u64x4_bit_extraction(
                        words4,
                        bit_buf,
                        window_mask,
                        w,
                        pos,
                        u64_idx,
                        bit_idx,
                    );
                };
            }

            // carry + (bit_buf & window_mask) won't overflow u64
            proof {
                assert(carry + (bit_buf & window_mask) <= (1u64 << (w as u64))) by {
                    lemma_naf_window_no_overflow(carry, bit_buf, window_mask, w);
                };
            }

            // Ghost: extracted value and connection to window
            let ghost extracted: nat = (scalar_val / pow2(pos as nat)) % pow2(w as nat);
            proof {
                // bit_buf & window_mask == extracted (via u64_4_as_nat == scalar_val)
                assert((bit_buf & window_mask) as nat == extracted) by {
                    let words4: [u64; 4] = [x_u64[0], x_u64[1], x_u64[2], x_u64[3]];
                    assert(u64_4_as_nat(&words4) == scalar_val);
                };
                // Since pos < 256 (loop guard), the capped invariant simplifies
                assert(reconstruct(naf@.take(pos as int)) + (carry as int) * pow2(pos as nat) as int
                    == (scalar_val as int) % pow2(pos as nat) as int);
            }

            // Save old carry before potential modification
            let ghost old_carry: u64 = carry;
            let window: u64 = carry + (bit_buf & window_mask);

            // Ghost: save the prefix before naf is modified (for odd branch proof)
            let ghost old_naf_prefix = naf@.take(pos as int);

            if window & 1 == 0 {
                // Even window: emit 0, advance by 1
                proof {
                    assert(window % 2 == 0) by (bit_vector)
                        requires
                            window & 1u64 == 0u64,
                    ;
                    assert((carry as nat + extracted) % 2 == 0) by {
                        assert(window as nat == carry as nat + extracted);
                    };
                    // Reconstruction invariant advances from pos to pos+1
                    assert(reconstruct(naf@.take((pos + 1) as int)) + (carry as int) * pow2(
                        (pos + 1) as nat,
                    ) as int == (scalar_val as int) % pow2((pos + 1) as nat) as int) by {
                        lemma_naf_even_step(
                            naf@,
                            pos as nat,
                            carry as nat,
                            scalar_val,
                            w as nat,
                            extracted,
                        );
                    };
                    // Terminal carry: pos=255, carry=1 leads to contradiction
                    // (extracted=0, window=1, but window&1==0)
                    if pos >= 255 && carry == 1 {
                        assert(extracted == 0nat) by {
                            assert(scalar_val / pow2(pos as nat) == 0nat) by {
                                lemma_naf_high_bits_zero(scalar_val, pos as nat);
                            };
                            assert(0nat % pow2(w as nat) == 0nat) by {
                                lemma_pow2_pos(w as nat);
                                lemma_small_mod(0nat, pow2(w as nat));
                            };
                        };
                        assert(false) by {
                            assert(window == 1u64);
                            assert(window & 1u64 == 1u64) by (bit_vector)
                                requires
                                    window == 1u64,
                            ;
                        };
                    }
                    assert(naf@[pos as int] == 0i8);
                }
                pos += 1;
                continue ;
            }
            // Truncate casts are safe: window < width = 2^w with w <= 8, so both fit in i8.

            if window < width / 2 {
                carry = 0;
                /* ORIGINAL CODE:
                naf[pos] = window as i8;
                 */
                #[cfg(verus_keep_ghost)]
                {
                    naf[pos] = #[verifier::truncate]
                    (window as i8);
                }
                #[cfg(not(verus_keep_ghost))]
                {
                    naf[pos] = window as i8;
                }
            } else {
                carry = 1;
                /* ORIGINAL CODE:
                naf[pos] = (window as i8).wrapping_sub(width as i8);
                 */
                #[cfg(verus_keep_ghost)]
                {
                    naf[pos] = (#[verifier::truncate]
                    (window as i8)).wrapping_sub(
                        #[verifier::truncate]
                        (width as i8),
                    );
                }
                #[cfg(not(verus_keep_ghost))]
                {
                    naf[pos] = (window as i8).wrapping_sub(width as i8);
                }
            }

            // Odd window: prove invariant preservation at pos + w
            proof {
                let new_pos_int: int = pos + w;

                // The prefix naf@.take(pos) is unchanged after writing to naf[pos]
                // (take(pos) only includes indices 0..pos-1)
                assert(naf@.take(pos as int) =~= old_naf_prefix);

                // Recover the old invariant with old_carry (before carry was modified)
                assert(reconstruct(naf@.take(pos as int)) + (old_carry as int) * pow2(
                    pos as nat,
                ) as int == (scalar_val as int) % pow2(pos as nat) as int);

                assert(extracted < pow2(w as nat)) by {
                    lemma_pow2_pos(w as nat);
                };
                assert(window as nat == old_carry as nat + extracted);

                // Digit relationship: naf[pos] = window - carry * 2^w
                if window < width / 2 {
                    // Positive case: naf[pos] = window, carry = 0
                    assert((window as i8) as int == window as int) by {
                        assert(width / 2 <= 128u64) by (bit_vector)
                            requires
                                width == 1u64 << (w as u64),
                                2u64 <= (w as u64) && (w as u64) <= 8u64,
                        ;
                        assert(window <= 127u64);
                    };
                    assert(carry == 0u64);
                } else {
                    // Negative case: naf[pos] = window - width, carry = 1
                    assert(carry == 1u64);
                    assert(window % 2 == 1) by (bit_vector)
                        requires
                            window & 1u64 != 0u64,
                    ;
                    assert(window <= width) by {
                        assert((bit_buf & window_mask) <= window_mask) by (bit_vector);
                    };
                    assert(naf@[pos as int] as int == window as int - width as int) by {
                        lemma_naf_wrapping_sub_correct(window, width, w);
                    };
                    assert(width as nat == pow2(w as nat)) by {
                        lemma_u64_shift_is_pow2(w as nat);
                    };
                }
                assert(naf@[pos as int] as int == (old_carry as int + extracted as int) - (
                carry as int) * pow2(w as nat) as int);

                // NAF digit validity: digit is odd and in (-2^(w-1), 2^(w-1))
                assert({
                    let d = naf@[pos as int] as int;
                    d % 2 != 0 && -pow2((w - 1) as nat) < d && d < pow2((w - 1) as nat)
                }) by {
                    assert(window % 2 == 1) by (bit_vector)
                        requires
                            window & 1u64 != 0u64,
                    ;
                    assert(window >= 1u64) by (bit_vector)
                        requires
                            window & 1u64 != 0u64,
                    ;
                    assert(window <= width) by {
                        assert((bit_buf & window_mask) <= window_mask) by (bit_vector);
                    };
                    lemma_naf_digit_bounds(window, w, width);
                };

                assert(forall|j: int| pos < j < pos + w && j < 256 ==> naf@[j] == 0i8);

                // Reconstruction invariant advances from pos to pos+w
                assert({
                    let end_pos = if pos + w <= 256 {
                        (pos + w) as nat
                    } else {
                        256nat
                    };
                    reconstruct(naf@.take(end_pos as int)) + (carry as int) * pow2(
                        (pos + w) as nat,
                    ) as int == (scalar_val as int) % pow2((pos + w) as nat) as int
                }) by {
                    lemma_naf_odd_step(
                        naf@,
                        pos as nat,
                        w as nat,
                        scalar_val,
                        old_carry as nat,
                        carry as nat,
                        extracted,
                    );
                };

                // The zeros invariant: positions >= pos+w are still 0
                // (we only wrote to position pos, and positions pos+1.. were 0 from invariant)
                assert(forall|j: int| new_pos_int <= j < 256 ==> naf@[j] == 0i8);

                // Terminal carry: if pos + w >= 256, carry == 0
                // (extracted is small enough that the positive branch was taken)
                if pos + w >= 256 {
                    if pos >= 255 {
                        assert(window < width / 2) by {
                            assert(extracted == 0nat) by {
                                assert(scalar_val / pow2(pos as nat) == 0nat) by {
                                    lemma_naf_high_bits_zero(scalar_val, pos as nat);
                                };
                                assert(0nat % pow2(w as nat) == 0nat) by {
                                    lemma_pow2_pos(w as nat);
                                    lemma_small_mod(0nat, pow2(w as nat));
                                };
                            };
                            assert(window <= 1u64);
                            assert(width >= 4u64) by (bit_vector)
                                requires
                                    width == 1u64 << (w as u64),
                                    2u64 <= (w as u64) && (w as u64) <= 8u64,
                            ;
                        };
                    } else {
                        // pos < 255, pos + w >= 256, so gap = 255 - pos < w
                        let gap = (255 - pos) as nat;
                        assert(window < width / 2) by {
                            assert(scalar_val / pow2(pos as nat) < pow2(gap)) by {
                                lemma_pow2_pos(pos as nat);
                                lemma_pow2_strictly_increases(pos as nat, 255);
                                lemma_pow2_adds(pos as nat, gap);
                                lemma_div_strictly_bounded(
                                    scalar_val as int,
                                    pow2(pos as nat) as int,
                                    pow2(gap) as int,
                                );
                            };
                            // gap < w, so small_mod gives extracted == scalar_val / pow2(pos)
                            assert(extracted == scalar_val / pow2(pos as nat) && extracted < pow2(
                                gap,
                            )) by {
                                lemma_pow2_strictly_increases(gap, w as nat);
                                lemma_small_mod(scalar_val / pow2(pos as nat), pow2(w as nat));
                            };
                            assert(pow2(gap) <= pow2((w - 1) as nat)) by {
                                if gap < (w - 1) as nat {
                                    lemma_pow2_strictly_increases(gap, (w - 1) as nat);
                                }
                            };
                            assert(pow2((w - 1) as nat) == width / 2) by {
                                lemma_pow2_adds((w - 1) as nat, 1);
                                assert(pow2(1) == 2) by {
                                    lemma2_to64();
                                };
                                lemma_u64_shift_is_pow2(w as nat);
                            };
                            // window <= pow2(gap) but window is odd and pow2(gap) is even,
                            // so window < pow2(gap) <= width/2
                            assert(window as nat <= pow2(gap));
                            assert(pow2(gap) % 2 == 0) by {
                                assert(gap >= 1nat);
                                lemma_pow2_adds(1, (gap - 1) as nat);
                                assert(pow2(1) == 2) by {
                                    lemma2_to64();
                                };
                            };
                            assert(window % 2 == 1) by (bit_vector)
                                requires
                                    window & 1u64 != 0u64,
                            ;
                            assert(window as nat != pow2(gap));
                            assert(!(window as nat >= pow2(gap)));
                            assert(!((window as nat) >= (width / 2) as nat));
                        };
                    }
                    assert(carry == 0u64);
                }
            }
            pos += w;
        }

        // Post-loop: carry = 0 and reconstruction equals scalar_val
        proof {
            assert(carry == 0);
            let p: int = if pos <= 256 {
                pos as int
            } else {
                256int
            };

            // scalar_val % pow2(pos) == scalar_val (since scalar < 2^255 < 2^pos)
            assert((scalar_val as int) % pow2(pos as nat) as int == scalar_val as int) by {
                lemma_pow2_strictly_increases(255, pos as nat);
                lemma_small_mod(scalar_val, pow2(pos as nat));
            };

            assert(reconstruct(naf@) == scalar_val as int) by {
                // From invariant with carry == 0:
                assert(reconstruct(naf@.take(p)) == (scalar_val as int) % pow2(pos as nat) as int);
                // naf@.take(p) =~= naf@ since p >= 256 and naf has 256 elements
                assert(naf@.take(p) =~= naf@) by {
                    assert(p >= 256);
                    assert(naf@.take(p) =~= naf@.take(256));
                    assert(naf@.take(256) =~= naf@);
                };
            };

            assert(is_valid_naf(naf@, w as nat));
        }

        naf
    }

    /// Write this scalar in radix 16, with coefficients in \\([-8,8)\\),
    /// i.e., compute \\(a\_i\\) such that
    /// $$
    ///    a = a\_0 + a\_1 16\^1 + \cdots + a_{63} 16\^{63},
    /// $$
    /// with \\(-8 \leq a_i < 8\\) for \\(0 \leq i < 63\\) and \\(-8 \leq a_{63} \leq 8\\).
    ///
    /// The largest value that can be decomposed like this is just over \\(2^{255}\\). Thus, in
    /// order to not error, the top bit MUST NOT be set, i.e., `Self` MUST be less than
    /// \\(2^{255}\\).
    pub(crate) fn as_radix_16(&self) -> (result: [i8; 64])
        requires
    // Top bit must be clear (scalar < 2^255)

            self.bytes[31] <= 127,
        ensures
    // Result digits are in valid range

            is_valid_radix_16(&result),
            // Simple bounds: all digits in [-8, 8] for easy access
            radix_16_all_bounded(&result),
            // Reconstruction property: digits reconstruct the scalar value
            reconstruct_radix_16(result@) == scalar_as_nat(self) as int,
    {
        // VERIFICATION NOTE: we tell verus not to verify debug assertions
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(self[31] <= 127);
        let mut output = [0i8;64];

        // Step 1: change radix.
        // Convert from radix 256 (bytes) to radix 16 (nibbles)
        // VERIFICATION NOTE: Moved helper functions outside for Verus compatibility
        /* <ORIGINAL CODE>
            #[allow(clippy::identity_op)]
            #[inline(always)]
            fn bot_half(x: u8) -> u8 {
                (x >> 0) & 15
            }
            #[inline(always)]
            fn top_half(x: u8) -> u8 {
                (x >> 4) & 15
            }

            for i in 0..32 {
                output[2 * i] = bot_half(self[i]) as i8;
                output[2 * i + 1] = top_half(self[i]) as i8;
            }
            </ORIGINAL CODE> */
        for i in 0..32
            invariant
        // Assigned entries: nibbles of processed bytes (pair relationship)

                forall|j: int|
                    #![trigger output[2 * j], output[2 * j + 1]]
                    0 <= j < i ==> output[2 * j] as int + 16 * (output[2 * j + 1] as int)
                        == self.bytes[j] as int,
                // All assigned entries are non-negative (in [0, 15])
                forall|j: int| 0 <= j < 2 * i ==> 0 <= #[trigger] output[j] && output[j] <= 15,
                // Unassigned entries are still zero
                forall|j: int| 2 * i <= j < 64 ==> #[trigger] output[j] == 0,
        {
            output[2 * i] = bot_half(self.bytes[i]) as i8;
            output[2 * i + 1] = top_half(self.bytes[i]) as i8;
            proof {
                // Nibble identity: byte == (byte % 16) + 16 * (byte / 16)
                let b = self.bytes[i as int];
                assert((b as u8) == (b as u8) % 16 + 16 * ((b as u8) / 16)) by (bit_vector);
            }
        }
        proof {
            // output[63] <= 7: from nibble identity at j=31 and precondition bytes[31] <= 127
            // Trigger the quantifier for j=31: output[2*31] and output[2*31+1]
            let j: int = 31;
            assert(output[2 * j] as int + 16 * (output[2 * j + 1] as int) == self.bytes[j] as int);
            assert(output[2 * j] >= 0);
            assert(self.bytes[31] <= 127);
            assert(output[63] <= 7) by {
                if output[63] >= 8i8 {
                    lemma_mul_left_inequality(8, output[63] as int, 16);
                    // 128 <= 16 * output[63], plus output[62] >= 0, contradicts sum <= 127
                    assert(false);
                }
            };

            // Establish the reconstruction property
            lemma_bytes32_to_radix16_nibbles(output, self.bytes);
        }

        // Step 2: recenter coefficients from [0,16) to [-8,8)
        for i in 0..63
            invariant
        // Reconstruction is preserved through carry operations

                reconstruct_radix_16(output@) == scalar_as_nat(self) as int,
                // Recentered prefix: digits 0..i are in [-8, 8)
                forall|j: int| 0 <= j < i ==> -8 <= #[trigger] output[j] && output[j] < 8,
                // Current entry: could have received carry from previous iteration
                0 <= output[i as int] && output[i as int] <= 16,
                // Untouched suffix: digits (i+1)..62 are in [0, 15]
                forall|j: int| i < j < 63 ==> 0 <= #[trigger] output[j] && output[j] <= 15,
                // Last digit: output[63] <= 7 before carry from i=62, <= 8 after
                0 <= output[63],
                i <= 62 ==> output[63] <= 7,
                i > 62 ==> output[63] <= 8,
        {
            // Save old value for proofs
            let old_oi = output[i];
            let ghost old_output = output;

            // Exec intermediate for bit_vector proofs (needs i8 type)
            let oi_plus_8: i8 = old_oi + 8;

            let carry = (output[i] + 8) >> 4;
            // carry is 0 or 1
            assert(oi_plus_8 >> 4u32 == 0i8 || oi_plus_8 >> 4u32 == 1i8) by (bit_vector)
                requires
                    8i8 <= oi_plus_8 && oi_plus_8 <= 24i8,
            ;
            proof {
                assert(carry == 0 || carry == 1);
            }
            // carry << 4 is 0 or 16 (no overflow)
            assert(carry << 4u32 == 0i8 || carry << 4u32 == 16i8) by (bit_vector)
                requires
                    carry == 0i8 || carry == 1i8,
            ;

            output[i] -= carry << 4;
            // output[i] is now in [-8, 7]
            assert(old_oi - ((oi_plus_8 >> 4u32) << 4u32) >= -8i8) by (bit_vector)
                requires
                    8i8 <= oi_plus_8 && oi_plus_8 <= 24i8,
                    old_oi == oi_plus_8 - 8i8,
            ;
            assert(old_oi - ((oi_plus_8 >> 4u32) << 4u32) < 8i8) by (bit_vector)
                requires
                    8i8 <= oi_plus_8 && oi_plus_8 <= 24i8,
                    old_oi == oi_plus_8 - 8i8,
            ;
            // carry * 16 == carry << 4 (connects bit shift to arithmetic)
            assert((oi_plus_8 >> 4u32) * 16i8 == (oi_plus_8 >> 4u32) << 4u32) by (bit_vector)
                requires
                    8i8 <= oi_plus_8 && oi_plus_8 <= 24i8,
            ;

            /* <ORIGINAL CODE> :
                output[i + 1] += carry;
                </ORIGINAL CODE> */
            // VERIFICATION NOTE: Changed += to explicit assignment for Verus compatibility
            // Verus doesn't support += on indexed arrays with computed indices
            let next_idx = i + 1;
            output[next_idx] += carry;
            proof {
                // output[i+1] is still bounded after carry
                if i + 1 < 63 {
                    assert(0 <= output[(i + 1) as int] && output[(i + 1) as int] <= 16);
                } else {
                    assert(0 <= output[63] && output[63] <= 8);
                }

                // Reconstruction is preserved: prove preconditions then apply lemma
                let new_output = output;
                assert(pow2(4) == 16) by {
                    lemma2_to64();
                }
                assert(new_output@[i as int] == old_output@[i as int] - (carry as int) * 16);
                assert(new_output@[(i + 1) as int] == old_output@[(i + 1) as int] + carry as int);
                assert forall|j: int| 0 <= j < 64 && j != i && j != i + 1 implies old_output@[j]
                    == new_output@[j] by {}
                lemma_carry_preserves_reconstruction(
                    old_output@,
                    new_output@,
                    i as nat,
                    carry as int,
                    4,
                );
            }
        }
        proof {
            // Postcondition 1: is_valid_radix_16
            assert(pow2(3) == 8) by {
                lemma2_to64();
            }
            assert forall|idx: int| 0 <= idx < 64 implies {
                let bound = pow2(3) as int;
                if idx < 63 {
                    -bound <= (#[trigger] output[idx]) && output[idx] < bound
                } else {
                    -bound <= (#[trigger] output[idx]) && output[idx] <= bound
                }
            } by {
                if idx < 63 {
                    assert(-8 <= output[idx] && output[idx] < 8);
                } else {
                    assert(0 <= output[63] && output[63] <= 8);
                }
            }
            assert(is_valid_radix_16(&output));

            // Postcondition 2: radix_16_all_bounded (follows from is_valid_radix_16)
            lemma_valid_radix_16_implies_all_bounded(output);

            // Postcondition 3: reconstruction property (maintained by loop 2 invariant)
            assert(reconstruct_radix_16(output@) == scalar_as_nat(self) as int);
        }

        output
    }

    /// Returns a size hint indicating how many entries of the return
    /// value of `to_radix_2w` are nonzero.
    pub(crate) fn to_radix_2w_size_hint(w: usize) -> usize
        requires
            4 <= w <= 8,
        returns
            if w < 8 {
                (256 + w - 1) / (w as int)
            } else {
                (256 + w - 1) / (w as int) + 1
            } as usize,
    {
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(w >= 4);
        #[cfg(not(verus_keep_ghost))]
            debug_assert!(w <= 8);

        let digits_count = match w {
            4..=7 => (256 + w - 1) / w,
            // See comment in to_radix_2w on handling the terminal carry.
            8 => (256 + w - 1) / w + 1_usize,
            // VERIFICATION NOTE: Verus doesn't understand `panic!`.
            // Tell Verus this unreachable branch returns a (wrong) value.
            // Tell rustc this panics.
            _ => {
                #[cfg(not(verus_keep_ghost))]
                panic!("invalid radix parameter");

                #[cfg(verus_keep_ghost)]
                42
            },
        };

        #[cfg(not(verus_keep_ghost))]
            debug_assert!(digits_count <= 64);

        digits_count
    }

    /// Creates a representation of a Scalar in radix \\( 2^w \\) with \\(w = 4, 5, 6, 7, 8\\) for
    /// use with the Pippenger algorithm. Higher radixes are not supported to save cache space.
    /// Radix 256 is near-optimal even for very large inputs.
    ///
    /// Radix below 16 or above 256 is prohibited.
    /// This method returns digits in a fixed-sized array, excess digits are zeroes.
    ///
    /// For radix 16, `Self` must be less than \\(2^{255}\\). This is because most integers larger
    /// than \\(2^{255}\\) are unrepresentable in the form described below for \\(w = 4\\). This
    /// would be true for \\(w = 8\\) as well, but it is compensated for by increasing the size
    /// hint by 1.
    ///
    /// ## Scalar representation
    ///
    /// Radix \\(2\^w\\), with \\(n = ceil(256/w)\\) coefficients in \\([-(2\^w)/2,(2\^w)/2)\\),
    /// i.e., scalar is represented using digits \\(a\_i\\) such that
    /// $$
    ///    a = a\_0 + a\_1 2\^1w + \cdots + a_{n-1} 2\^{w*(n-1)},
    /// $$
    /// with \\(-2\^w/2 \leq a_i < 2\^w/2\\) for \\(0 \leq i < (n-1)\\) and \\(-2\^w/2 \leq a_{n-1} \leq 2\^w/2\\).
    ///
    #[cfg(any(feature = "alloc", feature = "precomputed-tables"))]
    #[verifier::loop_isolation(false)]
    pub(crate) fn as_radix_2w(&self, w: usize) -> (result: [i8; 64])
        requires
            4 <= w <= 8,
            // For w=4 (radix 16), top bit must be clear
            w == 4 ==> self.bytes[31] <= 127,
        ensures
            ({
                let digits_count = if w < 8 {
                    (256 + (w as int) - 1) / (w as int)
                } else {
                    (256 + (w as int) - 1) / (w as int) + 1
                };
                // Result digits are in valid range for the given window size
                is_valid_radix_2w(&result, w as nat, digits_count as nat)
                    &&
                // Reconstruction property: digits reconstruct the scalar value
                reconstruct_radix_2w(result@.take(digits_count), w as nat) == scalar_as_nat(
                    self,
                ) as int
            }),
    {
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(w >= 4);
        #[cfg(not(verus_keep_ghost))]
        debug_assert!(w <= 8);

        if w == 4 {
            let result = self.as_radix_16();
            // VERIFICATION NOTE: Prove that as_radix_16 postcondition implies as_radix_2w postcondition for w=4
            proof {
                assert(w == 4);
                assert(w as int == 4);
                // For w=4: digits_count = (256 + 4 - 1) / 4 = 259 / 4 = 64
                assert(((256 + (w as int) - 1) / (w as int)) == ((256 + 4 - 1) / 4));
                assert(((256 + 4 - 1) / 4) == 64) by (compute);
                // is_valid_radix_16 is defined as is_valid_radix_2w(digits, 4, 64)
                assert(is_valid_radix_16(&result) == is_valid_radix_2w(&result, 4, 64));
                // reconstruct_radix_16 is defined as reconstruct_radix_2w(digits, 4)
                assert(reconstruct_radix_16(result@) == reconstruct_radix_2w(result@, 4));
                // result@.take(64) == result@ since result has exactly 64 elements
                assert(result@.take(64) =~= result@);
            }
            return result;
        }
        // Scalar formatted as four `u64`s with carry bit packed into the highest bit.
        // VERIFICATION NOTE: Inline the read_le_u64_into logic to avoid Verus unsupported features
        /* <ORIGINAL CODE>
        let mut scalar64x4 = [0u64; 4];
        read_le_u64_into(&self.bytes, &mut scalar64x4[0..4]);
        </ORIGINAL CODE> */
        // Read 4 u64s from the 32-byte array (self.bytes).
        // Named arrays serve double duty: exec (u64_from_le_bytes) and proof (lemma_u64x4_from_le_bytes).

        let chunk0: [u8; 8] = [
            self.bytes[0],
            self.bytes[1],
            self.bytes[2],
            self.bytes[3],
            self.bytes[4],
            self.bytes[5],
            self.bytes[6],
            self.bytes[7],
        ];
        let chunk1: [u8; 8] = [
            self.bytes[8],
            self.bytes[9],
            self.bytes[10],
            self.bytes[11],
            self.bytes[12],
            self.bytes[13],
            self.bytes[14],
            self.bytes[15],
        ];
        let chunk2: [u8; 8] = [
            self.bytes[16],
            self.bytes[17],
            self.bytes[18],
            self.bytes[19],
            self.bytes[20],
            self.bytes[21],
            self.bytes[22],
            self.bytes[23],
        ];
        let chunk3: [u8; 8] = [
            self.bytes[24],
            self.bytes[25],
            self.bytes[26],
            self.bytes[27],
            self.bytes[28],
            self.bytes[29],
            self.bytes[30],
            self.bytes[31],
        ];

        let mut scalar64x4 = [0u64;4];
        scalar64x4[0] = u64_from_le_bytes(chunk0);
        scalar64x4[1] = u64_from_le_bytes(chunk1);
        scalar64x4[2] = u64_from_le_bytes(chunk2);
        scalar64x4[3] = u64_from_le_bytes(chunk3);

        // Subgoal: u64x4 words reconstruct scalar_val (paper Section 3)
        let ghost scalar_val: nat = scalar_as_nat(self);
        proof {
            assert(bytes_as_nat_prefix(chunk0@, 8) + bytes_as_nat_prefix(chunk1@, 8) * pow2(64)
                + bytes_as_nat_prefix(chunk2@, 8) * pow2(128) + bytes_as_nat_prefix(chunk3@, 8)
                * pow2(192) == u8_32_as_nat(&self.bytes)) by {
                lemma_u64x4_from_le_bytes(self.bytes, chunk0, chunk1, chunk2, chunk3);
            }
            // Bridge: u64_4_as_nat matches scalar_val (used by bit extraction lemmas)
            assert(u64_4_as_nat(&scalar64x4) == scalar_val);
        }

        // Subgoal: Radix and window mask properties
        let radix: u64 = 1 << w;
        proof {
            assert(radix >= 1u64) by (bit_vector)
                requires
                    radix == 1u64 << (w as u64),
                    4u64 <= (w as u64) <= 8u64,
            ;
        }
        let window_mask: u64 = radix - 1;

        let mut carry = 0u64;
        let mut digits = [0i8;64];
        let digits_count = (256 + w - 1) / w;
        proof {
            assert(digits_count <= 52 && digits_count > 0 && digits_count * w >= 256 && digits_count
                * w <= 256 + w - 1 && radix <= 256u64 && radix as nat == pow2(w as nat)) by {
                lemma_digits_count_radix_bounds(w, digits_count);
            }
            assert(pow2(w as nat) >= 1) by {
                lemma_pow2_pos(w as nat);
            }
            assert(radix as nat == pow2(w as nat));
            // Subgoal: scalar_val < pow2(256)
            assert(scalar_val < pow2(256)) by {
                lemma_u8_32_as_nat_with_trailing_zeros(&self.bytes, 32);
                lemma_bytes_as_nat_prefix_bounded(self.bytes@, 32);
            }
            // Subgoal: Loop invariant base case (i=0)
            lemma2_to64();
            assert(reconstruct_radix_2w(digits@.take(0int), w as nat) == 0int) by {
                assert(digits@.take(0int).len() == 0);
            }
            assert((scalar_val as int) % (pow2(0nat) as int) == 0) by {
                lemma_small_mod(0 as nat, 1 as nat);
            }
            assert(w * 0 == 0) by {
                lemma_mul_basics(w as int);
            }
        }
        #[allow(clippy::needless_range_loop)]
        for i in 0..digits_count
            invariant
        // Core invariant: reconstruction + carry == scalar mod pow2(w*i)

                carry <= 1,
                reconstruct_radix_2w(digits@.take(i as int), w as nat) + (carry as int) * (pow2(
                    (w * i) as nat,
                ) as int) == (scalar_val as int) % (pow2((w * i) as nat) as int),
                // Digit bounds: processed digits are in [-2^(w-1), 2^(w-1))
                forall|j: int|
                    0 <= j < i ==> {
                        let bound = pow2((w - 1) as nat) as int;
                        -bound <= (#[trigger] digits[j]) && digits[j] < bound
                    },
                // Unassigned digits are zero
                forall|j: int| #![auto] i <= j < 64 ==> digits[j] == 0i8,
                // Final carry is 0 for w < 8 (needed for postcondition)
                (w < 8 && i == digits_count) ==> carry == 0,
        {
            proof {
                assert(w != 4);
                assert(5 <= w);
                // i*w < digits_count*w (overflow check on the exec multiplication i * w)
                assert(i * w < digits_count * w) by {
                    lemma_mul_strict_inequality(i as int, digits_count as int, w as int);
                }
                // Strengthen bound explicitly so `bit_offset <= 255` is available later.
                // (i+1)*w <= digits_count*w <= 256+w-1, so i*w+w <= 256+w-1, hence i*w <= 255
                assert((i * w) as int <= 255) by {
                    lemma_mul_inequality(i as int + 1, digits_count as int, w as int);
                    lemma_mul_is_distributive_add_other_way(w as int, i as int, 1int);
                };
            }
            let bit_offset = i * w;
            let u64_idx = bit_offset / 64;
            let bit_idx = bit_offset % 64;

            proof {
                // bit_offset + w == (i+1)*w <= digits_count*w <= 256+w-1 <= 263
                // so bit_offset <= 255, hence u64_idx = bit_offset/64 <= 255/64 = 3
                assert(bit_offset <= 255) by {
                    assert(bit_offset == i * w);
                    assert((i * w) as int <= 255);
                }
                assert(bit_offset <= 255 && u64_idx <= 3) by {
                    lemma_mul_is_distributive_add(w as int, i as int, 1);
                    lemma_mul_basics(w as int);
                    lemma_mul_inequality((i + 1) as int, digits_count as int, w as int);
                    lemma_div_is_ordered(bit_offset as int, 255, 64);
                }
            }

            // Read the bits from the scalar
            let bit_buf: u64 = if bit_idx < 64 - w || u64_idx == 3 {
                // This window's bits are contained in a single u64,
                // or it's the last u64 anyway.
                scalar64x4[u64_idx] >> bit_idx
            } else {
                // Combine the current u64's bits with the bits from the next u64
                (scalar64x4[u64_idx] >> bit_idx) | (scalar64x4[1 + u64_idx] << (64 - bit_idx))
            };

            // Prove extracted < radix BEFORE the coef computation (needed for overflow check)
            assert((bit_buf & window_mask) < radix) by (bit_vector)
                requires
                    window_mask == radix - 1u64,
                    radix > 0u64,
            ;

            // Read the actual coefficient value from the window
            // carry <= 1 (invariant), extracted < radix <= 256, so coef <= radix. No overflow.
            let coef = carry + (bit_buf & window_mask);

            proof {
                assert(coef <= radix);
                // Bit extraction: (bit_buf & window_mask) == (scalar_val / pow2(w*i)) % pow2(w)
                assert((bit_buf & window_mask) as nat == (u64_4_as_nat(&scalar64x4) / pow2(
                    bit_offset as nat,
                )) % pow2(w as nat)) by {
                    lemma_u64x4_bit_extraction(
                        scalar64x4,
                        bit_buf,
                        window_mask,
                        w,
                        bit_offset,
                        u64_idx,
                        bit_idx,
                    );
                }
                // bit_offset == i*w == w*i (commutativity for pow2 argument)
                assert(bit_offset == w * i) by {
                    lemma_mul_is_commutative(i as int, w as int);
                }
            }

            let ghost extracted: nat = (bit_buf & window_mask) as nat;
            let ghost old_carry = carry;
            let ghost old_digits = digits;

            // Recenter coefficients from [0,2^w) to [-2^w/2, 2^w/2).
            /* <ORIGINAL CODE>
            carry = (coef + (radix / 2)) >> w;
            let coef_i64 = coef as i64;
            let carry_shifted = (carry << w) as i64;
            digits[i] = (coef_i64 - carry_shifted) as i8;
            </ORIGINAL CODE> */
            let half_radix: u64 = radix / 2;
            carry = (coef + half_radix) >> w;
            let new_carry: u64 = carry;

            // Prove carry bound BEFORE carry_times_radix computation
            assert(new_carry <= 1u64) by (bit_vector)
                requires
                    new_carry == ((coef + half_radix) as u64) >> w,
                    coef <= radix,
                    half_radix == radix / 2u64,
                    radix == 1u64 << (w as u64),
                    5u64 <= (w as u64) <= 8u64,
            ;

            let coef_i64: i64 = coef as i64;
            let carry_shifted_u64: u64 = carry << w;
            let carry_shifted: i64 = carry_shifted_u64 as i64;
            proof {
                // Re-establish the algebraic bridge from the original shift to `new_carry * radix`.
                assert(new_carry * pow2(w as nat) <= u64::MAX) by {
                    assert(new_carry <= 1);
                    assert(pow2(w as nat) <= 256) by {
                        assert(radix as nat == pow2(w as nat));
                        assert(radix <= 256u64);
                    }
                    lemma_mul_upper_bound(new_carry as int, pow2(w as nat) as int, 1, 256);
                }
                assert(carry_shifted_u64 == new_carry * pow2(w as nat)) by {
                    lemma_u64_shl_is_mul(new_carry, w as u64);
                }
                assert(pow2(w as nat) == radix as nat);
                assert(carry_shifted_u64 == new_carry * radix);
                assert(carry_shifted_u64 <= 256u64);
                assert(carry_shifted_u64 <= i64::MAX as u64);
            }

            // Prove i8 cast bounds BEFORE the cast
            assert(coef_i64 - carry_shifted >= -128i64 && coef_i64 - carry_shifted <= 127i64)
                by (bit_vector)
                requires
                    coef_i64 == coef as i64,
                    carry_shifted == carry_shifted_u64 as i64,
                    carry_shifted_u64 == new_carry * radix,
                    new_carry == ((coef + half_radix) as u64) >> w,
                    coef <= radix,
                    half_radix == radix / 2u64,
                    radix == 1u64 << (w as u64),
                    5u64 <= (w as u64) <= 8u64,
            ;

            /* <ORIGINAL CODE>
            digits[i] = (coef_i64 - carry_shifted) as i8;
            </ORIGINAL CODE> */
            let digit_i8: i8 = (coef_i64 - carry_shifted) as i8;

            // Cast preservation: i8 roundtrip preserves value when in [-128, 127]
            assert(digit_i8 as i64 == coef_i64 - carry_shifted) by (bit_vector)
                requires
                    digit_i8 == (coef_i64 - carry_shifted) as i8,
                    coef_i64 - carry_shifted >= -128i64,
                    coef_i64 - carry_shifted <= 127i64,
            ;

            digits[i] = digit_i8;

            // Cast bridges: u64->i64 preserves value for small non-negative values
            assert(coef_i64 as int == coef as int);
            assert(carry_shifted as int == carry_shifted_u64 as int);

            proof {
                // ---- Loop invariant preservation (paper Section 6) ----
                // Ghost bindings for pow2 values used across subgoals
                // (also required for solver context stability)
                let digit_val = digits[i as int] as int;
                let pw = pow2(w as nat) as int;

                // Subgoal 1: digit = coef - new_carry * 2^w
                assert(digit_val == coef as int - new_carry as int * pw) by {
                    // digit_i8 as int == coef as int - carry_times_radix as int
                    // (from bit_vector via i64 bridge)
                }

                // Subgoal 2: coef = old_carry + extracted
                assert(coef as int == old_carry as int + extracted as int);

                // Subgoal 3: Digit bounds via recentering (paper Section 7)
                assert(-pow2((w - 1) as nat) as int <= digit_val && digit_val < pow2(
                    (w - 1) as nat,
                ) as int) by {
                    lemma_radix_2w_digit_bounds(coef, w, new_carry);
                }

                // Subgoal 4: Invariant preservation (paper Section 6)
                // recon(i+1) + carry * 2^(w*(i+1)) == scalar_val mod 2^(w*(i+1))
                assert(digits@.take((i + 1) as int) =~= old_digits@.take(i as int).push(
                    digits[i as int],
                ));
                assert(digits@.take((i + 1) as int).take(i as int) =~= digits@.take(i as int));
                assert(digits@.take(i as int) =~= old_digits@.take(i as int));

                assert(reconstruct_radix_2w(digits@.take((i + 1) as int), w as nat) + (carry as int)
                    * pow2((w * (i + 1)) as nat) as int == (scalar_val as int) % pow2(
                    (w * (i + 1)) as nat,
                ) as int) by {
                    lemma_radix_2w_loop_reconstruction_step(
                        digits@.take((i + 1) as int),
                        i,
                        w,
                        scalar_val,
                        old_carry,
                        new_carry,
                        extracted,
                    );
                }

                // Subgoal 5: Final carry = 0 at last iteration for w < 8 (paper Section 8)
                if w < 8 && i + 1 == digits_count {
                    let extracted_u64: u64 = (bit_buf & window_mask) as u64;
                    assert(coef < half_radix) by {
                        lemma_last_iter_carry_zero(scalar_val, old_carry, extracted_u64, w, i);
                    }

                    assert(carry == 0u64) by (bit_vector)
                        requires
                            carry == (((coef + half_radix) as u64) >> (w as u64)),
                            (coef as u64) < (half_radix as u64),
                            half_radix == radix / 2u64,
                            radix == 1u64 << (w as u64),
                            5u64 <= (w as u64) <= 8u64,
                    ;
                }
            }
        }

        // When 4 < w < 8, we can fold the final carry onto the last digit d,
        // because d < 2^w/2 so d + carry*2^w = d + 1*2^w < 2^(w+1) < 2^8.
        //
        // When w = 8, we can't fit carry*2^w into an i8.  This should
        // not happen anyways, because the final carry will be 0 for
        // reduced scalars, but Scalar invariant #1 allows 255-bit scalars.
        // To handle this, we expand the size_hint by 1 when w=8,
        // and accumulate the final carry onto another digit.
        // VERIFICATION NOTE: Changed += to regular assignment to avoid Verus limitation
        /* <ORIGINAL CODE>
        match w {
            8 => digits[digits_count] += carry as i8,
            _ => digits[digits_count - 1] += (carry << w) as i8,
        }
        </ORIGINAL CODE> */
        let ghost digits_after_loop = digits;

        match w {
            8 => {
                let idx = digits_count;
                let carry_i8 = carry as i8;
                digits[idx] += carry_i8;
            },
            _ => {
                let idx = digits_count - 1;
                assert(0u64 << (w as u64) == 0u64) by (bit_vector);
                let carry_shifted: u64 = carry << w;
                let carry_shifted_i8 = carry_shifted as i8;
                digits[idx] = digits[idx] + carry_shifted_i8;
            },
        }

        proof {
            // Prove the reconstruction invariant still holds after carry adjustment
            if w == 8 {
                // w=8: only index digits_count (=32) was modified
                // take(32) is unchanged, so the loop invariant for the first 32 digits holds
                assert(digits@.take(digits_count as int) =~= digits_after_loop@.take(
                    digits_count as int,
                ));
                assert(digits[digits_count as int] as int == carry as int);
            } else {
                // w<8: carry=0, carry_shifted_i8=0, so digits[idx] + 0 = digits[idx]
                // The array take(digits_count) is effectively unchanged
                assert(carry == 0);
                assert(digits@.take(digits_count as int) =~= digits_after_loop@.take(
                    digits_count as int,
                ));
            }

            // Subgoal: Final postconditions — valid radix-2^w representation
            // that reconstructs to scalar_val
            assert({
                let final_digits_count = if w < 8 {
                    (256 + (w as int) - 1) / (w as int)
                } else {
                    (256 + (w as int) - 1) / (w as int) + 1
                };
                is_valid_radix_2w(&digits, w as nat, final_digits_count as nat)
                    && reconstruct_radix_2w(digits@.take(final_digits_count), w as nat)
                    == scalar_val as int
            }) by {
                lemma_as_radix_2w_postconditions(digits, w, digits_count, carry, scalar_val);
            }
        }

        digits
    }

    /// Unpack this `Scalar` to an `UnpackedScalar` for faster arithmetic.
    pub fn unpack(&self) -> (result:
        UnpackedScalar)
    // VERIFICATION NOTE: VERIFIED (changed pub(crate) to pub)

        ensures
            limbs_bounded(&result),
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            scalar52_to_nat(&result) == u8_32_as_nat(&self.bytes),
            is_canonical_scalar(self) ==> is_canonical_scalar52(&result),
    {
        UnpackedScalar::from_bytes(&self.bytes)
    }

    /// Reduce this `Scalar` modulo \\(\ell\\).
    #[allow(non_snake_case)]
    fn reduce(&self) -> (result: Scalar)
        ensures
    // Result is equivalent to input modulo the group order

            u8_32_as_nat(&result.bytes) % group_order() == u8_32_as_nat(&self.bytes)
                % group_order(),
            // Result satisfies Scalar invariants #1 and #2
            is_canonical_scalar(&result),
    {
        let x = self.unpack();

        assert(limbs_bounded(&constants::R)) by {
            lemma_r_bounded(constants::R);

        }

        assert(scalar52_to_nat(&constants::R) < group_order()) by {
            lemma_r_equals_spec(constants::R);
        };

        proof { lemma_limbs_bounded_implies_prod_bounded(&x, &constants::R) }

        let xR = UnpackedScalar::mul_internal(&x, &constants::R);

        proof {
            // Establish montgomery_reduce's preconditions
            lemma_bounded_product_satisfies_input_bounds(&x, &constants::R, &xR);
            // R is canonical (< L), so product satisfies canonical_bound
            lemma_r_equals_spec(constants::R);
            lemma_canonical_product_satisfies_canonical_bound(&x, &constants::R, &xR);
        }

        let x_mod_l = UnpackedScalar::montgomery_reduce(&xR);
        // is_canonical_scalar52(&x_mod_l) follows from montgomery_reduce postcondition
        let result = x_mod_l.pack();

        proof {
            assert(slice128_to_nat(&xR) == scalar52_to_nat(&x) * scalar52_to_nat(&constants::R));

            // montgomery_reduce ensures:
            assert((scalar52_to_nat(&x_mod_l) * montgomery_radix()) % group_order()
                == slice128_to_nat(&xR) % group_order());

            assert((scalar52_to_nat(&x_mod_l) * montgomery_radix()) % group_order() == (
            scalar52_to_nat(&x) * scalar52_to_nat(&constants::R)) % group_order());

            lemma_r_equals_spec(constants::R);

            lemma_mul_factors_congruent_implies_products_congruent(
                scalar52_to_nat(&x) as int,
                montgomery_radix() as int,
                scalar52_to_nat(&constants::R) as int,
                group_order() as int,
            );

            assert((scalar52_to_nat(&x_mod_l) * montgomery_radix()) % group_order() == (
            scalar52_to_nat(&x) * montgomery_radix()) % group_order());

            lemma_cancel_mul_pow2_mod(
                scalar52_to_nat(&x_mod_l),
                scalar52_to_nat(&x),
                montgomery_radix(),
            );

            assert(scalar52_to_nat(&x_mod_l) % group_order() == scalar52_to_nat(&x)
                % group_order());

            assert(u8_32_as_nat(&result.bytes) == scalar52_to_nat(&x_mod_l) % pow2(256));
            assert(scalar52_to_nat(&x_mod_l) < group_order());

            assert(group_order() < pow2(256)) by { lemma_group_order_smaller_than_pow256() };

            assert(scalar52_to_nat(&x_mod_l) < pow2(256));
            lemma_small_mod(scalar52_to_nat(&x_mod_l), pow2(256));
            assert(u8_32_as_nat(&result.bytes) == scalar52_to_nat(&x_mod_l));
        }

        result
    }

    /// Check whether this `Scalar` is the canonical representative mod \\(\ell\\). This is not
    /// public because any `Scalar` that is publicly observed is reduced, by scalar invariant #2.
    fn is_canonical(&self) -> (result: Choice)
        ensures
    // Result is true iff the scalar satisfies Scalar invariants #1 and #2

            choice_is_true(result) == is_canonical_scalar(self),
    {
        let x = &self.reduce();
        let result = self.ct_eq(x);

        proof {
            lemma_is_canonical_correctness(&self.bytes, &x.bytes);
        }
        result
    }
}

// verus!
} // verus!
verus! {

// Helper function for montgomery_invert
#[inline]
fn square_multiply(
    y: &mut UnpackedScalar,
    squarings: usize,
    x: &UnpackedScalar,
)/*  VERIFICATION NOTE:
- This function was initially inside the body of montgomery_invert, but was moved outside for Verus
*/

    requires
// Both inputs must be canonical for montgomery_square/montgomery_mul

        is_canonical_scalar52(old(y)),
        is_canonical_scalar52(x),
    ensures
        limb_prod_bounded_u128(y.limbs, y.limbs, 5),
        // Output is canonical
        is_canonical_scalar52(y),
        // VERIFICATION NOTE: Changed postcondition from the original incorrect version
        // which used `montgomery_radix()` instead of `pow(montgomery_radix(), pow2(squarings))`
        (scalar52_to_nat(y) * pow(montgomery_radix() as int, pow2(squarings as nat)) as nat)
            % group_order() == (pow(scalar52_to_nat(old(y)) as int, pow2(squarings as nat))
            * scalar52_to_nat(x)) % (group_order() as int),
{
    let ghost y0: nat = scalar52_to_nat(y);
    let ghost xv: nat = scalar52_to_nat(&x);
    let ghost R: nat = montgomery_radix();
    let ghost L: nat = group_order();

    proof {
        lemma_pow2_pos(260);
        lemma2_to64();
        lemma_pow0(R as int);
        lemma_pow1(y0 as int);
        assert(pow(R as int, 0nat) == 1);
        assert((y0 * 1) as nat == y0);

    }

    // VERIFICATION NOTE: Named loop variable allows tracking iteration count
    for idx in 0..squarings
        invariant
    // Maintain canonicity for montgomery_square

            is_canonical_scalar52(y),
            L == group_order(),
            R == montgomery_radix(),
            L > 0,
            R > 0,
            (scalar52_to_nat(y) * pow(R as int, (pow2(idx as nat) - 1) as nat) as nat) % L == (pow(
                y0 as int,
                pow2(idx as nat),
            ) as nat) % L,
    {
        let ghost y_before: nat = scalar52_to_nat(y);
        *y = y.montgomery_square();
        proof {
            lemma_square_multiply_step(scalar52_to_nat(y), y_before, y0, R, L, idx as nat);
            // limbs_bounded is maintained by montgomery_square's ensures clause
        }
    }

    let ghost y_after: nat = scalar52_to_nat(y);
    let ghost exp_final: nat = (pow2(squarings as nat) - 1) as nat;

    proof {
        lemma_limbs_bounded_implies_prod_bounded(y, x);
    }

    *y = UnpackedScalar::montgomery_mul(y, x);

    proof {
        // After loop, i == squarings (from ensures), so invariant gives us:
        assert((y_after * pow(R as int, exp_final) as nat) % L == (pow(
            y0 as int,
            pow2(squarings as nat),
        ) as nat) % L);

        let final_y: nat = scalar52_to_nat(y);
        let n: nat = squarings as nat;
        let R_exp: int = pow(R as int, exp_final);
        let R_pow2n: int = pow(R as int, pow2(n));
        let y0_pow: int = pow(y0 as int, pow2(n));

        lemma_pow2_pos(n);
        lemma_pow_adds(R as int, 1nat, exp_final);
        lemma_pow1(R as int);
        lemma_pow_nonnegative(R as int, exp_final);
        lemma_pow_nonnegative(y0 as int, pow2(n));

        assert((y_after as int * xv as int) * R_exp == (y_after as int * R_exp) * xv as int) by {
            lemma_mul_is_associative(y_after as int, xv as int, R_exp);
            lemma_mul_is_commutative(xv as int, R_exp);
            lemma_mul_is_associative(y_after as int, R_exp, xv as int);
        };

        calc! {
            (==)
            (final_y as int * R_pow2n) % (L as int); {
                lemma_mul_is_associative(final_y as int, R as int, R_exp);
            }
            ((final_y * R) as int * R_exp) % (L as int); {
                lemma_mul_mod_noop((final_y * R) as int, R_exp, L as int);
                lemma_mul_mod_noop((y_after * xv) as int, R_exp, L as int);
            }
            ((y_after * xv) as int * R_exp) % (L as int); {}
            ((y_after * R_exp as nat) as int * xv as int) % (L as int); {
                lemma_mul_mod_noop((y_after * R_exp as nat) as int, xv as int, L as int);
                lemma_mul_mod_noop(y0_pow, xv as int, L as int);
            }
            (y0_pow * xv as int) % (L as int);
        }
    }
}

impl UnpackedScalar {
    /// Pack the limbs of this `UnpackedScalar` into a `Scalar`.
    fn pack(&self) -> (result: Scalar)
        requires
            limbs_bounded(self),
        ensures
            u8_32_as_nat(&result.bytes) == scalar52_to_nat(self) % pow2(256),
            // VERIFICATION NOTE: If input is canonical (< group order), output satisfies Scalar invariants
            scalar52_to_nat(self) < group_order() ==> is_canonical_scalar(&result),
    {
        let bytes = self.as_bytes();
        proof {
            lemma_five_limbs_equals_to_nat(&self.limbs);
        }
        let result = Scalar { bytes: bytes };
        // VERIFICATION NOTE: TODO: Prove these follow from as_bytes() spec
        // result.bytes is [u8; 32]
        // group order is pow2(252) + 27742317777372353535851937790883648493nat
        // if result.bytes[31] > 127, then when we apply u8_32_as_nat, we'll end up with
        // something large than group_order, contradiction
        // bytes[31] * 2^(31*8) + ...
        // 127 * 2^(31*8) == 57443731770074831323412168344153766786583156455220123566449660816425654157312
        // group order is     7237005577332262213973186563042994240857116359379907606001950938285454250989
        // which is smaller
        // unfold with fuel 32
        // Another approach is like lemma_nine_limbs_equals_slice128_to_nat,
        // which shows that a recursive defn equals a large polynomial

        proof {
            if scalar52_to_nat(self) < group_order() {
                lemma_scalar52_lt_pow2_256_if_canonical(self);
                lemma_small_mod(scalar52_to_nat(self), pow2(256));
                assert(scalar52_to_nat(self) % pow2(256) == scalar52_to_nat(self));
                assert(u8_32_as_nat(&result.bytes) == scalar52_to_nat(self));

                let v = u8_32_as_nat(&result.bytes);

                assert(u8_32_as_nat(&result.bytes) == u8_32_as_nat(&result.bytes));

                assert(v == u8_32_as_nat(&result.bytes));
                assert(v < group_order());
                {
                    lemma_group_order_bound();
                    assert(group_order() < pow2(255));

                    assert(v < pow2(255));  // by transitivity

                    let b31: nat = result.bytes[31] as nat;
                    if b31 >= 128 {
                        // v ≥ b31*2^248 ≥ 2^255
                        use vstd::arithmetic::power2::{pow2, lemma_pow2_adds, lemma2_to64};
                        use vstd::arithmetic::mul::lemma_mul_inequality;

                        // Use the lemma
                        use crate::lemmas::common_lemmas::to_nat_lemmas::lemma_u8_32_as_nat_lower_bound;
                        lemma_u8_32_as_nat_lower_bound(&result.bytes, 31);

                        lemma_pow2_adds(7, 248);

                        lemma2_to64();

                        // Keep types consistent; either do it in `int`:
                        assert((pow2(255) as nat) == 128 * (pow2(248) as nat));
                        assert(v >= b31 * pow2(248));
                        lemma_mul_inequality(128, b31 as int, pow2(248) as int);

                        assert(b31 >= 128);
                        assert(v >= pow2(255));
                        assert(false);  // contradicts v < 2^255
                    }
                    assert(result.bytes[31] <= 127);

                    assert(is_canonical_scalar(&result));
                }
            }
        }
        result
    }

    /// Inverts an UnpackedScalar in Montgomery form.
    ///
    /// # Preconditions
    /// - Input must be canonical for `montgomery_square`/`montgomery_mul`
    ///
    #[rustfmt::skip]  // keep alignment of addition chain and squarings
    #[allow(clippy::just_underscores_and_digits)]
    pub fn montgomery_invert(&self) -> (result:
        UnpackedScalar)/* VERIFICATION NOTE:
    PROOF BYPASS
    */

        requires
    // Must be canonical for montgomery_square/montgomery_mul

            is_canonical_scalar52(self),
        ensures
            limb_prod_bounded_u128(result.limbs, result.limbs, 5),
            // Output is canonical
            is_canonical_scalar52(&result),
            (scalar52_to_nat(&result) * scalar52_to_nat(self)) % group_order() == (
            montgomery_radix() * montgomery_radix())
                % group_order(),
    // Equivalent to: from_montgomery(result) * from_montgomery(self) ≡ 1 (mod L)
    // Expressed in Montgomery form: (result/R) * (self/R) ≡ 1, i.e., result * self ≡ R² (mod L)

    {
        // Uses the addition chain from
        // https://briansmith.org/ecc-inversion-addition-chains-01#curve25519_scalar_inversion
        let _1 = *self;
        // _1 has limbs_bounded from self's precondition
        let _10 = _1.montgomery_square();
        let _100 = _10.montgomery_square();
        assert(limb_prod_bounded_u128(_10.limbs, _1.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_10, &_1);
        }
        let _11 = UnpackedScalar::montgomery_mul(&_10, &_1);
        assert(limb_prod_bounded_u128(_10.limbs, _11.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_10, &_11);
        }
        let _101 = UnpackedScalar::montgomery_mul(&_10, &_11);
        assert(limb_prod_bounded_u128(_10.limbs, _101.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_10, &_101);
        }
        let _111 = UnpackedScalar::montgomery_mul(&_10, &_101);
        assert(limb_prod_bounded_u128(_10.limbs, _111.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_10, &_111);
        }
        let _1001 = UnpackedScalar::montgomery_mul(&_10, &_111);
        assert(limb_prod_bounded_u128(_10.limbs, _1001.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_10, &_1001);
        }
        let _1011 = UnpackedScalar::montgomery_mul(&_10, &_1001);
        assert(limb_prod_bounded_u128(_100.limbs, _1011.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_100, &_1011);
        }
        let _1111 = UnpackedScalar::montgomery_mul(&_100, &_1011);
        assert(limb_prod_bounded_u128(_1111.limbs, _1.limbs, 5)) by {
            lemma_limbs_bounded_implies_prod_bounded(&_1111, &_1);
        }

        // _10000
        let mut y = UnpackedScalar::montgomery_mul(&_1111, &_1);

        square_multiply(&mut y, 123 + 3, &_101);
        square_multiply(&mut y, 2 + 2, &_11);
        square_multiply(&mut y, 1 + 4, &_1111);
        square_multiply(&mut y, 1 + 4, &_1111);
        square_multiply(&mut y, 4, &_1001);
        square_multiply(&mut y, 2, &_11);
        square_multiply(&mut y, 1 + 4, &_1111);
        square_multiply(&mut y, 1 + 3, &_101);
        square_multiply(&mut y, 3 + 3, &_101);
        square_multiply(&mut y, 3, &_111);
        square_multiply(&mut y, 1 + 4, &_1111);
        square_multiply(&mut y, 2 + 3, &_111);
        square_multiply(&mut y, 2 + 2, &_11);
        square_multiply(&mut y, 1 + 4, &_1011);
        square_multiply(&mut y, 2 + 4, &_1011);
        square_multiply(&mut y, 6 + 4, &_1001);
        square_multiply(&mut y, 2 + 2, &_11);
        square_multiply(&mut y, 3 + 2, &_11);
        square_multiply(&mut y, 3 + 2, &_11);
        square_multiply(&mut y, 1 + 4, &_1001);
        square_multiply(&mut y, 1 + 3, &_111);
        square_multiply(&mut y, 2 + 4, &_1111);
        square_multiply(&mut y, 1 + 4, &_1011);
        square_multiply(&mut y, 3, &_101);
        square_multiply(&mut y, 2 + 4, &_1111);
        square_multiply(&mut y, 3, &_101);
        square_multiply(&mut y, 1 + 2, &_11);

        proof {
            assume((scalar52_to_nat(&y) * scalar52_to_nat(self)) % group_order() == (
            montgomery_radix() * montgomery_radix()) % group_order());
        }

        y
    }

    /// Inverts an UnpackedScalar not in Montgomery form.
    pub fn invert(&self) -> (result: UnpackedScalar)
        requires
            limbs_bounded(self),
        ensures
    // Postcondition: result * self ≡ 1 (mod group_order)

            scalar52_to_nat(&result) * scalar52_to_nat(self) % group_order() == 1,
            // Result is canonical (< group_order) - needed for pack() to produce canonical Scalar
            is_canonical_scalar52(&result),
    {
        /* <ORIGINAL CODE>
                self.as_montgomery().montgomery_invert().from_montgomery()
        </ORIGINAL CODE> */
        let mont = self.as_montgomery();
        // as_montgomery ensures limbs_bounded(&mont)
        let inv = mont.montgomery_invert();
        // montgomery_invert ensures limbs_bounded(&inv)
        proof {
            lemma_limbs_bounded_implies_prod_bounded(&inv, &inv);
        }
        let result = inv.from_montgomery();
        // from_montgomery ensures limbs_bounded(&result) and scalar52_to_nat(&result) < group_order()

        proof {
            // Apply the invert correctness lemma
            lemma_invert_correctness(
                scalar52_to_nat(self),
                scalar52_to_nat(&mont),
                scalar52_to_nat(&inv),
                scalar52_to_nat(&result),
            );
        }

        result
    }
}

} // verus!
#[cfg(feature = "group")]
impl Field for Scalar {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;

    fn random(mut rng: impl RngCore) -> Self {
        // NOTE: this is duplicated due to different `rng` bounds
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Self::from_bytes_mod_order_wide(&scalar_bytes)
    }

    fn square(&self) -> Self {
        self * self
    }

    fn double(&self) -> Self {
        self + self
    }

    fn invert(&self) -> CtOption<Self> {
        CtOption::new(self.invert(), !self.is_zero())
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        #[allow(unused_qualifications)]
        group::ff::helpers::sqrt_ratio_generic(num, div)
    }

    fn sqrt(&self) -> CtOption<Self> {
        #[allow(unused_qualifications)]
        group::ff::helpers::sqrt_tonelli_shanks(
            self,
            [
                0xcb02_4c63_4b9e_ba7d,
                0x029b_df3b_d45e_f39a,
                0x0000_0000_0000_0000,
                0x0200_0000_0000_0000,
            ],
        )
    }
}

#[cfg(feature = "group")]
impl PrimeField for Scalar {
    type Repr = [u8; 32];

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        Self::from_canonical_bytes(repr)
    }

    fn from_repr_vartime(repr: Self::Repr) -> Option<Self> {
        // Check that the high bit is not set
        if (repr[31] >> 7) != 0u8 {
            return None;
        }

        let candidate = Scalar { bytes: repr };

        if candidate == candidate.reduce() {
            Some(candidate)
        } else {
            None
        }
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.as_bytes()[0] & 1)
    }

    const MODULUS: &'static str =
        "0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed";
    const NUM_BITS: u32 = 253;
    const CAPACITY: u32 = 252;

    const TWO_INV: Self = Self {
        bytes: [
            0xf7, 0xe9, 0x7a, 0x2e, 0x8d, 0x31, 0x09, 0x2c, 0x6b, 0xce, 0x7b, 0x51, 0xef, 0x7c,
            0x6f, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x08,
        ],
    };
    const MULTIPLICATIVE_GENERATOR: Self = Self {
        bytes: [
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };
    const S: u32 = 2;
    const ROOT_OF_UNITY: Self = Self {
        bytes: [
            0xd4, 0x07, 0xbe, 0xeb, 0xdf, 0x75, 0x87, 0xbe, 0xfe, 0x83, 0xce, 0x42, 0x53, 0x56,
            0xf0, 0x0e, 0x7a, 0xc2, 0xc1, 0xab, 0x60, 0x6d, 0x3d, 0x7d, 0xe7, 0x81, 0x79, 0xe0,
            0x10, 0x73, 0x4a, 0x09,
        ],
    };
    const ROOT_OF_UNITY_INV: Self = Self {
        bytes: [
            0x19, 0xcc, 0x37, 0x71, 0x3a, 0xed, 0x8a, 0x99, 0xd7, 0x18, 0x29, 0x60, 0x8b, 0xa3,
            0xee, 0x05, 0x86, 0x3d, 0x3e, 0x54, 0x9f, 0x92, 0xc2, 0x82, 0x18, 0x7e, 0x86, 0x1f,
            0xef, 0x8c, 0xb5, 0x06,
        ],
    };
    const DELTA: Self = Self {
        bytes: [
            16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };
}

#[cfg(feature = "group-bits")]
impl PrimeFieldBits for Scalar {
    type ReprBits = [u8; 32];

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        self.to_repr().into()
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        constants::BASEPOINT_ORDER_PRIVATE.to_bytes().into()
    }
}

#[cfg(feature = "group")]
impl FromUniformBytes<64> for Scalar {
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Scalar::from_bytes_mod_order_wide(bytes)
    }
}

verus! {

/// Read one or more u64s stored as little endian bytes.
///
/// ## Panics
/// Panics if `src.len() != 8 * dst.len()`.
fn read_le_u64_into(src: &[u8], dst: &mut [u64])
    requires
        src.len() == 8 * old(dst).len(),
    ensures
        dst.len() == old(dst).len(),
        forall|i: int|
            0 <= i < dst.len() ==> {
                let byte_seq = Seq::new(8, |j: int| src[i * 8 + j] as u8);
                #[trigger] dst[i] as nat == bytes_seq_as_nat(byte_seq)
            },
{
    #[cfg(not(verus_keep_ghost))]
    assert!(
        src.len() == 8 * dst.len(),
        "src.len() = {}, dst.len() = {}",
        src.len(),
        dst.len()
    );

    /* <ORIGINAL CODE>
    for (bytes, val) in src.chunks(8).zip(dst.iter_mut()) {
        *val = u64_from_le_bytes(
            bytes
                .try_into()
                .expect("Incorrect src length, should be 8 * dst.len()"),
        );
    }
    </ORIGINAL CODE> */

    /* <MODIFIED CODE> Verus doesn't support chunks/zip/try_into, use explicit loops */
    let dst_len = dst.len();
    for i in 0..dst_len
        invariant
            src.len() == 8 * dst_len,
            dst.len() == dst_len,
            forall|k: int|
                0 <= k < i ==> {
                    let byte_seq = Seq::new(8, |j: int| src[k * 8 + j] as u8);
                    #[trigger] dst[k] as nat == bytes_seq_as_nat(byte_seq)
                },
    {
        let byte_start = (i * 8);
        let mut byte_array = [0u8;8];
        for j in 0..8usize
            invariant
                i < dst_len,
                byte_start == i * 8,
                byte_start + 8 <= src.len(),
                forall|k: int| 0 <= k < j ==> byte_array@[k] == src[(i * 8 + k) as int],
        {
            byte_array[j] = src[byte_start + j];
        }
        dst[i] = u64_from_le_bytes(byte_array);
        proof {
            let byte_seq = Seq::new(8, |j: int| src[i as int * 8 + j] as u8);
            assert(byte_array@ =~= byte_seq);
            assert(bytes_seq_as_nat(byte_array@) == bytes_as_nat_prefix(byte_array@, 8)) by {
                lemma_bytes_seq_as_nat_equals_prefix(byte_array@);
            }
        }
    }
    /* </MODIFIED CODE> */
}

/// _Clamps_ the given little-endian representation of a 32-byte integer. Clamping the value puts
/// it in the range:
///
/// **n ∈ 2^254 + 8\*{0, 1, 2, 3, . . ., 2^251 − 1}**
///
/// # Explanation of clamping
///
/// For Curve25519, h = 8, and multiplying by 8 is the same as a binary left-shift by 3 bits.
/// If you take a secret scalar value between 2^251 and 2^252 – 1 and left-shift by 3 bits
/// then you end up with a 255-bit number with the most significant bit set to 1 and
/// the least-significant three bits set to 0.
///
/// The Curve25519 clamping operation takes **an arbitrary 256-bit random value** and
/// clears the most-significant bit (making it a 255-bit number), sets the next bit, and then
/// clears the 3 least-significant bits. In other words, it directly creates a scalar value that is
/// in the right form and pre-multiplied by the cofactor.
///
/// See [here](https://neilmadden.blog/2020/05/28/whats-the-curve25519-clamping-all-about/) for
/// more details.
#[must_use]
pub const fn clamp_integer(bytes: [u8; 32]) -> (result: [u8; 32])
    ensures
// Result is a valid clamped integer for X25519

        is_clamped_integer(&result),
        // The result matches the spec function
        result == spec_clamp_integer(bytes),
        // All bytes except 0 and 31 remain unchanged
        forall|i: int| 1 <= i < 31 ==> #[trigger] result[i] == bytes[i],
        // Low byte preserves bits 3-7
        result[0] & 0b1111_1000 == bytes[0] & 0b1111_1000,
        // High byte preserves bits 0-5
        result[31] & 0b0011_1111 == bytes[31] & 0b0011_1111,
{
    let mut result = bytes;

    // Clear low 3 bits: result[0] = bytes[0] & 0b1111_1000
    result[0] &= 0b1111_1000;

    // Clear bit 7 (MSB): result[31] = result[31] & 0b0111_1111
    result[31] &= 0b0111_1111;

    // Set bit 6: result[31] = result[31] | 0b0100_0000
    result[31] |= 0b0100_0000;

    proof {
        let r0: u8 = result[0];
        let r31: u8 = result[31];
        let b0: u8 = bytes[0];
        let b31: u8 = bytes[31];

        // is_clamped_integer: low 3 bits of byte 0 are cleared
        assert(r0 & 0b0000_0111u8 == 0u8) by (bit_vector)
            requires
                r0 == b0 & 0b1111_1000u8,
        ;
        // is_clamped_integer: bit 7 of byte 31 is cleared
        assert(r31 & 0b1000_0000u8 == 0u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
        // is_clamped_integer: bit 6 of byte 31 is set
        assert(r31 & 0b0100_0000u8 == 0b0100_0000u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
        // is_clamped_integer: byte 31 <= 127
        assert(r31 <= 127u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;

        // Bit preservation: bits 3-7 of byte 0
        assert(r0 & 0b1111_1000u8 == b0 & 0b1111_1000u8) by (bit_vector)
            requires
                r0 == b0 & 0b1111_1000u8,
        ;
        // Bit preservation: bits 0-5 of byte 31
        assert(r31 & 0b0011_1111u8 == b31 & 0b0011_1111u8) by (bit_vector)
            requires
                r31 == (b31 & 0b0111_1111u8) | 0b0100_0000u8,
        ;
    }

    result
}

} // verus!
// #[cfg(test)]
// pub(crate) mod test {
//     use super::*;
//     #[cfg(feature = "alloc")]
//     use alloc::vec::Vec;
//     /// x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
//     pub static X: Scalar = Scalar {
//         bytes: [
//             0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84, 0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2,
//             0x7d, 0x52, 0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44, 0xd4, 0x49, 0xf4, 0xa8,
//             0x79, 0xd9, 0xf2, 0x04,
//         ],
//     };
//     /// 1/x = 6859937278830797291664592131120606308688036382723378951768035303146619657244
//     pub static XINV: Scalar = Scalar {
//         bytes: [
//             0x1c, 0xdc, 0x17, 0xfc, 0xe0, 0xe9, 0xa5, 0xbb, 0xd9, 0x24, 0x7e, 0x56, 0xbb, 0x01,
//             0x63, 0x47, 0xbb, 0xba, 0x31, 0xed, 0xd5, 0xa9, 0xbb, 0x96, 0xd5, 0x0b, 0xcd, 0x7a,
//             0x3f, 0x96, 0x2a, 0x0f,
//         ],
//     };
//     /// y = 2592331292931086675770238855846338635550719849568364935475441891787804997264
//     pub static Y: Scalar = Scalar {
//         bytes: [
//             0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4, 0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83,
//             0x86, 0xc3, 0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d, 0xe8, 0xef, 0x7a, 0xc3,
//             0x1f, 0x35, 0xbb, 0x05,
//         ],
//     };
//     /// The largest scalar that satisfies invariant #1, i.e., the largest scalar with the top bit
//     /// set to 0. Since this scalar violates invariant #2, i.e., it's greater than the modulus `l`,
//     /// addition and subtraction are broken. The only thing you can do with this is scalar-point
//     /// multiplication (and actually also scalar-scalar multiplication, but that's just a quirk of
//     /// our implementation).
//     pub(crate) static LARGEST_UNREDUCED_SCALAR: Scalar = Scalar {
//         bytes: [
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0x7f,
//         ],
//     };
//     /// x*y = 5690045403673944803228348699031245560686958845067437804563560795922180092780
//     static X_TIMES_Y: Scalar = Scalar {
//         bytes: [
//             0x6c, 0x33, 0x74, 0xa1, 0x89, 0x4f, 0x62, 0x21, 0x0a, 0xaa, 0x2f, 0xe1, 0x86, 0xa6,
//             0xf9, 0x2c, 0xe0, 0xaa, 0x75, 0xc2, 0x77, 0x95, 0x81, 0xc2, 0x95, 0xfc, 0x08, 0x17,
//             0x9a, 0x73, 0x94, 0x0c,
//         ],
//     };
//     /// sage: l = 2^252 + 27742317777372353535851937790883648493
//     /// sage: big = 2^256 - 1
//     /// sage: repr((big % l).digits(256))
//     static CANONICAL_2_256_MINUS_1: Scalar = Scalar {
//         bytes: [
//             28, 149, 152, 141, 116, 49, 236, 214, 112, 207, 125, 115, 244, 91, 239, 198, 254, 255,
//             255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 15,
//         ],
//     };
//     static A_SCALAR: Scalar = Scalar {
//         bytes: [
//             0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d, 0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8,
//             0x26, 0x4d, 0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1, 0x58, 0x9e, 0x7b, 0x7f,
//             0x23, 0x76, 0xef, 0x09,
//         ],
//     };
//     static A_NAF: [i8; 256] = [
//         0, 13, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, -11, 0, 0, 0, 0, 3, 0, 0,
//         0, 0, 1, 0, 0, 0, 0, 9, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 11, 0, 0, 0, 0,
//         11, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
//         0, -1, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, -15, 0, 0, 0, 0, -7, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 5,
//         0, 0, 0, 0, 13, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, -11, 0, 0, 0, 0, -7, 0, 0, 0, 0, -13, 0, 0,
//         0, 0, 11, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 1, 0, 0, 0, 0,
//         7, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 15,
//         0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, -15, 0,
//         0, 0, 0, 0, 15, 0, 0, 0, 0, 15, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
//     ];
//     const BASEPOINT_ORDER_MINUS_ONE: Scalar = Scalar {
//         bytes: [
//             0xec, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
//             0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//             0x00, 0x00, 0x00, 0x10,
//         ],
//     };
//     /// The largest clamped integer
//     static LARGEST_CLAMPED_INTEGER: [u8; 32] = clamp_integer(LARGEST_UNREDUCED_SCALAR.bytes);
//     #[test]
//     fn fuzzer_testcase_reduction() {
//         // LE bytes of 24519928653854221733733552434404946937899825954937634815
//         let a_bytes = [
//             255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
//             255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//         ];
//         // LE bytes of 4975441334397345751130612518500927154628011511324180036903450236863266160640
//         let b_bytes = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 210, 210,
//             210, 255, 255, 255, 255, 10,
//         ];
//         // LE bytes of 6432735165214683820902750800207468552549813371247423777071615116673864412038
//         let c_bytes = [
//             134, 171, 119, 216, 180, 128, 178, 62, 171, 132, 32, 62, 34, 119, 104, 193, 47, 215,
//             181, 250, 14, 207, 172, 93, 75, 207, 211, 103, 144, 204, 56, 14,
//         ];
//         let a = Scalar::from_bytes_mod_order(a_bytes);
//         let b = Scalar::from_bytes_mod_order(b_bytes);
//         let c = Scalar::from_bytes_mod_order(c_bytes);
//         let mut tmp = [0u8; 64];
//         // also_a = (a mod l)
//         tmp[0..32].copy_from_slice(&a_bytes[..]);
//         let also_a = Scalar::from_bytes_mod_order_wide(&tmp);
//         // also_b = (b mod l)
//         tmp[0..32].copy_from_slice(&b_bytes[..]);
//         let also_b = Scalar::from_bytes_mod_order_wide(&tmp);
//         let expected_c = a * b;
//         let also_expected_c = also_a * also_b;
//         assert_eq!(c, expected_c);
//         assert_eq!(c, also_expected_c);
//     }
//     #[test]
//     fn non_adjacent_form_test_vector() {
//         let naf = A_SCALAR.non_adjacent_form(5);
//         for i in 0..256 {
//             assert_eq!(naf[i], A_NAF[i]);
//         }
//     }
//     fn non_adjacent_form_iter(w: usize, x: &Scalar) {
//         let naf = x.non_adjacent_form(w);
//         // Reconstruct the scalar from the computed NAF
//         let mut y = Scalar::ZERO;
//         for i in (0..256).rev() {
//             y += y;
//             let digit = if naf[i] < 0 {
//                 -Scalar::from((-naf[i]) as u64)
//             } else {
//                 Scalar::from(naf[i] as u64)
//             };
//             y += digit;
//         }
//         assert_eq!(*x, y);
//     }
//     #[test]
//     fn non_adjacent_form_random() {
//         let mut rng = rand::thread_rng();
//         for _ in 0..1_000 {
//             let x = Scalar::random(&mut rng);
//             for w in &[5, 6, 7, 8] {
//                 non_adjacent_form_iter(*w, &x);
//             }
//         }
//     }
//     #[test]
//     fn from_u64() {
//         let val: u64 = 0xdeadbeefdeadbeef;
//         let s = Scalar::from(val);
//         assert_eq!(s[7], 0xde);
//         assert_eq!(s[6], 0xad);
//         assert_eq!(s[5], 0xbe);
//         assert_eq!(s[4], 0xef);
//         assert_eq!(s[3], 0xde);
//         assert_eq!(s[2], 0xad);
//         assert_eq!(s[1], 0xbe);
//         assert_eq!(s[0], 0xef);
//     }
//     #[test]
//     fn scalar_mul_by_one() {
//         let test_scalar = X * Scalar::ONE;
//         for i in 0..32 {
//             assert!(test_scalar[i] == X[i]);
//         }
//     }
//     #[test]
//     fn add_reduces() {
//         // Check that addition wraps around the modulus
//         assert_eq!(BASEPOINT_ORDER_MINUS_ONE + Scalar::ONE, Scalar::ZERO);
//     }
//     #[test]
//     fn sub_reduces() {
//         // Check that subtraction wraps around the modulus
//         assert_eq!(Scalar::ZERO - Scalar::ONE, BASEPOINT_ORDER_MINUS_ONE);
//     }
//     #[test]
//     fn impl_add() {
//         let two = Scalar::from(2u64);
//         let one = Scalar::ONE;
//         let should_be_two = one + one;
//         assert_eq!(should_be_two, two);
//     }
//     #[allow(non_snake_case)]
//     #[test]
//     fn impl_mul() {
//         let should_be_X_times_Y = X * Y;
//         assert_eq!(should_be_X_times_Y, X_TIMES_Y);
//     }
//     #[allow(non_snake_case)]
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_product() {
//         // Test that product works for non-empty iterators
//         let X_Y_vector = [X, Y];
//         let should_be_X_times_Y: Scalar = X_Y_vector.iter().product();
//         assert_eq!(should_be_X_times_Y, X_TIMES_Y);
//         // Test that product works for the empty iterator
//         let one = Scalar::ONE;
//         let empty_vector = [];
//         let should_be_one: Scalar = empty_vector.iter().product();
//         assert_eq!(should_be_one, one);
//         // Test that product works for iterators where Item = Scalar
//         let xs = [Scalar::from(2u64); 10];
//         let ys = [Scalar::from(3u64); 10];
//         // now zs is an iterator with Item = Scalar
//         let zs = xs.iter().zip(ys.iter()).map(|(x, y)| x * y);
//         let x_prod: Scalar = xs.iter().product();
//         let y_prod: Scalar = ys.iter().product();
//         let z_prod: Scalar = zs.product();
//         assert_eq!(x_prod, Scalar::from(1024u64));
//         assert_eq!(y_prod, Scalar::from(59049u64));
//         assert_eq!(z_prod, Scalar::from(60466176u64));
//         assert_eq!(x_prod * y_prod, z_prod);
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_sum() {
//         // Test that sum works for non-empty iterators
//         let two = Scalar::from(2u64);
//         let one_vector = [Scalar::ONE, Scalar::ONE];
//         let should_be_two: Scalar = one_vector.iter().sum();
//         assert_eq!(should_be_two, two);
//         // Test that sum works for the empty iterator
//         let zero = Scalar::ZERO;
//         let empty_vector = [];
//         let should_be_zero: Scalar = empty_vector.iter().sum();
//         assert_eq!(should_be_zero, zero);
//         // Test that sum works for owned types
//         let xs = [Scalar::from(1u64); 10];
//         let ys = [Scalar::from(2u64); 10];
//         // now zs is an iterator with Item = Scalar
//         let zs = xs.iter().zip(ys.iter()).map(|(x, y)| x + y);
//         let x_sum: Scalar = xs.iter().sum();
//         let y_sum: Scalar = ys.iter().sum();
//         let z_sum: Scalar = zs.sum();
//         assert_eq!(x_sum, Scalar::from(10u64));
//         assert_eq!(y_sum, Scalar::from(20u64));
//         assert_eq!(z_sum, Scalar::from(30u64));
//         assert_eq!(x_sum + y_sum, z_sum);
//     }
//     #[test]
//     fn square() {
//         let expected = X * X;
//         let actual = X.unpack().square().pack();
//         for i in 0..32 {
//             assert!(expected[i] == actual[i]);
//         }
//     }
//     #[test]
//     fn reduce() {
//         let biggest = Scalar::from_bytes_mod_order([0xff; 32]);
//         assert_eq!(biggest, CANONICAL_2_256_MINUS_1);
//     }
//     #[test]
//     fn from_bytes_mod_order_wide() {
//         let mut bignum = [0u8; 64];
//         // set bignum = x + 2^256x
//         for i in 0..32 {
//             bignum[i] = X[i];
//             bignum[32 + i] = X[i];
//         }
//         // 3958878930004874126169954872055634648693766179881526445624823978500314864344
//         // = x + 2^256x (mod l)
//         let reduced = Scalar {
//             bytes: [
//                 216, 154, 179, 139, 210, 121, 2, 71, 69, 99, 158, 216, 23, 173, 63, 100, 204, 0,
//                 91, 50, 219, 153, 57, 249, 28, 82, 31, 197, 100, 165, 192, 8,
//             ],
//         };
//         let test_red = Scalar::from_bytes_mod_order_wide(&bignum);
//         for i in 0..32 {
//             assert!(test_red[i] == reduced[i]);
//         }
//     }
//     #[allow(non_snake_case)]
//     #[test]
//     fn invert() {
//         let inv_X = X.invert();
//         assert_eq!(inv_X, XINV);
//         let should_be_one = inv_X * X;
//         assert_eq!(should_be_one, Scalar::ONE);
//     }
//     // Negating a scalar twice should result in the original scalar.
//     #[allow(non_snake_case)]
//     #[test]
//     fn neg_twice_is_identity() {
//         let negative_X = -&X;
//         let should_be_X = -&negative_X;
//         assert_eq!(should_be_X, X);
//     }
//     #[test]
//     fn to_bytes_from_bytes_roundtrips() {
//         let unpacked = X.unpack();
//         let bytes = unpacked.as_bytes();
//         let should_be_unpacked = UnpackedScalar::from_bytes(&bytes);
//         assert_eq!(should_be_unpacked.0, unpacked.0);
//     }
//     #[test]
//     fn montgomery_reduce_matches_from_bytes_mod_order_wide() {
//         let mut bignum = [0u8; 64];
//         // set bignum = x + 2^256x
//         for i in 0..32 {
//             bignum[i] = X[i];
//             bignum[32 + i] = X[i];
//         }
//         // x + 2^256x (mod l)
//         //         = 3958878930004874126169954872055634648693766179881526445624823978500314864344
//         let expected = Scalar {
//             bytes: [
//                 216, 154, 179, 139, 210, 121, 2, 71, 69, 99, 158, 216, 23, 173, 63, 100, 204, 0,
//                 91, 50, 219, 153, 57, 249, 28, 82, 31, 197, 100, 165, 192, 8,
//             ],
//         };
//         let reduced = Scalar::from_bytes_mod_order_wide(&bignum);
//         // The reduced scalar should match the expected
//         assert_eq!(reduced.bytes, expected.bytes);
//         //  (x + 2^256x) * R
//         let interim =
//             UnpackedScalar::mul_internal(&UnpackedScalar::from_bytes_wide(&bignum), &constants::R);
//         // ((x + 2^256x) * R) / R  (mod l)
//         let montgomery_reduced = UnpackedScalar::montgomery_reduce(&interim);
//         // The Montgomery reduced scalar should match the reduced one, as well as the expected
//         assert_eq!(montgomery_reduced.0, reduced.unpack().0);
//         assert_eq!(montgomery_reduced.0, expected.unpack().0)
//     }
//     #[test]
//     fn canonical_decoding() {
//         // canonical encoding of 1667457891
//         let canonical_bytes = [
//             99, 99, 99, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 0, 0,
//         ];
//         // encoding of
//         //   7265385991361016183439748078976496179028704920197054998554201349516117938192
//         // = 28380414028753969466561515933501938171588560817147392552250411230663687203 (mod l)
//         // non_canonical because unreduced mod l
//         let non_canonical_bytes_because_unreduced = [16; 32];
//         // encoding with high bit set, to check that the parser isn't pre-masking the high bit
//         let non_canonical_bytes_because_highbit = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 128,
//         ];
//         assert!(bool::from(
//             Scalar::from_canonical_bytes(canonical_bytes).is_some()
//         ));
//         assert!(bool::from(
//             Scalar::from_canonical_bytes(non_canonical_bytes_because_unreduced).is_none()
//         ));
//         assert!(bool::from(
//             Scalar::from_canonical_bytes(non_canonical_bytes_because_highbit).is_none()
//         ));
//     }
//     #[test]
//     #[cfg(feature = "serde")]
//     fn serde_bincode_scalar_roundtrip() {
//         use bincode;
//         let encoded = bincode::serialize(&X).unwrap();
//         let parsed: Scalar = bincode::deserialize(&encoded).unwrap();
//         assert_eq!(parsed, X);
//         // Check that the encoding is 32 bytes exactly
//         assert_eq!(encoded.len(), 32);
//         // Check that the encoding itself matches the usual one
//         assert_eq!(X, bincode::deserialize(X.as_bytes()).unwrap(),);
//     }
//     #[cfg(all(debug_assertions, feature = "alloc"))]
//     #[test]
//     #[should_panic]
//     fn batch_invert_with_a_zero_input_panics() {
//         let mut xs = vec![Scalar::ONE; 16];
//         xs[3] = Scalar::ZERO;
//         // This should panic in debug mode.
//         Scalar::batch_invert(&mut xs);
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_empty() {
//         assert_eq!(Scalar::ONE, Scalar::batch_invert(&mut []));
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn batch_invert_consistency() {
//         let mut x = Scalar::from(1u64);
//         let mut v1: Vec<_> = (0..16)
//             .map(|_| {
//                 let tmp = x;
//                 x = x + x;
//                 tmp
//             })
//             .collect();
//         let v2 = v1.clone();
//         let expected: Scalar = v1.iter().product();
//         let expected = expected.invert();
//         let ret = Scalar::batch_invert(&mut v1);
//         assert_eq!(ret, expected);
//         for (a, b) in v1.iter().zip(v2.iter()) {
//             assert_eq!(a * b, Scalar::ONE);
//         }
//     }
//     #[cfg(feature = "precomputed-tables")]
//     fn test_pippenger_radix_iter(scalar: Scalar, w: usize) {
//         let digits_count = Scalar::to_radix_2w_size_hint(w);
//         let digits = scalar.as_radix_2w(w);
//         let radix = Scalar::from((1 << w) as u64);
//         let mut term = Scalar::ONE;
//         let mut recovered_scalar = Scalar::ZERO;
//         for digit in &digits[0..digits_count] {
//             let digit = *digit;
//             if digit != 0 {
//                 let sdigit = if digit < 0 {
//                     -Scalar::from((-(digit as i64)) as u64)
//                 } else {
//                     Scalar::from(digit as u64)
//                 };
//                 recovered_scalar += term * sdigit;
//             }
//             term *= radix;
//         }
//         // When the input is unreduced, we may only recover the scalar mod l.
//         assert_eq!(recovered_scalar, scalar.reduce());
//     }
//     #[test]
//     #[cfg(feature = "precomputed-tables")]
//     fn test_pippenger_radix() {
//         use core::iter;
//         // For each valid radix it tests that 1000 random-ish scalars can be restored
//         // from the produced representation precisely.
//         let cases = (2..100)
//             .map(|s| Scalar::from(s as u64).invert())
//             // The largest unreduced scalar, s = 2^255-1. This is not reduced mod l. Scalar mult
//             // still works though.
//             .chain(iter::once(LARGEST_UNREDUCED_SCALAR));
//         for scalar in cases {
//             test_pippenger_radix_iter(scalar, 6);
//             test_pippenger_radix_iter(scalar, 7);
//             test_pippenger_radix_iter(scalar, 8);
//         }
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn test_read_le_u64_into() {
//         let cases: &[(&[u8], &[u64])] = &[
//             (
//                 &[0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F, 0xF0],
//                 &[0xF00F_F11F_0110_EFFE],
//             ),
//             (
//                 &[
//                     0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F, 0xF0, 0x12, 0x34, 0x56, 0x78, 0x9A,
//                     0xBC, 0xDE, 0xF0,
//                 ],
//                 &[0xF00F_F11F_0110_EFFE, 0xF0DE_BC9A_7856_3412],
//             ),
//         ];
//         for (src, expected) in cases {
//             let mut dst = vec![0; expected.len()];
//             read_le_u64_into(src, &mut dst);
//             assert_eq!(&dst, expected, "Expected {:x?} got {:x?}", expected, dst);
//         }
//     }
//     // Tests consistency of From<{integer}> impls for Scalar
//     #[test]
//     fn test_scalar_from_int() {
//         let s1 = Scalar::ONE;
//         // For `x` in `u8`, `u16`, `u32`, `u64`, and `u128`, check that
//         // `Scalar::from(x + 1) == Scalar::from(x) + Scalar::from(1)`
//         let x = 0x23u8;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//         let x = 0x2323u16;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//         let x = 0x2323_2323u32;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//         let x = 0x2323_2323_2323_2323u64;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//         let x = 0x2323_2323_2323_2323_2323_2323_2323_2323u128;
//         let sx = Scalar::from(x);
//         assert_eq!(sx + s1, Scalar::from(x + 1));
//     }
//     #[cfg(feature = "group")]
//     #[test]
//     fn ff_constants() {
//         assert_eq!(Scalar::from(2u64) * Scalar::TWO_INV, Scalar::ONE);
//         assert_eq!(
//             Scalar::ROOT_OF_UNITY * Scalar::ROOT_OF_UNITY_INV,
//             Scalar::ONE,
//         );
//         // ROOT_OF_UNITY^{2^s} mod m == 1
//         assert_eq!(
//             Scalar::ROOT_OF_UNITY.pow(&[1u64 << Scalar::S, 0, 0, 0]),
//             Scalar::ONE,
//         );
//         // DELTA^{t} mod m == 1
//         assert_eq!(
//             Scalar::DELTA.pow(&[
//                 0x9604_98c6_973d_74fb,
//                 0x0537_be77_a8bd_e735,
//                 0x0000_0000_0000_0000,
//                 0x0400_0000_0000_0000,
//             ]),
//             Scalar::ONE,
//         );
//     }
//     #[cfg(feature = "group")]
//     #[test]
//     fn ff_impls() {
//         assert!(bool::from(Scalar::ZERO.is_even()));
//         assert!(bool::from(Scalar::ONE.is_odd()));
//         assert!(bool::from(Scalar::from(2u64).is_even()));
//         assert!(bool::from(Scalar::DELTA.is_even()));
//         assert!(bool::from(Field::invert(&Scalar::ZERO).is_none()));
//         assert_eq!(Field::invert(&X).unwrap(), XINV);
//         let x_sq = X.square();
//         // We should get back either the positive or negative root.
//         assert!([X, -X].contains(&x_sq.sqrt().unwrap()));
//         assert_eq!(Scalar::from_repr_vartime(X.to_repr()), Some(X));
//         assert_eq!(Scalar::from_repr_vartime([0xff; 32]), None);
//         assert_eq!(Scalar::from_repr(X.to_repr()).unwrap(), X);
//         assert!(bool::from(Scalar::from_repr([0xff; 32]).is_none()));
//     }
//     #[test]
//     #[should_panic]
//     fn test_read_le_u64_into_should_panic_on_bad_input() {
//         let mut dst = [0_u64; 1];
//         // One byte short
//         read_le_u64_into(&[0xFE, 0xEF, 0x10, 0x01, 0x1F, 0xF1, 0x0F], &mut dst);
//     }
//     #[test]
//     fn test_scalar_clamp() {
//         let input = A_SCALAR.bytes;
//         let expected = [
//             0x18, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d, 0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8,
//             0x26, 0x4d, 0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1, 0x58, 0x9e, 0x7b, 0x7f,
//             0x23, 0x76, 0xef, 0x49,
//         ];
//         let actual = clamp_integer(input);
//         assert_eq!(actual, expected);
//         let expected = [
//             0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//             0, 0, 0x40,
//         ];
//         let actual = clamp_integer([0; 32]);
//         assert_eq!(expected, actual);
//         let expected = [
//             0xf8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//             0xff, 0xff, 0xff, 0x7f,
//         ];
//         let actual = clamp_integer([0xff; 32]);
//         assert_eq!(actual, expected);
//         assert_eq!(
//             LARGEST_CLAMPED_INTEGER,
//             clamp_integer(LARGEST_CLAMPED_INTEGER)
//         );
//     }
//     // Check that a * b == a.reduce() * a.reduce() for ANY scalars a,b, even ones that violate
//     // invariant #1, i.e., a,b > 2^255. Old versions of ed25519-dalek did multiplication where a
//     // was reduced and b was clamped and unreduced. This checks that that was always well-defined.
//     #[test]
//     fn test_mul_reduction_invariance() {
//         let mut rng = rand::thread_rng();
//         for _ in 0..10 {
//             // Also define c that's clamped. We'll make sure that clamping doesn't affect
//             // computation
//             let (a, b, c) = {
//                 let mut a_bytes = [0u8; 32];
//                 let mut b_bytes = [0u8; 32];
//                 let mut c_bytes = [0u8; 32];
//                 rng.fill_bytes(&mut a_bytes);
//                 rng.fill_bytes(&mut b_bytes);
//                 rng.fill_bytes(&mut c_bytes);
//                 (
//                     Scalar { bytes: a_bytes },
//                     Scalar { bytes: b_bytes },
//                     Scalar {
//                         bytes: clamp_integer(c_bytes),
//                     },
//                 )
//             };
//             // Make sure this is the same product no matter how you cut it
//             let reduced_mul_ab = a.reduce() * b.reduce();
//             let reduced_mul_ac = a.reduce() * c.reduce();
//             assert_eq!(a * b, reduced_mul_ab);
//             assert_eq!(a.reduce() * b, reduced_mul_ab);
//             assert_eq!(a * b.reduce(), reduced_mul_ab);
//             assert_eq!(a * c, reduced_mul_ac);
//             assert_eq!(a.reduce() * c, reduced_mul_ac);
//             assert_eq!(a * c.reduce(), reduced_mul_ac);
//         }
//     }
// }
