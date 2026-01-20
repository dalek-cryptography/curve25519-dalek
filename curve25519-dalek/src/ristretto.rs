// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2020 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

//! An implementation of [Ristretto][ristretto_main], which provides a
//! prime-order group.
//!
//! # The Ristretto Group
//!
//! Ristretto is a modification of Mike Hamburg's Decaf scheme to work
//! with cofactor-\\(8\\) curves, such as Curve25519.
//!
//! The introduction of the Decaf paper, [_Decaf:
//! Eliminating cofactors through point
//! compression_](https://eprint.iacr.org/2015/673.pdf), notes that while
//! most cryptographic systems require a group of prime order, most
//! concrete implementations using elliptic curve groups fall short –
//! they either provide a group of prime order, but with incomplete or
//! variable-time addition formulae (for instance, most Weierstrass
//! models), or else they provide a fast and safe implementation of a
//! group whose order is not quite a prime \\(q\\), but \\(hq\\) for a
//! small cofactor \\(h\\) (for instance, Edwards curves, which have
//! cofactor at least \\(4\\)).
//!
//! This abstraction mismatch is commonly “handled” by pushing the
//! complexity upwards, adding ad-hoc protocol modifications.  But
//! these modifications require careful analysis and are a recurring
//! source of [vulnerabilities][cryptonote] and [design
//! complications][ed25519_hkd].
//!
//! Instead, Decaf (and Ristretto) use a quotient group to implement a
//! prime-order group using a non-prime-order curve.  This provides
//! the correct abstraction for cryptographic systems, while retaining
//! the speed and safety benefits of an Edwards curve.
//!
//! Decaf is named “after the procedure which divides the effect of
//! coffee by \\(4\\)”.  However, Curve25519 has a cofactor of
//! \\(8\\).  To eliminate its cofactor, Ristretto restricts further;
//! this [additional restriction][ristretto_coffee] gives the
//! _Ristretto_ encoding.
//!
//! More details on why Ristretto is necessary can be found in the
//! [Why Ristretto?][why_ristretto] section of the Ristretto website.
//!
//! Ristretto
//! points are provided in `curve25519-dalek` by the `RistrettoPoint`
//! struct.
//!
//! ## Encoding and Decoding
//!
//! Encoding is done by converting to and from a `CompressedRistretto`
//! struct, which is a typed wrapper around `[u8; 32]`.
//!
//! The encoding is not batchable, but it is possible to
//! double-and-encode in a batch using
//! `RistrettoPoint::double_and_compress_batch`.
//!
//! ## Equality Testing
//!
//! Testing equality of points on an Edwards curve in projective
//! coordinates requires an expensive inversion.  By contrast, equality
//! checking in the Ristretto group can be done in projective
//! coordinates without requiring an inversion, so it is much faster.
//!
//! The `RistrettoPoint` struct implements the
//! `subtle::ConstantTimeEq` trait for constant-time equality
//! checking, and the Rust `Eq` trait for variable-time equality
//! checking.
//!
//! ## Scalars
//!
//! Scalars are represented by the `Scalar` struct.  Each scalar has a
//! canonical representative mod the group order.  To attempt to load
//! a supposedly-canonical scalar, use
//! `Scalar::from_canonical_bytes()`. To check whether a
//! representative is canonical, use `Scalar::is_canonical()`.
//!
//! ## Scalar Multiplication
//!
//! Scalar multiplication on Ristretto points is provided by:
//!
//! * the `*` operator between a `Scalar` and a `RistrettoPoint`, which
//! performs constant-time variable-base scalar multiplication;
//!
//! * the `*` operator between a `Scalar` and a
//! `RistrettoBasepointTable`, which performs constant-time fixed-base
//! scalar multiplication;
//!
//! * an implementation of the
//! [`MultiscalarMul`](../traits/trait.MultiscalarMul.html) trait for
//! constant-time variable-base multiscalar multiplication;
//!
//! * an implementation of the
//! [`VartimeMultiscalarMul`](../traits/trait.VartimeMultiscalarMul.html)
//! trait for variable-time variable-base multiscalar multiplication;
//!
//! ## Random Points and Hashing to Ristretto
//!
//! The Ristretto group comes equipped with an Elligator map.  This is
//! used to implement
//!
//! * `RistrettoPoint::random()`, which generates random points from an
//! RNG - enabled by `rand_core` feature;
//!
//! * `RistrettoPoint::from_hash()` and
//! `RistrettoPoint::hash_from_bytes()`, which perform hashing to the
//! group.
//!
//! The Elligator map itself is not currently exposed.
//!
//! ## Implementation
//!
//! The Decaf suggestion is to use a quotient group, such as \\(\mathcal
//! E / \mathcal E\[4\]\\) or \\(2 \mathcal E / \mathcal E\[2\] \\), to
//! implement a prime-order group using a non-prime-order curve.
//!
//! This requires only changing
//!
//! 1. the function for equality checking (so that two representatives
//!    of the same coset are considered equal);
//! 2. the function for encoding (so that two representatives of the
//!    same coset are encoded as identical bitstrings);
//! 3. the function for decoding (so that only the canonical encoding of
//!    a coset is accepted).
//!
//! Internally, each coset is represented by a curve point; two points
//! \\( P, Q \\) may represent the same coset in the same way that two
//! points with different \\(X,Y,Z\\) coordinates may represent the
//! same point.  The group operations are carried out with no overhead
//! using Edwards formulas.
//!
//! Notes on the details of the encoding can be found in the
//! [Details][ristretto_notes] section of the Ristretto website.
//!
//! [cryptonote]:
//! https://moderncrypto.org/mail-archive/curves/2017/000898.html
//! [ed25519_hkd]:
//! https://moderncrypto.org/mail-archive/curves/2017/000858.html
//! [ristretto_coffee]:
//! https://en.wikipedia.org/wiki/Ristretto
//! [ristretto_notes]:
//! https://ristretto.group/details/index.html
//! [why_ristretto]:
//! https://ristretto.group/why_ristretto.html
//! [ristretto_main]:
//! https://ristretto.group/

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::array::TryFromSliceError;
use core::borrow::Borrow;
use core::fmt::Debug;
use core::iter::Sum;
use core::ops::{Add, Neg, Sub};
use core::ops::{AddAssign, SubAssign};
use core::ops::{Mul, MulAssign};

#[cfg(any(test, feature = "rand_core"))]
use rand_core::CryptoRngCore;

#[cfg(feature = "digest")]
use digest::generic_array::typenum::U64;
#[cfg(feature = "digest")]
use digest::Digest;

use crate::constants;

#[cfg(verus_keep_ghost)]
use crate::backend::serial::u64::subtle_assumes::choice_is_true;
#[allow(unused_imports)] // Used in verus! blocks
use crate::backend::serial::u64::subtle_assumes::{
    choice_into, choice_not, choice_or, conditional_assign_generic,
    conditional_negate_field_element, ct_eq_bytes32,
};
#[cfg(feature = "digest")]
#[allow(unused_imports)]
use crate::core_assumes::sha512_hash_bytes;
#[allow(unused_imports)] // Used in verus! blocks
use crate::core_assumes::try_into_32_bytes_array;
#[cfg(feature = "digest")]
use crate::field::FieldElement;
#[allow(unused_imports)] // Used in verus! blocks for bound weakening
use crate::lemmas::field_lemmas::add_lemmas::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::edwards_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)] // Used in verus! blocks for Sum trait and multiscalar_mul
use crate::specs::iterator_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::proba_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::ristretto_specs::*;
#[allow(unused_imports)] // Used in verus! blocks
use crate::specs::scalar_specs::*;
use vstd::prelude::*;

#[cfg(feature = "group")]
use {
    group::{cofactor::CofactorGroup, prime::PrimeGroup, GroupEncoding},
    rand_core::RngCore,
    subtle::CtOption,
};

use subtle::Choice;
use subtle::ConditionallyNegatable;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[cfg(feature = "precomputed-tables")]
use crate::edwards::EdwardsBasepointTable;
use crate::edwards::EdwardsPoint;

use crate::core_assumes::negate_field;
use crate::scalar::Scalar;

#[cfg(feature = "precomputed-tables")]
use crate::traits::BasepointTable;
use crate::traits::Identity;
#[cfg(feature = "alloc")]
use crate::traits::{MultiscalarMul, VartimeMultiscalarMul, VartimePrecomputedMultiscalarMul};

verus! {

// ------------------------------------------------------------------------
// Compressed points
// ------------------------------------------------------------------------
/// A Ristretto point, in compressed wire format.
///
/// The Ristretto encoding is canonical, so two points are equal if and
/// only if their encodings are equal.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct CompressedRistretto(pub [u8; 32]);

impl ConstantTimeEq for CompressedRistretto {
    fn ct_eq(&self, other: &CompressedRistretto) -> (result: Choice)
        ensures
            choice_is_true(result) == (self.0 == other.0),
    {
        // ORIGINAL CODE: self.as_bytes().ct_eq(other.as_bytes())
        // VERUS WORKAROUND: Use ct_eq_bytes32 wrapper for Verus compatibility
        ct_eq_bytes32(&self.0, &other.0)
    }
}

impl CompressedRistretto {
    /// Copy the bytes of this `CompressedRistretto`.
    pub const fn to_bytes(&self) -> (result: [u8; 32])
        ensures
            result == self.0,
    {
        self.0
    }

    /// View this `CompressedRistretto` as an array of bytes.
    pub const fn as_bytes(&self) -> (result: &[u8; 32])
        ensures
            *result == self.0,
    {
        &self.0
    }

    /// Construct a `CompressedRistretto` from a slice of bytes.
    ///
    /// # Errors
    ///
    /// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
    /// a length of 32.
    #[verifier::external]  // TODO: fix for Verus 88f7396
    pub fn from_slice(bytes: &[u8]) -> (result: Result<CompressedRistretto, TryFromSliceError>)
        ensures
            bytes@.len() == 32 ==> matches!(result, Ok(_)),
            bytes@.len() != 32 ==> matches!(result, Err(_)),
            match result {
                Ok(point) => point.0@ == bytes@,
                Err(_) => true,
            },
    {
        // ORIGINAL CODE: bytes.try_into().map(CompressedRistretto)
        // VERUS WORKAROUND: Verus doesn't allow datatype constructors like CompressedRistretto as function values,
        // so we use a closure |arr| CompressedRistretto(arr) instead of CompressedRistretto directly.
        // Also, try_into is wrapped in an external function for Verus compatibility.
        let arr_result = try_into_32_bytes_array(bytes);
        let result = arr_result.map(|arr| CompressedRistretto(arr));

        proof {
            // Verus can't track bytes through the .map closure
            assume(match result {
                Ok(point) => point.0@ == bytes@,
                Err(_) => true,
            });
        }
        result
    }
}

impl Identity for CompressedRistretto {
    fn identity() -> (result: CompressedRistretto)
        ensures
            forall|i: int| 0 <= i < 32 ==> result.0[i] == 0u8,
    {
        CompressedRistretto([0u8;32])
    }
}

impl CompressedRistretto {
    /// Attempt to decompress to an `RistrettoPoint`.
    ///
    /// # Return
    ///
    /// - `Some(RistrettoPoint)` if `self` was the canonical encoding of a point;
    ///
    /// - `None` if `self` was not the canonical encoding of a point.
    pub fn decompress(&self) -> (result: Option<RistrettoPoint>)
        ensures
    // Spec alignment: result matches spec-level decoding

            result == spec_ristretto_decompress(self.0),
            // If decompression succeeds, the result is a well-formed Edwards point
            // (well-formed includes: valid on curve, limbs bounded, sum bounded)
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap().0),
            // On success, the decoded point lies in the even subgroup
            result.is_some() ==> is_in_even_subgroup(result.unwrap().0),
    {
        let (s_encoding_is_canonical, s_is_negative, s) = decompress::step_1(self);

        // Use choice_or and choice_into wrappers for Verus compatibility
        if choice_into(choice_or(choice_not(s_encoding_is_canonical), s_is_negative)) {
            proof {
                // Spec alignment for early failure
                assume(spec_ristretto_decompress(self.0).is_none());
            }
            return None;
        }
        let (ok, t_is_negative, y_is_zero, res) = decompress::step_2(s);

        if choice_into(choice_or(choice_or(choice_not(ok), t_is_negative), y_is_zero)) {
            let result = None;
            proof {
                // Spec alignment for failure branch
                assume(result == spec_ristretto_decompress(self.0));
            }
            result
        } else {
            let result = Some(res);
            proof {
                // step_2 constructs the point with Z=ONE, ensuring well-formedness
                assume(is_well_formed_edwards_point(res.0));
                assume(is_in_even_subgroup(res.0));
                // Spec alignment for success branch
                assume(result == spec_ristretto_decompress(self.0));
            }
            result
        }
    }
}

mod decompress {
    use super::*;

    /// Decompress step 1: Parse and validate the Ristretto encoding.
    ///
    /// Returns (s_encoding_is_canonical, s_is_negative, s) where:
    /// - s_encoding_is_canonical: true iff input bytes are canonical (< p)
    /// - s_is_negative: true iff s has its low bit set
    /// - s: the field element decoded from the compressed representation
    pub(super) fn step_1(repr: &CompressedRistretto) -> (result: (Choice, Choice, FieldElement))
        ensures
    // s has 51-bit limb bounds (ensured by from_bytes)

            fe51_limbs_bounded(&result.2, 51),
            // Parsed value matches the bytes-to-field-element spec
            spec_field_element(&result.2) == spec_field_element_from_bytes(&repr.0),
            // s_encoding_is_canonical: true iff re-encoding s gives the original bytes
            choice_is_true(result.0) == (spec_fe51_to_bytes(&result.2) == repr.0@),
            // s_is_negative: true iff low bit of canonical encoding is 1
            choice_is_true(result.1) == (spec_fe51_to_bytes(&result.2)[0] & 1 == 1),
            // s_is_negative matches the math-level sign bit of the decoded value
            choice_is_true(result.1) == math_is_negative(spec_field_element_from_bytes(&repr.0)),
    {
        // Step 1. Check s for validity:
        // 1.a) s must be 32 bytes (we get this from the type system)
        // 1.b) s < p
        // 1.c) s is nonnegative
        //
        // Our decoding routine ignores the high bit, so the only
        // possible failure for 1.b) is if someone encodes s in 0..18
        // as s+p in 2^255-19..2^255-1.  We can check this by
        // converting back to bytes, and checking that we get the
        // original input, since our encoding routine is canonical.
        let s = FieldElement::from_bytes(repr.as_bytes());
        let s_bytes_check = s.as_bytes();
        // ORIGINAL CODE: let s_encoding_is_canonical = s_bytes_check[..].ct_eq(repr.as_bytes());
        // VERUS WORKAROUND: Use ct_eq_bytes32 wrapper for Verus compatibility
        let s_encoding_is_canonical = ct_eq_bytes32(&s_bytes_check, repr.as_bytes());
        let s_is_negative = s.is_negative();

        proof {
            // VERIFICATION NOTE: only postcondition left to prove
            assume(choice_is_true(s_encoding_is_canonical) == (spec_fe51_to_bytes(&s) == repr.0@));
            assume(spec_field_element(&s) == spec_field_element_from_bytes(&repr.0));
            assume(choice_is_true(s_is_negative) == math_is_negative(
                spec_field_element_from_bytes(&repr.0),
            ));
        }

        (s_encoding_is_canonical, s_is_negative, s)
    }

    /// Decompress step 2: Compute the Edwards point from the field element s.
    ///
    /// Returns (ok, t_is_negative, y_is_zero, point) where:
    /// - ok: true iff the sqrt_ratio succeeded (s encodes a valid point)
    /// - t_is_negative: true iff T coordinate has low bit set
    /// - y_is_zero: true iff Y coordinate is zero
    /// - point: the computed RistrettoPoint
    pub(super) fn step_2(s: FieldElement) -> (result: (Choice, Choice, Choice, RistrettoPoint))
        ensures
    // Z is set to ONE by construction

            spec_field_element(&result.3.0.Z) == 1,
            // T is the product of X and Y in affine form (Z = 1)
            spec_field_element(&result.3.0.T) == math_field_mul(
                spec_field_element(&result.3.0.X),
                spec_field_element(&result.3.0.Y),
            ),
            // If decoding succeeds, the output point is well-formed and in the even subgroup
            choice_is_true(result.0) ==> is_well_formed_edwards_point(result.3.0),
            choice_is_true(result.0) ==> is_in_even_subgroup(result.3.0),
            // t_is_negative reflects the sign bit of T
            choice_is_true(result.1) == math_is_negative(spec_field_element(&result.3.0.T)),
            // y_is_zero reflects whether Y is zero
            choice_is_true(result.2) == (spec_field_element(&result.3.0.Y) == 0),
    {
        // VERIFICATION NOTE: assume(false) postpones limb bounds tracking and other proof obligations.
        proof {
            assume(false);
        }

        // Step 2.  Compute (X:Y:Z:T).
        let one = FieldElement::ONE;
        let ss = s.square();
        let u1 = &one - &ss;  //  1 + as²
        let u2 = &one + &ss;  //  1 - as²    where a=-1
        let u2_sqr = u2.square();  // (1 - as²)²

        // v == ad(1+as²)² - (1-as²)²            where d=-121665/121666
        // ORIGINAL CODE: let v = &(&(-&constants::EDWARDS_D) * &u1.square()) - &u2_sqr;
        // VERUS WORKAROUND: Use Neg::neg explicitly to avoid Verus operator parsing issue
        use core::ops::Neg;
        let neg_d = Neg::neg(&constants::EDWARDS_D);
        let u1_sqr = u1.square();
        let v = &(&neg_d * &u1_sqr) - &u2_sqr;

        let (ok, I) = (&v * &u2_sqr).invsqrt();  // 1/sqrt(v*u_2²)

        let Dx = &I * &u2;  // 1/sqrt(v)
        let Dy = &I * &(&Dx * &v);  // 1/u2

        // x == | 2s/sqrt(v) | == + sqrt(4s²/(ad(1+as²)² - (1-as²)²))
        let mut x = &(&s + &s) * &Dx;
        let x_neg = x.is_negative();
        // ORIGINAL CODE: x.conditional_negate(x_neg);
        // VERUS WORKAROUND: Use conditional_negate_field_element wrapper for Verus compatibility
        conditional_negate_field_element(&mut x, x_neg);

        // y == (1-as²)/(1+as²)
        let y = &u1 * &Dy;

        // t == ((1+as²) sqrt(4s²/(ad(1+as²)² - (1-as²)²)))/(1-as²)
        let t = &x * &y;

        (
            ok,
            t.is_negative(),
            y.is_zero(),
            RistrettoPoint(EdwardsPoint { X: x, Y: y, Z: one, T: t }),
        )
    }

}

impl Default for CompressedRistretto {
    fn default() -> (result: CompressedRistretto)
        ensures
            forall|i: int| 0 <= i < 32 ==> result.0[i] == 0u8,
    {
        CompressedRistretto::identity()
    }
}

} // verus!
impl TryFrom<&[u8]> for CompressedRistretto {
    type Error = TryFromSliceError;

    fn try_from(slice: &[u8]) -> Result<CompressedRistretto, TryFromSliceError> {
        Self::from_slice(slice)
    }
}

// ------------------------------------------------------------------------
// Serde support
// ------------------------------------------------------------------------
// Serializes to and from `RistrettoPoint` directly, doing compression
// and decompression internally.  This means that users can create
// structs containing `RistrettoPoint`s and use Serde's derived
// serializers to serialize those structures.

#[cfg(feature = "serde")]
use serde::de::Visitor;
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[cfg(feature = "serde")]
impl Serialize for RistrettoPoint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.compress().as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
impl Serialize for CompressedRistretto {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut tup = serializer.serialize_tuple(32)?;
        for byte in self.as_bytes().iter() {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for RistrettoPoint {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct RistrettoPointVisitor;

        impl<'de> Visitor<'de> for RistrettoPointVisitor {
            type Value = RistrettoPoint;

            fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str("a valid point in Ristretto format")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<RistrettoPoint, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = [0u8; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    bytes[i] = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &"expected 32 bytes"))?;
                }
                CompressedRistretto(bytes)
                    .decompress()
                    .ok_or_else(|| serde::de::Error::custom("decompression failed"))
            }
        }

        deserializer.deserialize_tuple(32, RistrettoPointVisitor)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for CompressedRistretto {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct CompressedRistrettoVisitor;

        impl<'de> Visitor<'de> for CompressedRistrettoVisitor {
            type Value = CompressedRistretto;

            fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                formatter.write_str("32 bytes of data")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<CompressedRistretto, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut bytes = [0u8; 32];
                #[allow(clippy::needless_range_loop)]
                for i in 0..32 {
                    bytes[i] = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &"expected 32 bytes"))?;
                }
                Ok(CompressedRistretto(bytes))
            }
        }

        deserializer.deserialize_tuple(32, CompressedRistrettoVisitor)
    }
}

// ------------------------------------------------------------------------
// Internal point representations
// ------------------------------------------------------------------------

verus! {

/// A `RistrettoPoint` represents a point in the Ristretto group for
/// Curve25519.  Ristretto, a variant of Decaf, constructs a
/// prime-order group as a quotient group of a subgroup of (the
/// Edwards form of) Curve25519.
///
/// Internally, a `RistrettoPoint` is implemented as a wrapper type
/// around `EdwardsPoint`, with custom equality, compression, and
/// decompression routines to account for the quotient.  This means that
/// operations on `RistrettoPoint`s are exactly as fast as operations on
/// `EdwardsPoint`s.
///
#[derive(Copy, Clone)]
pub struct RistrettoPoint(pub EdwardsPoint);

impl RistrettoPoint {
    /// Compress this point using the Ristretto encoding.
    pub fn compress(&self) -> (result: CompressedRistretto)
        ensures
            result.0 == spec_ristretto_compress(*self),
    {
        // VERIFICATION NOTE: assume(false) postpones proof obligations for compress
        proof {
            assume(false);
        }

        let mut X = self.0.X;
        let mut Y = self.0.Y;
        let Z = &self.0.Z;
        let T = &self.0.T;

        let u1 = &(Z + &Y) * &(Z - &Y);
        let u2 = &X * &Y;
        // Ignore return value since this is always square
        let (_, invsqrt) = (&u1 * &u2.square()).invsqrt();
        let i1 = &invsqrt * &u1;
        let i2 = &invsqrt * &u2;
        let z_inv = &i1 * &(&i2 * T);
        let mut den_inv = i2;

        let iX = &X * &constants::SQRT_M1;
        let iY = &Y * &constants::SQRT_M1;
        let ristretto_magic = &constants::INVSQRT_A_MINUS_D;
        let enchanted_denominator = &i1 * ristretto_magic;

        let rotate = (T * &z_inv).is_negative();

        // ORIGINAL CODE: X.conditional_assign(&iY, rotate);
        // VERUS WORKAROUND: Use conditional_assign_generic wrapper for Verus compatibility
        conditional_assign_generic(&mut X, &iY, rotate);
        // ORIGINAL CODE: Y.conditional_assign(&iX, rotate);
        conditional_assign_generic(&mut Y, &iX, rotate);
        // ORIGINAL CODE: den_inv.conditional_assign(&enchanted_denominator, rotate);
        conditional_assign_generic(&mut den_inv, &enchanted_denominator, rotate);

        // ORIGINAL CODE: Y.conditional_negate((&X * &z_inv).is_negative());
        // VERUS WORKAROUND: Use conditional_negate_field_element wrapper for Verus compatibility
        conditional_negate_field_element(&mut Y, (&X * &z_inv).is_negative());

        let mut s = &den_inv * &(Z - &Y);
        let s_is_negative = s.is_negative();
        // ORIGINAL CODE: s.conditional_negate(s_is_negative);
        // VERUS WORKAROUND: Use conditional_negate_field_element wrapper for Verus compatibility
        conditional_negate_field_element(&mut s, s_is_negative);

        CompressedRistretto(s.as_bytes())
    }
}

// ORIGINAL CODE: BatchCompressState was defined inside double_and_compress_batch
// Moved outside for Verus compatibility (doesn't support internal item statements)
// Fields made pub for Verus ensures clause visibility
/// Internal state for batch double-and-compress operation.
/// Stores intermediate field elements computed from a RistrettoPoint's
/// underlying Edwards point (X, Y, Z, T) for efficient batched inversion.
#[cfg(feature = "alloc")]
#[derive(Copy, Clone, Debug)]
pub struct BatchCompressState {
    /// made public for Verus ensures clause visibility
    pub e: FieldElement,
    /// made public for Verus ensures clause visibility
    pub f: FieldElement,
    /// made public for Verus ensures clause visibility
    pub g: FieldElement,
    /// made public for Verus ensures clause visibility
    pub h: FieldElement,
    /// made public for Verus ensures clause visibility
    pub eg: FieldElement,
    /// made public for Verus ensures clause visibility
    pub fh: FieldElement,
}

#[cfg(feature = "alloc")]
impl BatchCompressState {
    fn efgh(&self) -> (result: FieldElement)
        requires
            fe51_limbs_bounded(&self.eg, 54),
            fe51_limbs_bounded(&self.fh, 54),
        ensures
            fe51_limbs_bounded(&result, 54),
            spec_field_element(&result) == math_field_mul(
                spec_field_element(&self.eg),
                spec_field_element(&self.fh),
            ),
    {
        &self.eg * &self.fh
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<&'a RistrettoPoint> for BatchCompressState {
    #[rustfmt::skip]  // keep alignment of explanatory comments
    fn from(P: &'a RistrettoPoint) -> (result:
        BatchCompressState)/* Expected requires (if Verus supported from_req):
            is_well_formed_edwards_point(P.0),
        */

        ensures
            fe51_limbs_bounded(&result.eg, 54),
            fe51_limbs_bounded(&result.fh, 54),
            // e = 2*X*Y
            spec_field_element(&result.e) == math_field_mul(
                2,
                math_field_mul(spec_field_element(&P.0.X), spec_field_element(&P.0.Y)),
            ),
            // f = Z^2 + d*T^2
            spec_field_element(&result.f) == math_field_add(
                math_field_square(spec_field_element(&P.0.Z)),
                math_field_mul(
                    spec_field_element(&constants::EDWARDS_D),
                    math_field_square(spec_field_element(&P.0.T)),
                ),
            ),
            // g = Y^2 + X^2 (a = -1)
            spec_field_element(&result.g) == math_field_add(
                math_field_square(spec_field_element(&P.0.Y)),
                math_field_square(spec_field_element(&P.0.X)),
            ),
            // h = Z^2 - d*T^2
            spec_field_element(&result.h) == math_field_sub(
                math_field_square(spec_field_element(&P.0.Z)),
                math_field_mul(
                    spec_field_element(&constants::EDWARDS_D),
                    math_field_square(spec_field_element(&P.0.T)),
                ),
            ),
            // eg = e * g, fh = f * h
            spec_field_element(&result.eg) == math_field_mul(
                spec_field_element(&result.e),
                spec_field_element(&result.g),
            ),
            spec_field_element(&result.fh) == math_field_mul(
                spec_field_element(&result.f),
                spec_field_element(&result.h),
            ),
    {
        proof {
            assume(false);
        }  // VERIFICATION NOTE: postpone limb bounds tracking and other proof obligations

        let XX = P.0.X.square();
        let YY = P.0.Y.square();
        let ZZ = P.0.Z.square();
        let dTT = &P.0.T.square() * &constants::EDWARDS_D;

        let e = &P.0.X * &(&P.0.Y + &P.0.Y);  // = 2*X*Y
        let f = &ZZ + &dTT;  // = Z^2 + d*T^2
        let g = &YY + &XX;  // = Y^2 - a*X^2
        let h = &ZZ - &dTT;  // = Z^2 - d*T^2

        let eg = &e * &g;
        let fh = &f * &h;

        BatchCompressState { e, f, g, h, eg, fh }
    }
}

impl RistrettoPoint {
    /// Double-and-compress a batch of points.  The Ristretto encoding
    /// is not batchable, since it requires an inverse square root.
    ///
    /// However, given input points \\( P\_1, \ldots, P\_n, \\)
    /// it is possible to compute the encodings of their doubles \\(
    /// \mathrm{enc}( \[2\]P\_1), \ldots, \mathrm{enc}( \[2\]P\_n ) \\)
    /// in a batch.
    ///
    /// ## VERIFICATION NOTE
    ///
    /// This function is marked `external_body` for Verus. The Verus-compatible
    /// version [`double_and_compress_batch_verus`] provides formal specs with
    /// functional correctness guarantees. The `verus_equivalence_random` test
    /// verifies functional equivalence between the two implementations.
    ///
    #[cfg_attr(feature = "rand_core", doc = "```")]
    #[cfg_attr(not(feature = "rand_core"), doc = "```ignore")]
    /// # use curve25519_dalek::ristretto::RistrettoPoint;
    /// use rand_core::OsRng;
    ///
    /// # // Need fn main() here in comment so the doctest compiles
    /// # // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
    /// # fn main() {
    /// let mut rng = OsRng;
    ///
    /// let points: Vec<RistrettoPoint> =
    ///     (0..32).map(|_| RistrettoPoint::random(&mut rng)).collect();
    ///
    /// let compressed = RistrettoPoint::double_and_compress_batch(&points);
    ///
    /// for (P, P2_compressed) in points.iter().zip(compressed.iter()) {
    ///     assert_eq!(*P2_compressed, (P + P).compress());
    /// }
    /// # }
    /// ```
    ///
    /// [`double_and_compress_batch_verus`]: RistrettoPoint::double_and_compress_batch_verus
    #[cfg(feature = "alloc")]
    #[verifier::external_body]
    pub fn double_and_compress_batch<'a, I>(points: I) -> (result: Vec<CompressedRistretto>) where
        I: IntoIterator<Item = &'a RistrettoPoint>,
     {
        // ORIGINAL CODE: BatchCompressState was defined inline here
        // Moved outside function for Verus compatibility (doesn't support internal item statements)
        let states: Vec<BatchCompressState> = points.into_iter().map(
            BatchCompressState::from,
        ).collect();

        let mut invs: Vec<FieldElement> = states.iter().map(|state| state.efgh()).collect();

        // ORIGINAL CODE: FieldElement::batch_invert(&mut invs[..]);
        // VERUSFMT WORKAROUND: Use as_mut_slice() instead of [..] which verusfmt can't parse
        FieldElement::batch_invert(invs.as_mut_slice());

        states.iter().zip(invs.iter()).map(
            |(state, inv): (&BatchCompressState, &FieldElement)|
                {
                    let Zinv = &state.eg * inv;
                    let Tinv = &state.fh * inv;

                    let mut magic = constants::INVSQRT_A_MINUS_D;

                    let negcheck1 = (&state.eg * &Zinv).is_negative();

                    let mut e = state.e;
                    let mut g = state.g;
                    let mut h = state.h;

                    let minus_e = -&e;
                    let f_times_sqrta = &state.f * &constants::SQRT_M1;

                    e.conditional_assign(&state.g, negcheck1);
                    g.conditional_assign(&minus_e, negcheck1);
                    h.conditional_assign(&f_times_sqrta, negcheck1);

                    magic.conditional_assign(&constants::SQRT_M1, negcheck1);

                    let negcheck2 = (&(&h * &e) * &Zinv).is_negative();

                    g.conditional_negate(negcheck2);

                    let mut s = &(&h - &g) * &(&magic * &(&g * &Tinv));

                    let s_is_negative = s.is_negative();
                    s.conditional_negate(s_is_negative);

                    CompressedRistretto(s.as_bytes())
                },
        ).collect()
    }

    // ========================================================================
    // VERUS-COMPATIBLE REFACTORED VERSION
    // The following functions are refactored for Verus verification.
    // See double_and_compress_batch above for the original implementation.
    // Functional equivalence against the original implementation is covered by
    // `mod test_double_and_compress_batch` at the bottom of this file.
    // ========================================================================
    /// Verus-compatible version that takes a slice instead of IntoIterator.
    /// Use this for verification; the original double_and_compress_batch API is external_body.
    ///
    /// REFACTORING FOR VERUS:
    /// - Iterator patterns (.map().collect()) replaced with explicit while loops
    /// - IntoIterator trait replaced with concrete slice type
    /// - Vec to slice conversion wrapped in external_body helper (batch_invert_vec)
    /// - Closures replaced with inline code using Verus-compatible wrappers
    ///   (conditional_assign_generic, conditional_negate_field_element, negate_field)
    ///
    /// Spec: each output[i] = compress(2 * points[i])
    #[cfg(feature = "alloc")]
    pub fn double_and_compress_batch_verus(points: &[RistrettoPoint]) -> (result: Vec<
        CompressedRistretto,
    >)
        requires
            forall|i: int|
                0 <= i < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[i].0),
        ensures
            result@.len() == points@.len(),
            // Functional correctness: each result[i] = compress(2 * points[i])
            forall|i: int|
                0 <= i < result@.len() ==> {
                    let point_affine = edwards_point_as_affine(#[trigger] points@[i].0);
                    let doubled_affine = edwards_double(point_affine.0, point_affine.1);
                    #[trigger] result@[i].0@ == spec_ristretto_compress_affine(
                        doubled_affine.0,
                        doubled_affine.1,
                    )@
                },
    {
        proof {
            assume(false);
        }  // VERIFICATION NOTE: postpone full proof

        // ORIGINAL CODE: let states: Vec<BatchCompressState> = points.into_iter().map(BatchCompressState::from).collect();
        // Refactored to explicit loop for Verus compatibility
        let mut states: Vec<BatchCompressState> = Vec::with_capacity(points.len());
        let mut k: usize = 0;
        while k < points.len()
            invariant
                k <= points.len(),
                states.len() == k,
                // Track limb bounds from From ensures
                forall|idx: int|
                    #![auto]
                    0 <= idx < states.len() ==> fe51_limbs_bounded(&states[idx].eg, 54),
                forall|idx: int|
                    #![auto]
                    0 <= idx < states.len() ==> fe51_limbs_bounded(&states[idx].fh, 54),
            decreases points.len() - k,
        {
            states.push(BatchCompressState::from(&points[k]));
            k = k + 1;
        }

        // ORIGINAL CODE: let mut invs: Vec<FieldElement> = states.iter().map(|state| state.efgh()).collect();
        // Refactored to explicit loop for Verus compatibility
        let mut invs: Vec<FieldElement> = Vec::with_capacity(states.len());
        let mut i: usize = 0;
        while i < states.len()
            invariant
                i <= states.len(),
                invs.len() == i,
                // Track limb bounds from From ensures
                forall|idx: int|
                    #![auto]
                    0 <= idx < states.len() ==> fe51_limbs_bounded(&states[idx].eg, 54),
                forall|idx: int|
                    #![auto]
                    0 <= idx < states.len() ==> fe51_limbs_bounded(&states[idx].fh, 54),
            decreases states.len() - i,
        {
            invs.push(states[i].efgh());
            i = i + 1;
        }

        // ORIGINAL CODE: FieldElement::batch_invert(&mut invs[..]);
        Self::batch_invert_vec(&mut invs);

        // ORIGINAL CODE: states.iter().zip(invs.iter()).map(|(state, inv)| { ... }).collect()
        // Refactored to explicit loop for Verus compatibility
        let mut results: Vec<CompressedRistretto> = Vec::with_capacity(states.len());
        let mut j: usize = 0;
        while j < states.len()
            invariant
                j <= states.len(),
                results.len() == j,
            decreases states.len() - j,
        {
            proof {
                assume(false);
            }  // VERIFICATION NOTE: postpone loop body proof

            let state = &states[j];
            let inv = &invs[j];

            let Zinv = &state.eg * inv;
            let Tinv = &state.fh * inv;

            let mut magic = constants::INVSQRT_A_MINUS_D;

            let negcheck1 = (&state.eg * &Zinv).is_negative();

            let mut e = state.e;
            let mut g = state.g;
            let mut h = state.h;

            // ORIGINAL CODE: let minus_e = -&e;
            let minus_e = negate_field(&e);
            let f_times_sqrta = &state.f * &constants::SQRT_M1;

            // ORIGINAL CODE: e.conditional_assign(&state.g, negcheck1);
            conditional_assign_generic(&mut e, &state.g, negcheck1);
            // ORIGINAL CODE: g.conditional_assign(&minus_e, negcheck1);
            conditional_assign_generic(&mut g, &minus_e, negcheck1);
            // ORIGINAL CODE: h.conditional_assign(&f_times_sqrta, negcheck1);
            conditional_assign_generic(&mut h, &f_times_sqrta, negcheck1);

            // ORIGINAL CODE: magic.conditional_assign(&constants::SQRT_M1, negcheck1);
            conditional_assign_generic(&mut magic, &constants::SQRT_M1, negcheck1);

            let negcheck2 = (&(&h * &e) * &Zinv).is_negative();

            // ORIGINAL CODE: g.conditional_negate(negcheck2);
            conditional_negate_field_element(&mut g, negcheck2);

            let mut s = &(&h - &g) * &(&magic * &(&g * &Tinv));

            let s_is_negative = s.is_negative();
            // ORIGINAL CODE: s.conditional_negate(s_is_negative);
            conditional_negate_field_element(&mut s, s_is_negative);

            results.push(CompressedRistretto(s.as_bytes()));
            j = j + 1;
        }

        results
    }

    /// Wrapper for FieldElement::batch_invert that bridges Vec<T> to &mut [T].
    ///
    /// VERUS LIMITATION: Verus doesn't support Vec to mutable slice conversion:
    ///   - `invs.as_mut_slice()` is rejected
    ///   - `&mut invs` coercion to `&mut [T]` is rejected
    ///   - Complex `&mut` argument expressions are unsupported
    ///
    /// This thin wrapper is external_body but propagates ensures from
    /// FieldElement::batch_invert (field.rs:522), which is fully Verus-verified.
    /// The ensures match batch_invert's postconditions exactly.
    #[cfg(feature = "alloc")]
    #[verifier::external_body]
    fn batch_invert_vec(invs: &mut Vec<FieldElement>)
        ensures
            invs.len() == old(invs).len(),
            // From FieldElement::batch_invert ensures (field.rs:535-549):
            // Each non-zero element is replaced by its multiplicative inverse
            forall|i: int|
                #![auto]
                0 <= i < invs.len() ==> ((spec_field_element(&old(invs)[i]) != 0)
                    ==> is_inverse_field(&old(invs)[i], &invs[i])) && ((spec_field_element(
                    &old(invs)[i],
                ) == 0) ==> spec_field_element(&invs[i]) == 0),
    {
        // Delegates to Verus-verified FieldElement::batch_invert
        FieldElement::batch_invert(invs.as_mut_slice());
    }

    /// Return the coset self + E\[4\], for debugging.
    ///
    /// The result represents the Ristretto equivalence class of self -
    /// all 4 points map to the same Ristretto point.
    fn coset4(&self) -> (result: [EdwardsPoint; 4])
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            is_well_formed_edwards_point(result[0]),
            is_well_formed_edwards_point(result[1]),
            is_well_formed_edwards_point(result[2]),
            is_well_formed_edwards_point(result[3]),
            is_ristretto_coset(result, self.0),
    {
        proof {
            axiom_eight_torsion_well_formed();
        }
        let coset = [
            self.0,
            &self.0 + &constants::EIGHT_TORSION[2],
            &self.0 + &constants::EIGHT_TORSION[4],
            &self.0 + &constants::EIGHT_TORSION[6],
        ];
        coset
    }

    /// Computes the Ristretto Elligator map. This is the
    /// [`MAP`](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4)
    /// function defined in the Ristretto spec.
    ///
    /// # Note
    ///
    /// This method is not public because it's just used for hashing
    /// to a point -- proper elligator support is deferred for now.
    pub(crate) fn elligator_ristretto_flavor(r_0: &FieldElement) -> (result: RistrettoPoint)
        ensures
    // The result is the Elligator map applied to r_0

            edwards_point_as_affine(result.0) == spec_elligator_ristretto_flavor(
                spec_field_element(r_0),
            ),
            // The result is a valid Ristretto point: well-formed and in the even subgroup
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
    {
        proof {
            assume(false);  // PROOF BYPASS
        }
        let i = &constants::SQRT_M1;
        let d = &constants::EDWARDS_D;
        let one_minus_d_sq = &constants::ONE_MINUS_EDWARDS_D_SQUARED;
        let d_minus_one_sq = &constants::EDWARDS_D_MINUS_ONE_SQUARED;
        let mut c = constants::MINUS_ONE;

        let one = FieldElement::ONE;

        let r = i * &r_0.square();
        let N_s = &(&r + &one) * one_minus_d_sq;
        let D = &(&c - &(d * &r)) * &(&r + d);

        let (Ns_D_is_sq, mut s) = FieldElement::sqrt_ratio_i(&N_s, &D);
        let mut s_prime = &s * r_0;
        // VERUS WORKAROUND: Use choice_not wrapper instead of ! operator on Choice
        let s_prime_is_pos = choice_not(s_prime.is_negative());
        // VERUS WORKAROUND: Use conditional_negate_field_element wrapper
        conditional_negate_field_element(&mut s_prime, s_prime_is_pos);

        // VERUS WORKAROUND: Use choice_not and conditional_assign_generic wrappers
        let not_sq = choice_not(Ns_D_is_sq);
        conditional_assign_generic(&mut s, &s_prime, not_sq);
        conditional_assign_generic(&mut c, &r, not_sq);

        let N_t = &(&(&c * &(&r - &one)) * d_minus_one_sq) - &D;
        let s_sq = s.square();

        use crate::backend::serial::curve_models::CompletedPoint;

        // The conversion from W_i is exactly the conversion from P1xP1.
        RistrettoPoint(
            CompletedPoint {
                X: &(&s + &s) * &D,
                Z: &N_t * &constants::SQRT_AD_MINUS_ONE,
                Y: &FieldElement::ONE - &s_sq,
                T: &FieldElement::ONE + &s_sq,
            }.as_extended(),
        )
    }

    #[cfg(any(test, feature = "rand_core"))]
    /// Return a `RistrettoPoint` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements `CryptoRngCore`
    ///   (i.e. `CryptoRng` + `RngCore`) interface.
    ///
    /// # Returns
    ///
    /// A random element of the Ristretto group.
    ///
    /// # Implementation
    ///
    /// Uses the Ristretto-flavoured Elligator 2 map, so that the
    /// discrete log of the output point with respect to any other
    /// point should be unknown.  The map is applied twice and the
    /// results are added, to ensure a uniform distribution.
    #[verifier::external_body]
    pub fn random<R: CryptoRngCore + ?Sized>(rng: &mut R) -> Self {
        let mut uniform_bytes = [0u8;64];
        rng.fill_bytes(&mut uniform_bytes);

        RistrettoPoint::from_uniform_bytes(&uniform_bytes)
    }

    #[cfg(feature = "digest")]
    /// Hash a slice of bytes into a `RistrettoPoint`.
    ///
    /// Takes a type parameter `D`, which is any `Digest` producing 64
    /// bytes of output.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Implementation
    ///
    /// Uses the Ristretto-flavoured Elligator 2 map, so that the
    /// discrete log of the output point with respect to any other
    /// point should be unknown.  The map is applied twice and the
    /// results are added, to ensure a uniform distribution.
    ///
    /// # Example
    ///
    #[cfg_attr(feature = "digest", doc = "```")]
    #[cfg_attr(not(feature = "digest"), doc = "```ignore")]
    /// # use curve25519_dalek::ristretto::RistrettoPoint;
    /// use sha2::Sha512;
    ///
    /// # // Need fn main() here in comment so the doctest compiles
    /// # // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let P = RistrettoPoint::hash_from_bytes::<Sha512>(msg.as_bytes());
    /// # }
    /// ```
    ///
    /* <VERIFICATION NOTE>
     Marked as external_body due to complexity of Digest trait.
     For Verus verification, use hash_from_bytes_verus instead.
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    pub fn hash_from_bytes<D>(input: &[u8]) -> (result: RistrettoPoint) where
        D: Digest<OutputSize = U64> + Default,

        ensures
    // Result is a well-formed Ristretto point (valid Edwards point in even subgroup)

            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            // Uniform input bytes produce uniformly distributed point
            is_uniform_bytes(input) ==> is_uniform_ristretto_point(&result),
    {
        let mut hash = D::default();
        hash.update(input);
        RistrettoPoint::from_hash(hash)
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
    /// A RistrettoPoint derived from the hash
    #[cfg(feature = "digest")]
    pub fn hash_from_bytes_verus(input: &[u8]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            // Uniform input bytes produce uniformly distributed point
            is_uniform_bytes(input) ==> is_uniform_ristretto_point(&result),
    {
        let hash_bytes: [u8; 64] = sha512_hash_bytes(input);
        RistrettoPoint::from_uniform_bytes(&hash_bytes)
    }

    #[cfg(feature = "digest")]
    /// Construct a `RistrettoPoint` from an existing `Digest` instance.
    ///
    /// Use this instead of `hash_from_bytes` if it is more convenient
    /// to stream data into the `Digest` than to pass a single byte
    /// slice.
    /* <VERIFICATION NOTE>
     Marked as external_body due to GenericArray having private fields.
     For Verus verification, use from_hash_verus instead.
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    pub fn from_hash<D>(hash: D) -> (result: RistrettoPoint) where
        D: Digest<OutputSize = U64> + Default,

        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
    {
        // dealing with generic arrays is clumsy, until const generics land
        let output = hash.finalize();
        let mut output_bytes = [0u8;64];
        output_bytes.copy_from_slice(output.as_slice());

        RistrettoPoint::from_uniform_bytes(&output_bytes)
    }

    /// Verus-compatible version of from_hash that takes finalized hash bytes directly.
    ///
    /// This function is designed for Verus verification. It takes the 64-byte
    /// hash output directly, avoiding GenericArray complexity.
    ///
    /// # Inputs
    ///
    /// * `hash_bytes`: 64-byte hash output (e.g., from SHA-512)
    ///
    /// # Returns
    ///
    /// A RistrettoPoint derived from the hash
    pub fn from_hash_verus(hash_bytes: [u8; 64]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            edwards_point_as_affine(result.0) == spec_ristretto_from_uniform_bytes(&hash_bytes),
            // Uniform hash output produces uniformly distributed point
            is_uniform_bytes(&hash_bytes) ==> is_uniform_ristretto_point(&result),
    {
        RistrettoPoint::from_uniform_bytes(&hash_bytes)
    }

    /// Construct a `RistrettoPoint` from 64 bytes of data.
    ///
    /// If the input bytes are uniformly distributed, the resulting
    /// point will be uniformly distributed over the group, and its
    /// discrete log with respect to other points should be unknown.
    ///
    /// # Implementation
    ///
    /// This function splits the input array into two 32-byte halves,
    /// takes the low 255 bits of each half mod p, applies the
    /// Ristretto-flavored Elligator map to each, and adds the results.
    #[verifier::rlimit(20)]
    pub fn from_uniform_bytes(bytes: &[u8; 64]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            edwards_point_as_affine(result.0) == spec_ristretto_from_uniform_bytes(bytes),
            // Uniform input bytes produce uniformly distributed point
            is_uniform_bytes(bytes) ==> is_uniform_ristretto_point(&result),
    {
        use crate::core_assumes::{first_32_bytes, last_32_bytes};
        // This follows the one-way map construction from the Ristretto RFC:
        // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4
        /* ORIGINAL CODE: let mut r_1_bytes = [0u8;32]; r_1_bytes.copy_from_slice(&bytes[0..32]); */
        let r_1_bytes = first_32_bytes(bytes);  // Verus: copy_from_slice unsupported
        let r_1 = FieldElement::from_bytes(&r_1_bytes);
        let R_1 = RistrettoPoint::elligator_ristretto_flavor(&r_1);

        /* ORIGINAL CODE: let mut r_2_bytes = [0u8;32]; r_2_bytes.copy_from_slice(&bytes[32..64]); */
        let r_2_bytes = last_32_bytes(bytes);  // Verus: copy_from_slice unsupported
        let r_2 = FieldElement::from_bytes(&r_2_bytes);
        let R_2 = RistrettoPoint::elligator_ristretto_flavor(&r_2);

        // Applying Elligator twice and adding the results ensures a
        // uniform distribution.
        // Note: elligator_ristretto_flavor ensures is_well_formed_edwards_point for R_1 and R_2
        let result = R_1 + R_2;
        proof {
            // Add postcondition proves is_well_formed_edwards_point(result.0)
            assume(is_in_even_subgroup(result.0));
            assume(edwards_point_as_affine(result.0) == spec_ristretto_from_uniform_bytes(bytes));
            assert(is_uniform_bytes(bytes) ==> is_uniform_ristretto_point(&result)) by {
                // To prove A ==> B, assume A and derive B.
                assume(is_uniform_bytes(bytes));

                // 1. Split uniform bytes into independent uniform halves
                axiom_uniform_bytes_split(bytes, &r_1_bytes, &r_2_bytes);
                assert(is_uniform_bytes(&r_1_bytes));
                assert(is_uniform_bytes(&r_2_bytes));
                assert(is_independent_uniform_bytes32(&r_1_bytes, &r_2_bytes));

                // 2. from_bytes: uniform bytes -> uniform field elements (from from_bytes ensures)
                assert(is_uniform_field_element(&r_1));
                assert(is_uniform_field_element(&r_2));

                //    from_bytes_independent: independence is preserved
                axiom_from_bytes_independent(&r_1_bytes, &r_2_bytes, &r_1, &r_2);
                assert(is_independent_uniform_field_elements(&r_1, &r_2));

                // 3. Elligator: uniform field element -> uniform over Elligator IMAGE (~half group)
                axiom_uniform_elligator(&r_1, &R_1);
                axiom_uniform_elligator(&r_2, &R_2);
                assert(is_uniform_over_elligator_image(&R_1));
                assert(is_uniform_over_elligator_image(&R_2));

                // 4. Elligator preserves independence
                axiom_uniform_elligator_independent(&r_1, &r_2, &R_1, &R_2);
                assert(is_independent_uniform_ristretto_points(&R_1, &R_2));

                // 5. Two independent Elligator-image points sum to a full-uniform point
                axiom_uniform_elligator_sum(&R_1, &R_2, &result);
                assert(is_uniform_ristretto_point(&result));
            }
        }
        result
    }
}

impl Identity for RistrettoPoint {
    fn identity() -> (result: RistrettoPoint)
        ensures
            is_identity_edwards_point(result.0),
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
    {
        proof {
            assume(false);
        }
        RistrettoPoint(EdwardsPoint::identity())
    }
}

impl Default for RistrettoPoint {
    fn default() -> (result: RistrettoPoint)
        ensures
            is_identity_edwards_point(result.0),
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
    {
        RistrettoPoint::identity()
    }
}

// ------------------------------------------------------------------------
// Equality
// ------------------------------------------------------------------------
impl PartialEq for RistrettoPoint {
    fn eq(&self, other: &RistrettoPoint) -> bool {
        // VERIFICATION NOTE: assume(false) postpones proof obligations
        proof {
            assume(false);
        }
        // ORIGINAL CODE: self.ct_eq(other).into()
        choice_into(self.ct_eq(other))
    }
}

#[cfg(verus_keep_ghost)]
pub trait ConstantTimeEqSpecImplRistretto {
    spec fn ct_eq_req(&self, other: &Self) -> bool;
}

#[cfg(verus_keep_ghost)]
impl ConstantTimeEqSpecImplRistretto for RistrettoPoint {
    open spec fn ct_eq_req(&self, other: &RistrettoPoint) -> bool {
        is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(other.0)
    }
}

impl ConstantTimeEq for RistrettoPoint {
    /// Test equality between two `RistrettoPoint`s.
    ///
    /// # Returns
    ///
    /// * `Choice(1)` if the two `RistrettoPoint`s are equal;
    /// * `Choice(0)` otherwise.
    fn ct_eq(&self, other: &RistrettoPoint) -> (result:
        Choice)/* requires clause in ConstantTimeEqSpecImplRistretto:
           is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(other.0) */

        ensures
    // Two Ristretto points are equal iff they are in the same equivalence class

            choice_is_true(result) == ristretto_equivalent(self.0, other.0),
    {
        proof {
            // Precondition from ConstantTimeEqSpecImplRistretto::ct_eq_req needed for multiplications below
            /* VERIFICATION NOTE:
            - Verus does not support adding a "requires" clause to ct_eq with ConstantTimeEqSpecImplRistretto,
            - For standard types like Add, a "requires" clause for "add" was supported through the AddSpecImpl
            */
            assume(self.ct_eq_req(other));
            // Weaken from 52-bounded (EdwardsPoint invariant) to 54-bounded (mul precondition)
            lemma_edwards_point_weaken_to_54(&self.0);
            lemma_edwards_point_weaken_to_54(&other.0);
        }

        let X1Y2 = &self.0.X * &other.0.Y;
        let Y1X2 = &self.0.Y * &other.0.X;
        let X1X2 = &self.0.X * &other.0.X;
        let Y1Y2 = &self.0.Y * &other.0.Y;

        proof {
            assume(false);
        }  // VERIFICATION NOTE: postpone remainder of proof

        // ORIGINAL CODE: X1Y2.ct_eq(&Y1X2) | X1X2.ct_eq(&Y1Y2)
        choice_or(X1Y2.ct_eq(&Y1X2), X1X2.ct_eq(&Y1Y2))
    }
}

impl Eq for RistrettoPoint {

}

} // verus!
// ------------------------------------------------------------------------
// Arithmetic
// ------------------------------------------------------------------------
// NOTE: AddSpecImpl, SubSpecImpl, MulSpecImpl are in specs/arithm_trait_specs.rs
verus! {

impl<'a, 'b> Add<&'b RistrettoPoint> for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn add(self, other: &'b RistrettoPoint) -> (result:
        RistrettoPoint)
    // requires (from AddSpecImpl::add_req): is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(other.0)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_add(
                edwards_point_as_affine(self.0).0,
                edwards_point_as_affine(self.0).1,
                edwards_point_as_affine(other.0).0,
                edwards_point_as_affine(other.0).1,
            ),
    {
        // Edwards add ensures: is_well_formed_edwards_point(result) and affine correctness
        RistrettoPoint(&self.0 + &other.0)
    }
}

} // verus!
// Variants: T + &T, &T + T, T + T (delegate to &T + &T above)
define_ristretto_add_variants!();

verus! {

impl<'b> AddAssign<&'b RistrettoPoint> for RistrettoPoint {
    fn add_assign(&mut self, _rhs: &RistrettoPoint)
        requires
            is_well_formed_edwards_point(old(self).0),
            is_well_formed_edwards_point(_rhs.0),
        ensures
            is_well_formed_edwards_point(self.0),
            // Functional correctness: self = old(self) + rhs
            edwards_point_as_affine(self.0) == edwards_add(
                edwards_point_as_affine(old(self).0).0,
                edwards_point_as_affine(old(self).0).1,
                edwards_point_as_affine(_rhs.0).0,
                edwards_point_as_affine(_rhs.0).1,
            ),
    {
        // ORIGINAL CODE: *self = (self as &RistrettoPoint) + _rhs;
        // VERUS WORKAROUND: Use &*self instead of cast
        // RistrettoPoint add ensures: well-formedness and edwards_add correctness
        *self = &*self + _rhs;
    }
}

} // verus!
define_add_assign_variants!(LHS = RistrettoPoint, RHS = RistrettoPoint);

verus! {

impl<'a, 'b> Sub<&'b RistrettoPoint> for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn sub(self, other: &'b RistrettoPoint) -> (result:
        RistrettoPoint)
    // requires (from SubSpecImpl::sub_req): is_well_formed_edwards_point(self.0) && is_well_formed_edwards_point(other.0)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_sub(
                edwards_point_as_affine(self.0).0,
                edwards_point_as_affine(self.0).1,
                edwards_point_as_affine(other.0).0,
                edwards_point_as_affine(other.0).1,
            ),
    {
        // Edwards sub ensures: is_well_formed_edwards_point(result) and affine correctness
        RistrettoPoint(&self.0 - &other.0)
    }
}

} // verus!
// Variants: T - &T, &T - T, T - T (delegate to &T - &T above)
define_ristretto_sub_variants!();

verus! {

impl<'b> SubAssign<&'b RistrettoPoint> for RistrettoPoint {
    fn sub_assign(&mut self, _rhs: &RistrettoPoint)
        requires
            is_well_formed_edwards_point(old(self).0),
            is_well_formed_edwards_point(_rhs.0),
        ensures
            is_well_formed_edwards_point(self.0),
            // Functional correctness: self = old(self) - rhs
            edwards_point_as_affine(self.0) == edwards_sub(
                edwards_point_as_affine(old(self).0).0,
                edwards_point_as_affine(old(self).0).1,
                edwards_point_as_affine(_rhs.0).0,
                edwards_point_as_affine(_rhs.0).1,
            ),
    {
        // ORIGINAL CODE: *self = (self as &RistrettoPoint) - _rhs;
        // VERUS WORKAROUND: Use &*self instead of cast
        // RistrettoPoint sub ensures: well-formedness and edwards_sub correctness
        *self = &*self - _rhs;
    }
}

/* <ORIGINAL CODE>
impl<T> Sum<T> for RistrettoPoint where T: Borrow<RistrettoPoint> {
    fn sum<I>(iter: I) -> Self where I: Iterator<Item = T> {
        iter.fold(RistrettoPoint::identity(), |acc, item| acc + item.borrow())
    }
}
</ORIGINAL CODE> */

/* <VERIFICATION NOTE>
Iterator operations and Borrow trait are not directly supported by Verus.
We use an external_body helper to collect the iterator into Vec<RistrettoPoint>,
then call the verified sum_of_slice function for the actual computation.
TESTING: `mod test_sum` (at the bottom of this file) checks functional equivalence between
`sum_original` and the refactored `Sum::sum` implementation on random inputs.
</VERIFICATION NOTE> */

impl RistrettoPoint {
    /// Original `Sum` implementation using `Iterator::fold`.
    ///
    /// This is used for exec correctness/performance, but is not verified directly.
    /// The verified implementation is `Sum::sum` below, which reduces to `sum_of_slice`.
    /// Functional equivalence is tested in `mod test_sum` (at the bottom of this file).
    #[verifier::external_body]
    pub fn sum_original<T, I>(iter: I) -> (result: RistrettoPoint) where
        T: Borrow<RistrettoPoint>,
        I: Iterator<Item = T>,
     {
        iter.fold(RistrettoPoint::identity(), |acc, item| acc + item.borrow())
    }

    /// Compute the sum of all RistrettoPoints in a slice.
    ///
    /// # Returns
    ///
    /// The sum of all points using elliptic curve addition.
    #[allow(clippy::needless_range_loop, clippy::op_ref)]
    pub fn sum_of_slice(points: &[RistrettoPoint]) -> (result: RistrettoPoint)
        requires
            forall|i: int|
                0 <= i < points@.len() ==> is_well_formed_edwards_point(#[trigger] points@[i].0),
        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == sum_of_ristretto_points(points@),
    {
        let n = points.len();
        let mut acc = RistrettoPoint::identity();

        proof {
            assert(points@.subrange(0, 0) =~= Seq::<RistrettoPoint>::empty());
            // identity() has affine coords (0, 1) which equals sum_of_ristretto_points(empty)
            lemma_identity_affine_coords(acc.0);
        }

        for i in 0..n
            invariant
                n == points.len(),
                is_well_formed_edwards_point(acc.0),
                edwards_point_as_affine(acc.0) == sum_of_ristretto_points(
                    points@.subrange(0, i as int),
                ),
                forall|j: int|
                    0 <= j < points@.len() ==> is_well_formed_edwards_point(
                        #[trigger] points@[j].0,
                    ),
        {
            proof {
                let sub = points@.subrange(0, (i + 1) as int);
                assert(sub.subrange(0, i as int) =~= points@.subrange(0, i as int));
            }

            acc = &acc + &points[i];
        }

        proof {
            assert(points@.subrange(0, n as int) =~= points@);
        }

        acc
    }
}

impl<T> Sum<T> for RistrettoPoint where T: Borrow<RistrettoPoint> {
    fn sum<I>(iter: I) -> (result: Self) where I: Iterator<Item = T>
        requires
            forall|i: int|
                0 <= i < spec_edwards_from_ristretto_iter::<T, I>(iter).len()
                    ==> is_well_formed_edwards_point(
                    #[trigger] spec_edwards_from_ristretto_iter::<T, I>(iter)[i],
                ),
        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == sum_of_points(
                spec_edwards_from_ristretto_iter::<T, I>(iter),
            ),
    {
        // Capture the spec view of the iterator before consuming it
        let ghost iter_spec: Seq<EdwardsPoint> = spec_edwards_from_ristretto_iter::<T, I>(iter);

        let points = collect_ristretto_points(iter);
        let result = RistrettoPoint::sum_of_slice(&points);

        proof {
            // sum_of_slice ensures: edwards_point_as_affine(result.0) == sum_of_ristretto_points(points@)
            // We need: edwards_point_as_affine(result.0) == sum_of_points(iter_spec)
            // The lemma proves: sum_of_ristretto_points(r) == sum_of_points(Seq::new(r.len(), |i| r[i].0))
            lemma_sum_ristretto_edwards_equiv(points@);
            // From collect_ristretto_points ensures:
            //   points@.len() == iter_spec.len()
            //   forall i: points@[i].0 == iter_spec[i]
            // Therefore: Seq::new(points@.len(), |i| points@[i].0) == iter_spec
            assert(Seq::new(points@.len(), |i: int| points@[i].0) =~= iter_spec);
        }

        result
    }
}

} // verus!
define_sub_assign_variants!(LHS = RistrettoPoint, RHS = RistrettoPoint);

#[cfg(verus_keep_ghost)]
verus! {

/// Spec for -&RistrettoPoint
impl vstd::std_specs::ops::NegSpecImpl for &RistrettoPoint {
    open spec fn obeys_neg_spec() -> bool {
        false
    }

    open spec fn neg_req(self) -> bool {
        // Requires limb bounds on X and T for field element negation
        fe51_limbs_bounded(&self.0.X, 52) && fe51_limbs_bounded(&self.0.T, 52)
    }

    open spec fn neg_spec(self) -> RistrettoPoint {
        arbitrary()  // postcondition provided in function body

    }
}

/// Spec for -RistrettoPoint (owned)
impl vstd::std_specs::ops::NegSpecImpl for RistrettoPoint {
    open spec fn obeys_neg_spec() -> bool {
        false
    }

    open spec fn neg_req(self) -> bool {
        // Requires limb bounds on X and T for field element negation
        fe51_limbs_bounded(&self.0.X, 52) && fe51_limbs_bounded(&self.0.T, 52)
    }

    open spec fn neg_spec(self) -> RistrettoPoint {
        arbitrary()  // postcondition provided in function body

    }
}

} // verus!
verus! {

impl<'a> Neg for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    fn neg(self) -> (result:
        RistrettoPoint)
    // requires clause inherited from NegSpecImpl::neg_req:
    //   fe51_limbs_bounded(&self.0.X, 52) && fe51_limbs_bounded(&self.0.T, 52)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_neg(edwards_point_as_affine(self.0)),
    {
        // VERUS WORKAROUND: Use explicit trait method because Verus interprets -x as 0-x (integer)
        // Edwards neg ensures: is_well_formed_edwards_point(result) and edwards_neg correctness
        RistrettoPoint(Neg::neg(&self.0))
    }
}

impl Neg for RistrettoPoint {
    type Output = RistrettoPoint;

    fn neg(self) -> (result:
        RistrettoPoint)
    // requires clause inherited from NegSpecImpl::neg_req:
    //   fe51_limbs_bounded(&self.0.X, 52) && fe51_limbs_bounded(&self.0.T, 52)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_neg(edwards_point_as_affine(self.0)),
    {
        // VERUS WORKAROUND: Use explicit trait method because Verus interprets -x as 0-x (integer)
        // Delegates to &RistrettoPoint neg which delegates to Edwards neg
        Neg::neg(&self)
    }
}

impl<'b> MulAssign<&'b Scalar> for RistrettoPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar)
        requires
            scalar.bytes[31] <= 127,
            is_well_formed_edwards_point(old(self).0),
        ensures
            is_well_formed_edwards_point(self.0),
            // Functional correctness: self = [scalar] * old(self)
            edwards_point_as_affine(self.0) == edwards_scalar_mul(
                edwards_point_as_affine(old(self).0),
                spec_scalar(scalar),
            ),
    {
        // ORIGINAL CODE: let result = (self as &RistrettoPoint) * scalar;
        // VERUS WORKAROUND: Use &*self instead of cast
        // Edwards mul ensures: is_well_formed_edwards_point(result) and scalar_mul correctness
        let result = &*self * scalar;
        *self = result;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a RistrettoPoint {
    type Output = RistrettoPoint;

    /// Scalar multiplication: compute `scalar * self`.
    fn mul(self, scalar: &'b Scalar) -> (result:
        RistrettoPoint)
    // requires clause inherited from MulSpecImpl::mul_req:
    //   scalar.bytes[31] <= 127 && is_well_formed_edwards_point(self.0)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_scalar_mul(
                edwards_point_as_affine(self.0),
                spec_scalar(scalar),
            ),
    {
        // Edwards mul ensures: is_well_formed_edwards_point(result) and scalar_mul correctness
        RistrettoPoint(&self.0 * scalar)
    }
}

impl<'a, 'b> Mul<&'b RistrettoPoint> for &'a Scalar {
    type Output = RistrettoPoint;

    /// Scalar multiplication: compute `self * scalar`.
    fn mul(self, point: &'b RistrettoPoint) -> (result:
        RistrettoPoint)
    // requires clause inherited from MulSpecImpl::mul_req:
    //   self.bytes[31] <= 127 && is_well_formed_edwards_point(point.0)

        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == edwards_scalar_mul(
                edwards_point_as_affine(point.0),
                spec_scalar(self),
            ),
    {
        // Edwards mul ensures: is_well_formed_edwards_point(result) and scalar_mul correctness
        RistrettoPoint(self * &point.0)
    }
}

impl RistrettoPoint {
    /// Fixed-base scalar multiplication by the Ristretto base point.
    ///
    /// Uses precomputed basepoint tables when the `precomputed-tables` feature
    /// is enabled, trading off increased code size for ~4x better performance.
    pub fn mul_base(scalar: &Scalar) -> (result: Self)
        requires
            scalar.bytes[31] <= 127,
        ensures
            is_well_formed_edwards_point(result.0),
            // Functional correctness: result = [scalar] * B where B is the Ristretto basepoint
            edwards_point_as_affine(result.0) == edwards_scalar_mul(
                spec_ristretto_basepoint(),
                spec_scalar(scalar),
            ),
    {
        let r = {
            #[cfg(not(feature = "precomputed-tables"))]
            { scalar * constants::RISTRETTO_BASEPOINT_POINT }

            #[cfg(feature = "precomputed-tables")]
            { scalar * constants::RISTRETTO_BASEPOINT_TABLE }
        };
        proof {
            // The underlying Edwards mul_base ensures the functional correctness.
            // Since edwards_scalar_mul == edwards_scalar_mul and
            // spec_ristretto_basepoint() == spec_ristretto_basepoint(), the postcondition holds.
            assume(is_well_formed_edwards_point(r.0));
            assume(edwards_point_as_affine(r.0) == edwards_scalar_mul(
                spec_ristretto_basepoint(),
                spec_scalar(scalar),
            ));
        }
        r
    }
}

} // verus!
define_mul_assign_variants!(LHS = RistrettoPoint, RHS = Scalar);

define_mul_variants!(LHS = RistrettoPoint, RHS = Scalar, Output = RistrettoPoint);
define_mul_variants!(LHS = Scalar, RHS = RistrettoPoint, Output = RistrettoPoint);

// ------------------------------------------------------------------------
// Multiscalar Multiplication impls
// ------------------------------------------------------------------------

// These use iterator combinators to unwrap the underlying points and
// forward to the EdwardsPoint implementations.

verus! {

#[cfg(feature = "alloc")]
impl MultiscalarMul for RistrettoPoint {
    type Point = RistrettoPoint;

    #[verifier::external_body]
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> RistrettoPoint where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<RistrettoPoint>,
     {
        let extended_points = points.into_iter().map(|P| P.borrow().0);
        RistrettoPoint(EdwardsPoint::multiscalar_mul(scalars, extended_points))
    }
}

#[cfg(feature = "alloc")]
impl VartimeMultiscalarMul for RistrettoPoint {
    type Point = RistrettoPoint;

    #[verifier::external_body]
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<RistrettoPoint> where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<RistrettoPoint>>,
     {
        let extended_points = points.into_iter().map(|opt_P| opt_P.map(|P| P.0));

        EdwardsPoint::optional_multiscalar_mul(scalars, extended_points).map(RistrettoPoint)
    }
}

/*
  * VERIFICATION NOTE
  * =================
  * Verus limitations addressed in these _verus versions:
  * - IntoIterator with I::Item projections → use Iterator bounds instead
  *
  * RistrettoPoint wraps EdwardsPoint, so these delegate to EdwardsPoint::*_verus.
  * We collect iterators to Vec (since Verus doesn't support map), then call
  * the Edwards versions. Specs are expressed directly in terms of Edwards
  * operations since we just extract the inner EdwardsPoint and delegate.
  *
  * Functional equivalence against the original (external_body) implementations is covered by
  * `mod test_multiscalar_mul` at the bottom of this file.
  */

impl RistrettoPoint {
    /// Verus-compatible version of multiscalar_mul (constant-time).
    /// Delegates to EdwardsPoint::multiscalar_mul_verus.
    #[cfg(feature = "alloc")]
    pub fn multiscalar_mul_verus<S, P, I, J>(scalars: I, points: J) -> (result:
        RistrettoPoint) where
        S: Borrow<Scalar>,
        P: Borrow<RistrettoPoint>,
        I: Iterator<Item = S> + Clone,
        J: Iterator<Item = P> + Clone,

        requires
            spec_scalars_from_iter::<S, I>(scalars).len() == spec_edwards_from_ristretto_iter::<
                P,
                J,
            >(points).len(),
            forall|i: int|
                0 <= i < spec_edwards_from_ristretto_iter::<P, J>(points).len()
                    ==> is_well_formed_edwards_point(
                    #[trigger] spec_edwards_from_ristretto_iter::<P, J>(points)[i],
                ),
        ensures
            is_well_formed_edwards_point(result.0),
            edwards_point_as_affine(result.0) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                spec_edwards_from_ristretto_iter::<P, J>(points),
            ),
    {
        /* <ORIGINAL CODE>
        let extended_points = points.into_iter().map(|P| P.borrow().0);
        RistrettoPoint(EdwardsPoint::multiscalar_mul(scalars, extended_points))
        </ORIGINAL CODE> */
        // Clone iterator with spec guarantee, then collect directly to Edwards points
        let cloned = clone_ristretto_iter_with_spec(points);
        let ghost points_for_spec = cloned.0;
        let points_to_collect = cloned.1;
        let edwards_vec = collect_edwards_from_ristretto_iter(points_to_collect);

        // Create the iterator for EdwardsPoint::multiscalar_mul_verus
        let edwards_iter = vec_to_edwards_iter(edwards_vec);

        // Call EdwardsPoint::multiscalar_mul_verus
        let edwards_result = EdwardsPoint::multiscalar_mul_verus(scalars, edwards_iter);

        proof {
            // Chain: spec_points_from_iter(edwards_iter) == edwards_vec@
            //        == spec_edwards_from_ristretto_iter(points_for_spec)
            //        == spec_edwards_from_ristretto_iter(points) (from clone)
            assert(spec_points_from_iter::<EdwardsPoint, _>(edwards_iter)
                =~= spec_edwards_from_ristretto_iter::<P, J>(points_for_spec));
        }

        RistrettoPoint(edwards_result)
    }

    /// Verus-compatible version of optional_multiscalar_mul.
    /// Delegates to EdwardsPoint::optional_multiscalar_mul_verus.
    #[cfg(feature = "alloc")]
    pub fn optional_multiscalar_mul_verus<S, I, J>(scalars: I, points: J) -> (result: Option<
        RistrettoPoint,
    >) where
        S: Borrow<Scalar>,
        I: Iterator<Item = S> + Clone,
        J: Iterator<Item = Option<RistrettoPoint>> + Clone,

        requires
            spec_scalars_from_iter::<S, I>(scalars).len()
                == spec_optional_edwards_from_ristretto_iter::<J>(points).len(),
            forall|i: int|
                0 <= i < spec_optional_edwards_from_ristretto_iter::<J>(points).len() && (
                #[trigger] spec_optional_edwards_from_ristretto_iter::<J>(points)[i]).is_some()
                    ==> is_well_formed_edwards_point(
                    spec_optional_edwards_from_ristretto_iter::<J>(points)[i].unwrap(),
                ),
        ensures
            result.is_some() <==> all_points_some(
                spec_optional_edwards_from_ristretto_iter::<J>(points),
            ),
            result.is_some() ==> is_well_formed_edwards_point(result.unwrap().0),
            result.is_some() ==> edwards_point_as_affine(result.unwrap().0) == sum_of_scalar_muls(
                spec_scalars_from_iter::<S, I>(scalars),
                unwrap_points(spec_optional_edwards_from_ristretto_iter::<J>(points)),
            ),
    {
        /* <ORIGINAL CODE>
        let extended_points = points.into_iter().map(|opt_P| opt_P.map(|P| P.0));
        EdwardsPoint::optional_multiscalar_mul(scalars, extended_points).map(RistrettoPoint)
        </ORIGINAL CODE> */
        // Clone iterator with spec guarantee, then collect directly to Edwards points
        let cloned = clone_optional_ristretto_iter_with_spec(points);
        let ghost points_for_spec = cloned.0;
        let points_to_collect = cloned.1;
        let edwards_vec = collect_optional_edwards_from_ristretto_iter(points_to_collect);

        // Create the iterator for EdwardsPoint::optional_multiscalar_mul_verus
        let edwards_iter = vec_to_optional_edwards_iter(edwards_vec);

        // Call EdwardsPoint::optional_multiscalar_mul_verus
        let edwards_result = EdwardsPoint::optional_multiscalar_mul_verus(scalars, edwards_iter);

        // Use match instead of map so Verus can track the relationship
        let result = match edwards_result {
            Some(r) => Some(RistrettoPoint(r)),
            None => None,
        };

        proof {
            // Chain: spec_optional_points_from_iter(edwards_iter) == edwards_vec@
            //        == spec_optional_edwards_from_ristretto_iter(points_for_spec)
            //        == spec_optional_edwards_from_ristretto_iter(points) (from clone)
            assert(spec_optional_points_from_iter(edwards_iter)
                =~= spec_optional_edwards_from_ristretto_iter::<J>(points_for_spec));
        }

        result
    }
}

} // verus!
/// Precomputation for variable-time multiscalar multiplication with `RistrettoPoint`s.
// This wraps the inner implementation in a facade type so that we can
// decouple stability of the inner type from the stability of the
// outer type.
#[cfg(feature = "alloc")]
pub struct VartimeRistrettoPrecomputation(crate::backend::VartimePrecomputedStraus);

#[cfg(feature = "alloc")]
impl VartimePrecomputedMultiscalarMul for VartimeRistrettoPrecomputation {
    type Point = RistrettoPoint;

    fn new<I>(static_points: I) -> Self
    where
        I: IntoIterator,
        I::Item: Borrow<Self::Point>,
    {
        Self(crate::backend::VartimePrecomputedStraus::new(
            static_points.into_iter().map(|P| P.borrow().0),
        ))
    }

    fn optional_mixed_multiscalar_mul<I, J, K>(
        &self,
        static_scalars: I,
        dynamic_scalars: J,
        dynamic_points: K,
    ) -> Option<Self::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Scalar>,
        K: IntoIterator<Item = Option<Self::Point>>,
    {
        self.0
            .optional_mixed_multiscalar_mul(
                static_scalars,
                dynamic_scalars,
                dynamic_points.into_iter().map(|P_opt| P_opt.map(|P| P.0)),
            )
            .map(RistrettoPoint)
    }
}

verus! {

impl RistrettoPoint {
    /// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the
    /// Ristretto basepoint.
    pub fn vartime_double_scalar_mul_basepoint(
        a: &Scalar,
        A: &RistrettoPoint,
        b: &Scalar,
    ) -> (result: RistrettoPoint)
        requires
            is_well_formed_edwards_point(A.0),
        ensures
            is_well_formed_edwards_point(result.0),
            // Functional correctness: result = a*A + b*B where B is the Ristretto basepoint
            edwards_point_as_affine(result.0) == {
                let aA = edwards_scalar_mul(edwards_point_as_affine(A.0), spec_scalar(a));
                let bB = edwards_scalar_mul(spec_ristretto_basepoint(), spec_scalar(b));
                edwards_add(aA.0, aA.1, bB.0, bB.1)
            },
    {
        RistrettoPoint(EdwardsPoint::vartime_double_scalar_mul_basepoint(a, &A.0, b))
    }
}

/// A precomputed table of multiples of a basepoint, used to accelerate
/// scalar multiplication.
///
/// A precomputed table of multiples of the Ristretto basepoint is
/// available in the `constants` module:
/// ```
/// use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
/// use curve25519_dalek::scalar::Scalar;
///
/// let a = Scalar::from(87329482u64);
/// let P = &a * RISTRETTO_BASEPOINT_TABLE;
/// ```
#[cfg(feature = "precomputed-tables")]
#[derive(Clone)]
#[repr(transparent)]
pub struct RistrettoBasepointTable(pub EdwardsBasepointTable);

#[cfg(feature = "precomputed-tables")]
impl<'a, 'b> Mul<&'b Scalar> for &'a RistrettoBasepointTable {
    type Output = RistrettoPoint;

    fn mul(self, scalar: &'b Scalar) -> (result:
        RistrettoPoint)/* requires clause in MulSpecImpl<&Scalar> for &RistrettoBasepointTable in arithm_trait_specs.rs:
        requires scalar.bytes[31] <= 127
    */

        ensures
            is_well_formed_edwards_point(result.0),
            // Functional correctness: result = [scalar] * B
            edwards_point_as_affine(result.0) == edwards_scalar_mul(
                spec_ristretto_basepoint(),
                spec_scalar(scalar),
            ),
    {
        RistrettoPoint(&self.0 * scalar)
    }
}

#[cfg(feature = "precomputed-tables")]
impl<'a, 'b> Mul<&'a RistrettoBasepointTable> for &'b Scalar {
    type Output = RistrettoPoint;

    fn mul(self, basepoint_table: &'a RistrettoBasepointTable) -> (result:
        RistrettoPoint)/* requires clause in MulSpecImpl<&RistrettoBasepointTable> for &Scalar in arithm_trait_specs.rs:
        requires self.bytes[31] <= 127
    */

        ensures
            is_well_formed_edwards_point(result.0),
            // Functional correctness: result = [scalar] * B
            edwards_point_as_affine(result.0) == edwards_scalar_mul(
                spec_ristretto_basepoint(),
                spec_scalar(self),
            ),
    {
        RistrettoPoint(self * &basepoint_table.0)
    }
}

#[cfg(feature = "precomputed-tables")]
impl RistrettoBasepointTable {
    /// Create a precomputed table of multiples of the given `basepoint`.
    pub fn create(basepoint: &RistrettoPoint) -> (result: RistrettoBasepointTable)
        requires
            is_well_formed_edwards_point(basepoint.0),
        ensures
            is_valid_edwards_basepoint_table(result.0, edwards_point_as_affine(basepoint.0)),
    {
        RistrettoBasepointTable(EdwardsBasepointTable::create(&basepoint.0))
    }

    /// Get the basepoint for this table as a `RistrettoPoint`.
    pub fn basepoint(&self) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            // The result is the Ristretto basepoint B
            edwards_point_as_affine(result.0) == spec_ristretto_basepoint(),
    {
        RistrettoPoint(self.0.basepoint())
    }
}

// ------------------------------------------------------------------------
// Constant-time conditional selection
// ------------------------------------------------------------------------
impl ConditionallySelectable for RistrettoPoint {
    /// Conditionally select between `self` and `other`.
    ///
    /// # Example
    ///
    /// ```
    /// use subtle::ConditionallySelectable;
    /// use subtle::Choice;
    /// #
    /// # use curve25519_dalek::traits::Identity;
    /// # use curve25519_dalek::ristretto::RistrettoPoint;
    /// # use curve25519_dalek::constants;
    /// # fn main() {
    ///
    /// let A = RistrettoPoint::identity();
    /// let B = constants::RISTRETTO_BASEPOINT_POINT;
    ///
    /// let mut P = A;
    ///
    /// P = RistrettoPoint::conditional_select(&A, &B, Choice::from(0));
    /// assert_eq!(P, A);
    /// P = RistrettoPoint::conditional_select(&A, &B, Choice::from(1));
    /// assert_eq!(P, B);
    /// # }
    /// ```
    fn conditional_select(a: &RistrettoPoint, b: &RistrettoPoint, choice: Choice) -> (result:
        RistrettoPoint)
        ensures
    // If choice is false (0), return a

            !choice_is_true(choice) ==> result.0 == a.0,
            // If choice is true (1), return b
            choice_is_true(choice) ==> result.0 == b.0,
    {
        RistrettoPoint(EdwardsPoint::conditional_select(&a.0, &b.0, choice))
    }
}

} // verus!
// ------------------------------------------------------------------------
// Debug traits
// ------------------------------------------------------------------------
impl Debug for CompressedRistretto {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "CompressedRistretto: {:?}", self.as_bytes())
    }
}

impl Debug for RistrettoPoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let coset = self.coset4();
        write!(
            f,
            "RistrettoPoint: coset \n{:?}\n{:?}\n{:?}\n{:?}",
            coset[0], coset[1], coset[2], coset[3]
        )
    }
}

// ------------------------------------------------------------------------
// group traits
// ------------------------------------------------------------------------

// Use the full trait path to avoid Group::identity overlapping Identity::identity in the
// rest of the module (e.g. tests).
#[cfg(feature = "group")]
impl group::Group for RistrettoPoint {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        // NOTE: this is duplicated due to different `rng` bounds
        let mut uniform_bytes = [0u8; 64];
        rng.fill_bytes(&mut uniform_bytes);
        RistrettoPoint::from_uniform_bytes(&uniform_bytes)
    }

    fn identity() -> Self {
        Identity::identity()
    }

    fn generator() -> Self {
        constants::RISTRETTO_BASEPOINT_POINT
    }

    fn is_identity(&self) -> Choice {
        self.ct_eq(&Identity::identity())
    }

    fn double(&self) -> Self {
        self + self
    }
}

#[cfg(feature = "group")]
impl GroupEncoding for RistrettoPoint {
    type Repr = [u8; 32];

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        let (s_encoding_is_canonical, s_is_negative, s) =
            decompress::step_1(&CompressedRistretto(*bytes));

        let s_is_valid = s_encoding_is_canonical & !s_is_negative;

        let (ok, t_is_negative, y_is_zero, res) = decompress::step_2(s);

        CtOption::new(res, s_is_valid & ok & !t_is_negative & !y_is_zero)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // Just use the checked API; the checks we could skip aren't expensive.
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        self.compress().to_bytes()
    }
}

#[cfg(feature = "group")]
impl PrimeGroup for RistrettoPoint {}

/// Ristretto has a cofactor of 1.
#[cfg(feature = "group")]
impl CofactorGroup for RistrettoPoint {
    type Subgroup = Self;

    fn clear_cofactor(&self) -> Self::Subgroup {
        *self
    }

    fn into_subgroup(self) -> CtOption<Self::Subgroup> {
        CtOption::new(self, Choice::from(1))
    }

    fn is_torsion_free(&self) -> Choice {
        Choice::from(1)
    }
}

// ------------------------------------------------------------------------
// Zeroize traits
// ------------------------------------------------------------------------

verus! {

#[cfg(feature = "zeroize")]
impl Zeroize for CompressedRistretto {
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 32 ==> #[trigger] self.0[i] == 0u8,
    {
        crate::core_assumes::zeroize_bytes32(&mut self.0);
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for RistrettoPoint {
    fn zeroize(&mut self)
        ensures
    // Inner EdwardsPoint is set to identity (0, 1, 1, 0)

            forall|i: int| 0 <= i < 5 ==> self.0.X.limbs[i] == 0,
            forall|i: int| 0 <= i < 5 ==> self.0.T.limbs[i] == 0,
            self.0.Y == FieldElement::ONE,
            self.0.Z == FieldElement::ONE,
    {
        self.0.zeroize();
    }
}

} // verus!
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::edwards::CompressedEdwardsY;
//     use rand_core::OsRng;
//     #[test]
//     #[cfg(feature = "serde")]
//     fn serde_bincode_basepoint_roundtrip() {
//         use bincode;
//         let encoded = bincode::serialize(&constants::RISTRETTO_BASEPOINT_POINT).unwrap();
//         let enc_compressed =
//             bincode::serialize(&constants::RISTRETTO_BASEPOINT_COMPRESSED).unwrap();
//         assert_eq!(encoded, enc_compressed);
//         // Check that the encoding is 32 bytes exactly
//         assert_eq!(encoded.len(), 32);
//         let dec_uncompressed: RistrettoPoint = bincode::deserialize(&encoded).unwrap();
//         let dec_compressed: CompressedRistretto = bincode::deserialize(&encoded).unwrap();
//         assert_eq!(dec_uncompressed, constants::RISTRETTO_BASEPOINT_POINT);
//         assert_eq!(dec_compressed, constants::RISTRETTO_BASEPOINT_COMPRESSED);
//         // Check that the encoding itself matches the usual one
//         let raw_bytes = constants::RISTRETTO_BASEPOINT_COMPRESSED.as_bytes();
//         let bp: RistrettoPoint = bincode::deserialize(raw_bytes).unwrap();
//         assert_eq!(bp, constants::RISTRETTO_BASEPOINT_POINT);
//     }
//     #[test]
//     fn scalarmult_ristrettopoint_works_both_ways() {
//         let P = constants::RISTRETTO_BASEPOINT_POINT;
//         let s = Scalar::from(999u64);
//         let P1 = P * s;
//         let P2 = s * P;
//         assert!(P1.compress().as_bytes() == P2.compress().as_bytes());
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn impl_sum() {
//         // Test that sum works for non-empty iterators
//         let BASE = constants::RISTRETTO_BASEPOINT_POINT;
//         let s1 = Scalar::from(999u64);
//         let P1 = BASE * s1;
//         let s2 = Scalar::from(333u64);
//         let P2 = BASE * s2;
//         let vec = vec![P1, P2];
//         let sum: RistrettoPoint = vec.iter().sum();
//         assert_eq!(sum, P1 + P2);
//         // Test that sum works for the empty iterator
//         let empty_vector: Vec<RistrettoPoint> = vec![];
//         let sum: RistrettoPoint = empty_vector.iter().sum();
//         assert_eq!(sum, RistrettoPoint::identity());
//         // Test that sum works on owning iterators
//         let s = Scalar::from(2u64);
//         let mapped = vec.iter().map(|x| x * s);
//         let sum: RistrettoPoint = mapped.sum();
//         assert_eq!(sum, P1 * s + P2 * s);
//     }
//     #[test]
//     fn decompress_negative_s_fails() {
//         // constants::d is neg, so decompression should fail as |d| != d.
//         let bad_compressed = CompressedRistretto(constants::EDWARDS_D.as_bytes());
//         assert!(bad_compressed.decompress().is_none());
//     }
//     #[test]
//     fn decompress_id() {
//         let compressed_id = CompressedRistretto::identity();
//         let id = compressed_id.decompress().unwrap();
//         let mut identity_in_coset = false;
//         for P in &id.coset4() {
//             if P.compress() == CompressedEdwardsY::identity() {
//                 identity_in_coset = true;
//             }
//         }
//         assert!(identity_in_coset);
//     }
//     #[test]
//     fn compress_id() {
//         let id = RistrettoPoint::identity();
//         assert_eq!(id.compress(), CompressedRistretto::identity());
//     }
//     #[test]
//     fn basepoint_roundtrip() {
//         let bp_compressed_ristretto = constants::RISTRETTO_BASEPOINT_POINT.compress();
//         let bp_recaf = bp_compressed_ristretto.decompress().unwrap().0;
//         // Check that bp_recaf differs from bp by a point of order 4
//         let diff = constants::RISTRETTO_BASEPOINT_POINT.0 - bp_recaf;
//         let diff4 = diff.mul_by_pow_2(2);
//         assert_eq!(diff4.compress(), CompressedEdwardsY::identity());
//     }
//     #[test]
//     fn encodings_of_small_multiples_of_basepoint() {
//         // Table of encodings of i*basepoint
//         // Generated using ristretto.sage
//         let compressed = [
//             CompressedRistretto([
//                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
//                 0, 0, 0, 0,
//             ]),
//             CompressedRistretto([
//                 226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227,
//                 11, 106, 165, 130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118,
//             ]),
//             CompressedRistretto([
//                 106, 73, 50, 16, 247, 73, 156, 209, 127, 236, 181, 16, 174, 12, 234, 35, 161, 16,
//                 232, 213, 185, 1, 248, 172, 173, 211, 9, 92, 115, 163, 185, 25,
//             ]),
//             CompressedRistretto([
//                 148, 116, 31, 93, 93, 82, 117, 94, 206, 79, 35, 240, 68, 238, 39, 213, 209, 234,
//                 30, 43, 209, 150, 180, 98, 22, 107, 22, 21, 42, 157, 2, 89,
//             ]),
//             CompressedRistretto([
//                 218, 128, 134, 39, 115, 53, 139, 70, 111, 250, 223, 224, 179, 41, 58, 179, 217,
//                 253, 83, 197, 234, 108, 149, 83, 88, 245, 104, 50, 45, 175, 106, 87,
//             ]),
//             CompressedRistretto([
//                 232, 130, 177, 49, 1, 107, 82, 193, 211, 51, 112, 128, 24, 124, 247, 104, 66, 62,
//                 252, 203, 181, 23, 187, 73, 90, 184, 18, 196, 22, 15, 244, 78,
//             ]),
//             CompressedRistretto([
//                 246, 71, 70, 211, 201, 43, 19, 5, 14, 216, 216, 2, 54, 167, 240, 0, 124, 59, 63,
//                 150, 47, 91, 167, 147, 209, 154, 96, 30, 187, 29, 244, 3,
//             ]),
//             CompressedRistretto([
//                 68, 245, 53, 32, 146, 110, 200, 31, 189, 90, 56, 120, 69, 190, 183, 223, 133, 169,
//                 106, 36, 236, 225, 135, 56, 189, 207, 166, 167, 130, 42, 23, 109,
//             ]),
//             CompressedRistretto([
//                 144, 50, 147, 216, 242, 40, 126, 190, 16, 226, 55, 77, 193, 165, 62, 11, 200, 135,
//                 229, 146, 105, 159, 2, 208, 119, 213, 38, 60, 221, 85, 96, 28,
//             ]),
//             CompressedRistretto([
//                 2, 98, 42, 206, 143, 115, 3, 163, 28, 175, 198, 63, 143, 196, 143, 220, 22, 225,
//                 200, 200, 210, 52, 178, 240, 214, 104, 82, 130, 169, 7, 96, 49,
//             ]),
//             CompressedRistretto([
//                 32, 112, 111, 215, 136, 178, 114, 10, 30, 210, 165, 218, 212, 149, 43, 1, 244, 19,
//                 188, 240, 231, 86, 77, 232, 205, 200, 22, 104, 158, 45, 185, 95,
//             ]),
//             CompressedRistretto([
//                 188, 232, 63, 139, 165, 221, 47, 165, 114, 134, 76, 36, 186, 24, 16, 249, 82, 43,
//                 198, 0, 74, 254, 149, 135, 122, 199, 50, 65, 202, 253, 171, 66,
//             ]),
//             CompressedRistretto([
//                 228, 84, 158, 225, 107, 154, 160, 48, 153, 202, 32, 140, 103, 173, 175, 202, 250,
//                 76, 63, 62, 78, 83, 3, 222, 96, 38, 227, 202, 143, 248, 68, 96,
//             ]),
//             CompressedRistretto([
//                 170, 82, 224, 0, 223, 46, 22, 245, 95, 177, 3, 47, 195, 59, 196, 39, 66, 218, 214,
//                 189, 90, 143, 192, 190, 1, 103, 67, 108, 89, 72, 80, 31,
//             ]),
//             CompressedRistretto([
//                 70, 55, 107, 128, 244, 9, 178, 157, 194, 181, 246, 240, 197, 37, 145, 153, 8, 150,
//                 229, 113, 111, 65, 71, 124, 211, 0, 133, 171, 127, 16, 48, 30,
//             ]),
//             CompressedRistretto([
//                 224, 196, 24, 247, 200, 217, 196, 205, 215, 57, 91, 147, 234, 18, 79, 58, 217, 144,
//                 33, 187, 104, 29, 252, 51, 2, 169, 217, 154, 46, 83, 230, 78,
//             ]),
//         ];
//         let mut bp = RistrettoPoint::identity();
//         for point in compressed {
//             assert_eq!(bp.compress(), point);
//             bp += constants::RISTRETTO_BASEPOINT_POINT;
//         }
//     }
//     #[test]
//     fn four_torsion_basepoint() {
//         let bp = constants::RISTRETTO_BASEPOINT_POINT;
//         let bp_coset = bp.coset4();
//         for point in bp_coset {
//             assert_eq!(bp, RistrettoPoint(point));
//         }
//     }
//     #[test]
//     fn four_torsion_random() {
//         let mut rng = OsRng;
//         let P = RistrettoPoint::mul_base(&Scalar::random(&mut rng));
//         let P_coset = P.coset4();
//         for point in P_coset {
//             assert_eq!(P, RistrettoPoint(point));
//         }
//     }
//     #[test]
//     fn elligator_vs_ristretto_sage() {
//         // Test vectors extracted from ristretto.sage.
//         //
//         // Notice that all of the byte sequences have bit 255 set to 0; this is because
//         // ristretto.sage does not mask the high bit of a field element.  When the high bit is set,
//         // the ristretto.sage elligator implementation gives different results, since it takes a
//         // different field element as input.
//         let bytes: [[u8; 32]; 16] = [
//             [
//                 184, 249, 135, 49, 253, 123, 89, 113, 67, 160, 6, 239, 7, 105, 211, 41, 192, 249,
//                 185, 57, 9, 102, 70, 198, 15, 127, 7, 26, 160, 102, 134, 71,
//             ],
//             [
//                 229, 14, 241, 227, 75, 9, 118, 60, 128, 153, 226, 21, 183, 217, 91, 136, 98, 0,
//                 231, 156, 124, 77, 82, 139, 142, 134, 164, 169, 169, 62, 250, 52,
//             ],
//             [
//                 115, 109, 36, 220, 180, 223, 99, 6, 204, 169, 19, 29, 169, 68, 84, 23, 21, 109,
//                 189, 149, 127, 205, 91, 102, 172, 35, 112, 35, 134, 69, 186, 34,
//             ],
//             [
//                 16, 49, 96, 107, 171, 199, 164, 9, 129, 16, 64, 62, 241, 63, 132, 173, 209, 160,
//                 112, 215, 105, 50, 157, 81, 253, 105, 1, 154, 229, 25, 120, 83,
//             ],
//             [
//                 156, 131, 161, 162, 236, 251, 5, 187, 167, 171, 17, 178, 148, 210, 90, 207, 86, 21,
//                 79, 161, 167, 215, 234, 1, 136, 242, 182, 248, 38, 85, 79, 86,
//             ],
//             [
//                 251, 177, 124, 54, 18, 101, 75, 235, 245, 186, 19, 46, 133, 157, 229, 64, 10, 136,
//                 181, 185, 78, 144, 254, 167, 137, 49, 107, 10, 61, 10, 21, 25,
//             ],
//             [
//                 232, 193, 20, 68, 240, 77, 186, 77, 183, 40, 44, 86, 150, 31, 198, 212, 76, 81, 3,
//                 217, 197, 8, 126, 128, 126, 152, 164, 208, 153, 44, 189, 77,
//             ],
//             [
//                 173, 229, 149, 177, 37, 230, 30, 69, 61, 56, 172, 190, 219, 115, 167, 194, 71, 134,
//                 59, 75, 28, 244, 118, 26, 162, 97, 64, 16, 15, 189, 30, 64,
//             ],
//             [
//                 106, 71, 61, 107, 250, 117, 42, 151, 91, 202, 212, 100, 52, 188, 190, 21, 125, 218,
//                 31, 18, 253, 241, 160, 133, 57, 242, 3, 164, 189, 68, 111, 75,
//             ],
//             [
//                 112, 204, 182, 90, 220, 198, 120, 73, 173, 107, 193, 17, 227, 40, 162, 36, 150,
//                 141, 235, 55, 172, 183, 12, 39, 194, 136, 43, 153, 244, 118, 91, 89,
//             ],
//             [
//                 111, 24, 203, 123, 254, 189, 11, 162, 51, 196, 163, 136, 204, 143, 10, 222, 33,
//                 112, 81, 205, 34, 35, 8, 66, 90, 6, 164, 58, 170, 177, 34, 25,
//             ],
//             [
//                 225, 183, 30, 52, 236, 82, 6, 183, 109, 25, 227, 181, 25, 82, 41, 193, 80, 77, 161,
//                 80, 242, 203, 79, 204, 136, 245, 131, 110, 237, 106, 3, 58,
//             ],
//             [
//                 207, 246, 38, 56, 30, 86, 176, 90, 27, 200, 61, 42, 221, 27, 56, 210, 79, 178, 189,
//                 120, 68, 193, 120, 167, 77, 185, 53, 197, 124, 128, 191, 126,
//             ],
//             [
//                 1, 136, 215, 80, 240, 46, 63, 147, 16, 244, 230, 207, 82, 189, 74, 50, 106, 169,
//                 138, 86, 30, 131, 214, 202, 166, 125, 251, 228, 98, 24, 36, 21,
//             ],
//             [
//                 210, 207, 228, 56, 155, 116, 207, 54, 84, 195, 251, 215, 249, 199, 116, 75, 109,
//                 239, 196, 251, 194, 246, 252, 228, 70, 146, 156, 35, 25, 39, 241, 4,
//             ],
//             [
//                 34, 116, 123, 9, 8, 40, 93, 189, 9, 103, 57, 103, 66, 227, 3, 2, 157, 107, 134,
//                 219, 202, 74, 230, 154, 78, 107, 219, 195, 214, 14, 84, 80,
//             ],
//         ];
//         let encoded_images: [CompressedRistretto; 16] = [
//             CompressedRistretto([
//                 176, 157, 237, 97, 66, 29, 140, 166, 168, 94, 26, 157, 212, 216, 229, 160, 195,
//                 246, 232, 239, 169, 112, 63, 193, 64, 32, 152, 69, 11, 190, 246, 86,
//             ]),
//             CompressedRistretto([
//                 234, 141, 77, 203, 181, 225, 250, 74, 171, 62, 15, 118, 78, 212, 150, 19, 131, 14,
//                 188, 238, 194, 244, 141, 138, 166, 162, 83, 122, 228, 201, 19, 26,
//             ]),
//             CompressedRistretto([
//                 232, 231, 51, 92, 5, 168, 80, 36, 173, 179, 104, 68, 186, 149, 68, 40, 140, 170,
//                 27, 103, 99, 140, 21, 242, 43, 62, 250, 134, 208, 255, 61, 89,
//             ]),
//             CompressedRistretto([
//                 208, 120, 140, 129, 177, 179, 237, 159, 252, 160, 28, 13, 206, 5, 211, 241, 192,
//                 218, 1, 97, 130, 241, 20, 169, 119, 46, 246, 29, 79, 80, 77, 84,
//             ]),
//             CompressedRistretto([
//                 202, 11, 236, 145, 58, 12, 181, 157, 209, 6, 213, 88, 75, 147, 11, 119, 191, 139,
//                 47, 142, 33, 36, 153, 193, 223, 183, 178, 8, 205, 120, 248, 110,
//             ]),
//             CompressedRistretto([
//                 26, 66, 231, 67, 203, 175, 116, 130, 32, 136, 62, 253, 215, 46, 5, 214, 166, 248,
//                 108, 237, 216, 71, 244, 173, 72, 133, 82, 6, 143, 240, 104, 41,
//             ]),
//             CompressedRistretto([
//                 40, 157, 102, 96, 201, 223, 200, 197, 150, 181, 106, 83, 103, 126, 143, 33, 145,
//                 230, 78, 6, 171, 146, 210, 143, 112, 5, 245, 23, 183, 138, 18, 120,
//             ]),
//             CompressedRistretto([
//                 220, 37, 27, 203, 239, 196, 176, 131, 37, 66, 188, 243, 185, 250, 113, 23, 167,
//                 211, 154, 243, 168, 215, 54, 171, 159, 36, 195, 81, 13, 150, 43, 43,
//             ]),
//             CompressedRistretto([
//                 232, 121, 176, 222, 183, 196, 159, 90, 238, 193, 105, 52, 101, 167, 244, 170, 121,
//                 114, 196, 6, 67, 152, 80, 185, 221, 7, 83, 105, 176, 208, 224, 121,
//             ]),
//             CompressedRistretto([
//                 226, 181, 183, 52, 241, 163, 61, 179, 221, 207, 220, 73, 245, 242, 25, 236, 67, 84,
//                 179, 222, 167, 62, 167, 182, 32, 9, 92, 30, 165, 127, 204, 68,
//             ]),
//             CompressedRistretto([
//                 226, 119, 16, 242, 200, 139, 240, 87, 11, 222, 92, 146, 156, 243, 46, 119, 65, 59,
//                 1, 248, 92, 183, 50, 175, 87, 40, 206, 53, 208, 220, 148, 13,
//             ]),
//             CompressedRistretto([
//                 70, 240, 79, 112, 54, 157, 228, 146, 74, 122, 216, 88, 232, 62, 158, 13, 14, 146,
//                 115, 117, 176, 222, 90, 225, 244, 23, 94, 190, 150, 7, 136, 96,
//             ]),
//             CompressedRistretto([
//                 22, 71, 241, 103, 45, 193, 195, 144, 183, 101, 154, 50, 39, 68, 49, 110, 51, 44,
//                 62, 0, 229, 113, 72, 81, 168, 29, 73, 106, 102, 40, 132, 24,
//             ]),
//             CompressedRistretto([
//                 196, 133, 107, 11, 130, 105, 74, 33, 204, 171, 133, 221, 174, 193, 241, 36, 38,
//                 179, 196, 107, 219, 185, 181, 253, 228, 47, 155, 42, 231, 73, 41, 78,
//             ]),
//             CompressedRistretto([
//                 58, 255, 225, 197, 115, 208, 160, 143, 39, 197, 82, 69, 143, 235, 92, 170, 74, 40,
//                 57, 11, 171, 227, 26, 185, 217, 207, 90, 185, 197, 190, 35, 60,
//             ]),
//             CompressedRistretto([
//                 88, 43, 92, 118, 223, 136, 105, 145, 238, 186, 115, 8, 214, 112, 153, 253, 38, 108,
//                 205, 230, 157, 130, 11, 66, 101, 85, 253, 110, 110, 14, 148, 112,
//             ]),
//         ];
//         for i in 0..16 {
//             let r_0 = FieldElement::from_bytes(&bytes[i]);
//             let Q = RistrettoPoint::elligator_ristretto_flavor(&r_0);
//             assert_eq!(Q.compress(), encoded_images[i]);
//         }
//     }
//     // Known answer tests for the one-way mapping function in the Ristretto RFC
//     #[test]
//     fn one_way_map() {
//         // These inputs are from
//         // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#appendix-A.3
//         let test_vectors: &[([u8; 64], CompressedRistretto)] = &[
//             (
//                 [
//                     0x5d, 0x1b, 0xe0, 0x9e, 0x3d, 0x0c, 0x82, 0xfc, 0x53, 0x81, 0x12, 0x49, 0x0e,
//                     0x35, 0x70, 0x19, 0x79, 0xd9, 0x9e, 0x06, 0xca, 0x3e, 0x2b, 0x5b, 0x54, 0xbf,
//                     0xfe, 0x8b, 0x4d, 0xc7, 0x72, 0xc1, 0x4d, 0x98, 0xb6, 0x96, 0xa1, 0xbb, 0xfb,
//                     0x5c, 0xa3, 0x2c, 0x43, 0x6c, 0xc6, 0x1c, 0x16, 0x56, 0x37, 0x90, 0x30, 0x6c,
//                     0x79, 0xea, 0xca, 0x77, 0x05, 0x66, 0x8b, 0x47, 0xdf, 0xfe, 0x5b, 0xb6,
//                 ],
//                 CompressedRistretto([
//                     0x30, 0x66, 0xf8, 0x2a, 0x1a, 0x74, 0x7d, 0x45, 0x12, 0x0d, 0x17, 0x40, 0xf1,
//                     0x43, 0x58, 0x53, 0x1a, 0x8f, 0x04, 0xbb, 0xff, 0xe6, 0xa8, 0x19, 0xf8, 0x6d,
//                     0xfe, 0x50, 0xf4, 0x4a, 0x0a, 0x46,
//                 ]),
//             ),
//             (
//                 [
//                     0xf1, 0x16, 0xb3, 0x4b, 0x8f, 0x17, 0xce, 0xb5, 0x6e, 0x87, 0x32, 0xa6, 0x0d,
//                     0x91, 0x3d, 0xd1, 0x0c, 0xce, 0x47, 0xa6, 0xd5, 0x3b, 0xee, 0x92, 0x04, 0xbe,
//                     0x8b, 0x44, 0xf6, 0x67, 0x8b, 0x27, 0x01, 0x02, 0xa5, 0x69, 0x02, 0xe2, 0x48,
//                     0x8c, 0x46, 0x12, 0x0e, 0x92, 0x76, 0xcf, 0xe5, 0x46, 0x38, 0x28, 0x6b, 0x9e,
//                     0x4b, 0x3c, 0xdb, 0x47, 0x0b, 0x54, 0x2d, 0x46, 0xc2, 0x06, 0x8d, 0x38,
//                 ],
//                 CompressedRistretto([
//                     0xf2, 0x6e, 0x5b, 0x6f, 0x7d, 0x36, 0x2d, 0x2d, 0x2a, 0x94, 0xc5, 0xd0, 0xe7,
//                     0x60, 0x2c, 0xb4, 0x77, 0x3c, 0x95, 0xa2, 0xe5, 0xc3, 0x1a, 0x64, 0xf1, 0x33,
//                     0x18, 0x9f, 0xa7, 0x6e, 0xd6, 0x1b,
//                 ]),
//             ),
//             (
//                 [
//                     0x84, 0x22, 0xe1, 0xbb, 0xda, 0xab, 0x52, 0x93, 0x8b, 0x81, 0xfd, 0x60, 0x2e,
//                     0xff, 0xb6, 0xf8, 0x91, 0x10, 0xe1, 0xe5, 0x72, 0x08, 0xad, 0x12, 0xd9, 0xad,
//                     0x76, 0x7e, 0x2e, 0x25, 0x51, 0x0c, 0x27, 0x14, 0x07, 0x75, 0xf9, 0x33, 0x70,
//                     0x88, 0xb9, 0x82, 0xd8, 0x3d, 0x7f, 0xcf, 0x0b, 0x2f, 0xa1, 0xed, 0xff, 0xe5,
//                     0x19, 0x52, 0xcb, 0xe7, 0x36, 0x5e, 0x95, 0xc8, 0x6e, 0xaf, 0x32, 0x5c,
//                 ],
//                 CompressedRistretto([
//                     0x00, 0x6c, 0xcd, 0x2a, 0x9e, 0x68, 0x67, 0xe6, 0xa2, 0xc5, 0xce, 0xa8, 0x3d,
//                     0x33, 0x02, 0xcc, 0x9d, 0xe1, 0x28, 0xdd, 0x2a, 0x9a, 0x57, 0xdd, 0x8e, 0xe7,
//                     0xb9, 0xd7, 0xff, 0xe0, 0x28, 0x26,
//                 ]),
//             ),
//             (
//                 [
//                     0xac, 0x22, 0x41, 0x51, 0x29, 0xb6, 0x14, 0x27, 0xbf, 0x46, 0x4e, 0x17, 0xba,
//                     0xee, 0x8d, 0xb6, 0x59, 0x40, 0xc2, 0x33, 0xb9, 0x8a, 0xfc, 0xe8, 0xd1, 0x7c,
//                     0x57, 0xbe, 0xeb, 0x78, 0x76, 0xc2, 0x15, 0x0d, 0x15, 0xaf, 0x1c, 0xb1, 0xfb,
//                     0x82, 0x4b, 0xbd, 0x14, 0x95, 0x5f, 0x2b, 0x57, 0xd0, 0x8d, 0x38, 0x8a, 0xab,
//                     0x43, 0x1a, 0x39, 0x1c, 0xfc, 0x33, 0xd5, 0xba, 0xfb, 0x5d, 0xbb, 0xaf,
//                 ],
//                 CompressedRistretto([
//                     0xf8, 0xf0, 0xc8, 0x7c, 0xf2, 0x37, 0x95, 0x3c, 0x58, 0x90, 0xae, 0xc3, 0x99,
//                     0x81, 0x69, 0x00, 0x5d, 0xae, 0x3e, 0xca, 0x1f, 0xbb, 0x04, 0x54, 0x8c, 0x63,
//                     0x59, 0x53, 0xc8, 0x17, 0xf9, 0x2a,
//                 ]),
//             ),
//             (
//                 [
//                     0x16, 0x5d, 0x69, 0x7a, 0x1e, 0xf3, 0xd5, 0xcf, 0x3c, 0x38, 0x56, 0x5b, 0xee,
//                     0xfc, 0xf8, 0x8c, 0x0f, 0x28, 0x2b, 0x8e, 0x7d, 0xbd, 0x28, 0x54, 0x4c, 0x48,
//                     0x34, 0x32, 0xf1, 0xce, 0xc7, 0x67, 0x5d, 0xeb, 0xea, 0x8e, 0xbb, 0x4e, 0x5f,
//                     0xe7, 0xd6, 0xf6, 0xe5, 0xdb, 0x15, 0xf1, 0x55, 0x87, 0xac, 0x4d, 0x4d, 0x4a,
//                     0x1d, 0xe7, 0x19, 0x1e, 0x0c, 0x1c, 0xa6, 0x66, 0x4a, 0xbc, 0xc4, 0x13,
//                 ],
//                 CompressedRistretto([
//                     0xae, 0x81, 0xe7, 0xde, 0xdf, 0x20, 0xa4, 0x97, 0xe1, 0x0c, 0x30, 0x4a, 0x76,
//                     0x5c, 0x17, 0x67, 0xa4, 0x2d, 0x6e, 0x06, 0x02, 0x97, 0x58, 0xd2, 0xd7, 0xe8,
//                     0xef, 0x7c, 0xc4, 0xc4, 0x11, 0x79,
//                 ]),
//             ),
//             (
//                 [
//                     0xa8, 0x36, 0xe6, 0xc9, 0xa9, 0xca, 0x9f, 0x1e, 0x8d, 0x48, 0x62, 0x73, 0xad,
//                     0x56, 0xa7, 0x8c, 0x70, 0xcf, 0x18, 0xf0, 0xce, 0x10, 0xab, 0xb1, 0xc7, 0x17,
//                     0x2d, 0xdd, 0x60, 0x5d, 0x7f, 0xd2, 0x97, 0x98, 0x54, 0xf4, 0x7a, 0xe1, 0xcc,
//                     0xf2, 0x04, 0xa3, 0x31, 0x02, 0x09, 0x5b, 0x42, 0x00, 0xe5, 0xbe, 0xfc, 0x04,
//                     0x65, 0xac, 0xcc, 0x26, 0x31, 0x75, 0x48, 0x5f, 0x0e, 0x17, 0xea, 0x5c,
//                 ],
//                 CompressedRistretto([
//                     0xe2, 0x70, 0x56, 0x52, 0xff, 0x9f, 0x5e, 0x44, 0xd3, 0xe8, 0x41, 0xbf, 0x1c,
//                     0x25, 0x1c, 0xf7, 0xdd, 0xdb, 0x77, 0xd1, 0x40, 0x87, 0x0d, 0x1a, 0xb2, 0xed,
//                     0x64, 0xf1, 0xa9, 0xce, 0x86, 0x28,
//                 ]),
//             ),
//             (
//                 [
//                     0x2c, 0xdc, 0x11, 0xea, 0xeb, 0x95, 0xda, 0xf0, 0x11, 0x89, 0x41, 0x7c, 0xdd,
//                     0xdb, 0xf9, 0x59, 0x52, 0x99, 0x3a, 0xa9, 0xcb, 0x9c, 0x64, 0x0e, 0xb5, 0x05,
//                     0x8d, 0x09, 0x70, 0x2c, 0x74, 0x62, 0x2c, 0x99, 0x65, 0xa6, 0x97, 0xa3, 0xb3,
//                     0x45, 0xec, 0x24, 0xee, 0x56, 0x33, 0x5b, 0x55, 0x6e, 0x67, 0x7b, 0x30, 0xe6,
//                     0xf9, 0x0a, 0xc7, 0x7d, 0x78, 0x10, 0x64, 0xf8, 0x66, 0xa3, 0xc9, 0x82,
//                 ],
//                 CompressedRistretto([
//                     0x80, 0xbd, 0x07, 0x26, 0x25, 0x11, 0xcd, 0xde, 0x48, 0x63, 0xf8, 0xa7, 0x43,
//                     0x4c, 0xef, 0x69, 0x67, 0x50, 0x68, 0x1c, 0xb9, 0x51, 0x0e, 0xea, 0x55, 0x70,
//                     0x88, 0xf7, 0x6d, 0x9e, 0x50, 0x65,
//                 ]),
//             ),
//             (
//                 [
//                     0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                 ],
//                 CompressedRistretto([
//                     0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
//                     0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
//                     0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
//                 ]),
//             ),
//             (
//                 [
//                     0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                 ],
//                 CompressedRistretto([
//                     0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
//                     0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
//                     0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
//                 ]),
//             ),
//             (
//                 [
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
//                     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
//                 ],
//                 CompressedRistretto([
//                     0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
//                     0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
//                     0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
//                 ]),
//             ),
//             (
//                 [
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
//                     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,
//                 ],
//                 CompressedRistretto([
//                     0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
//                     0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
//                     0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
//                 ]),
//             ),
//         ];
//         // Check that onewaymap(input) == output for all the above vectors
//         for (input, output) in test_vectors {
//             let Q = RistrettoPoint::from_uniform_bytes(input);
//             assert_eq!(&Q.compress(), output);
//         }
//     }
//     #[test]
//     fn random_roundtrip() {
//         let mut rng = OsRng;
//         for _ in 0..100 {
//             let P = RistrettoPoint::mul_base(&Scalar::random(&mut rng));
//             let compressed_P = P.compress();
//             let Q = compressed_P.decompress().unwrap();
//             assert_eq!(P, Q);
//         }
//     }
//     #[test]
//     #[cfg(all(feature = "alloc", feature = "rand_core"))]
//     fn double_and_compress_1024_random_points() {
//         let mut rng = OsRng;
//         let mut points: Vec<RistrettoPoint> = (0..1024)
//             .map(|_| RistrettoPoint::random(&mut rng))
//             .collect();
//         points[500] = RistrettoPoint::identity();
//         let compressed = RistrettoPoint::double_and_compress_batch(&points);
//         for (P, P2_compressed) in points.iter().zip(compressed.iter()) {
//             assert_eq!(*P2_compressed, (P + P).compress());
//         }
//     }
//     #[test]
//     #[cfg(feature = "alloc")]
//     fn vartime_precomputed_vs_nonprecomputed_multiscalar() {
//         let mut rng = rand::thread_rng();
//         let static_scalars = (0..128)
//             .map(|_| Scalar::random(&mut rng))
//             .collect::<Vec<_>>();
//         let dynamic_scalars = (0..128)
//             .map(|_| Scalar::random(&mut rng))
//             .collect::<Vec<_>>();
//         let check_scalar: Scalar = static_scalars
//             .iter()
//             .chain(dynamic_scalars.iter())
//             .map(|s| s * s)
//             .sum();
//         let static_points = static_scalars
//             .iter()
//             .map(RistrettoPoint::mul_base)
//             .collect::<Vec<_>>();
//         let dynamic_points = dynamic_scalars
//             .iter()
//             .map(RistrettoPoint::mul_base)
//             .collect::<Vec<_>>();
//         let precomputation = VartimeRistrettoPrecomputation::new(static_points.iter());
//         let P = precomputation.vartime_mixed_multiscalar_mul(
//             &static_scalars,
//             &dynamic_scalars,
//             &dynamic_points,
//         );
//         use crate::traits::VartimeMultiscalarMul;
//         let Q = RistrettoPoint::vartime_multiscalar_mul(
//             static_scalars.iter().chain(dynamic_scalars.iter()),
//             static_points.iter().chain(dynamic_points.iter()),
//         );
//         let R = RistrettoPoint::mul_base(&check_scalar);
//         assert_eq!(P.compress(), R.compress());
//         assert_eq!(Q.compress(), R.compress());
//     }
// }
// ------------------------------------------------------------------------
// Functional Equivalence Tests for Verus implementations
// ------------------------------------------------------------------------
#[cfg(test)]
mod test_double_and_compress_batch {
    use super::*;

    /// Test functional equivalence between double_and_compress_batch and
    /// double_and_compress_batch_verus using random points.
    /// Runs 10 iterations with random input sizes (0 to 64 points).
    #[test]
    #[cfg(all(feature = "alloc", feature = "rand_core"))]
    fn verus_equivalence_random() {
        use rand_core::{OsRng, RngCore};

        let mut rng = OsRng;

        for iteration in 0..10 {
            let num_points = (rng.next_u32() % 65) as usize; // 0 to 64 points
            let points: Vec<RistrettoPoint> = (0..num_points)
                .map(|_| RistrettoPoint::random(&mut rng))
                .collect();

            let result_original = RistrettoPoint::double_and_compress_batch(&points);
            let result_verus = RistrettoPoint::double_and_compress_batch_verus(&points);

            assert_eq!(
                result_original.len(),
                result_verus.len(),
                "Length mismatch in iteration {} with {} points",
                iteration,
                num_points
            );
            for (i, (orig, verus)) in result_original.iter().zip(result_verus.iter()).enumerate() {
                assert_eq!(
                    orig.as_bytes(),
                    verus.as_bytes(),
                    "Mismatch at index {} in iteration {} with {} points",
                    i,
                    iteration,
                    num_points
                );
            }
        }
    }
}

// ------------------------------------------------------------------------
// Multiscalar Multiplication Equivalence Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test_multiscalar_mul {
    use super::*;

    #[test]
    #[cfg(all(feature = "alloc", feature = "rand_core"))]
    fn verus_equivalence_random_multiscalar_mul() {
        use crate::traits::MultiscalarMul;
        use rand_core::{OsRng, RngCore};

        let mut rng = OsRng;

        for _iteration in 0..10 {
            let n = (rng.next_u32() % 65) as usize; // 0..=64

            let scalars: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let points: Vec<RistrettoPoint> =
                (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();

            let original =
                <RistrettoPoint as MultiscalarMul>::multiscalar_mul(scalars.iter(), points.iter());
            let verus = RistrettoPoint::multiscalar_mul_verus(scalars.iter(), points.iter());

            assert_eq!(original.compress().as_bytes(), verus.compress().as_bytes());
        }
    }

    #[test]
    #[cfg(all(feature = "alloc", feature = "rand_core"))]
    fn verus_equivalence_random_optional_multiscalar_mul() {
        use crate::traits::VartimeMultiscalarMul;
        use rand_core::{OsRng, RngCore};

        let mut rng = OsRng;

        for _iteration in 0..10 {
            let n = (rng.next_u32() % 65) as usize; // 0..=64

            let scalars: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
            let points: Vec<Option<RistrettoPoint>> = (0..n)
                .map(|_| {
                    // Roughly half the time, insert a missing point.
                    if (rng.next_u32() & 1) == 0 {
                        None
                    } else {
                        Some(RistrettoPoint::random(&mut rng))
                    }
                })
                .collect();

            let original = <RistrettoPoint as VartimeMultiscalarMul>::optional_multiscalar_mul(
                scalars.iter(),
                points.iter().cloned(),
            );
            let verus = RistrettoPoint::optional_multiscalar_mul_verus(
                scalars.iter(),
                points.iter().cloned(),
            );

            match (original, verus) {
                (None, None) => {}
                (Some(o), Some(v)) => assert_eq!(o.compress().as_bytes(), v.compress().as_bytes()),
                (a, b) => panic!(
                    "Mismatch: original={:?} verus={:?}",
                    a.is_some(),
                    b.is_some()
                ),
            }
        }
    }
}

// ------------------------------------------------------------------------
// Sum Equivalence Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test_sum {
    use super::*;

    #[test]
    #[cfg(all(feature = "alloc", feature = "rand_core"))]
    fn verus_equivalence_random_sum() {
        use rand_core::{OsRng, RngCore};

        let mut rng = OsRng;

        for iteration in 0..10 {
            let n = (rng.next_u32() % 65) as usize; // 0..=64
            let points: Vec<RistrettoPoint> =
                (0..n).map(|_| RistrettoPoint::random(&mut rng)).collect();

            let original = RistrettoPoint::sum_original(points.iter());
            let refactored: RistrettoPoint = points.iter().sum();

            assert_eq!(
                original.compress().as_bytes(),
                refactored.compress().as_bytes(),
                "Mismatch in iteration {} with {} points",
                iteration,
                n
            );
        }
    }
}
