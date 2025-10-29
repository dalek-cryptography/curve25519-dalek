// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
//! Field arithmetic modulo \\(p = 2\^{255} - 19\\), using \\(64\\)-bit
//! limbs with \\(128\\)-bit products.
use core::fmt::Debug;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};

use subtle::Choice;
use subtle::ConditionallySelectable;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::bit_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::div_mod_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::mask_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::mul_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::pow_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::common_verus::shift_lemmas::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::as_nat_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::field_core::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::from_bytes_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::load8_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::negate_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::pow2_51_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::pow2k_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field_lemmas::reduce_lemmas::*;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::*;
#[allow(unused_imports)]
use crate::field_specs::*;

verus! {

/* MANUALLY moved outside and made explicit */
// LOW_51_BIT_MASK: u64 = (1u64 << 51) -1; originally
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64;

/// A `FieldElement51` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 64-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{51}\\) as five `u64`s; the coefficients are allowed to
/// grow up to \\(2\^{54}\\) between reductions modulo \\(p\\).
///
/// # Note
///
/// The `curve25519_dalek::field` module provides a type alias
/// `curve25519_dalek::field::FieldElement` to either `FieldElement51`
/// or `FieldElement2625`.
///
/// The backend-specific type `FieldElement51` should not be used
/// outside of the `curve25519_dalek::field` module.
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    // ADAPTED CODE LINE: we give a name to the field: "limbs"
    pub limbs: [u64; 5],
}

impl Debug for FieldElement51 {
    /* VERIFICATION NOTE: we don't cover debugging */
    #[verifier::external_body]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FieldElement51({:?})", &self.limbs[..])
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for FieldElement51 {
    /* <VERIFICATION NOTE>
    External body annotation
    </VERIFICATION NOTE> */
    #[verifier::external_body]
    fn zeroize(&mut self)
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] == 0,
    {
        self.limbs.zeroize();
    }
}

/* MANUALLY moved outside, named return value */

const fn load8_at(input: &[u8], i: usize) -> (r: u64)
    requires
        i + 7 < input.len(),
    ensures
        r as nat == load8_at_spec(input, i),
{
    proof {
        rec_version_is_exec(input, i);
        load8_at_versions_equivalent(input, i, 7);
        plus_version_is_spec(input, i);
    }
    (input[i] as u64) | ((input[i + 1] as u64) << 8) | ((input[i + 2] as u64) << 16) | ((input[i
        + 3] as u64) << 24) | ((input[i + 4] as u64) << 32) | ((input[i + 5] as u64) << 40) | ((
    input[i + 6] as u64) << 48) | ((input[i + 7] as u64) << 56)
}

/* MANUALLY moved outside */

#[inline(always)]
fn m(x: u64, y: u64) -> (r: u128)
    ensures
        (r as nat) == (x as nat) * (y as nat),
        r <= u128::MAX,
{
    proof {
        // if a <= a' and b <= b' then ab <= a'b'
        mul_le(x as nat, u64::MAX as nat, y as nat, u64::MAX as nat);
    }
    (x as u128) * (y as u128)
}

impl<'a> AddAssign<&'a FieldElement51> for FieldElement51 {
    fn add_assign(&mut self, _rhs: &'a FieldElement51)
        requires
            forall|i: int| 0 <= i < 5 ==> #[trigger] (old(self).limbs[i] + _rhs.limbs[i]) <= u64::MAX,
        ensures
            forall|i: int| 0 <= i < 5 ==> #[trigger] self.limbs[i] == old(self).limbs[i] + _rhs.limbs[i],
            forall|i: int| 0 <= i < 5 ==> #[trigger] self.limbs[i] <= u64::MAX,
    {
        let ghost original_limbs = self.limbs;
        for i in 0..5
            invariant
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> self.limbs[j] == original_limbs[j] + _rhs.limbs[j],
                forall|j: int| #![auto] i <= j < 5 ==> self.limbs[j] == original_limbs[j],
                forall|j: int|
                    0 <= j < 5 ==> #[trigger] original_limbs[j] + _rhs.limbs[j] <= u64::MAX,
        {
            // Trigger the forall
            assert(original_limbs[i as int] + _rhs.limbs[i as int] <= u64::MAX);
            self.limbs[i] += _rhs.limbs[i];
        }
    }
}

#[cfg(verus_keep_ghost)]
impl vstd::std_specs::ops::AddSpecImpl<&FieldElement51> for &FieldElement51 {
    // Does the implementation of this trait obey basic addition principles
    open spec fn obeys_add_spec() -> bool {
        true
    }

    // Pre-condition of add
    open spec fn add_req(self, rhs: &FieldElement51) -> bool {
        forall|i: int| 0 <= i < 5 ==> #[trigger] (self.limbs[i] + rhs.limbs[i]) <= u64::MAX
    }

    // Postcondition of add
    open spec fn add_spec(self, rhs: &FieldElement51) -> FieldElement51 {
        FieldElement51 {
            limbs: [
                (self.limbs[0] + rhs.limbs[0]) as u64,
                (self.limbs[1] + rhs.limbs[1]) as u64,
                (self.limbs[2] + rhs.limbs[2]) as u64,
                (self.limbs[3] + rhs.limbs[3]) as u64,
                (self.limbs[4] + rhs.limbs[4]) as u64,
            ],
        }
    }
}

impl<'a> Add<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    fn add(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    ensures
        forall|i: int| 0 <= i < 5 ==> #[trigger] output.limbs[i] == self.limbs[i] + _rhs.limbs[i],
        forall|i: int| 0 <= i < 5 ==> #[trigger] output.limbs[i] <= u64::MAX,
    {
        let mut output = *self;
        /* ORIGINAL CODE
        output += _rhs;
        */
        /* MODIFIED CODE */
        let ghost original_limbs = self.limbs;
        for i in 0..5
            invariant
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> output.limbs[j] == original_limbs[j] + _rhs.limbs[j],
                forall|j: int| #![auto] i <= j < 5 ==> output.limbs[j] == original_limbs[j],
                forall|j: int|
                    0 <= j < 5 ==> #[trigger] original_limbs[j] + _rhs.limbs[j] <= u64::MAX,
        {
            // Trigger the forall
            assert(original_limbs[i as int] + _rhs.limbs[i as int] <= u64::MAX);
            output.limbs[i] += _rhs.limbs[i];
        }
        /* </MODIFIED CODE> */
        // Trigger the forall invariant
        assert(output.limbs == [
            (original_limbs[0] + _rhs.limbs[0]) as u64,
            (original_limbs[1] + _rhs.limbs[1]) as u64,
            (original_limbs[2] + _rhs.limbs[2]) as u64,
            (original_limbs[3] + _rhs.limbs[3]) as u64,
            (original_limbs[4] + _rhs.limbs[4]) as u64,
        ]);
        output
    }
}

impl<'a> SubAssign<&'a FieldElement51> for FieldElement51 {
    fn sub_assign(&mut self, _rhs: &'a FieldElement51)
        requires
            forall|i: int| 0 <= i < 5 ==> old(self).limbs[i] < (1u64 << 54),
            forall|i: int| 0 <= i < 5 ==> _rhs.limbs[i] < (1u64 << 54),
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
            as_nat(self.limbs) % p() == (as_nat(old(self).limbs) as int - as_nat(_rhs.limbs) as int) % p(),
    {
        /* ORIGINAL CODE
        let result = (self as &FieldElement51) - _rhs;
        self.0 = result.0;
        */
        /* MODIFIED CODE */
        proof {
            assume(false);
        }
        let result = &*self - _rhs;
        proof {
            assume(false);  // BECAUSE OF VERUS TRAIT ISSUES
        }
        self.limbs = result.limbs;
    }
}

impl<'a> Sub<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    fn sub(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
        requires
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 54),
            forall|i: int| 0 <= i < 5 ==> _rhs.limbs[i] < (1u64 << 54),
        ensures
            forall|i: int| 0 <= i < 5 ==> output.limbs[i] < (1u64 << 52),
            as_nat(output.limbs) % p() == (as_nat(self.limbs) as int - as_nat(_rhs.limbs) as int) % p(),
    {
        // To avoid underflow, first add a multiple of p.
        // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
        //
        // If we could statically track the bitlengths of the limbs
        // of every FieldElement51, we could choose a multiple of p
        // just bigger than _rhs and avoid having to do a reduction.
        //
        // Since we don't yet have type-level integers to do this, we
        // have to add an explicit reduction call here.
        //
        // Note on "magic numbers":
        // 36028797018963664u64 = 2^55 - 304 = 16 * (2^51 - 19)
        // 36028797018963952u64 = 2^55 - 16 =  16 * (2^51 - 1)
        proof {
            assume(false);
        }
        FieldElement51::reduce(
            [
                (self.limbs[0] + 36028797018963664u64) - _rhs.limbs[0],
                (self.limbs[1] + 36028797018963952u64) - _rhs.limbs[1],
                (self.limbs[2] + 36028797018963952u64) - _rhs.limbs[2],
                (self.limbs[3] + 36028797018963952u64) - _rhs.limbs[3],
                (self.limbs[4] + 36028797018963952u64) - _rhs.limbs[4],
            ],
        )
    }
}

impl<'a> MulAssign<&'a FieldElement51> for FieldElement51 {
    fn mul_assign(&mut self, _rhs: &'a FieldElement51) {
        proof {
            assume(false);
        }  // PROOF BYPASS due to vstd trait spec preconditions
        let result = &*self * _rhs;
        self.limbs = result.limbs;
    }
}

impl<'a> Mul<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    #[rustfmt::skip]  // keep alignment of c* calculations
    fn mul(self, _rhs: &'a FieldElement51) -> FieldElement51 {
        /// Helper function to multiply two 64-bit integers with 128
        /// bits of output.
        // VERIFICATION NOTE: manually moved outside
        // #[inline(always)]
        // fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }
        assume(false);
        // Alias self, _rhs for more readable formulas
        let a: &[u64; 5] = &self.limbs;
        let b: &[u64; 5] = &_rhs.limbs;

        // Precondition: assume input limbs a[i], b[i] are bounded as
        //
        // a[i], b[i] < 2^(51 + b)
        //
        // where b is a real parameter measuring the "bit excess" of the limbs.

        // 64-bit precomputations to avoid 128-bit multiplications.
        //
        // This fits into a u64 whenever 51 + b + lg(19) < 64.
        //
        // Since 51 + b + lg(19) < 51 + 4.25 + b
        //                       = 55.25 + b,
        // this fits if b < 8.75.
        let b1_19 = b[1] * 19;
        let b2_19 = b[2] * 19;
        let b3_19 = b[3] * 19;
        let b4_19 = b[4] * 19;

        // Multiply to get 128-bit coefficients of output
        let c0: u128 = m(a[0], b[0]) + m(a[4], b1_19) + m(a[3], b2_19) + m(a[2], b3_19) + m(
            a[1],
            b4_19,
        );
        let mut c1: u128 = m(a[1], b[0]) + m(a[0], b[1]) + m(a[4], b2_19) + m(a[3], b3_19) + m(
            a[2],
            b4_19,
        );
        let mut c2: u128 = m(a[2], b[0]) + m(a[1], b[1]) + m(a[0], b[2]) + m(a[4], b3_19) + m(
            a[3],
            b4_19,
        );
        let mut c3: u128 = m(a[3], b[0]) + m(a[2], b[1]) + m(a[1], b[2]) + m(a[0], b[3]) + m(
            a[4],
            b4_19,
        );
        let mut c4: u128 = m(a[4], b[0]) + m(a[3], b[1]) + m(a[2], b[2]) + m(a[1], b[3]) + m(
            a[0],
            b[4],
        );

        // How big are the c[i]? We have
        //
        //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
        //         < 2^(102 + lg(1 + 4*19) + 2*b)
        //         < 2^(108.27 + 2*b)
        //
        // The carry (c[i] >> 51) fits into a u64 when
        //    108.27 + 2*b - 51 < 64
        //    2*b < 6.73
        //    b < 3.365.
        //
        // So we require b < 3 to ensure this fits.
        #[cfg(not(verus_keep_ghost))]
        {
            debug_assert!(a[0] < (1 << 54));
            debug_assert!(b[0] < (1 << 54));
            debug_assert!(a[1] < (1 << 54));
            debug_assert!(b[1] < (1 << 54));
            debug_assert!(a[2] < (1 << 54));
            debug_assert!(b[2] < (1 << 54));
            debug_assert!(a[3] < (1 << 54));
            debug_assert!(b[3] < (1 << 54));
            debug_assert!(a[4] < (1 << 54));
            debug_assert!(b[4] < (1 << 54));
        }

        // Casting to u64 and back tells the compiler that the carry is
        // bounded by 2^64, so that the addition is a u128 + u64 rather
        // than u128 + u128.

        // const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1; // already defined at module level
        let mut out = [0u64;5];

        c1 += ((c0 >> 51) as u64) as u128;
        out[0] = (c0 as u64) & LOW_51_BIT_MASK;

        c2 += ((c1 >> 51) as u64) as u128;
        out[1] = (c1 as u64) & LOW_51_BIT_MASK;

        c3 += ((c2 >> 51) as u64) as u128;
        out[2] = (c2 as u64) & LOW_51_BIT_MASK;

        c4 += ((c3 >> 51) as u64) as u128;
        out[3] = (c3 as u64) & LOW_51_BIT_MASK;

        let carry: u64 = (c4 >> 51) as u64;
        out[4] = (c4 as u64) & LOW_51_BIT_MASK;

        // To see that this does not overflow, we need out[0] + carry * 19 < 2^64.
        //
        // c4 < a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + (carry from c3)
        //    < 5*(2^(51 + b) * 2^(51 + b)) + (carry from c3)
        //    < 2^(102 + 2*b + lg(5)) + 2^64.
        //
        // When b < 3 we get
        //
        // c4 < 2^110.33  so that carry < 2^59.33
        //
        // so that
        //
        // out[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
        //
        // and there is no overflow.
        out[0] += carry * 19;

        // Now out[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
        out[1] += out[0] >> 51;
        out[0] &= LOW_51_BIT_MASK;

        // Now out[i] < 2^(51 + epsilon) for all i.
        FieldElement51 { limbs: out }
    }
}

impl Neg for &FieldElement51 {
    type Output = FieldElement51;

    fn neg(self) -> FieldElement51 {
        let mut output = *self;
        assume(false);
        output.negate();
        output
    }
}

} // verus!
verus! {

impl ConditionallySelectable for FieldElement51 {
    fn conditional_select(a: &FieldElement51, b: &FieldElement51, choice: Choice) -> (result:
        FieldElement51)
        ensures
    // If choice is false, return a

            !choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] result.limbs[i] == a.limbs[i]),
            // If choice is true, return b
            choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] result.limbs[i] == b.limbs[i]),
    {
        FieldElement51 {
            limbs: [
                conditional_select_u64(&a.limbs[0], &b.limbs[0], choice),
                conditional_select_u64(&a.limbs[1], &b.limbs[1], choice),
                conditional_select_u64(&a.limbs[2], &b.limbs[2], choice),
                conditional_select_u64(&a.limbs[3], &b.limbs[3], choice),
                conditional_select_u64(&a.limbs[4], &b.limbs[4], choice),
            ],
        }
    }

    fn conditional_swap(a: &mut FieldElement51, b: &mut FieldElement51, choice: Choice)
        ensures
    // If choice is false, a and b remain unchanged

            !choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] a.limbs[i] == old(a).limbs[i]) && (forall|i: int|
                0 <= i < 5 ==> #[trigger] b.limbs[i] == old(b).limbs[i]),
            // If choice is true, a and b are swapped
            choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] a.limbs[i] == old(b).limbs[i]) && (forall|i: int|
                0 <= i < 5 ==> #[trigger] b.limbs[i] == old(a).limbs[i]),
    {
        // Originally this was
        // u64::conditional_swap(&mut a.limbs[0], &mut b.limbs[0], choice);
        // But Verus doesn't support index for &mut
        // Hence first do the indexing, then pass mut ref, then substitute back in
        let mut a0 = a.limbs[0];
        let mut b0 = b.limbs[0];
        conditional_swap_u64(&mut a0, &mut b0, choice);
        a.limbs[0] = a0;
        b.limbs[0] = b0;

        let mut a1 = a.limbs[1];
        let mut b1 = b.limbs[1];
        conditional_swap_u64(&mut a1, &mut b1, choice);
        a.limbs[1] = a1;
        b.limbs[1] = b1;

        let mut a2 = a.limbs[2];
        let mut b2 = b.limbs[2];
        conditional_swap_u64(&mut a2, &mut b2, choice);
        a.limbs[2] = a2;
        b.limbs[2] = b2;

        let mut a3 = a.limbs[3];
        let mut b3 = b.limbs[3];
        conditional_swap_u64(&mut a3, &mut b3, choice);
        a.limbs[3] = a3;
        b.limbs[3] = b3;

        let mut a4 = a.limbs[4];
        let mut b4 = b.limbs[4];
        conditional_swap_u64(&mut a4, &mut b4, choice);
        a.limbs[4] = a4;
        b.limbs[4] = b4;
    }

    fn conditional_assign(&mut self, other: &FieldElement51, choice: Choice)
        ensures
    // If choice is false, self remains unchanged

            !choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] self.limbs[i] == old(self).limbs[i]),
            // If choice is true, self is assigned from other
            choice_is_true(choice) ==> (forall|i: int|
                0 <= i < 5 ==> #[trigger] self.limbs[i] == other.limbs[i]),
    {
        let mut self0 = self.limbs[0];
        conditional_assign_u64(&mut self0, &other.limbs[0], choice);
        self.limbs[0] = self0;

        let mut self1 = self.limbs[1];
        conditional_assign_u64(&mut self1, &other.limbs[1], choice);
        self.limbs[1] = self1;

        let mut self2 = self.limbs[2];
        conditional_assign_u64(&mut self2, &other.limbs[2], choice);
        self.limbs[2] = self2;

        let mut self3 = self.limbs[3];
        conditional_assign_u64(&mut self3, &other.limbs[3], choice);
        self.limbs[3] = self3;

        let mut self4 = self.limbs[4];
        conditional_assign_u64(&mut self4, &other.limbs[4], choice);
        self.limbs[4] = self4;
    }
}

} // verus!
verus! {

impl FieldElement51 {
    pub(crate) const fn from_limbs(limbs: [u64; 5]) -> FieldElement51 {
        FieldElement51 { limbs }
    }

    // Modified to use direct struct
    pub const ZERO: FieldElement51 = FieldElement51 { limbs: [0, 0, 0, 0, 0] };

    pub const ONE: FieldElement51 = FieldElement51 { limbs: [1, 0, 0, 0, 0] };

    pub const MINUS_ONE: FieldElement51 = FieldElement51 {
        limbs: [
            2251799813685228,
            2251799813685247,
            2251799813685247,
            2251799813685247,
            2251799813685247,
        ],
    };

    /// Invert the sign of this field element
    pub fn negate(&mut self)
        requires
            forall|i: int| 0 <= i < 5 ==> old(self).limbs[i] < (1u64 << 51),
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
            // Assume we start with l = (l0, l1, l2, l3, l4).
            // Using c0 = 2^51 - 19 and c = 2^51 - 1, we can see that
            // ( 36028797018963664u64 - l0,
            //   36028797018963952u64 - l1,
            //   36028797018963952u64 - l2,
            //   36028797018963952u64 - l3,
            //   36028797018963952u64 - l4 )
            // is just 16 * (c0, c, c, c, c) - l (in vector notation)
            // Further, as_nat((c0, c, c, c, c)) = p, so
            // as_nat(16 * (c0, c, c, c, c) - l) is 16p - as_nat(l)
            // We know as_nat(reduce(v)) = as_nat(v) - p * (v4 >> 51) for any v.
            // This gives us the identity
            // as_nat(negate(l)) = as_nat(reduce(16 * (c0, c, c, c, c) - l))
            //                   = 16p - as_nat(l) - p * ((16c - l4) >> 51)
            // Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
            as_nat(self.limbs) == 16 * p() - as_nat(old(self).limbs) - p() * ((36028797018963952u64
                - old(self).limbs[4]) as u64 >> 51),
            (as_nat(self.limbs) + as_nat(old(self).limbs)) % p() == 0,
    {
        proof {
            lemma_neg_no_underflow(self.limbs);
            negate_proof(self.limbs);
        }
        // See commentary in the Sub impl: (copied below)
        // To avoid underflow, first add a multiple of p.
        // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
        //
        // If we could statically track the bitlengths of the limbs
        // of every FieldElement51, we could choose a multiple of p
        // just bigger than _rhs and avoid having to do a reduction.
        //
        // Since we don't yet have type-level integers to do this, we
        // have to add an explicit reduction call here.
        // Note on "magic numbers":
        // 36028797018963664u64 = 2^55 - 304 = 16 * (2^51 - 19)
        // 36028797018963952u64 = 2^55 - 16 =  16 * (2^51 - 1)
        let neg = FieldElement51::reduce(
            [
                36028797018963664u64 - self.limbs[0],
                36028797018963952u64 - self.limbs[1],
                36028797018963952u64 - self.limbs[2],
                36028797018963952u64 - self.limbs[3],
                36028797018963952u64 - self.limbs[4],
            ],
        );
        self.limbs = neg.limbs;
    }

    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)
        ensures
            r.limbs == spec_reduce(limbs),
            forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
            (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
            as_nat(r.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51),
            as_nat(r.limbs) % p() == as_nat(limbs) % p(),
    {
        proof {
            lemma_boundaries(limbs);
            lemma_reduce(limbs);
        }

        // Since the input limbs are bounded by 2^64, the biggest
        // carry-out is bounded by 2^13.
        //
        // The biggest carry-in is c4 * 19, resulting in
        //
        // 2^51 + 19*2^13 < 2^51.0000000001
        //
        // Because we don't need to canonicalize, only to reduce the
        // limb sizes, it's OK to do a "weak reduction", where we
        // compute the carry-outs in parallel.

        let c0 = limbs[0] >> 51;
        let c1 = limbs[1] >> 51;
        let c2 = limbs[2] >> 51;
        let c3 = limbs[3] >> 51;
        let c4 = limbs[4] >> 51;

        limbs[0] &= LOW_51_BIT_MASK;
        limbs[1] &= LOW_51_BIT_MASK;
        limbs[2] &= LOW_51_BIT_MASK;
        limbs[3] &= LOW_51_BIT_MASK;
        limbs[4] &= LOW_51_BIT_MASK;

        limbs[0] += c4 * 19;
        limbs[1] += c0;
        limbs[2] += c1;
        limbs[3] += c2;
        limbs[4] += c3;

        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51 { limbs }
    }

    /// Load a `FieldElement51` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    ///
    ///
    #[rustfmt::skip]  // keep alignment of bit shifts
    pub const fn from_bytes(bytes: &[u8; 32]) -> (r: FieldElement51)
        ensures
    // last bit is ignored

            as_nat(r.limbs) == as_nat_32_u8(bytes) % pow2(255),
    {
        /* MANUALLY moved outside */
        /*
        const fn load8_at(input: &[u8], i: usize) -> u64 {
                (input[i] as u64)
            | ((input[i + 1] as u64) << 8)
            | ((input[i + 2] as u64) << 16)
            | ((input[i + 3] as u64) << 24)
            | ((input[i + 4] as u64) << 32)
            | ((input[i + 5] as u64) << 40)
            | ((input[i + 6] as u64) << 48)
            | ((input[i + 7] as u64) << 56)
        }
        */
        proof {
            assert(mask51 == (1u64 << 51) - 1) by (compute);

            let l0 = load8_at_spec(bytes, 0);
            let l1 = load8_at_spec(bytes, 6);
            let l2 = load8_at_spec(bytes, 12);
            let l3 = load8_at_spec(bytes, 19);
            let l4 = load8_at_spec(bytes, 24);

            assert(l0 <= u64::MAX && l1 <= u64::MAX && l2 <= u64::MAX && l3 <= u64::MAX && l4
                <= u64::MAX) by {
                load8_at_spec_fits_u64(bytes, 0);
                load8_at_spec_fits_u64(bytes, 6);
                load8_at_spec_fits_u64(bytes, 12);
                load8_at_spec_fits_u64(bytes, 19);
                load8_at_spec_fits_u64(bytes, 24);
            }

            let rr = [
                l0 as u64 & mask51,
                (l1 as u64 >> 3) & mask51,
                (l2 as u64 >> 6) & mask51,
                (l3 as u64 >> 1) & mask51,
                (l4 as u64 >> 12) & mask51,
            ];

            assert(as_nat(rr) == as_nat_32_u8(bytes) % pow2(255)) by {
                from_bytes_as_nat(bytes);
                as_nat_32_mod_255(bytes);
            }
        }
        let low_51_bit_mask = (1u64 << 51) - 1;
        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51 {
            limbs:
            // load bits [  0, 64), no shift
            [
                load8_at(bytes, 0)
                    & low_51_bit_mask
                // load bits [ 48,112), shift to [ 51,112)
                ,
                (load8_at(bytes, 6) >> 3)
                    & low_51_bit_mask
                // load bits [ 96,160), shift to [102,160)
                ,
                (load8_at(bytes, 12) >> 6)
                    & low_51_bit_mask
                // load bits [152,216), shift to [153,216)
                ,
                (load8_at(bytes, 19) >> 1)
                    & low_51_bit_mask
                // load bits [192,256), shift to [204,112)
                ,
                (load8_at(bytes, 24) >> 12) & low_51_bit_mask,
            ],
        }
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    #[rustfmt::skip]  // keep alignment of s[*] calculations
    pub fn as_bytes(self) -> (r: [u8; 32])
        ensures  // TODO: Update after https:
    //github.com/Beneficial-AI-Foundation/dalek-lite/pull/63

            true,
            // VERIFICATION NOTE: tentative spec function addition
            r@ == field_element_as_bytes(&self),
    {
        proof {
            // PROOF SKIP
            assume(false);
        }

        // Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.
        //
        // Write h = pq + r with 0 <= r < p.
        //
        // We want to compute r = h mod p.
        //
        // If h < 2*p = 2^256 - 38,
        // then q = 0 or 1,
        //
        // with q = 0 when h < p
        //  and q = 1 when h >= p.
        //
        // Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
        // Therefore q can be computed as the carry bit of h + 19.
        // First, reduce the limbs to ensure h < 2*p.
        let mut limbs = FieldElement51::reduce(self.limbs).limbs;

        let mut q = (limbs[0] + 19) >> 51;
        q = (limbs[1] + q) >> 51;
        q = (limbs[2] + q) >> 51;
        q = (limbs[3] + q) >> 51;
        q = (limbs[4] + q) >> 51;

        // Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

        limbs[0] += 19 * q;

        // Now carry the result to compute r + 19q ...
        let low_51_bit_mask = (1u64 << 51) - 1;
        limbs[1] += limbs[0] >> 51;
        limbs[0] &= low_51_bit_mask;
        limbs[2] += limbs[1] >> 51;
        limbs[1] &= low_51_bit_mask;
        limbs[3] += limbs[2] >> 51;
        limbs[2] &= low_51_bit_mask;
        limbs[4] += limbs[3] >> 51;
        limbs[3] &= low_51_bit_mask;
        // ... but instead of carrying (limbs[4] >> 51) = 2^255q
        // into another limb, discard it, subtracting the value
        limbs[4] &= low_51_bit_mask;

        // Now arrange the bits of the limbs.
        let mut s = [0u8;32];
        s[0] = limbs[0] as u8;
        s[1] = (limbs[0] >> 8) as u8;
        s[2] = (limbs[0] >> 16) as u8;
        s[3] = (limbs[0] >> 24) as u8;
        s[4] = (limbs[0] >> 32) as u8;
        s[5] = (limbs[0] >> 40) as u8;
        s[6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[7] = (limbs[1] >> 5) as u8;
        s[8] = (limbs[1] >> 13) as u8;
        s[9] = (limbs[1] >> 21) as u8;
        s[10] = (limbs[1] >> 29) as u8;
        s[11] = (limbs[1] >> 37) as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] = (limbs[2] >> 2) as u8;
        s[14] = (limbs[2] >> 10) as u8;
        s[15] = (limbs[2] >> 18) as u8;
        s[16] = (limbs[2] >> 26) as u8;
        s[17] = (limbs[2] >> 34) as u8;
        s[18] = (limbs[2] >> 42) as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] = (limbs[3] >> 7) as u8;
        s[21] = (limbs[3] >> 15) as u8;
        s[22] = (limbs[3] >> 23) as u8;
        s[23] = (limbs[3] >> 31) as u8;
        s[24] = (limbs[3] >> 39) as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] = (limbs[4] >> 4) as u8;
        s[27] = (limbs[4] >> 12) as u8;
        s[28] = (limbs[4] >> 20) as u8;
        s[29] = (limbs[4] >> 28) as u8;
        s[30] = (limbs[4] >> 36) as u8;
        s[31] = (limbs[4] >> 44) as u8;

        // High bit should be zero.
        #[cfg(not(verus_keep_ghost))]
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

    /// Given `k > 0`, return `self^(2^k)`.
    #[rustfmt::skip]  // keep alignment of c* calculations
    pub fn pow2k(&self, mut k: u32) -> (r: FieldElement51)
        requires
            k > 0,  // debug_assert!( k > 0 );
            forall|i: int|
                0 <= i < 5 ==> self.limbs[i] < 1u64 << 54  // 51 + b for b = 3
            ,
        ensures
            forall|i: int| 0 <= i < 5 ==> r.limbs[i] < 1u64 << 54,
            as_nat(r.limbs) % p() == pow(as_nat(self.limbs) as int, pow2(k as nat)) as nat % p(),
    {
        #[cfg(not(verus_keep_ghost))]
        debug_assert!( k > 0 );

        /// Multiply two 64-bit integers with 128 bits of output.
        /* VERIFICATION NOTE: manually moved outside */
        /* #[inline(always)]
        fn m(x: u64, y: u64) -> u128 {
            (x as u128) * (y as u128)
        }
        */
        let mut a: [u64; 5] = self.limbs;

        let ghost k0 = k;
        // pre-loop invariant, i = 0
        proof {
            assert(as_nat(a) == pow(as_nat(self.limbs) as int, pow2(0))) by {
                lemma2_to64();  // pow2(0) = 1
                lemma_pow1(as_nat(self.limbs) as int);
            }
        }
        loop
            invariant_except_break
                forall|j: int| 0 <= j < 5 ==> a[j] < 1u64 << 54,
                as_nat(a) % p() == pow(as_nat(self.limbs) as int, pow2((k0 - k) as nat)) as nat
                    % p(),
                0 < k <= k0,
            ensures
                k == 0,
                forall|j: int| 0 <= j < 5 ==> a[j] < 1u64 << 54,
                as_nat(a) % p() == pow(as_nat(self.limbs) as int, pow2(k0 as nat)) as nat % p(),
            decreases k,
        {
            proof {
                let ghost i = (k0 - k) as nat;

                pow255_gt_19();  // p > 0
                lemma2_to64_rest();  // pow2(51 | 54)
                shift_is_pow2(54);

                let bound = 1u64 << 54;
                let bound19 = (19 * bound) as u64;
                let bound_sq = 1u128 << 108;

                // u64 to u128 conversion forces extra assert
                assert((1u64 << 54) * ((19 * (1u64 << 54)) as u64) == 19 * (1u128 << 108))
                    by (bit_vector);
                assert(((1u64 << 54) as u128) * ((1u64 << 54) as u128) == (1u128 << 108))
                    by (bit_vector);

                // precond for term_product_bounds
                assert(19 * bound <= u64::MAX) by {
                    assert(19 * (1u64 << 54) <= u64::MAX) by (compute);
                }
                // If a[i] < 2^54 then a[i] * a[j] < 2^108 and a[i] * (19 * a[j]) < 19 * 2^108
                term_product_bounds(a, bound);

                // ci_0 < 77 * (1u128 << 108)
                c_i_0_bounded(a, bound);

                // precond for c_i_shift_bounded
                assert(77 * (bound * bound) + u64::MAX <= ((u64::MAX as u128) << 51)) by {
                    assert(77 * (1u128 << 108) + u64::MAX <= ((u64::MAX as u128) << 51))
                        by (compute);
                }
                // ci >> 51 <= u64::MAX
                c_i_shift_bounded(a, bound);

                // bv arithmetic
                assert(19 < (1u64 << 5)) by (bit_vector);
                assert((1u64 << 51) < (1u64 << 52)) by (bit_vector);
                assert((1u64 << 52) < (1u64 << 54)) by (bit_vector);
                assert((1u64 << 54) < (1u64 << 59)) by (bit_vector);
                assert((1u64 << 54) * (1u64 << 5) == (1u64 << 59)) by (bit_vector);
                assert(((1u64 << 54) as u128) * ((1u64 << 59) as u128) == (1u128 << 113))
                    by (bit_vector);

                let a3_19 = (19 * a[3]) as u64;
                let a4_19 = (19 * a[4]) as u64;

                // NOTE: we assert the properties derived from c_i_0_bounded
                // and c_i_shift_bounded after every variable declaration,
                // to trigger the solver instantiation

                // ci_0 defs

                let c0_0: u128 = c0_0_val(a);  // a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19
                assert(c0_0 < 77 * bound_sq);

                let c1_0: u128 = c1_0_val(a);  // a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19
                assert(c1_0 < 59 * bound_sq);

                let c2_0: u128 = c2_0_val(a);  // a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * a3_19
                assert(c2_0 < 41 * bound_sq);

                let c3_0: u128 = c3_0_val(a);  // a[4] * a4_19 + 2*( a[0] *  a[3] + a[1] *  a[2]
                assert(c3_0 < 23 * bound_sq);

                let c4_0: u128 = c4_0_val(a);  // a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3]
                assert(c4_0 < 5 * bound_sq);

                // ci defs

                let c1 = c1_val(a);  // (c1_0 + ((c0_0 >> 51) as u64) as u128) as u128;
                assert((c1 >> 51) <= (u64::MAX as u128));

                let c2 = c2_val(a);  // (c2_0 + ((c1 >> 51) as u64) as u128) as u128;
                assert((c2 >> 51) <= (u64::MAX as u128));

                let c3 = c3_val(a);  // (c3_0 + ((c2 >> 51) as u64) as u128) as u128;
                assert((c3 >> 51) <= (u64::MAX as u128));

                let c4 = c4_val(a);  // (c4_0 + ((c3 >> 51) as u64) as u128) as u128;
                assert((c4 >> 51) <= (u64::MAX as u128));

                let a0_0 = (c0_0 as u64) & LOW_51_BIT_MASK;
                // a0_0 < (1u64 << 51)
                masked_lt_51(c0_0 as u64);

                let a1_0 = (c1 as u64) & LOW_51_BIT_MASK;
                // a1_0 < (1u64 << 51)
                masked_lt_51(c1 as u64);

                let a2 = (c2 as u64) & LOW_51_BIT_MASK;
                // a2 < (1u64 << 51)
                masked_lt_51(c2 as u64);

                let a3 = (c3 as u64) & LOW_51_BIT_MASK;
                // a3 < (1u64 << 51)
                masked_lt_51(c3 as u64);

                let carry: u64 = (c4 >> 51) as u64;
                let a4 = (c4 as u64) & LOW_51_BIT_MASK;
                // a4 < (1u64 << 51)
                masked_lt_51(c4 as u64);

                assert(c4 <= c4_0 + (u64::MAX as u128));
                lemma_shr_51_le(c4, (5 * bound_sq + (u64::MAX as u128)) as u128);

                // From the comments below:
                // c4 < 2^110.33  so that carry < 2^59.33
                // and
                // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58

                // ceil(2^59.33)
                let pow2_5933 = 724618875532318195u64;

                assert((5 * (1u128 << 108) + (u64::MAX as u128)) as u128 >> 51 < (
                pow2_5933 as u128)) by (compute);
                assert(carry < pow2_5933);

                // a[0] += carry * 19 fits in u64
                assert(a0_0 + carry * 19 <= u64::MAX) by {
                    assert((1u64 << 51) + 19 * pow2_5933 <= u64::MAX) by (compute);
                }

                let a0_1 = (a0_0 + carry * 19) as u64;

                lemma_shr_51_le(a0_1 as u128, u64::MAX as u128);
                assert(((u64::MAX as u128) >> 51) < (1u64 << 13)) by (compute);

                // a1_0 < (1u64 << 51)
                assert((1u64 << 51) + (1u64 << 13) < (1u64 << 52)) by (compute);

                // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
                assert(a1_0 + (a0_1 >> 51) < (1u64 << 52));
                let a1_1 = (a1_0 + (a0_1 >> 51)) as u64;

                let a0_2 = a0_1 & LOW_51_BIT_MASK;
                // a0_2 < (1u64 << 51)
                masked_lt_51(a0_1 as u64);

                //---- end of no-overflow proof ----
                // Loop invariant: after i loops we have as_nat(a) % p = as_nat(self.limbs) ^ (2 ^ i) % p
                let a_hat = [a0_2, a1_1, a2, a3, a4];
                assert(as_nat(a_hat) % p() == (as_nat(a) * as_nat(a)) % p()) by {
                    // it suffices to prove as_nat(a_hat) == (as_nat(a))^2 (mod p)
                    // let s = pow2(51) for brevity
                    // By definition, as_nat(a_hat) = a0_2 + s * a1_1 + s^2 * a2 + s^3 * a3 + s^4 * a4
                    // a0_2 + s * a1_1 cancel out terms via the div/mod identity:
                    assert(as_nat(a_hat) == a0_1 + pow2(51) * a1_0 + pow2(102) * a2 + pow2(153) * a3
                        + pow2(204) * a4) by {
                        // a0_2 + s * a1_1 =
                        // a0_1 % s  + s * (a1_0 + s * (a0_1 / s)) =
                        // s * a1_0 + [s * (a0_1 / s) + a0_1 % s] = (by the div-mod identity)
                        // s * a1_0 + a0_1
                        assert(a0_2 + pow2(51) * a1_1 == a0_1 + pow2(51) * a1_0) by {
                            lemma_div_and_mod_51((a0_1 >> 51), a0_2, a0_1);
                        }
                    }

                    // Next, we replace all _ & LOW_BITS_MASK with (mod s)
                    assert(as_nat(a_hat) == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry + pow2(
                        51,
                    ) * ((c1 as u64) % (pow2(51) as u64)) + pow2(102) * ((c2 as u64) % (pow2(
                        51,
                    ) as u64)) + pow2(153) * ((c3 as u64) % (pow2(51) as u64)) + pow2(204) * ((
                    c4 as u64) % (pow2(51) as u64))) by {
                        l51_bit_mask_lt();

                        assert((pow2(51) as u64) == (pow2(51) as u128));

                        assert(a0_1 == ((c0_0 as u64) % (pow2(51) as u64)) + 19 * carry) by {
                            lemma_u64_low_bits_mask_is_mod(c0_0 as u64, 51);
                        }

                        assert(a1_0 == (c1 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c1 as u64, 51);
                        }

                        assert(a2 == (c2 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c2 as u64, 51);
                        }

                        assert(a3 == (c3 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c3 as u64, 51);
                        }

                        assert(a4 == (c4 as u64) % (pow2(51) as u64)) by {
                            lemma_u64_low_bits_mask_is_mod(c4 as u64, 51);
                        }
                    }

                    // We can see all mod operations in u128
                    assert(as_nat(a_hat) == (c0_0 % (pow2(51) as u128)) + 19 * carry + pow2(51) * (
                    c1 % (pow2(51) as u128)) + pow2(102) * (c2 % (pow2(51) as u128)) + pow2(153) * (
                    c3 % (pow2(51) as u128)) + pow2(204) * (c4 % (pow2(51) as u128))) by {
                        // pow2(51) is the same in u64 and 128
                        lemma_cast_then_mod_51(c0_0);
                        lemma_cast_then_mod_51(c1);
                        lemma_cast_then_mod_51(c2);
                        lemma_cast_then_mod_51(c3);
                        lemma_cast_then_mod_51(c4);
                    }

                    // Next, we categorically replace a % s with a - s * ( a / s )
                    assert(as_nat(a_hat) == (c0_0 - pow2(51) * (c0_0 / (pow2(51) as u128))) + 19
                        * carry + pow2(51) * (c1 - pow2(51) * (c1 / (pow2(51) as u128))) + pow2(102)
                        * (c2 - pow2(51) * (c2 / (pow2(51) as u128))) + pow2(153) * (c3 - pow2(51)
                        * (c3 / (pow2(51) as u128))) + pow2(204) * (c4 - pow2(51) * (c4 / (pow2(
                        51,
                    ) as u128)))) by {
                        lemma_fundamental_div_mod(c0_0 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c1 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c2 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c3 as int, pow2(51) as int);
                        lemma_fundamental_div_mod(c4 as int, pow2(51) as int);
                    }

                    // Then, we know that
                    // carry = c4/s
                    // c4 = c4_0 + c3/s <=> c3/s = c4 - c4_0
                    // c3 = c3_0 + c2/s <=> c2/s = c3 - c3_0
                    // c2 = c2_0 + c1/s <=> c1/s = c2 - c2_0
                    // c1 = c1_0 + c0_0/s <=> c0_0/s = c1 - c1_0
                    assert(as_nat(a_hat) == (c0_0 - pow2(51) * (c1 - c1_0)) + 19 * carry + pow2(51)
                        * (c1 - pow2(51) * (c2 - c2_0)) + pow2(102) * (c2 - pow2(51) * (c3 - c3_0))
                        + pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) + pow2(204) * (c4 - pow2(51)
                        * carry)) by {
                        lemma_u128_shr_is_div(c0_0, 51);
                        lemma_u128_shr_is_div(c1, 51);
                        lemma_u128_shr_is_div(c2, 51);
                        lemma_u128_shr_is_div(c3, 51);
                        lemma_u128_shr_is_div(c4, 51);
                    }

                    // Now we use distributivity and pow exponent sums, which cancels out any ci terms and leaves only ci_0 terms
                    // Conveniently, we're left with a difference of c * p
                    assert(as_nat(a_hat) == c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153)
                        * c3_0 + pow2(204) * c4_0 - p() * carry) by {
                        assert(c0_0 - pow2(51) * (c1 - c1_0) == c0_0 - pow2(51) * c1 + pow2(51)
                            * c1_0) by {
                            lemma_mul_is_distributive_sub(pow2(51) as int, c1 as int, c1_0 as int);
                        }

                        assert(pow2(51) * (c1 - pow2(51) * (c2 - c2_0)) == pow2(51) * c1 - pow2(102)
                            * c2 + pow2(102) * c2_0) by {
                            lemma_mul_sub(c1 as int, c2 as int, c2_0 as int, 51);
                        }

                        assert(pow2(102) * (c2 - pow2(51) * (c3 - c3_0)) == pow2(102) * c2 - pow2(
                            153,
                        ) * c3 + pow2(153) * c3_0) by {
                            lemma_mul_sub(c2 as int, c3 as int, c3_0 as int, 102);
                        }

                        assert(pow2(153) * (c3 - pow2(51) * (c4 - c4_0)) == pow2(153) * c3 - pow2(
                            204,
                        ) * c4 + pow2(204) * c4_0) by {
                            lemma_mul_sub(c3 as int, c4 as int, c4_0 as int, 153);
                        }

                        assert(pow2(204) * (c4 - pow2(51) * carry) == pow2(204) * c4 - pow2(255)
                            * carry) by {
                            lemma_mul_is_distributive_sub(
                                pow2(204) as int,
                                c4 as int,
                                pow2(51) * carry,
                            );
                            lemma_mul_is_associative(
                                pow2(204) as int,
                                pow2(51) as int,
                                carry as int,
                            );
                            lemma_pow2_adds(204, 51);
                        }

                        // carry on the right, get p
                        assert(c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0 + pow2(
                            204,
                        ) * c4_0 + 19 * carry - pow2(255) * carry == c0_0 + pow2(51) * c1_0 + pow2(
                            102,
                        ) * c2_0 + pow2(153) * c3_0 + pow2(204) * c4_0 - p() * carry) by {
                            pow255_gt_19();
                            lemma_mul_is_distributive_sub_other_way(
                                carry as int,
                                pow2(255) as int,
                                19,
                            );
                        }
                    }

                    let c_arr_as_nat = (c0_0 + pow2(51) * c1_0 + pow2(102) * c2_0 + pow2(153) * c3_0
                        + pow2(204) * c4_0);

                    assert(as_nat(a_hat) % p() == c_arr_as_nat as nat % p()) by {
                        lemma_mod_diff_factor(carry as int, c_arr_as_nat as int, p() as int);
                    }

                    // We use the as_nat_squared lemma to see what (as_nat(a)^2) evaluates to (mod p)

                    // The nat_squared lemma gives us the following:
                    // as_nat(a) * as_nat(a) ==
                    // pow2(8 * 51) * (a[4] * a[4]) +
                    // pow2(7 * 51) * (2 * (a[3] * a[4])) +
                    // pow2(6 * 51) * (a[3] * a[3] + 2 * (a[2] * a[4])) +
                    // pow2(5 * 51) * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])) +
                    // pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
                    // pow2(3 * 51) * (2 * (a[1] * a[2]) + 2 * (a[0] * a[3])) +
                    // pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] * a[2])) +
                    // pow2(1 * 51) * (2 * (a[0] * a[1])) +
                    //                (a[0] * a[0])
                    //
                    // AND
                    //
                    // (as_nat(a) * as_nat(a)) % p() ==
                    // (
                    //     pow2(4 * 51) * (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])) +
                    //     pow2(3 * 51) * (2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])) +
                    //     pow2(2 * 51) * (a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))) +
                    //     pow2(1 * 51) * (2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))) +
                    //                    (a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4])))
                    // ) as nat % p()
                    as_nat_squared(a);

                    // We're basically done, what remains is to prove that the coefficients next to pow2(i * 51)
                    // are exactly ci_0s (via distributivity and associativity)

                    // let c0_0: u128 = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
                    assert(c0_0 == (a[0] * a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4]))))
                        by {
                        // The solver does distributivity on its own.
                        // LHS = a[0] *  a[0] + 2*( a[1] * a4_19 + a[2] * a3_19);
                        //     = a[0] *  a[0] + 2*( a[1] * a4_19 ) + 2 * (a[2] * a3_19);
                        // RHS = a[0] *  a[0] + 19 * (2 * (a[2] * a[3]) + 2 * (a[1] * a[4]))
                        //     = a[0] *  a[0] + 19 * (2 * (a[2] * a[3])) + 19 * (2 * (a[1] * a[4]))
                        // goals
                        // 1) 2 * (a[1] * a4_19) = 19 * (2 * (a[1] * a[4]))
                        // 2) 2 * (a[2] * a3_19) = 19 * (2 * (a[2] * a[3]))
                        assert(2 * (a[1] * a4_19) == 19 * (2 * (a[1] * a[4]))) by {
                            lemma_reorder_mul(a[1] as int, a[4] as int);
                        }

                        assert(2 * (a[2] * a3_19) == 19 * (2 * (a[2] * a[3]))) by {
                            lemma_reorder_mul(a[2] as int, a[3] as int);
                        }
                    }

                    // let c1_0: u128 = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19);
                    assert(c1_0 == (2 * (a[0] * a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))))
                        by {
                        // The solver does distributivity on its own.
                        // LHS = a[3] * a3_19 + 2*( a[0] *  a[1] + a[2] * a4_19)
                        //     = a[3] * a3_19 + 2*( a[0] *  a[1]) + 2 * (a[2] * a4_19)
                        // RHS = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3] + 2 * (a[2] * a[4]))
                        //     = 2 * (a[0] *  a[1]) + 19 * (a[3] * a[3]) + 19 * (2 * (a[2] * a[4]))
                        // goals: 1) a[3] * a3_19 = 19 * (a[3] * a[3])
                        //        2) 2 * (a[2] * a4_19) = 19 * (2 * (a[2] * a[4]))
                        assert(a[3] * a3_19 == 19 * (a[3] * a[3])) by {
                            lemma_mul_is_associative(a[3] as int, a[3] as int, 19);
                        }

                        assert(2 * (a[2] * a4_19) == 19 * (2 * (a[2] * a[4]))) by {
                            lemma_reorder_mul(a[2] as int, a[4] as int);
                        }
                    }

                    // let c2_0: u128 = a[1] *  a[1] + 2*( a[0] *  a[2] + a[4] * a3_19);
                    assert(c2_0 == (a[1] * a[1] + 2 * (a[0] * a[2]) + 19 * (2 * (a[3] * a[4]))))
                        by {
                        // The solver does distributivity on its own.
                        // LHS = a[1] * a[1] + 2 * (a[0] *  a[2] + a[4] * a3_19)
                        //     = a[1] * a[1] + 2 * (a[0] *  a[2]) +  2 * (a[4] * a3_19)
                        // RHS = a[1] * a[1] + 2 * (a[0] *  a[2]) + 19 * (2 * (a[3] * a[4]))
                        // goals: 2 * (a[4] * a3_19) = 19 * (2 * (a[3] * a[4]))
                        assert(2 * (a[4] * a3_19) == 19 * (2 * (a[3] * a[4]))) by {
                            lemma_mul_is_associative(a[4] as int, a[3] as int, 19);
                        }
                    }

                    // let c3_0: u128 = a[4] * a4_19 + 2*( a[0] *  a[3] + a[1] *  a[2]);
                    assert(c3_0 == (2 * (a[1] * a[2]) + 2 * (a[0] * a[3]) + 19 * (a[4] * a[4])))
                        by {
                        // The solver does distributivity on its own.
                        // LHS = a[4] * a4_19 + 2 * (a[0] *  a[3] + a[1] *  a[2])
                        //     = a[4] * a4_19 + 2 * (a[0] *  a[3]) + 2 * (a[1] *  a[2])
                        // RHS = 2 * (a[1] *  a[2]) + 2 * (a[0] *  a[3]) + 19 * (a[4] * a[4])
                        // goals: a[4] * a4_19 = 19 * (a[4] * a[4])
                        assert(a[4] * a4_19 == 19 * (a[4] * a[4])) by {
                            lemma_mul_is_associative(a[4] as int, a[4] as int, 19);
                        }
                    }

                    // let c4_0: u128 = a[2] *  a[2] + 2*( a[0] *  a[4] + a[1] *  a[3]);
                    assert(c4_0 == (a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4]))) by {
                        // The solver does distributivity on its own.
                        // LHS = a[2] * a[2] + 2 * (a[0] * a[4] + a[1] * a[3])
                        //     = a[2] * a[2] + 2 * (a[0] * a[4]) + 2 * (a[1] * a[3])
                        // RHS = a[2] * a[2] + 2 * (a[1] * a[3]) + 2 * (a[0] * a[4])
                        // goals: none
                    }
                }

                let a_pow_2i_int = pow(as_nat(self.limbs) as int, pow2(i as nat));
                assert(a_pow_2i_int >= 0) by {
                    lemma_pow_nat_is_nat(as_nat(self.limbs), i as nat);
                }
                let a_pow_2i: nat = a_pow_2i_int as nat;

                assert(as_nat(a_hat) % p() == ((as_nat(a) % p()) * (as_nat(a) % p())) % p()) by {
                    lemma_mul_mod_noop(as_nat(a) as int, as_nat(a) as int, p() as int);
                }

                // (a_pow_2i % p)^2 % p = (a_pow_2i^2) % p
                lemma_mul_mod_noop(a_pow_2i as int, a_pow_2i as int, p() as int);

                // We know, by the loop inv, that
                // as_nat(a) % p == a_pow_2i % p
                // and, by the above
                // as_nat(a_hat) % p  = (as_nat(a) * as_nat(a)) % p = (a_pow_2i ^ 2)) % p
                // It suffices to prove that
                // (v^(2^i))^2 = v^(2^(i + 1))
                lemma_pow2_square(as_nat(self.limbs) as int, i as nat);
            }

            // Precondition: assume input limbs a[i] are bounded as
            //
            // a[i] < 2^(51 + b)
            //
            // where b is a real parameter measuring the "bit excess" of the limbs.
            // Precomputation: 64-bit multiply by 19.
            //
            // This fits into a u64 whenever 51 + b + lg(19) < 64.
            //
            // Since 51 + b + lg(19) < 51 + 4.25 + b
            //                       = 55.25 + b,
            // this fits if b < 8.75.
            let a3_19 = 19 * a[3];
            let a4_19 = 19 * a[4];

            // Multiply to get 128-bit coefficients of output.
            //
            // The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
            // which doesn't seem any better or worse than doing them as precomputations
            // on the 64-bit inputs.
            let c0: u128 = m(a[0], a[0]) + 2 * (m(a[1], a4_19) + m(a[2], a3_19));
            let mut c1: u128 = m(a[3], a3_19) + 2 * (m(a[0], a[1]) + m(a[2], a4_19));
            let mut c2: u128 = m(a[1], a[1]) + 2 * (m(a[0], a[2]) + m(a[4], a3_19));
            let mut c3: u128 = m(a[4], a4_19) + 2 * (m(a[0], a[3]) + m(a[1], a[2]));
            let mut c4: u128 = m(a[2], a[2]) + 2 * (m(a[0], a[4]) + m(a[1], a[3]));

            // Same bound as in multiply:
            //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
            //         < 2^(102 + lg(1 + 4*19) + 2*b)
            //         < 2^(108.27 + 2*b)
            //
            // The carry (c[i] >> 51) fits into a u64 when
            //    108.27 + 2*b - 51 < 64
            //    2*b < 6.73
            //    b < 3.365.
            //
            // So we require b < 3 to ensure this fits.
            #[cfg(not(verus_keep_ghost))]
            {
                debug_assert!(a[0] < (1 << 54));
                debug_assert!(a[1] < (1 << 54));
                debug_assert!(a[2] < (1 << 54));
                debug_assert!(a[3] < (1 << 54));
                debug_assert!(a[4] < (1 << 54));
            }

            // const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1; // already defined at module level

            // Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
            // that the addition is a u128 + u64 rather than u128 + u128.
            c1 += ((c0 >> 51) as u64) as u128;
            a[0] = (c0 as u64) & LOW_51_BIT_MASK;

            c2 += ((c1 >> 51) as u64) as u128;
            a[1] = (c1 as u64) & LOW_51_BIT_MASK;

            c3 += ((c2 >> 51) as u64) as u128;
            a[2] = (c2 as u64) & LOW_51_BIT_MASK;

            c4 += ((c3 >> 51) as u64) as u128;
            a[3] = (c3 as u64) & LOW_51_BIT_MASK;

            let carry: u64 = (c4 >> 51) as u64;
            a[4] = (c4 as u64) & LOW_51_BIT_MASK;

            // To see that this does not overflow, we need a[0] + carry * 19 < 2^64.
            //
            // c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
            //    < 2^(102 + 2*b + lg(5)) + 2^64.
            //
            // When b < 3 we get
            //
            // c4 < 2^110.33  so that carry < 2^59.33
            //
            // so that
            //
            // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
            //
            // and there is no overflow.
            a[0] += carry * 19;

            // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
            a[1] += a[0] >> 51;
            a[0] &= LOW_51_BIT_MASK;

            // Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).

            k -= 1;
            if k == 0 {
                break ;
            }
        }

        FieldElement51 { limbs: a }
    }

    /// Returns the square of this field element.
    pub fn square(&self) -> (r: FieldElement51)
        requires
    // The precondition in pow2k loop propagates to here

            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54,
        ensures
            as_nat(r.limbs) % p() == pow(as_nat(self.limbs) as int, 2) as nat % p(),
    {
        proof {
            // pow2(1) == 2
            lemma2_to64();
        }
        self.pow2k(1)
    }

    /// Returns 2 times the square of this field element.
    pub fn square2(&self) -> (r: FieldElement51)
        requires
    // The precondition in pow2k loop propagates to here

            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < 1u64 << 54,
        ensures
            as_nat(r.limbs) % p() == (2 * pow(as_nat(self.limbs) as int, 2)) as nat % p(),
    {
        let mut square = self.pow2k(1);

        // Since square is mut, we save the initial value
        let ghost old_limbs = square.limbs;

        proof {
            // forall |i: int| 0 <= i < 5 ==> 2 * old_limbs[i] <= u64::MAX
            assert forall|i: int| 0 <= i < 5 implies 2 * square.limbs[i] <= u64::MAX by {
                // if LHS < RHS, then 2 * LHS < 2 * RHS
                lemma_mul_left_inequality(2, square.limbs[i] as int, (1u64 << 54) as int);
                assert(2 * (1u64 << 54) <= u64::MAX) by (compute);
            }

            let ka = [
                (2 * square.limbs[0]) as u64,
                (2 * square.limbs[1]) as u64,
                (2 * square.limbs[2]) as u64,
                (2 * square.limbs[3]) as u64,
                (2 * square.limbs[4]) as u64,
            ];

            // as_nat(ka) == 2 * as_nat(square.limbs)
            // and
            // as_nat(ka) % p() == (2 * as_nat(square.limbs)) % p()
            as_nat_k(square.limbs, 2);

            // By pow2k ensures:
            // as_nat(square.limbs) % p() == pow(as_nat(self.limbs) as int, pow2(1)) as nat % p()
            // We just need pow2(1) == 2
            lemma2_to64();

            // p > 0
            pow255_gt_19();

            assert(as_nat(ka) % p() == ((2nat % p()) * (as_nat(square.limbs) % p())) % p() == ((2nat
                % p()) * (pow(as_nat(self.limbs) as int, 2) as nat % p())) % p()) by {
                lemma_mul_mod_noop(2, as_nat(square.limbs) as int, p() as int);
            }

            // as_nat(self.limbs)^2 >= 0
            assert(pow(as_nat(self.limbs) as int, 2) >= 0) by {
                lemma_pow_nat_is_nat(as_nat(self.limbs), 1);
            }

            assert(((2nat % p()) * (pow(as_nat(self.limbs) as int, 2) as nat % p())) % p() == (2 * (
            pow(as_nat(self.limbs) as int, 2))) as nat % p()) by {
                lemma_mul_mod_noop(2, pow(as_nat(self.limbs) as int, 2) as int, p() as int);
            }

            assert(as_nat(ka) % p() == (2 * (pow(as_nat(self.limbs) as int, 2))) as nat % p());
        }

        for i in 0..5
            invariant
                forall|j: int| 0 <= j < 5 ==> old_limbs[j] < (1u64 << 54),
                forall|j: int| 0 <= j < i ==> #[trigger] square.limbs[j] == 2 * old_limbs[j],
                forall|j: int| i <= j < 5 ==> #[trigger] square.limbs[j] == old_limbs[j],
        {
            proof {
                assert(2 * (1u64 << 54) <= u64::MAX) by (compute);
                lemma_mul_strict_inequality(square.limbs[i as int] as int, (1u64 << 54) as int, 2);
            }
            square.limbs[i] *= 2;
        }

        square
    }
}

} // verus!
