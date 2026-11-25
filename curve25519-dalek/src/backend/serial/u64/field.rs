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

/// Limbs representing the integer 16p, where p is 2^255 - 19. Used in subtraction routines.
const SIXTEEN_P: [u64; 5] = [
    36028797018963664u64,
    36028797018963952u64,
    36028797018963952u64,
    36028797018963952u64,
    36028797018963952u64,
];

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
pub struct FieldElement51(pub(crate) [u64; 5]);

impl Debug for FieldElement51 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FieldElement51({:?})", &self.0[..])
    }
}

#[cfg(feature = "zeroize")]
impl Zeroize for FieldElement51 {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<'a> AddAssign<&'a FieldElement51> for FieldElement51 {
    /// Given `self` and `_rhs`, set `self` to `self + _rhs`
    ///
    /// # Requires
    /// `self.0[i] + _rhs.0[i]` MUST be < 2^64 for all `i`
    ///
    /// # Postcondition
    /// `out.0[i] == self.0 + _rhs.0[i]` for all `i`
    fn add_assign(&mut self, _rhs: &'a FieldElement51) {
        for i in 0..5 {
            self.0[i] += _rhs.0[i];
        }
    }
}

impl<'a> Add<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    /// Given `self` and `_rhs`, return `self + _rhs`
    ///
    /// # Requires
    /// `self.0[i] + _rhs.[i]` MUST be < 2^64 for all `i`
    fn add(self, _rhs: &'a FieldElement51) -> FieldElement51 {
        let mut output = *self;
        output += _rhs;
        output
    }
}

impl<'a> SubAssign<&'a FieldElement51> for FieldElement51 {
    /// Given \\(x,y\\), return \\(x - y\\).
    ///
    /// # Requires
    /// Each limb of `self` must be < 2^64 - 2^55. And each limb of `rhs`
    /// MUST be ≤ 2^55 - 304.
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-10
    fn sub_assign(&mut self, _rhs: &'a FieldElement51) {
        let result = (self as &FieldElement51) - _rhs;
        self.0 = result.0;
    }
}

impl<'a> Sub<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    /// Given \\(x,y\\), return \\(x - y\\).
    ///
    /// # Requires
    /// Each limb of `self` must be < 2^64 - 2^55. And each limb of `rhs`
    /// MUST be ≤ 2^55 - 304.
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-10
    fn sub(self, _rhs: &'a FieldElement51) -> FieldElement51 {
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
        // Note the constant added in limb 0 is 2^55 - 304, hence our
        // precondition
        FieldElement51::reduce(core::array::from_fn(|i| {
            self.0[i] + SIXTEEN_P[i] - _rhs.0[i]
        }))
    }
}

impl<'a> MulAssign<&'a FieldElement51> for FieldElement51 {
    /// Given `self` and `_rhs`, set `self` to `self * _rhs`
    ///
    /// # Requires
    /// Each limb in `self` and `_rhs` MUST be < 2^54
    ///
    /// # Postcondition
    /// The limbs of the output are all < 2^(51 + epsilon) where epsilon is 1e-11
    fn mul_assign(&mut self, _rhs: &'a FieldElement51) {
        let result = (self as &FieldElement51) * _rhs;
        self.0 = result.0;
    }
}

impl<'a> Mul<&'a FieldElement51> for &FieldElement51 {
    type Output = FieldElement51;

    /// Given `self` and `_rhs`, return `self * _rhs`
    ///
    /// # Requires
    /// Each limb in `self` and `_rhs` MUST be < 2^54
    ///
    /// # Postcondition
    /// The limbs of the output are all < 2^(51 + epsilon) where epsilon is 1e-11
    #[rustfmt::skip] // keep alignment of c* calculations
    fn mul(self, _rhs: &'a FieldElement51) -> FieldElement51 {
        /// Helper function to multiply two 64-bit integers with 128
        /// bits of output.
        #[inline(always)]
        fn m(x: u64, y: u64) -> u128 { (x as u128) * (y as u128) }

        // Alias self, _rhs for more readable formulas
        let a: &[u64; 5] = &self.0;
        let b: &[u64; 5] = &_rhs.0;

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
        let     c0: u128 = m(a[0], b[0]) + m(a[4], b1_19) + m(a[3], b2_19) + m(a[2], b3_19) + m(a[1], b4_19);
        let mut c1: u128 = m(a[1], b[0]) + m(a[0],  b[1]) + m(a[4], b2_19) + m(a[3], b3_19) + m(a[2], b4_19);
        let mut c2: u128 = m(a[2], b[0]) + m(a[1],  b[1]) + m(a[0],  b[2]) + m(a[4], b3_19) + m(a[3], b4_19);
        let mut c3: u128 = m(a[3], b[0]) + m(a[2],  b[1]) + m(a[1],  b[2]) + m(a[0],  b[3]) + m(a[4], b4_19);
        let mut c4: u128 = m(a[4], b[0]) + m(a[3],  b[1]) + m(a[2],  b[2]) + m(a[1],  b[3]) + m(a[0] , b[4]);

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
        debug_assert!(a[0] < (1 << 54)); debug_assert!(b[0] < (1 << 54));
        debug_assert!(a[1] < (1 << 54)); debug_assert!(b[1] < (1 << 54));
        debug_assert!(a[2] < (1 << 54)); debug_assert!(b[2] < (1 << 54));
        debug_assert!(a[3] < (1 << 54)); debug_assert!(b[3] < (1 << 54));
        debug_assert!(a[4] < (1 << 54)); debug_assert!(b[4] < (1 << 54));

        // Casting to u64 and back tells the compiler that the carry is
        // bounded by 2^64, so that the addition is a u128 + u64 rather
        // than u128 + u128.

        const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;
        let mut out = [0u64; 5];

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
        FieldElement51(out)
    }
}

impl Neg for &FieldElement51 {
    type Output = FieldElement51;

    /// Given \\(x\\), return \\(-x\\).
    ///
    /// # Requires
    /// Each limb of `self` MUST be ≤ 2^55 - 304
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-10
    fn neg(self) -> FieldElement51 {
        let mut output = *self;
        output.negate();
        output
    }
}

impl ConditionallySelectable for FieldElement51 {
    fn conditional_select(
        a: &FieldElement51,
        b: &FieldElement51,
        choice: Choice,
    ) -> FieldElement51 {
        FieldElement51([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
            u64::conditional_select(&a.0[4], &b.0[4], choice),
        ])
    }

    fn conditional_swap(a: &mut FieldElement51, b: &mut FieldElement51, choice: Choice) {
        u64::conditional_swap(&mut a.0[0], &mut b.0[0], choice);
        u64::conditional_swap(&mut a.0[1], &mut b.0[1], choice);
        u64::conditional_swap(&mut a.0[2], &mut b.0[2], choice);
        u64::conditional_swap(&mut a.0[3], &mut b.0[3], choice);
        u64::conditional_swap(&mut a.0[4], &mut b.0[4], choice);
    }

    fn conditional_assign(&mut self, other: &FieldElement51, choice: Choice) {
        self.0[0].conditional_assign(&other.0[0], choice);
        self.0[1].conditional_assign(&other.0[1], choice);
        self.0[2].conditional_assign(&other.0[2], choice);
        self.0[3].conditional_assign(&other.0[3], choice);
        self.0[4].conditional_assign(&other.0[4], choice);
    }
}

impl FieldElement51 {
    pub(crate) const fn from_limbs(limbs: [u64; 5]) -> FieldElement51 {
        FieldElement51(limbs)
    }

    /// The scalar \\( 0 \\).
    pub const ZERO: FieldElement51 = FieldElement51::from_limbs([0, 0, 0, 0, 0]);
    /// The scalar \\( 1 \\).
    pub const ONE: FieldElement51 = FieldElement51::from_limbs([1, 0, 0, 0, 0]);
    /// The scalar \\( -1 \\).
    pub const MINUS_ONE: FieldElement51 = FieldElement51::from_limbs([
        2251799813685228,
        2251799813685247,
        2251799813685247,
        2251799813685247,
        2251799813685247,
    ]);

    /// Invert the sign of this field element
    ///
    /// # Requires
    /// Each limb of `self` MUST be ≤ 2^55 - 304
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-10
    pub fn negate(&mut self) {
        // See commentary in the Sub impl
        let neg = FieldElement51::reduce(core::array::from_fn(|i| SIXTEEN_P[i] - self.0[i]));
        self.0 = neg.0;
    }

    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon) for all
    /// limbs, where epsilon = 1e-10.
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> FieldElement51 {
        const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;

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

        FieldElement51(limbs)
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
    /// # Postcondition
    /// The limbs of the output are all < 2^51
    #[rustfmt::skip] // keep alignment of bit shifts
    pub const fn from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
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

        let low_51_bit_mask = (1u64 << 51) - 1;
        FieldElement51(
        // load bits [  0, 64), no shift
        [  load8_at(bytes,  0)        & low_51_bit_mask
        // load bits [ 48,112), shift to [ 51,112)
        , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
        // load bits [ 96,160), shift to [102,160)
        , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
        // load bits [152,216), shift to [153,216)
        , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
        // load bits [192,256), shift to [204,112)
        , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
        ])
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    #[rustfmt::skip] // keep alignment of s[*] calculations
    pub fn to_bytes(self) -> [u8; 32] {
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
        let mut limbs = FieldElement51::reduce(self.0).0;

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
        s[ 0] =   limbs[0]                           as u8;
        s[ 1] =  (limbs[0] >>  8)                    as u8;
        s[ 2] =  (limbs[0] >> 16)                    as u8;
        s[ 3] =  (limbs[0] >> 24)                    as u8;
        s[ 4] =  (limbs[0] >> 32)                    as u8;
        s[ 5] =  (limbs[0] >> 40)                    as u8;
        s[ 6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[ 7] =  (limbs[1] >>  5)                    as u8;
        s[ 8] =  (limbs[1] >> 13)                    as u8;
        s[ 9] =  (limbs[1] >> 21)                    as u8;
        s[10] =  (limbs[1] >> 29)                    as u8;
        s[11] =  (limbs[1] >> 37)                    as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] =  (limbs[2] >>  2)                    as u8;
        s[14] =  (limbs[2] >> 10)                    as u8;
        s[15] =  (limbs[2] >> 18)                    as u8;
        s[16] =  (limbs[2] >> 26)                    as u8;
        s[17] =  (limbs[2] >> 34)                    as u8;
        s[18] =  (limbs[2] >> 42)                    as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] =  (limbs[3] >>  7)                    as u8;
        s[21] =  (limbs[3] >> 15)                    as u8;
        s[22] =  (limbs[3] >> 23)                    as u8;
        s[23] =  (limbs[3] >> 31)                    as u8;
        s[24] =  (limbs[3] >> 39)                    as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] =  (limbs[4] >>  4)                    as u8;
        s[27] =  (limbs[4] >> 12)                    as u8;
        s[28] =  (limbs[4] >> 20)                    as u8;
        s[29] =  (limbs[4] >> 28)                    as u8;
        s[30] =  (limbs[4] >> 36)                    as u8;
        s[31] =  (limbs[4] >> 44)                    as u8;

        // High bit should be zero.
        debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

    /// Given `k > 0`, return `self^(2^k)`.
    ///
    /// # Requires
    /// Each limb in `self` MUST be < 2^54
    ///
    /// # Postcondition
    /// The entries of the output are all < 2^(51 + epsilon), where epsilon = 1e-9
    pub fn pow2k(&self, mut k: u32) -> FieldElement51 {
        debug_assert!(k > 0);

        let mut a: [u64; 5] = self.0;

        loop {
            // square_limbs has the same precondition and postcondition as this function.
            // Also its precondition is satisfied by its postcondition, so we can feed the
            // output into itself.
            a = square_limbs(a);

            k -= 1;
            if k == 0 {
                break;
            }
        }

        FieldElement51(a)
    }

    /// Returns the square of this field element.
    ///
    /// # Requires
    /// Each limb in `self` MUST be < 2^54
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-11
    pub fn square(&self) -> FieldElement51 {
        FieldElement51(square_limbs(self.0))
    }

    /// Returns 2 times the square of this field element.
    ///
    /// # Requires
    /// Each limb in `self` MUST be < 2^54
    ///
    /// # Postcondition
    /// Each limb of the output is < 2^(51 + epsilon) where epsilon = 1e-11
    pub fn square2(&self) -> FieldElement51 {
        let mut square = square_limbs(self.0);
        for limb in &mut square {
            *limb *= 2;
        }

        // square_limbs returns limbs less than 2^(51 + epsilon). Multiplying by 2 gives
        // us our postcondition
        FieldElement51(square)
    }
}

/// Given the limbs of \\(x\\), return the limbs of \\(x^2\\).
///
/// # Requires
/// Each entry in `a` MUST be < 2^54
///
/// # Postcondition
/// Each entry of the output is < 2^(51 + epsilon) where epsilon = 1e-11
#[rustfmt::skip] // keep alignment of c* calculations
#[inline(always)]
fn square_limbs(mut a: [u64; 5]) -> [u64; 5] {
    /// Multiply two 64-bit integers with 128 bits of output.
    #[inline(always)]
    fn m(x: u64, y: u64) -> u128 {
        (x as u128) * (y as u128)
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

    // Precomputation: the doublings.
    //
    // Every product below other than the five squares a[i]^2 appears exactly
    // twice in the full 5x5 product, so it is computed once and doubled. The
    // doubling is done here, on one 64-bit operand, rather than on the 128-bit
    // product: `2*(x*y) == (2*x)*y`, so the coefficients are unchanged, but a
    // 64-bit shift is one instruction where a 128-bit one is two, and four
    // shifts here cover ten doubled products.
    //
    // `2*a[i]` fits into a u64 whenever 51 + b + 1 < 64, i.e. b < 12, and
    // `2*19*a[3]` whenever 51 + b + lg(19) + 1 < 64, i.e. b < 7.75. Both are
    // slacker than the b < 3 this function already requires.
    let a0_2 = 2 * a[0];
    let a1_2 = 2 * a[1];
    let a2_2 = 2 * a[2];
    let a3_19_2 = 2 * a3_19;

    // Multiply to get 128-bit coefficients of output.
    let     c0: u128 = m(a[0], a[0]) + m(a1_2, a4_19) + m(a2_2, a3_19);
    let mut c1: u128 = m(a[3], a3_19) + m(a0_2,  a[1]) + m(a2_2, a4_19);
    let mut c2: u128 = m(a[1], a[1])  + m(a0_2,  a[2]) + m(a[4], a3_19_2);
    let mut c3: u128 = m(a[4], a4_19) + m(a0_2,  a[3]) + m(a1_2, a[2]);
    let mut c4: u128 = m(a[2], a[2])  + m(a0_2,  a[4]) + m(a1_2, a[3]);

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
    debug_assert!(a[0] < (1 << 54));
    debug_assert!(a[1] < (1 << 54));
    debug_assert!(a[2] < (1 << 54));
    debug_assert!(a[3] < (1 << 54));
    debug_assert!(a[4] < (1 << 54));

    const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;

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

    // Now all a[i] < 2^(51 + epsilon) and a = (input)^2.

    a
}

#[cfg(test)]
mod test {
    use super::*;

    proptest::proptest! {
        /// `square` and `square2` must agree with `mul` on all valid inputs.
        #[test]
        fn proptest_square_agrees_with_mul(
            bits in 50u32..=54, // Go up to the max allowable input to square* functions, 2^54-1
            limbs in proptest::array::uniform5(proptest::num::u64::ANY),
        ) {
            // Sample uniform limbs and then mask to `bits`, so that we explore various bitlengths
            let mask = (1u64 << bits) - 1;
            let x = FieldElement51(limbs.map(|limb| limb & mask));
            let sq = x.square();

            proptest::prop_assert_eq!(sq.to_bytes(), (&x * &x).to_bytes());
            proptest::prop_assert_eq!(x.square2().to_bytes(), (&sq + &sq).to_bytes());
        }
    }

    /// `square` and `square2` must agree with `mul` at the edges of the valid input range:
    /// zero, one, and the largest limbs `square` accepts
    #[test]
    fn square_agrees_with_mul_at_bounds() {
        for limbs in [[0; 5], [1, 0, 0, 0, 0], [(1 << 54) - 1; 5]] {
            let x = FieldElement51(limbs);
            let sq = x.square();

            assert_eq!(sq.to_bytes(), (&x * &x).to_bytes());
            assert_eq!(x.square2().to_bytes(), (&sq + &sq).to_bytes());
        }
    }
}
