//! Small Aeneas - Standalone functions extracted from curve25519-dalek
//!

/// u64 * u64 = u128 multiply helper
///
/// # Verus Specification (converted from original Verus code):
///
/// ## Requires:
/// - `x < (1u64 << 52)`
/// - `y < (1u64 << 52)`
///
/// ## Ensures:
/// - `result < (1u128 << 104)`
/// - `result == x * y`
#[inline(always)]
pub fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

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

impl FieldElement51 {
    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    ///
    /// # Verus Specification:
    ///    ensures
    ///        forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
    ///        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
    ///        as_nat(r.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51)
    ///
    /// Suppose l = (l0, l1, l2, l3, l4) are the input limbs.
    /// They represent a number
    /// e(l) =  l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204
    /// in Z_p, for p = 2^255 - 19
    /// reduce(l) returns v = (v0, v1, v2, v3, v4), such that
    /// v0 = 19 * a4 + b0
    /// v1 =      a0 + b1
    /// v2 =      a1 + b2
    /// v3 =      a2 + b3
    /// v4 =      a3 + b4
    /// where ai = li >> 51 and bi = li & LOW_51_BIT_MASK
    /// we can reformulate this as ai = li / 2^51 (flooring division) and bi = li % 2^51
    /// Using the following identity connecting integer division and remainder:
    /// x = y * (x / y) + x % y
    /// we can see that li = ai * 2^51 + bi
    /// Plugging the above identities into the equations for v, we can observe that
    /// e(v) = e(l) - p * (l4 >> 51)
    /// IOW, e(reduce(l)) = e(l) (mod p)
    /// additionally, if all limbs are below 2^51, reduce(l) = l
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
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
//pub open spec fn as_nat(limbs: [u64; 5]) -> nat {
//    (limbs[0] as nat) +
//    pow2(51) * (limbs[1] as nat) +
//    pow2(102) * (limbs[2] as nat) +
//    pow2(153) * (limbs[3] as nat) +
//    pow2(204) * (limbs[4] as nat)
//}
