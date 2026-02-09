//! Specifications for the Montgomery reduction algorithm.
//!
//! Montgomery reduction computes T × R⁻¹ mod L efficiently, where:
//! - T is the input value (product of two Montgomery-form scalars)
//! - R = 2^260 is the Montgomery radix
//! - L is the group order (prime order of the ed25519 curve)
//!
//! The algorithm computes:
//! 1. N such that (T + N×L) ≡ 0 (mod R)  (the Montgomery adjustment)
//! 2. intermediate = (T + N×L) / R  (guaranteed to be an integer)
//! 3. result = intermediate mod L  (conditional subtraction)
use super::scalar52_specs::*;
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::scalar::Scalar52;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// FUNCTION-CENTRIC PREDICATES FOR montgomery_reduce
// ============================================================================
// These predicates describe what montgomery_reduce actually needs from its input,
// without reference to how the input was obtained.
/// The limb bounds that montgomery_reduce requires to avoid overflow.
/// These are the bounds produced by mul_internal(bounded, bounded).
///
/// # Motivation
/// montgomery_reduce performs iterative computations where each iteration
/// accumulates products of limbs. To avoid overflow in u128 arithmetic,
/// we need these specific bounds on each input limb.
#[verusfmt::skip]
pub open spec fn montgomery_reduce_input_bounds(limbs: &[u128; 9]) -> bool {
    limbs[0] < pow2(104) &&  // 1 product term
    limbs[1] < pow2(105) &&  // 2 product terms
    limbs[2] < pow2(106) &&  // 3 product terms
    limbs[3] < pow2(107) &&  // 4 product terms
    limbs[4] < pow2(107) &&  // 5 product terms
    limbs[5] < pow2(107) &&  // 4 product terms
    limbs[6] < pow2(106) &&  // 3 product terms
    limbs[7] < pow2(105) &&  // 2 product terms
    limbs[8] < pow2(104)     // 1 product term
}

/// The value bound that montgomery_reduce requires to produce a canonical output.
/// When the total value is < R * L, the intermediate result_raw will be < 2L,
/// which allows sub(result_raw, L) to produce a canonical result.
///
/// # Motivation
/// - result_raw = (input + N*L) / R, where N < R
/// - For result_raw < 2L: we need input/R + L < 2L, i.e., input < R*L
///
/// # Relationship to r4_safe_bound
/// - canonical_bound (T < R×L ≈ 2^512) implies r4_safe_bound (T < 2^520)
/// - canonical_bound additionally ensures result < L (canonical)
///
/// # Note
/// This is purely a VALUE constraint. The per-limb overflow bounds
/// (montgomery_reduce_input_bounds) must be established separately.
pub open spec fn montgomery_reduce_canonical_bound(limbs: &[u128; 9]) -> bool {
    slice128_to_nat(limbs) < montgomery_radix() * group_order()
}

/// The Montgomery reduction property: result * R ≡ input (mod L)
pub open spec fn montgomery_congruent(result: &Scalar52, limbs: &[u128; 9]) -> bool {
    (scalar52_to_nat(result) * montgomery_radix()) % group_order() == slice128_to_nat(limbs)
        % group_order()
}

// ============================================================================
// Part 2 Helper Specs
// ============================================================================
// These specs are used in the Part 2 chain proof for carry cancellation analysis.
/// The high part of T (positions 5-8)
/// This represents limbs[5] + limbs[6]×2^52 + limbs[7]×2^104 + limbs[8]×2^156
#[inline(always)]
pub(crate) open spec fn t_high(limbs: &[u128; 9]) -> nat {
    (limbs[5] as nat) + (limbs[6] as nat) * pow2(52) + (limbs[7] as nat) * pow2(104) + (
    limbs[8] as nat) * pow2(156)
}

/// The high part of N×L (positions 5-8, the parts that contribute to division)
/// These are the cross products nᵢ × L[m] where i + m ≥ 5
#[inline(always)]
pub(crate) open spec fn nl_high_contribution(n0: u64, n1: u64, n2: u64, n3: u64, n4: u64) -> nat {
    let l1 = constants::L.limbs[1] as nat;
    let l2 = constants::L.limbs[2] as nat;
    // L[3] = 0
    let l4 = constants::L.limbs[4] as nat;

    // Position 5 contributions: n1×L[4] + n3×L[2] + n4×L[1]
    let pos5 = (n1 as nat) * l4 + (n3 as nat) * l2 + (n4 as nat) * l1;

    // Position 6 contributions: n2×L[4] + n4×L[2]
    let pos6 = (n2 as nat) * l4 + (n4 as nat) * l2;

    // Position 7 contributions: n3×L[4]
    let pos7 = (n3 as nat) * l4;

    // Position 8 contributions: n4×L[4]
    let pos8 = (n4 as nat) * l4;

    pos5 + pos6 * pow2(52) + pos7 * pow2(104) + pos8 * pow2(156)
}

} // verus!
