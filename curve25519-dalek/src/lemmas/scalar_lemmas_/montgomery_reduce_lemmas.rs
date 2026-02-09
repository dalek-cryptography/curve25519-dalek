#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;
use super::super::common_lemmas::shift_lemmas::*;
use super::super::scalar_lemmas::*;
use super::montgomery_reduce_part1_chain_lemmas::*;
use super::montgomery_reduce_part2_chain_lemmas::*;
use crate::backend::serial::u64::constants;
use crate::backend::serial::u64::scalar::Scalar52;
use crate::specs::field_specs_u64::*;
use crate::specs::montgomery_reduce_specs::*;
use crate::specs::scalar52_specs::*;

verus! {

// =============================================================================
// LEMMA: 2L / 2^208 == 2^45
// =============================================================================
/// Proves 2L / 2^208 == 2^45, where L = group_order() = 2^252 + delta.
///
/// Proof: 2L = pow2(253) + 2*delta, pow2(253) = pow2(45) * pow2(208),
/// and 2*delta < pow2(127) < pow2(208), so the quotient is pow2(45).
pub(crate) proof fn lemma_two_l_div_pow2_208_eq_pow2_45()
    ensures
        (2 * group_order()) / pow2(208) == pow2(45),
{
    let delta: nat = 27742317777372353535851937790883648493nat;
    let two_l = 2 * group_order();

    // Step 1: 2L = pow2(253) + 2*delta
    assert(two_l == pow2(253) + 2 * delta) by {
        assert(group_order() == pow2(252) + delta);
        lemma_pow2_plus_one(252);  // pow2(253) = 2 * pow2(252)
    }

    // Step 2: pow2(253) = pow2(45) * pow2(208)
    assert(pow2(253) == pow2(45) * pow2(208)) by {
        assert(45 + 208 == 253nat);
        lemma_pow2_adds(45, 208);
    }

    // Step 3: 2*delta < pow2(208)
    // Strategy (following lemma_group_order_bound pattern):
    //   - Compare delta against pow2(126) using hex literals
    //   - Build pow2(126) = pow2(63) * pow2(63)
    //   - Then 2*delta < 2*pow2(126) = pow2(127) < pow2(208)
    assert(2 * delta < pow2(208)) by {
        // delta < pow2(126): compare decimal literal against hex (pattern from lemma_group_order_bound)
        assert(27742317777372353535851937790883648493nat < 0x40000000000000000000000000000000nat)
            by (compute_only);
        assert(pow2(63) == 0x8000000000000000nat) by {
            lemma2_to64_rest();
        }
        lemma_pow2_adds(63, 63);
        assert(pow2(126) == 0x40000000000000000000000000000000nat);
        assert(delta < pow2(126));

        // 2*delta < 2*pow2(126) = pow2(127)
        lemma_pow2_plus_one(126);  // pow2(127) = 2 * pow2(126)

        // pow2(127) < pow2(208)
        lemma_pow2_strictly_increases(127, 208);
    }

    // Step 4: Apply fundamental_div_mod_converse
    // two_l = pow2(45) * pow2(208) + 2*delta, with 0 <= 2*delta < pow2(208)
    // => two_l / pow2(208) = pow2(45)
    lemma_fundamental_div_mod_converse(
        two_l as int,
        pow2(208) as int,
        pow2(45) as int,
        (2 * delta) as int,
    );
}

// =============================================================================
// Bit Operation Lemmas (NOT IN VSTD YET)
// =============================================================================
/// Masking a truncated value: combining truncation and masking
///
/// Proof outline:
///   (x as u64) = x % 2^64             [lemma_u128_cast_64_is_mod]
///   y & mask(n) = y % pow2(n)          [lemma_u64_low_bits_mask_is_mod]
///   (x % 2^64) % pow2(n) = x % pow2(n) [lemma_mod_mod with 2^64 = pow2(n) * pow2(64-n)]
pub proof fn lemma_u128_truncate_and_mask(x: u128, n: nat)
    requires
        n <= 64,
    ensures
        ((x as u64) & (low_bits_mask(n) as u64)) as nat == (x as nat) % pow2(n),
{
    let trunc = x as u64;  // truncation: x mod 2^64

    // Establish pow2(64) == 0x10000000000000000 once
    assert(pow2(64) == 0x10000000000000000nat) by {
        lemma_u128_shift_is_pow2(64);
        assert((1u128 << 64) == 0x10000000000000000u128) by (bit_vector);
    }

    if n == 64 {
        // low_bits_mask(64) = pow2(64) - 1 = u64::MAX, so mask is identity
        assert(low_bits_mask(64) as u64 == u64::MAX) by {
            assert(low_bits_mask(64) == pow2(64) - 1) by {
                reveal(low_bits_mask);
            }
            assert(0x10000000000000000nat - 1 == u64::MAX as nat);
        }
        assert((trunc & u64::MAX) == trunc) by (bit_vector);
        // (x as u64) as nat == x % pow2(64)
        lemma_u128_cast_64_is_mod(x);
        assert((trunc as nat) == (x as nat) % pow2(64));
    } else {
        // n < 64
        // Step 1: mask on u64 = mod pow2(n) on u64
        lemma_u64_low_bits_mask_is_mod(trunc, n);
        // gives: trunc & (low_bits_mask(n) as u64) == trunc % (pow2(n) as u64)
        let masked = trunc & (low_bits_mask(n) as u64);
        assert(masked == trunc % (pow2(n) as u64));

        // Step 2: truncation is mod 2^64
        lemma_u128_cast_64_is_mod(x);
        assert((trunc as nat) == (x as nat) % pow2(64));

        // Step 3: nested mod: (x % pow2(64)) % pow2(n) == x % pow2(n)
        // Use lemma_mod_mod(x, a, b) which gives (x % (a*b)) % a == x % a
        // Set a = pow2(n), b = pow2(64-n), so a*b = pow2(64)
        let d = (64 - n) as nat;
        lemma_pow2_pos(n);
        lemma_pow2_pos(d);
        lemma_pow2_adds(n, d);
        assert(pow2(n) * pow2(d) == pow2(64));
        lemma_mod_mod(x as nat as int, pow2(n) as int, pow2(d) as int);
        // gives: ((x as nat) % pow2(64)) % pow2(n) == (x as nat) % pow2(n)
        assert(((x as nat) % pow2(64)) % pow2(n) == (x as nat) % pow2(n));

        // Step 4: connect u64 mod to nat mod
        // (trunc % (pow2(n) as u64)) as nat == (trunc as nat) % pow2(n)
        // Since trunc: u64 and pow2(n) fits in u64 for n < 64
        assert(pow2(n) <= u64::MAX as nat) by {
            lemma_pow2_strictly_increases(n, 64);
        }
        assert((trunc % (pow2(n) as u64)) as nat == (trunc as nat) % pow2(n)) by {
            // For unsigned types, (a % b) as nat == (a as nat) % (b as nat) when b > 0
            assert(pow2(n) > 0) by {
                lemma_pow2_pos(n);
            }
        }

        // Combine all steps
        assert((masked as nat) == (trunc as nat) % pow2(n));
        assert((trunc as nat) % pow2(n) == ((x as nat) % pow2(64)) % pow2(n));
        assert(((x as nat) % pow2(64)) % pow2(n) == (x as nat) % pow2(n));
    }
}

// =============================================================================
// Carry Shift-to-Nat Conversion
// =============================================================================
/// Converts carry << 52 to nat form: (carry << 52) as nat == (carry as nat) * pow2(52)
///
/// Used in montgomery_reduce to convert u128 shift operations to nat arithmetic.
/// Works for both part1 carries (< 2^57) and part2 carries (< 2^56).
///
/// # Precondition
/// - `carry_bound_bits <= 72` ensures `carry * pow2(52) <= u128::MAX`
/// - `carry < pow2(carry_bound_bits)` is the actual carry bound
pub(crate) proof fn lemma_carry_shift_to_nat(carry: u128, carry_bound_bits: nat)
    requires
        carry_bound_bits <= 72,
        carry < pow2(carry_bound_bits),
    ensures
        (carry << 52) as nat == (carry as nat) * pow2(52),
{
    // Overflow check: carry * pow2(52) < pow2(carry_bound_bits + 52) <= pow2(124) <= u128::MAX
    lemma_pow2_adds(carry_bound_bits, 52);
    lemma_u128_pow2_le_max(carry_bound_bits + 52);
    lemma_pow2_pos(52);

    assert(carry * pow2(52) <= u128::MAX) by {
        lemma_mul_strict_inequality(
            carry as nat as int,
            pow2(carry_bound_bits) as int,
            pow2(52) as int,
        );
    }

    // Convert shift to multiplication
    lemma_u128_shl_is_mul(carry, 52);
}

// =============================================================================
// Core Divisibility Lemma for part1
// =============================================================================
/// Core divisibility: (s + p * L[0]) % 2^52 = 0 where p = s * LFACTOR mod 2^52
///
/// This is the key insight of Montgomery reduction: LFACTOR * L[0] ≡ -1 (mod 2^52),
/// so p * L[0] ≡ s * (-1) ≡ -s, and s + p * L[0] ≡ 0.
pub(crate) proof fn lemma_part1_sum_divisible_by_pow2_52(s: u64, p: nat)
    requires
        s < pow2(52),
        p == ((s as nat) * (constants::LFACTOR as nat)) % pow2(52),
    ensures
        ((s as nat) + p * (constants::L.limbs[0] as nat)) % pow2(52) == 0,
{
    let L0: nat = 0x0002631a5cf5d3edu64 as nat;
    let lfac: nat = 0x51da312547e1bu64 as nat;
    let p52: nat = 0x10000000000000nat;
    let sn = s as nat;

    // Establish constant values
    assert(constants::L.limbs[0] == 0x0002631a5cf5d3edu64);
    assert(constants::LFACTOR == 0x51da312547e1bu64);
    assert(pow2(52) == p52) by {
        lemma2_to64_rest();
    }

    // Step 1: LFACTOR property - (1 + LFACTOR * L[0]) % 2^52 = 0
    assert((1 + lfac * L0) % p52 == 0) by {
        assert(((constants::LFACTOR as nat) * (constants::L.limbs[0] as nat) + 1)
            % 0x10000000000000nat == 0) by (compute);
    }

    // Step 2: Scale - s * (1 + LFACTOR * L[0]) % 2^52 = 0
    assert((sn * (1 + lfac * L0)) % p52 == 0) by {
        lemma_mul_mod_noop_right(sn as int, (1 + lfac * L0) as int, p52 as int);
    }

    // Step 3: Expand - s * (1 + LFACTOR * L[0]) = s + s * LFACTOR * L[0]
    assert(sn * (1 + lfac * L0) == sn + sn * lfac * L0) by {
        lemma_mul_is_distributive_add(sn as int, 1, (lfac * L0) as int);
        lemma_mul_basics(sn as int);
        lemma_mul_is_associative(sn as int, lfac as int, L0 as int);
    }

    // Step 4: Substitute - p * L[0] ≡ s * LFACTOR * L[0] (mod 2^52)
    assert((p * L0) % p52 == (sn * lfac * L0) % p52) by {
        lemma_mul_mod_noop_left((sn * lfac) as int, L0 as int, p52 as int);
        lemma_mul_is_associative(sn as int, lfac as int, L0 as int);
    }

    // Step 5: Combine Steps 2+3 - (s + s*LFACTOR*L[0]) % 2^52 = 0
    assert((sn + sn * lfac * L0) % p52 == 0);

    // Goal: (s + p * L[0]) % 2^52 = 0
    // Bridge: (sn + p*L0) and (sn + sn*lfac*L0) are congruent mod p52
    // because p*L0 ≡ sn*lfac*L0 (mod p52) from Step 4
    assert((sn + p * L0) % p52 == 0) by {
        lemma_add_mod_noop(sn as int, (p * L0) as int, p52 as int);
        lemma_add_mod_noop(sn as int, (sn * lfac * L0) as int, p52 as int);
    }
}

// =============================================================================
// Main part1 correctness lemma
// =============================================================================
/// Main correctness lemma for part1: sum + p*L[0] == carry << 52
///
/// Structure:
/// 1. Establish bitwise-to-arithmetic conversions using lemmas (not bit_vector)
/// 2. Prove arithmetic properties using pow2 lemmas
pub(crate) proof fn lemma_part1_correctness(sum: u128)
    requires
        sum < (1u128 << 108),
    ensures
        ({
            let mask52: u64 = 0xFFFFFFFFFFFFFu64;
            let sum_low52: u64 = (sum as u64) & mask52;
            let product: u128 = ((sum_low52 as u128) * (constants::LFACTOR as u128)) as u128;
            let p: u64 = (product as u64) & mask52;
            let total: u128 = (sum + (p as u128) * (constants::L.limbs[0] as u128)) as u128;
            let carry: u128 = total >> 52;
            &&& p < (1u64 << 52)
            &&& total == carry << 52
        }),
{
    let mask52: u64 = 0xFFFFFFFFFFFFFu64;
    let p52: nat = pow2(52);

    // Compute all derived values from sum
    let sum_low52: u64 = (sum as u64) & mask52;
    let product: u128 = ((sum_low52 as u128) * (constants::LFACTOR as u128)) as u128;
    let p: u64 = (product as u64) & mask52;
    let total: u128 = (sum + (p as u128) * (constants::L.limbs[0] as u128)) as u128;
    let carry: u128 = total >> 52;
    let L0 = constants::L.limbs[0] as nat;

    // =======================================================================
    // PHASE 1: Bitwise-to-arithmetic conversions (used in multiple places)
    // =======================================================================

    // Used in: L0 < pow2(50), pow2_adds, mod_bound, mul_strict_inequality
    assert(p52 == 0x10000000000000nat) by {
        lemma2_to64_rest();
    }
    // Used in: postcondition `p < (1u64 << 52)`
    assert((1u64 << 52) == p52) by {
        lemma_u64_shift_is_pow2(52);
    }

    // Used in: (1) sum_low52 < p52 bound, (2) mod_add_eq for divisibility
    assert(sum_low52 as nat == (sum as nat) % p52) by {
        lemma_u128_truncate_and_mask(sum, 52);
    }
    // Used in: (1) p < p52 bound, (2) lemma_part1_sum_divisible_by_pow2_52 precondition
    assert(p as nat == (product as nat) % p52) by {
        lemma_u128_truncate_and_mask(product, 52);
    }

    // =======================================================================
    // PHASE 2: Arithmetic proofs
    // =======================================================================

    // p < pow2(52): for postcondition and multiplication bound
    assert(p < p52) by {
        lemma_pow2_pos(52nat);
        lemma_mod_bound((product as nat) as int, p52 as int);
    }

    // Core divisibility: (sum_low52 + p*L[0]) ≡ 0 (mod pow2(52))
    assert(((sum_low52 as nat) + (p as nat) * L0) % p52 == 0) by {
        assert(sum_low52 < p52) by {
            lemma_pow2_pos(52nat);
            lemma_mod_bound((sum as nat) as int, p52 as int);
        }
        lemma_part1_sum_divisible_by_pow2_52(sum_low52, p as nat);
    }

    // Multiplication bound: p * L[0] < pow2(102)
    assert((p as nat) * L0 < pow2(102)) by {
        assert(L0 < pow2(50)) by {
            assert(pow2(50) == 0x4000000000000nat) by {
                lemma2_to64_rest();
            }
        }
        assert(pow2(52) * pow2(50) == pow2(102)) by {
            lemma_pow2_adds(52, 50);
        }
        lemma_mul_strict_inequality((p as nat) as int, p52 as int, L0 as int);
    }

    // No overflow: sum + p*L[0] < u128::MAX
    assert((sum as nat) + (p as nat) * L0 < u128::MAX as nat) by {
        assert((1u128 << 108) == pow2(108)) by {
            assert(pow2(108) <= u128::MAX) by {
                lemma_u128_pow2_le_max(108);
            }
            lemma_u128_shl_is_mul(1, 108);
        }
        assert(pow2(108) + pow2(102) < u128::MAX as nat) by {
            assert(pow2(102) < pow2(108)) by {
                lemma_pow2_strictly_increases(102, 108);
            }
            assert(2 * pow2(108) == pow2(109)) by {
                lemma_pow2_unfold(109);
            }
            assert(pow2(109) < pow2(127)) by {
                lemma_pow2_strictly_increases(109, 127);
            }
            assert(pow2(127) <= u128::MAX) by {
                lemma_u128_pow2_le_max(127);
            }
        }
    }

    // Shift round-trip: (total >> 52) << 52 == total
    assert((total >> 52) << 52 == total) by {
        assert((total as nat) % pow2(52) == 0) by {
            assert((sum as nat) % p52 == sum_low52 as nat);
            lemma_mod_add_eq(
                (sum as nat) as int,
                (sum_low52 as nat) as int,
                ((p as nat) * L0) as int,
                p52 as int,
            );
        }
        lemma_u128_right_left_shift_divisible(total, 52);
    }
}

/// Helper function for part2 bounds
/// With precondition sum < 2^108, we can prove carry < 2^56
///
/// # Structure
/// sum = w + (carry << 52) where:
/// - w = low 52 bits of sum (< 2^52)
/// - carry = sum >> 52 (< 2^56 when sum < 2^108)
pub proof fn lemma_part2_bounds(sum: u128)
    requires
        sum < (1u128 << 108),
    ensures
        ({
            let carry = sum >> 52;
            let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
            &&& w < (1u64 << 52)
            &&& sum == w + (carry << 52)
            &&& carry < (1u128 << 56)
        }),
{
    let carry = sum >> 52;
    let w = (sum as u64) & (((1u64 << 52) - 1) as u64);
    let p52 = pow2(52);

    // Subgoal 1: w < 2^52 (masking always gives < 2^52)
    assert(w < 1u64 << 52) by {
        assert((sum as u64) & (((1u64 << 52) - 1) as u64) < (1u64 << 52)) by (bit_vector);
    }

    // Subgoal 2: carry < 2^56 (follows from sum < 2^108)
    assert((sum >> 52) < (1u128 << 56)) by (bit_vector)
        requires
            sum < (1u128 << 108),
    ;

    // Subgoal 3: sum == w + (carry << 52)
    assert(sum == w + (carry << 52)) by {
        // 3a: Establish p52 > 0 for division lemmas
        lemma_pow2_pos(52);

        // 3b: Fundamental division: sum = p52 * quotient + remainder
        lemma_fundamental_div_mod(sum as int, p52 as int);
        assert(sum == p52 * (sum as nat / p52) + sum as nat % p52);

        // 3c: carry = sum >> 52 = sum / p52
        lemma_u128_shr_is_div(sum, 52);
        assert(carry as nat == sum as nat / p52);

        // 3d: carry << 52 = p52 * (sum / p52)
        assert(carry << 52 == p52 * (sum as nat / p52)) by {
            // 3d.i: No overflow: carry * p52 <= u128::MAX
            assert(carry * p52 <= u128::MAX) by {
                // quotient * p52 <= sum by div-mul property
                lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
                lemma_mul_hoist_inequality(p52 as int, sum as int, p52 as int);
                lemma_div_multiples_vanish(sum as int, p52 as int);
            }
            lemma_u128_shl_is_mul(carry, 52);
            lemma_mul_is_commutative(p52 as int, (sum as nat / p52) as int);
        }

        // 3e: w = sum % p52
        assert(w == sum as nat % p52) by {
            // Mask (1 << 52) - 1 == low_bits_mask(52)
            lemma_u64_shift_is_pow2(52);
            assert(((1u64 << 52) - 1) as u64 == low_bits_mask(52));

            // Masking extracts mod
            lemma_u64_low_bits_mask_is_mod(sum as u64, 52);

            // Connect u64 mod to nat mod
            lemma2_to64_rest();
            assert(p52 == 0x10000000000000);
            assert(sum as u64 == sum % 0x10000000000000000) by (bit_vector);
            assert(sum % 0x10000000000000 == (sum % 0x10000000000000000) % 0x10000000000000)
                by (bit_vector);
        }
    }
}

// =============================================================================
// mul_internal Output Bounds Lemmas
// =============================================================================
/// Bounds on the output of mul_internal when both inputs are bounded.
/// Each output limb[i] is the sum of (min(i+1, 5, 9-i)) products of 52-bit numbers.
///
/// limbs[0] = 1 product  → < 2^104
/// limbs[1] = 2 products → < 2^105
/// limbs[2] = 3 products → < 2^106 (3 * 2^104 < 2^106)
/// limbs[3] = 4 products → < 2^107 (4 * 2^104 = 2^106 < 2^107)
/// limbs[4] = 5 products → < 2^107 (5 * 2^104 < 2^107)
/// limbs[5] = 4 products → < 2^107
/// limbs[6] = 3 products → < 2^106
/// limbs[7] = 2 products → < 2^105
/// limbs[8] = 1 product  → < 2^104
pub(crate) proof fn lemma_mul_internal_limbs_bounds(a: &Scalar52, b: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        spec_mul_internal(a, b) == *limbs,
    ensures
        limbs[0] < (1u128 << 104),  // 1 product
        limbs[1] < (1u128 << 105),  // 2 products
        limbs[2] < (1u128 << 106),  // 3 products
        limbs[3] < (1u128 << 107),  // 4 products
        limbs[4] < (1u128 << 107),  // 5 products
        limbs[5] < (1u128 << 107),  // 4 products
        limbs[6] < (1u128 << 106),  // 3 products
        limbs[7] < (1u128 << 105),  // 2 products
        limbs[8] < (1u128 << 104),  // 1 product
{
    // Extract limb bounds from limbs_bounded
    assert(a.limbs[0] < (1u64 << 52));
    assert(a.limbs[1] < (1u64 << 52));
    assert(a.limbs[2] < (1u64 << 52));
    assert(a.limbs[3] < (1u64 << 52));
    assert(a.limbs[4] < (1u64 << 52));
    assert(b.limbs[0] < (1u64 << 52));
    assert(b.limbs[1] < (1u64 << 52));
    assert(b.limbs[2] < (1u64 << 52));
    assert(b.limbs[3] < (1u64 << 52));
    assert(b.limbs[4] < (1u64 << 52));

    let a0 = a.limbs[0] as u128;
    let a1 = a.limbs[1] as u128;
    let a2 = a.limbs[2] as u128;
    let a3 = a.limbs[3] as u128;
    let a4 = a.limbs[4] as u128;
    let b0 = b.limbs[0] as u128;
    let b1 = b.limbs[1] as u128;
    let b2 = b.limbs[2] as u128;
    let b3 = b.limbs[3] as u128;
    let b4 = b.limbs[4] as u128;

    assert((1u64 << 52) as u128 == (1u128 << 52)) by (bit_vector);

    assert(a0 < (1u128 << 52));
    assert(a1 < (1u128 << 52));
    assert(a2 < (1u128 << 52));
    assert(a3 < (1u128 << 52));
    assert(a4 < (1u128 << 52));
    assert(b0 < (1u128 << 52));
    assert(b1 < (1u128 << 52));
    assert(b2 < (1u128 << 52));
    assert(b3 < (1u128 << 52));
    assert(b4 < (1u128 << 52));

    // Key: product of two values < 2^52 is < 2^104 (asserted once, SMT applies to all pairs)
    assert(forall|x: u128, y: u128|
        x < (1u128 << 52) && y < (1u128 << 52) ==> #[trigger] (x * y) < (1u128 << 104))
        by (bit_vector);

    // Sum bounds: n products of < 2^104 each
    assert(2 * (1u128 << 104) == (1u128 << 105)) by (bit_vector);
    assert(3 * (1u128 << 104) < (1u128 << 106)) by (bit_vector);
    assert(4 * (1u128 << 104) < (1u128 << 107)) by (bit_vector);
    assert(5 * (1u128 << 104) < (1u128 << 107)) by (bit_vector);
}

// =============================================================================
// Bridge Lemmas: mul_internal Output → montgomery_reduce Preconditions
// =============================================================================
/// Bridge lemma: bounded × bounded product satisfies montgomery_reduce_input_bounds
///
/// montgomery_reduce_input_bounds requires:
///   limbs[0] < pow2(104), limbs[1] < pow2(105), limbs[2] < pow2(106),
///   limbs[3] < pow2(107), limbs[4] < pow2(107), limbs[5] < pow2(107),
///   limbs[6] < pow2(106), limbs[7] < pow2(105), limbs[8] < pow2(104)
///
/// lemma_mul_internal_limbs_bounds provides:
///   limbs[0] < 2^104, limbs[1] < 2^105, limbs[2] < 2^106,
///   limbs[3] < 2^107, limbs[4] < 2^107, limbs[5] < 2^107,
///   limbs[6] < 2^106, limbs[7] < 2^105, limbs[8] < 2^104
///
/// The bounds are an exact match, so the bridge is trivial.
pub(crate) proof fn lemma_bounded_product_satisfies_input_bounds(
    a: &Scalar52,
    b: &Scalar52,
    limbs: &[u128; 9],
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        spec_mul_internal(a, b) == *limbs,
    ensures
        montgomery_reduce_input_bounds(limbs),
{
    // lemma_mul_internal_limbs_bounds proves: limbs[i] < (1u128 << N_i)
    // which exactly matches montgomery_reduce_input_bounds: limbs[i] < pow2(N_i)
    lemma_mul_internal_limbs_bounds(a, b, limbs);

    // Convert (1u128 << N) to pow2(N) for each distinct bound
    lemma_u128_shift_is_pow2(104);
    lemma_u128_shift_is_pow2(105);
    lemma_u128_shift_is_pow2(106);
    lemma_u128_shift_is_pow2(107);
}

// =============================================================================
// Bridge Lemma: Canonical Input → Canonical Output
// =============================================================================
/// Bridge lemma: when one input is canonical (< L), the product satisfies canonical_bound
///
/// This is the KEY lemma for proving montgomery_reduce returns canonical outputs.
/// It applies when multiplying any bounded scalar by a canonical scalar (like R or RR).
///
/// # Proof Structure
/// 1. limbs_bounded(a) → a < R = 2^260
/// 2. b is canonical → b < L
/// 3. Therefore: a × b < R × L → canonical_bound holds
pub(crate) proof fn lemma_canonical_product_satisfies_canonical_bound(
    a: &Scalar52,
    b: &Scalar52,
    limbs: &[u128; 9],
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        scalar52_to_nat(b) < group_order(),  // b is canonical
        spec_mul_internal(a, b) == *limbs,
        slice128_to_nat(limbs) == scalar52_to_nat(a) * scalar52_to_nat(b),
    ensures
        montgomery_reduce_canonical_bound(limbs),
{
    let a_nat = scalar52_to_nat(a);
    let b_nat = scalar52_to_nat(b);
    let R = montgomery_radix();
    let L = group_order();

    // Subgoal 1: input_bounds hold
    lemma_bounded_product_satisfies_input_bounds(a, b, limbs);

    // Subgoal 2: a < R = 2^260
    super::super::scalar_lemmas::lemma_bound_scalar(a);
    assert(a_nat < pow2(260));
    assert(R == pow2(260));

    // Subgoal 3: b < L (from precondition)
    assert(b_nat < L);

    // Subgoal 4: a × b < R × L
    if b_nat == 0 {
        // a × 0 = 0 < R × L (since R × L > 0)
        lemma_mul_basics(a_nat as int);
        assert(a_nat * b_nat == 0);
        assert(L > 0) by {
            assert(L == pow2(252) + 27742317777372353535851937790883648493);
            lemma_pow2_pos(252);
        }
        lemma_pow2_pos(260);
        assert(R > 0);
        // R > 0 and L > 0 implies R * L > 0
        lemma_mul_strictly_positive(R as int, L as int);
        assert(R * L > 0);
    } else {
        // b_nat > 0, so we can use strict inequality
        // a < R and b > 0 → a * b < R * b
        lemma_mul_strict_inequality(a_nat as int, R as int, b_nat as int);
        assert(a_nat * b_nat < R * b_nat);

        // b < L → R * b < R * L (since R > 0)
        lemma_pow2_pos(260);
        assert(R > 0);
        lemma_mul_strict_inequality(b_nat as int, L as int, R as int);
        assert(R * b_nat < R * L);

        // Transitivity: a * b < R * b < R * L
    }

    assert(slice128_to_nat(limbs) < montgomery_radix() * group_order());
}

// =============================================================================
// Bridge Lemmas: Identity Array (from_montgomery) → montgomery_reduce Preconditions
// =============================================================================
/// Bridge lemma: identity-style array satisfies montgomery_reduce_input_bounds
///
/// This lemma is needed for `from_montgomery` which directly converts a Scalar52
/// to a 9-limb array by padding with zeros: [a0, a1, a2, a3, a4, 0, 0, 0, 0]
///
/// Proof sketch:
///   - limbs[i] = a.limbs[i] < 2^52 for i < 5
///   - limbs[i] = 0 for i >= 5
///   - 2^52 < 2^104 < 2^105 < ... < 2^107
///   - So all bounds are trivially satisfied
pub(crate) proof fn lemma_identity_array_satisfies_input_bounds(a: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        forall|i: int| #![auto] 0 <= i < 5 ==> limbs[i] == a.limbs[i] as u128,
        forall|i: int| #![auto] 5 <= i < 9 ==> limbs[i] == 0,
    ensures
        montgomery_reduce_input_bounds(limbs),
{
    // For i < 5: limbs[i] = a.limbs[i] < 2^52, and 2^52 < pow2(104..107) for all required bounds
    // For i >= 5: limbs[i] = 0 < pow2(anything)
    assert((1u64 << 52) == pow2(52)) by {
        lemma_u64_shift_is_pow2(52);
    }

    // 2^52 < each required bound
    lemma_pow2_strictly_increases(52, 104);
    lemma_pow2_strictly_increases(52, 105);
    lemma_pow2_strictly_increases(52, 106);
    lemma_pow2_strictly_increases(52, 107);

    // 0 < each required bound (for the zero limbs 5-8)
    lemma_pow2_pos(104);
    lemma_pow2_pos(105);
    lemma_pow2_pos(106);
    lemma_pow2_pos(107);
}

/// Bridge lemma: identity array satisfies canonical_bound for bounded input
///
/// For from_montgomery:
///   - Input value = scalar52_to_nat(a) < 2^260 (from limbs_bounded)
///   - R × L = 2^260 × (2^252 + ...) ≈ 2^513
///   - So input < 2^260 < R × L ✓
///
/// This means from_montgomery gets the stronger postcondition: is_canonical_scalar52
pub(crate) proof fn lemma_identity_array_satisfies_canonical_bound(a: &Scalar52, limbs: &[u128; 9])
    requires
        limbs_bounded(a),
        forall|i: int| #![auto] 0 <= i < 5 ==> limbs[i] == a.limbs[i] as u128,
        forall|i: int| #![auto] 5 <= i < 9 ==> limbs[i] == 0,
    ensures
        montgomery_reduce_canonical_bound(limbs),
{
    // First establish input_bounds
    lemma_identity_array_satisfies_input_bounds(a, limbs);

    // Show slice128_to_nat(limbs) == scalar52_to_nat(a)
    super::super::scalar_lemmas::lemma_from_montgomery_limbs_conversion(limbs, &a.limbs);

    // Show scalar52_to_nat(a) < pow2(260)
    super::super::scalar_lemmas::lemma_bound_scalar(a);
    assert(scalar52_to_nat(a) < pow2(260));

    // Show pow2(260) < montgomery_radix() * group_order()
    // montgomery_radix() = pow2(260)
    // group_order() = 2^252 + 27742317777372353535851937790883648493 > 2^252
    assert(montgomery_radix() == pow2(260));

    // group_order() > 1, so R * L > R = 2^260
    assert(group_order() > 1) by {
        assert(group_order() == pow2(252) + 27742317777372353535851937790883648493);
        lemma_pow2_pos(252);
    }

    // For slice128_to_nat(limbs) < R * L, we need to show:
    // scalar52_to_nat(a) < pow2(260) < pow2(260) * group_order()
    assert(pow2(260) * group_order() > pow2(260)) by {
        assert(group_order() > 1);
        lemma_mul_basics(pow2(260) as int);
        lemma_mul_strict_inequality(1, group_order() as int, pow2(260) as int);
    }

    assert(slice128_to_nat(limbs) < montgomery_radix() * group_order());
}

// =============================================================================
// r4 Bounds Lemmas - Proving r4 < 2^52 + L[4]
// =============================================================================
/// L[4] = 2^44 (the highest limb of the group order L)
pub(crate) proof fn lemma_l_limb4_is_pow2_44()
    ensures
        constants::L.limbs[4] as nat == pow2(44),
        constants::L.limbs[4] == 0x0000100000000000u64,
{
    // Direct computation
    assert(constants::L.limbs[4] == 0x0000100000000000u64);

    // 0x0000100000000000 = 2^44
    // Using bit_vector for hex computation
    assert(0x0000100000000000u64 == (1u64 << 44)) by (bit_vector);

    // Convert shift to pow2
    lemma_u64_shift_is_pow2(44);
    assert((1u64 << 44) as nat == pow2(44));
}

// =============================================================================
// Pre-sub and Post-sub lemmas
// =============================================================================
/// Pre-subtraction lemma: Establishes the quotient relationship for post_sub.
///
/// # What This Lemma Proves
///
/// intermediate × R = T + N×L
///
/// where:
/// - intermediate = scalar52_to_nat(r0..r4)
/// - R = 2^260 (Montgomery radix)
/// - T = slice128_to_nat(limbs) (input value)
/// - N = five_u64_limbs_to_nat(n0..n4) (Montgomery quotient from Part 1)
/// - L = group_order()
///
/// # Proof Strategy
///
/// 1. Call Part 2 chain lemma to get: five_u64_limbs_to_nat(r0..r4) × R = T + N×L
/// 2. Connect scalar52_to_nat(intermediate) to five_u64_limbs_to_nat(r0..r4)
///
/// # Note
///
/// This lemma does NOT prove r4 bounds or intermediate < 2L.
/// For the canonical path, use lemma_r4_bound_from_canonical separately.
pub(crate) proof fn lemma_montgomery_reduce_pre_sub(
    limbs: &[u128; 9],
    // N values from Part 1
    n0: u64,
    n1: u64,
    n2: u64,
    n3: u64,
    n4: u64,
    // N as nat (caller proves N < 2^260 via lemma_general_bound)
    n: nat,
    // Final carry from Part 1
    carry4: u128,
    // Part 2 sums
    sum5: u128,
    sum6: u128,
    sum7: u128,
    sum8: u128,
    // Part 2 carries
    carry5: u128,
    carry6: u128,
    carry7: u128,
    // Part 2 outputs: the r values computed by part2
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
    intermediate: &Scalar52,
)
    requires
        montgomery_reduce_input_bounds(limbs),
        // N bounds (from part1 postconditions: each n_i < 2^52)
        n0 < pow2(52),
        n1 < pow2(52),
        n2 < pow2(52),
        n3 < pow2(52),
        n4 < pow2(52),
        // N = five_u64_limbs_to_nat(n0..n4)
        n == five_u64_limbs_to_nat(n0, n1, n2, n3, n4),
        // Part 1 divisibility result (caller proves this via lemma_part1_chain_divisibility)
        ({
            let n = five_u64_limbs_to_nat(n0, n1, n2, n3, n4);
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l_low = constants::L.limbs[0] as nat + constants::L.limbs[1] as nat * pow2(52)
                + constants::L.limbs[2] as nat * pow2(104) + constants::L.limbs[3] as nat * pow2(
                156,
            ) + constants::L.limbs[4] as nat * pow2(208);
            (t_low + n * l_low) % pow2(260) == 0
        }),
        // Part 1 quotient result (caller proves this via lemma_part1_chain_divisibility)
        // This is the exact quotient: t_low + nl_low_coeffs = carry4 × 2^260
        ({
            let t_low = limbs[0] as nat + limbs[1] as nat * pow2(52) + limbs[2] as nat * pow2(104)
                + limbs[3] as nat * pow2(156) + limbs[4] as nat * pow2(208);
            let l0_val = constants::L.limbs[0] as nat;
            let l1 = constants::L.limbs[1] as nat;
            let l2 = constants::L.limbs[2] as nat;
            let l4 = constants::L.limbs[4] as nat;
            let coeff0 = (n0 as nat) * l0_val;
            let coeff1 = (n0 as nat) * l1 + (n1 as nat) * l0_val;
            let coeff2 = (n0 as nat) * l2 + (n1 as nat) * l1 + (n2 as nat) * l0_val;
            let coeff3 = (n1 as nat) * l2 + (n2 as nat) * l1 + (n3 as nat) * l0_val;
            let coeff4 = (n0 as nat) * l4 + (n2 as nat) * l2 + (n3 as nat) * l1 + (n4 as nat)
                * l0_val;
            let nl_low_coeffs = coeff0 + coeff1 * pow2(52) + coeff2 * pow2(104) + coeff3 * pow2(156)
                + coeff4 * pow2(208);
            t_low + nl_low_coeffs == (carry4 as nat) * pow2(260)
        }),
        // Sum definitions (how part2 inputs are computed)
        sum5 as nat == carry4 as nat + limbs[5] as nat + (n1 as nat) * (
        constants::L.limbs[4] as nat) + (n3 as nat) * (constants::L.limbs[2] as nat) + (n4 as nat)
            * (constants::L.limbs[1] as nat),
        sum6 as nat == carry5 as nat + limbs[6] as nat + (n2 as nat) * (
        constants::L.limbs[4] as nat) + (n4 as nat) * (constants::L.limbs[2] as nat),
        sum7 as nat == carry6 as nat + limbs[7] as nat + (n3 as nat) * (
        constants::L.limbs[4] as nat),
        sum8 as nat == carry7 as nat + limbs[8] as nat + (n4 as nat) * (
        constants::L.limbs[4] as nat),
        // Part2 stage equations (from part2 postconditions)
        sum5 as nat == (r0 as nat) + (carry5 as nat) * pow2(52),
        sum6 as nat == (r1 as nat) + (carry6 as nat) * pow2(52),
        sum7 as nat == (r2 as nat) + (carry7 as nat) * pow2(52),
        sum8 as nat == (r3 as nat) + (r4 as nat) * pow2(52),
        // Bounds on r0-r3 from part2
        (r0 as nat) < pow2(52),
        (r1 as nat) < pow2(52),
        (r2 as nat) < pow2(52),
        (r3 as nat) < pow2(52),
        // intermediate is constructed from r0..r4
        intermediate.limbs[0] == r0,
        intermediate.limbs[1] == r1,
        intermediate.limbs[2] == r2,
        intermediate.limbs[3] == r3,
        intermediate.limbs[4] == r4,
    ensures
// Quotient relationship: intermediate × R = T + N×L

        scalar52_to_nat(intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n
            * group_order(),
{
    // Call Part 2 chain lemma to get: five_u64_limbs_to_nat(r0..r4) × 2^260 = T + N×L
    lemma_part2_chain_quotient(
        limbs,
        n0,
        n1,
        n2,
        n3,
        n4,
        carry4,
        sum5,
        sum6,
        sum7,
        sum8,
        carry5,
        carry6,
        carry7,
        r0,
        r1,
        r2,
        r3,
        r4,
    );

    let inter_nat = five_u64_limbs_to_nat(r0, r1, r2, r3, r4);

    // Connect scalar52_to_nat(intermediate) to five_u64_limbs_to_nat(r0..r4)
    assert(scalar52_to_nat(intermediate) == inter_nat) by {
        use crate::lemmas::scalar_lemmas::lemma_five_limbs_equals_to_nat;
        use crate::specs::scalar52_specs::five_limbs_to_nat_aux;

        // five_limbs_to_nat_aux(intermediate.limbs) == scalar52_to_nat(intermediate)
        lemma_five_limbs_equals_to_nat(&intermediate.limbs);

        // five_limbs_to_nat_aux uses pow2(k)*limbs[i], five_u64_limbs_to_nat uses limbs[i]*pow2(k)
        // These are equal by commutativity
        lemma_mul_is_commutative(pow2(52) as int, r1 as int);
        lemma_mul_is_commutative(pow2(104) as int, r2 as int);
        lemma_mul_is_commutative(pow2(156) as int, r3 as int);
        lemma_mul_is_commutative(pow2(208) as int, r4 as int);
    }

    // montgomery_radix() == pow2(260) by definition
    // Part 2 ensures: inter_nat * pow2(260) == slice128_to_nat(limbs) + n * group_order()
    // Combined: scalar52_to_nat(intermediate) * montgomery_radix() == T + N×L
}

/// Carry8 bound lemma: Proves the final carry fits in 53 bits
///
/// This lemma is called BEFORE the `carry as u64` cast to establish that
/// the cast is safe. It solves the chicken-and-egg problem where:
/// - We need `carry < 2^53` to safely cast to u64
/// - `lemma_montgomery_reduce_pre_sub` takes `r4: u64` as input
///
/// # Direct Sum8 Bound Proof
///
/// From the computation: sum8 = carry7 + limb8 + n4 × L[4]
///   - carry7 < 2^56     (from part2(sum7) postcondition)
///   - limb8 < 2^104     (from montgomery_reduce_input_bounds)
///   - n4 < 2^52, L[4] = 2^44, so n4 × L[4] < 2^96
///
/// Therefore: sum8 < 2^56 + 2^104 + 2^96 < 2^105
/// And: carry8 = sum8 >> 52 < 2^105 / 2^52 = 2^53
pub(crate) proof fn lemma_carry8_bound(
    limb8: u128,  // limbs[8] passed separately to avoid array indexing in bit_vector
    n4: u64,
    l4: u64,  // constants::L.limbs[4] passed separately
    carry7: u128,
    sum8: u128,
    carry8: u128,
)
    requires
// limb8 < 2^104 (from montgomery_reduce_input_bounds on limbs[8])

        limb8 < (1u128 << 104),
        // n4 from part1 postcondition
        n4 < (1u64 << 52),
        // l4 = L[4] = 2^44
        l4 == (1u64 << 44),
        // carry7 from part2(sum7) postcondition
        carry7 < (1u128 << 56),
        // sum8 definition
        sum8 == carry7 + limb8 + (n4 as u128) * (l4 as u128),
        // carry8 from part2(sum8) postcondition: carry = sum >> 52
        carry8 == sum8 >> 52,
    ensures
// The tight bound: carry8 < 2^53 (allows safe cast to u64)

        carry8 < pow2(53),
{
    // =========================================================================
    // Combined proof using bit_vector
    // =========================================================================
    //
    // sum8 = carry7 + limb8 + n4×L[4]
    //      < 2^56 + 2^104 + (2^52 × 2^44)
    //      = 2^56 + 2^104 + 2^96
    //      < 2^105
    //
    // carry8 = sum8 >> 52 < 2^105 >> 52 = 2^53
    //
    // Note: L[4] = 2^44 is passed in as l4 to avoid array indexing in bit_vector
    assert(carry8 < (1u128 << 53)) by (bit_vector)
        requires
            limb8 < (1u128 << 104),
            n4 < (1u64 << 52),
            l4 == (1u64 << 44),
            carry7 < (1u128 << 56),
            sum8 == carry7 + limb8 + (n4 as u128) * (l4 as u128),
            carry8 == sum8 >> 52,
    ;

    // Convert to pow2 for the postcondition
    lemma_u128_shift_is_pow2(53);
    assert(carry8 < pow2(53));
}

/// Post-subtraction lemma: Establishes the montgomery congruence
///
/// This lemma is called after the conditional subtraction and proves:
/// `result × R ≡ T (mod L)` (montgomery_congruent)
///
/// # Mathematical Proof
///
/// **Given** (preconditions):
/// 1. (Quotient): intermediate × R = T + N×L  (from Part 2)
/// 2. (Sub result): result = (intermediate - L) mod L
///
/// **Derivation**:
/// 1. result ≡ intermediate (mod L)           [from sub: (x - L) mod L ≡ x mod L]
/// 2. result × R ≡ intermediate × R (mod L)   [multiply by R]
/// 3. result × R ≡ T + N×L (mod L)            [substitute quotient]
/// 4. result × R ≡ T (mod L)                  [N×L ≡ 0 mod L]  ∎
pub(crate) proof fn lemma_montgomery_reduce_post_sub(
    limbs: &[u128; 9],
    intermediate: &Scalar52,
    result: &Scalar52,
    n: nat,  // N value from Part 1
)
    requires
// Sub's postcondition: result = (intermediate - L) mod L

        scalar52_to_nat(result) == (scalar52_to_nat(intermediate) as int - group_order() as int) % (
        group_order() as int),
        // Part 2 quotient result: intermediate × R = T + N×L
        scalar52_to_nat(intermediate) * montgomery_radix() == slice128_to_nat(limbs) + n
            * group_order(),
    ensures
        montgomery_congruent(result, limbs),
{
    let t = slice128_to_nat(limbs);
    let l = group_order();
    let r = montgomery_radix();
    let inter = scalar52_to_nat(intermediate);
    let res = scalar52_to_nat(result);

    // Goal: montgomery_congruent(result, limbs)
    //       i.e., (res * r) % l == t % l
    assert(montgomery_congruent(result, limbs)) by {
        // Step 1: result ≡ intermediate (mod L)
        // From sub: res = (inter - l) % l, so res % l == inter % l
        assert((res as int) % (l as int) == (inter as int) % (l as int)) by {
            // Subgoal 1a: (inter - l) % l == inter % l
            lemma_mod_sub_multiples_vanish(inter as int, l as int);

            // Subgoal 1b: res % l == res (mod idempotence via lemma_small_mod)
            // res = (inter - l) % l, and 0 <= res < l by lemma_mod_bound
            lemma_mod_bound((inter as int) - (l as int), l as int);
            // So res < l, meaning res % l == res
            lemma_small_mod(res, l);
            // Therefore: res % l == res == (inter - l) % l == inter % l
        }

        // Step 2: result × R ≡ intermediate × R (mod L)
        assert(((res * r) as int) % (l as int) == ((inter * r) as int) % (l as int)) by {
            // If a ≡ b (mod m), then a×c ≡ b×c (mod m)
            lemma_mul_factors_congruent_implies_products_congruent(
                r as int,
                res as int,
                inter as int,
                l as int,
            );
        }

        // Step 3: intermediate × R = T + N×L (from precondition)
        assert(inter * r == t + n * l);

        // Step 4: T + N×L ≡ T (mod L)
        assert(((t + n * l) as int) % (l as int) == (t as int) % (l as int)) by {
            // (a + k×m) % m == a % m
            lemma_mod_multiples_vanish(n as int, t as int, l as int);
        }

        // Combine: (res * r) % l == (inter * r) % l == (t + n*l) % l == t % l
        assert((res * r) % l == t % l);
    }
}

// =============================================================================
// REDC Bound: intermediate < 2L
// =============================================================================
/// Proves r4 < 2^52 + L[4] and intermediate < 2L from the quotient relationship.
///
/// # Proof Strategy
///
/// ```text
/// N < R, T < R×L  ⟹  T + N×L < 2R×L
///                  ⟹  intermediate = (T + N×L)/R < 2L
///                  ⟹  r4 ≤ inter/2^208 ≤ 2L/2^208 = 2^45
///                  ⟹  r4 < 2^52 + L[4]
/// ```
pub(crate) proof fn lemma_r4_bound_from_canonical(
    limbs: &[u128; 9],
    r0: u64,
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
    n: nat,  // Montgomery adjustment factor from Part 1
)
    requires
        montgomery_reduce_canonical_bound(limbs),
        // N < R (from Part 1: each n_i < 2^52, so N < 2^260)
        n < montgomery_radix(),
        // Quotient relationship from Part 2: intermediate × R = T + N×L
        ({
            let inter = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat)
                * pow2(156) + (r4 as nat) * pow2(208);
            inter * montgomery_radix() == slice128_to_nat(limbs) + n * group_order()
        }),
    ensures
        (r4 as nat) < pow2(52) + (constants::L.limbs[4] as nat),
        ({
            let inter = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat)
                * pow2(156) + (r4 as nat) * pow2(208);
            inter < 2 * group_order()
        }),
{
    let t = slice128_to_nat(limbs);
    let r = montgomery_radix();
    let l = group_order();
    let inter = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat) * pow2(
        156,
    ) + (r4 as nat) * pow2(208);
    let two_l = 2 * group_order();
    let l4 = constants::L.limbs[4] as nat;

    // Subgoal 1: inter < 2L (direct REDC proof — no spec functions needed)
    assert(inter < two_l) by {
        let sum = t + n * l;
        // inter * R == sum (from precondition)
        assert(inter * r == sum);

        // N×L < R×L (since N < R and L > 0)
        assert(n * l < r * l) by {
            assert(l > 0) by {
                assert(l == pow2(252) + 27742317777372353535851937790883648493);
            }
            lemma_mul_strict_inequality(n as int, r as int, l as int);
        }

        // sum = T + N×L < R×L + R×L = 2×R×L
        assert(sum < 2 * r * l) by {
            lemma_mul_is_distributive_add_other_way((r * l) as int, 1, 1);
            lemma_mul_is_associative(2, r as int, l as int);
        }

        // inter = sum / R < 2L
        // Since inter * R == sum, we have inter == sum / R
        lemma_pow2_pos(260);
        lemma_div_by_multiple(inter as int, r as int);
        // Rewrite 2×R×L as R×(2×L) for lemma_div_strictly_bounded
        lemma_mul_is_commutative(2, r as int);
        lemma_mul_is_associative(r as int, 2, l as int);
        lemma_div_strictly_bounded(sum as int, r as int, (2 * l) as int);
    }

    // Subgoal 2: r4 <= 2L / 2^208
    let two_l_div = two_l / pow2(208);
    assert((r4 as nat) <= two_l_div) by {
        lemma_pow2_pos(208);

        // r4 * 2^208 <= inter (lower limbs are non-negative)
        let lower = (r0 as nat) + (r1 as nat) * pow2(52) + (r2 as nat) * pow2(104) + (r3 as nat)
            * pow2(156);
        assert((r4 as nat) * pow2(208) <= inter);

        // r4 <= inter / 2^208
        lemma_mul_le_implies_div_le(r4 as nat, pow2(208), inter);

        // inter < two_l implies inter / 2^208 <= two_l / 2^208
        lemma_div_is_ordered(inter as int, two_l as int, pow2(208) as int);
    }

    // Subgoal 3: r4 < 2^52 + L[4]
    assert((r4 as nat) < pow2(52) + l4) by {
        // 2L / 2^208 == 2^45 (fully proven)
        lemma_two_l_div_pow2_208_eq_pow2_45();
        assert((r4 as nat) <= pow2(45));

        // L[4] == 2^44
        lemma_l_limb4_is_pow2_44();

        // 2^45 + 1 < 2^52 + 2^44 (bit arithmetic)
        lemma_u64_shift_is_pow2(44);
        lemma_u64_shift_is_pow2(45);
        lemma_u64_shift_is_pow2(52);
        assert((1u64 << 45) + 1 < (1u64 << 52) + (1u64 << 44)) by (bit_vector);
    }
}

} // verus!
