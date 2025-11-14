//! Lemma for proving pow_p58: x^(2^252-3)
//!
//! This lemma proves that pow_p58 correctly computes x^((p-5)/8) = x^(2^252-3).
//!
//! The computation is straightforward:
//! 1. Start with t19 = x^(2^250-1) from pow22501
//! 2. Square twice: t20 = t19^4 = x^(4*(2^250-1)) = x^(2^252-4)
//! 3. Multiply by x: t21 = x * t20 = x^(1 + 2^252-4) = x^(2^252-3)
//!
//! This proof uses helper lemmas from pow_chain_lemmas for conciseness.
//!
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::mul_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::lemmas::field_lemmas::pow_chain_lemmas::*;
use crate::specs::field_specs_u64::*;

verus! {

/// Proves that pow_p58 correctly computes x^(2^252-3)
///
/// # Arguments
/// * `self_limbs` - The base value x
/// * `t19_limbs` - x^(2^250-1) (from pow22501)
/// * `t20_limbs` - Result of t19.pow2k(2) = x^(2^252-4)
/// * `t21_limbs` - Result of self * t20 = x^(2^252-3)
///
/// # Preconditions
/// * t19 = x^(2^250-1) mod p
/// * t20 = t19^4 mod p (from pow2k(2))
/// * t21 = self * t20 mod p
///
/// # Postconditions
/// * as_nat(t21_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(252) - 3) as nat) % p()
pub proof fn lemma_pow_p58_prove(
    self_limbs: [u64; 5],
    t19_limbs: [u64; 5],
    t20_limbs: [u64; 5],
    t21_limbs: [u64; 5],
)
    requires
// t19 = x^(2^250-1) from pow22501

        as_nat(t19_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(250) - 1) as nat) as nat
            % p(),
        // t20 = t19^4 (from pow2k(2))
        as_nat(t20_limbs) % p() == pow(as_nat(t19_limbs) as int, pow2(2)) as nat % p(),
        // t21 = self * t20
        as_nat(t21_limbs) % p() == (as_nat(self_limbs) * as_nat(t20_limbs)) % p(),
    ensures
        as_nat(t21_limbs) % p() == pow(as_nat(self_limbs) as int, (pow2(252) - 3) as nat) as nat
            % p(),
{
    let base = as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    let exp_250_m1 = (pow2(250) - 1) as nat;
    let exp_252_m4 = (pow2(252) - 4) as nat;
    let exp_252_m3 = (pow2(252) - 3) as nat;

    // ========================================================================
    // Prove t20 = x^(2^252-4) using lemma_prove_pow2k_step
    // ========================================================================
    // t20 = t19^4 = (x^(2^250-1))^4 = x^(4*(2^250-1)) = x^(2^252-4)

    // First prove that 4 = pow2(2)
    assert(pow2(2) == 4) by {
        lemma2_to64();
    }

    // Prove the arithmetic: 4 * (2^250 - 1) = 2^252 - 4
    assert(exp_250_m1 * 4 == exp_252_m4) by {
        assert(pow2(252) == pow2(2) * pow2(250)) by {
            lemma_pow2_adds(2, 250);
        }
        assert(4 * pow2(250) == pow2(252));

        // Prove bounds needed for the cast
        assert(pow2(250) >= 1) by {
            lemma_pow2_pos(250);
        }
        assert(pow2(252) >= 4) by {
            lemma_pow2_pos(252);
            lemma_pow2_strictly_increases(2, 252);
        }

        // Use distributive property: 4 * (2^250 - 1) = 4 * 2^250 - 4 = 2^252 - 4
        let a_int = pow2(250) as int - 1;
        let b_int = pow2(252) as int - 4;

        assert(4 * a_int == b_int) by {
            lemma_mul_is_distributive_sub(4, pow2(250) as int, 1);
        }

        assert(a_int >= 0);
        assert(b_int >= 0);
        assert((4 * a_int) as nat == 4 * (a_int as nat));
        assert(exp_250_m1 == a_int as nat);
        assert(exp_252_m4 == b_int as nat);
    }

    // Apply the helper lemma
    assert(pow2(2) > 0) by {
        lemma_pow2_pos(2);
    }
    lemma_prove_pow2k_step(base, as_nat(t19_limbs), as_nat(t20_limbs), exp_250_m1, pow2(2));

    assert(as_nat(t20_limbs) % p() == pow(base, exp_252_m4) as nat % p());

    // ========================================================================
    // Prove t21 = x^(2^252-3) using lemma_prove_geometric_mul_step
    // ========================================================================
    // t21 = self * t20 = x^1 * x^(2^252-4) = x^(1 + 2^252-4) = x^(2^252-3)

    // Establish self = x^1
    assert(pow(base, 1) == base) by {
        lemma_pow1(base);
    }
    assert(pow(base, 1) as nat == as_nat(self_limbs));

    // Prove the arithmetic: 1 + (2^252 - 4) = 2^252 - 3
    assert(1 + exp_252_m4 == exp_252_m3) by {
        // Simple arithmetic: 1 + (n - 4) = n - 3 when n >= 4
        assert(pow2(252) >= 4) by {
            lemma_pow2_pos(252);
            lemma_pow2_strictly_increases(2, 252);
        }
        let n = pow2(252) as int;
        assert(1 + (n - 4) == n - 3);
        assert(exp_252_m4 == (n - 4) as nat);
        assert(exp_252_m3 == (n - 3) as nat);
    }

    // Apply the helper lemma
    lemma_prove_geometric_mul_step(
        base,
        as_nat(self_limbs),
        as_nat(t20_limbs),
        as_nat(t21_limbs),
        1,
        exp_252_m4,
    );

    assert(as_nat(t21_limbs) % p() == pow(base, exp_252_m3) as nat % p());
}

} // verus!
