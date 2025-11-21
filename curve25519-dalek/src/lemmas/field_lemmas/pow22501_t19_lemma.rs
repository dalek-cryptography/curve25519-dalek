//! Lemma for proving t19 = x^(2^250-1) in pow22501
//!
//! This lemma proves the complete exponentiation chain in pow22501:
//! Starting from x^11 (t3), we compute through a series of squaring and multiplication
//! operations to reach x^(2^250-1) (t19).
//!
//! The computation follows a pattern of building larger exponents:
//! - t4 = x^22         (square of t3)
//! - t5 = x^31         (= x^(2^5-1))
//! - t7 = x^(2^10-1)
//! - t9 = x^(2^20-1)
//! - t11 = x^(2^40-1)
//! - t13 = x^(2^50-1)
//! - t15 = x^(2^100-1)
//! - t17 = x^(2^200-1)
//! - t19 = x^(2^250-1)
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

/// Proves that t19 = x^(2^250-1) given the complete computation chain from pow22501
///
/// # Arguments
/// * `self_limbs` - The base value x
/// * `t0_limbs` - x^2
/// * `t1_limbs` - x^8
/// * `t2_limbs` - x^9
/// * `t3_limbs` - x^11
/// * `t4_limbs` - x^22 (result of t3.square())
/// * `t5_limbs` - x^31 = x^(2^5-1) (result of t2 * t4)
/// * `t6_limbs` - x^((2^5-1)*2^5) (result of t5.pow2k(5))
/// * `t7_limbs` - x^(2^10-1) (result of t6 * t5)
/// * `t8_limbs` - x^((2^10-1)*2^10) (result of t7.pow2k(10))
/// * `t9_limbs` - x^(2^20-1) (result of t8 * t7)
/// * `t10_limbs` - x^((2^20-1)*2^20) (result of t9.pow2k(20))
/// * `t11_limbs` - x^(2^40-1) (result of t10 * t9)
/// * `t12_limbs` - x^((2^40-1)*2^10) (result of t11.pow2k(10))
/// * `t13_limbs` - x^(2^50-1) (result of t12 * t7)
/// * `t14_limbs` - x^((2^50-1)*2^50) (result of t13.pow2k(50))
/// * `t15_limbs` - x^(2^100-1) (result of t14 * t13)
/// * `t16_limbs` - x^((2^100-1)*2^100) (result of t15.pow2k(100))
/// * `t17_limbs` - x^(2^200-1) (result of t16 * t15)
/// * `t18_limbs` - x^((2^200-1)*2^50) (result of t17.pow2k(50))
/// * `t19_limbs` - x^(2^250-1) (result of t18 * t13)
///
/// # Preconditions
/// * Limbs are properly bounded (< 2^54)
/// * Each step follows the correct field operation postconditions
/// * t0, t1, t2, t3 satisfy the t3 checkpoint properties
///
/// # Postconditions
/// * u64_5_as_nat(t19_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, (pow2(250) - 1) as nat) as nat % p()
/// * Also proves all intermediate values through the chain
pub proof fn lemma_pow22501_prove_t19(
    self_limbs: [u64; 5],
    t0_limbs: [u64; 5],
    t1_limbs: [u64; 5],
    t2_limbs: [u64; 5],
    t3_limbs: [u64; 5],
    t4_limbs: [u64; 5],
    t5_limbs: [u64; 5],
    t6_limbs: [u64; 5],
    t7_limbs: [u64; 5],
    t8_limbs: [u64; 5],
    t9_limbs: [u64; 5],
    t10_limbs: [u64; 5],
    t11_limbs: [u64; 5],
    t12_limbs: [u64; 5],
    t13_limbs: [u64; 5],
    t14_limbs: [u64; 5],
    t15_limbs: [u64; 5],
    t16_limbs: [u64; 5],
    t17_limbs: [u64; 5],
    t18_limbs: [u64; 5],
    t19_limbs: [u64; 5],
)
    requires
// Limbs are bounded

        forall|i: int| 0 <= i < 5 ==> self_limbs[i] < 1u64 << 54,
        // Already established by lemma_pow22501_prove_t3
        u64_5_as_nat(t2_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 9) as nat % p(),
        u64_5_as_nat(t3_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 11) as nat % p(),
        // Postconditions from square operations
        u64_5_as_nat(t0_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 2) as nat % p(),
        u64_5_as_nat(t1_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 8) as nat % p(),
        u64_5_as_nat(t4_limbs) % p() == pow(u64_5_as_nat(t3_limbs) as int, 2) as nat % p(),
        // Postconditions from pow2k operations
        u64_5_as_nat(t6_limbs) % p() == pow(u64_5_as_nat(t5_limbs) as int, pow2(5)) as nat % p(),
        u64_5_as_nat(t8_limbs) % p() == pow(u64_5_as_nat(t7_limbs) as int, pow2(10)) as nat % p(),
        u64_5_as_nat(t10_limbs) % p() == pow(u64_5_as_nat(t9_limbs) as int, pow2(20)) as nat % p(),
        u64_5_as_nat(t12_limbs) % p() == pow(u64_5_as_nat(t11_limbs) as int, pow2(10)) as nat % p(),
        u64_5_as_nat(t14_limbs) % p() == pow(u64_5_as_nat(t13_limbs) as int, pow2(50)) as nat % p(),
        u64_5_as_nat(t16_limbs) % p() == pow(u64_5_as_nat(t15_limbs) as int, pow2(100)) as nat
            % p(),
        u64_5_as_nat(t18_limbs) % p() == pow(u64_5_as_nat(t17_limbs) as int, pow2(50)) as nat % p(),
        // Postconditions from mul operations
        u64_5_as_nat(t5_limbs) % p() == (u64_5_as_nat(t2_limbs) * u64_5_as_nat(t4_limbs)) % p(),
        u64_5_as_nat(t7_limbs) % p() == (u64_5_as_nat(t6_limbs) * u64_5_as_nat(t5_limbs)) % p(),
        u64_5_as_nat(t9_limbs) % p() == (u64_5_as_nat(t8_limbs) * u64_5_as_nat(t7_limbs)) % p(),
        u64_5_as_nat(t11_limbs) % p() == (u64_5_as_nat(t10_limbs) * u64_5_as_nat(t9_limbs)) % p(),
        u64_5_as_nat(t13_limbs) % p() == (u64_5_as_nat(t12_limbs) * u64_5_as_nat(t7_limbs)) % p(),
        u64_5_as_nat(t15_limbs) % p() == (u64_5_as_nat(t14_limbs) * u64_5_as_nat(t13_limbs)) % p(),
        u64_5_as_nat(t17_limbs) % p() == (u64_5_as_nat(t16_limbs) * u64_5_as_nat(t15_limbs)) % p(),
        u64_5_as_nat(t19_limbs) % p() == (u64_5_as_nat(t18_limbs) * u64_5_as_nat(t13_limbs)) % p(),
    ensures
        u64_5_as_nat(t19_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(250) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t2_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 9) as nat % p(),
        u64_5_as_nat(t3_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 11) as nat % p(),
        u64_5_as_nat(t4_limbs) % p() == pow(u64_5_as_nat(self_limbs) as int, 22) as nat % p(),
        u64_5_as_nat(t5_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(5) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t7_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(10) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t9_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(20) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t11_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(40) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t13_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(50) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t15_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(100) - 1) as nat,
        ) as nat % p(),
        u64_5_as_nat(t17_limbs) % p() == pow(
            u64_5_as_nat(self_limbs) as int,
            (pow2(200) - 1) as nat,
        ) as nat % p(),
{
    let base = u64_5_as_nat(self_limbs) as int;

    assert(p() > 0) by {
        pow255_gt_19();
    }

    // Establish that base >= 0, which makes all pow(base, n) >= 0
    assert(base >= 0);

    // t2 = x^9 and t3 = x^11 are already established as preconditions
    // (proven by lemma_pow22501_prove_t3 before calling this lemma)

    // ========================================================================
    // Establish non-negativity facts needed throughout the proof
    // ========================================================================

    // Prove pow(base, 9) >= 0 for use throughout the proof
    assert(pow(base, 9) >= 0) by {
        lemma_pow_nonnegative(base, 9);
    }

    // ========================================================================
    // Prove t4 = x^22
    // ========================================================================
    // t4 = t3^2 = (x^11)^2 = x^22

    // Establish pow(base, 11) >= 0 for use in subsequent proofs
    assert(pow(base, 11) >= 0) by {
        lemma_pow_nonnegative(base, 11);
    }

    let t3_val = u64_5_as_nat(t3_limbs) as int;
    assert(t3_val >= 0);
    assert(pow(t3_val, 2) >= 0) by {
        lemma_pow_nonnegative(t3_val, 2);
    }
    assert(pow(base, 22) >= 0) by {
        lemma_pow_nonnegative(base, 22);
    }

    assert((pow(u64_5_as_nat(t3_limbs) as int, 2) as nat) % p() == (pow(
        u64_5_as_nat(t3_limbs) as int,
        2,
    ) % (p() as int)) as nat);
    assert((pow(base, 22) as nat) % p() == (pow(base, 22) % (p() as int)) as nat);

    assert((pow(u64_5_as_nat(t3_limbs) as int, 2) % (p() as int)) as nat == (pow(pow(base, 11), 2)
        % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(u64_5_as_nat(t3_limbs) as int, pow(base, 11), 2, p() as int);
    }

    assert(pow(pow(base, 11), 2) == pow(base, 22)) by {
        lemma_pow_multiplies(base, 11, 2);
    }

    assert(u64_5_as_nat(t4_limbs) % p() == pow(base, 22) as nat % p());

    // ========================================================================
    // Prove t5 = x^31 = x^(2^5-1)
    // ========================================================================
    // t5 = t2 * t4 = x^9 * x^22 = x^31

    assert(u64_5_as_nat(t5_limbs) % p() == ((u64_5_as_nat(t2_limbs) % p()) * (u64_5_as_nat(t4_limbs)
        % p())) % p()) by {
        lemma_mul_mod_noop_general(
            u64_5_as_nat(t2_limbs) as int,
            u64_5_as_nat(t4_limbs) as int,
            p() as int,
        );
    }

    assert(u64_5_as_nat(t5_limbs) % p() == ((pow(base, 9) as nat % p()) * (pow(base, 22) as nat
        % p())) % p());

    assert(u64_5_as_nat(t5_limbs) % p() == (pow(base, 9) as nat * pow(base, 22) as nat) % p()) by {
        lemma_mul_mod_noop_general(
            pow(base, 9) as nat as int,
            pow(base, 22) as nat as int,
            p() as int,
        );
    }

    assert(pow(base, 9) * pow(base, 22) == pow(base, 31)) by {
        lemma_pow_adds(base, 9, 22);
    }

    assert(pow(base, 22) >= 0);  // known from earlier
    assert((pow(base, 9) * pow(base, 22)) >= 0) by {
        lemma_mul_nonnegative(pow(base, 9), pow(base, 22));
    }
    assert(pow(base, 9) as nat * pow(base, 22) as nat == (pow(base, 9) * pow(base, 22)) as nat);
    assert(pow(base, 9) as nat * pow(base, 22) as nat == pow(base, 31) as nat);

    assert(31 == pow2(5) - 1) by {
        lemma2_to64();
    }

    assert(u64_5_as_nat(t5_limbs) % p() == pow(base, (pow2(5) - 1) as nat) as nat % p());

    // ========================================================================
    // Prove t6 = x^((2^5-1)*2^5)
    // ========================================================================
    // t6 = t5.pow2k(5) = (x^(2^5-1))^(2^5)
    assert(pow2(5) > 0) by {
        lemma_pow2_pos(5);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t5_limbs),
        u64_5_as_nat(t6_limbs),
        (pow2(5) - 1) as nat,
        pow2(5),
    );

    // ========================================================================
    // Prove t7 = x^(2^10-1)
    // ========================================================================
    // t7 = t6 * t5 = x^((2^5-1)*2^5) * x^(2^5-1) = x^(2^10-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t6_limbs),
        u64_5_as_nat(t5_limbs),
        u64_5_as_nat(t7_limbs),
        ((pow2(5) - 1) * pow2(5)) as nat,
        (pow2(5) - 1) as nat,
    );
    lemma_pow2_geometric(5, 5);

    // ========================================================================
    // Prove t8 = x^((2^10-1)*2^10)
    // ========================================================================
    // t8 = t7.pow2k(10) = (x^(2^10-1))^(2^10)
    assert(pow2(10) > 0) by {
        lemma_pow2_pos(10);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t7_limbs),
        u64_5_as_nat(t8_limbs),
        (pow2(10) - 1) as nat,
        pow2(10),
    );

    // ========================================================================
    // Prove t9 = x^(2^20-1)
    // ========================================================================
    // t9 = t8 * t7 = x^((2^10-1)*2^10) * x^(2^10-1) = x^(2^20-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t8_limbs),
        u64_5_as_nat(t7_limbs),
        u64_5_as_nat(t9_limbs),
        ((pow2(10) - 1) * pow2(10)) as nat,
        (pow2(10) - 1) as nat,
    );
    lemma_pow2_geometric(10, 10);

    // ========================================================================
    // Prove t10 = x^((2^20-1)*2^20)
    // ========================================================================
    // t10 = t9.pow2k(20) = (x^(2^20-1))^(2^20)
    assert(pow2(20) > 0) by {
        lemma_pow2_pos(20);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t9_limbs),
        u64_5_as_nat(t10_limbs),
        (pow2(20) - 1) as nat,
        pow2(20),
    );

    // ========================================================================
    // Prove t11 = x^(2^40-1)
    // ========================================================================
    // t11 = t10 * t9 = x^((2^20-1)*2^20) * x^(2^20-1) = x^(2^40-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t10_limbs),
        u64_5_as_nat(t9_limbs),
        u64_5_as_nat(t11_limbs),
        ((pow2(20) - 1) * pow2(20)) as nat,
        (pow2(20) - 1) as nat,
    );
    lemma_pow2_geometric(20, 20);

    // ========================================================================
    // Prove t12 = x^((2^40-1)*2^10)
    // ========================================================================
    // t12 = t11.pow2k(10) = (x^(2^40-1))^(2^10)
    assert(pow2(10) > 0) by {
        lemma_pow2_pos(10);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t11_limbs),
        u64_5_as_nat(t12_limbs),
        (pow2(40) - 1) as nat,
        pow2(10),
    );

    // ========================================================================
    // Prove t13 = x^(2^50-1)
    // ========================================================================
    // t13 = t12 * t7 = x^((2^40-1)*2^10) * x^(2^10-1) = x^(2^50-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t12_limbs),
        u64_5_as_nat(t7_limbs),
        u64_5_as_nat(t13_limbs),
        ((pow2(40) - 1) * pow2(10)) as nat,
        (pow2(10) - 1) as nat,
    );
    lemma_pow2_geometric(40, 10);

    // ========================================================================
    // Prove t14 = x^((2^50-1)*2^50)
    // ========================================================================
    // t14 = t13.pow2k(50) = (x^(2^50-1))^(2^50)
    assert(pow2(50) > 0) by {
        lemma_pow2_pos(50);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t13_limbs),
        u64_5_as_nat(t14_limbs),
        (pow2(50) - 1) as nat,
        pow2(50),
    );

    // ========================================================================
    // Prove t15 = x^(2^100-1)
    // ========================================================================
    // t15 = t14 * t13 = x^((2^50-1)*2^50) * x^(2^50-1) = x^(2^100-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t14_limbs),
        u64_5_as_nat(t13_limbs),
        u64_5_as_nat(t15_limbs),
        ((pow2(50) - 1) * pow2(50)) as nat,
        (pow2(50) - 1) as nat,
    );
    lemma_pow2_geometric(50, 50);

    // ========================================================================
    // Prove t16 = x^((2^100-1)*2^100)
    // ========================================================================
    // t16 = t15.pow2k(100) = (x^(2^100-1))^(2^100)
    assert(pow2(100) > 0) by {
        lemma_pow2_pos(100);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t15_limbs),
        u64_5_as_nat(t16_limbs),
        (pow2(100) - 1) as nat,
        pow2(100),
    );

    // ========================================================================
    // Prove t17 = x^(2^200-1)
    // ========================================================================
    // t17 = t16 * t15 = x^((2^100-1)*2^100) * x^(2^100-1) = x^(2^200-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t16_limbs),
        u64_5_as_nat(t15_limbs),
        u64_5_as_nat(t17_limbs),
        ((pow2(100) - 1) * pow2(100)) as nat,
        (pow2(100) - 1) as nat,
    );
    lemma_pow2_geometric(100, 100);

    // ========================================================================
    // Prove t18 = x^((2^200-1)*2^50)
    // ========================================================================
    // t18 = t17.pow2k(50) = (x^(2^200-1))^(2^50)
    assert(pow2(50) > 0) by {
        lemma_pow2_pos(50);
    }
    lemma_prove_pow2k_step(
        base,
        u64_5_as_nat(t17_limbs),
        u64_5_as_nat(t18_limbs),
        (pow2(200) - 1) as nat,
        pow2(50),
    );

    // ========================================================================
    // Prove t19 = x^(2^250-1) - FINAL STEP
    // ========================================================================
    // t19 = t18 * t13 = x^((2^200-1)*2^50) * x^(2^50-1) = x^(2^250-1)
    lemma_prove_geometric_mul_step(
        base,
        u64_5_as_nat(t18_limbs),
        u64_5_as_nat(t13_limbs),
        u64_5_as_nat(t19_limbs),
        ((pow2(200) - 1) * pow2(50)) as nat,
        (pow2(50) - 1) as nat,
    );
    lemma_pow2_geometric(200, 50);
}

} // verus!
