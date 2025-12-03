//! Lemmas for proving the correctness of field inversion
//!
//! The inversion function computes self^(p-2) using Fermat's Little Theorem:
//! For a prime p and non-zero a: a^(p-1) ≡ 1 (mod p), therefore a^(p-2) is the inverse.
//!
//! The exponent p-2 = 2^255 - 21 is computed as:
//!   (2^250 - 1) * 2^5 + 11 = 2^255 - 32 + 11 = 2^255 - 21
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use crate::backend::serial::u64::field::*;
use crate::lemmas::common_lemmas::div_mod_lemmas::*;
use crate::lemmas::common_lemmas::pow_lemmas::*;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

/// Lemma: Lift pow2k postcondition from limb-level to field-level
///
/// This lemma derives a field-level postcondition from pow2k's limb-level postcondition.
/// It bridges the abstraction gap between u64_5_as_nat(limbs) and spec_field_element.
///
/// **Purpose**: pow2k gives us postconditions in terms of limbs, but we need them in terms
/// of field elements for higher-level reasoning.
///
/// **Strategy**: Since spec_field_element(x) = u64_5_as_nat(x.limbs) % p() by definition,
/// we use modular congruence properties to show that pow(limbs, k) ≡ pow(field_element, k) (mod p).
pub proof fn lemma_pow2k_to_field_element(fe: &FieldElement51, result: &FieldElement51, k: nat)
    requires
        k > 0,  // Required by lemma0_pow and lemma_pow_positive
        // From pow2k postcondition (limb-level):
        u64_5_as_nat(result.limbs) % p() == (pow(u64_5_as_nat(fe.limbs) as int, k) as nat) % p(),
    ensures
// Derived field-level postcondition:

        spec_field_element(result) == (pow(spec_field_element(fe) as int, k) as nat) % p(),
{
    // Key insight: Both sides are already "% p()" by definition
    // - spec_field_element(result) = u64_5_as_nat(result.limbs) % p()  (by definition)
    // - spec_field_element(fe) = u64_5_as_nat(fe.limbs) % p()          (by definition)
    assert(p() > 0) by {
        pow255_gt_19();
    }

    // From requires: u64_5_as_nat(result.limbs) % p() == (pow(u64_5_as_nat(fe.limbs), k) as nat) % p()
    // By definition: spec_field_element(result) == u64_5_as_nat(result.limbs) % p()
    // Therefore: spec_field_element(result) == (pow(u64_5_as_nat(fe.limbs), k) as nat) % p()
    assert(spec_field_element(result) == (pow(u64_5_as_nat(fe.limbs) as int, k) as nat) % p());

    // Show that pow(spec_field_element(fe), k) % p() == pow(u64_5_as_nat(fe.limbs), k) % p()
    // This follows from lemma_pow_mod_noop: pow(b % m, e) % m == pow(b, e) % m
    assert(pow(spec_field_element(fe) as int, k) % (p() as int) == pow(
        u64_5_as_nat(fe.limbs) as int,
        k,
    ) % (p() as int)) by {
        lemma_pow_mod_noop(u64_5_as_nat(fe.limbs) as int, k, p() as int);
    }

    // Prove pow results are non-negative to justify int-to-nat casts
    assert(pow(u64_5_as_nat(fe.limbs) as int, k) >= 0) by {
        lemma_pow_nonnegative(u64_5_as_nat(fe.limbs) as int, k);
    }

    assert(pow(spec_field_element(fe) as int, k) >= 0) by {
        lemma_pow_nonnegative(spec_field_element(fe) as int, k);
    }

    // Complete the chain:
    // spec_field_element(result) == (pow(u64_5_as_nat(fe.limbs), k) as nat) % p()  (proven above)
    // pow(spec_field_element(fe), k) % p() == pow(u64_5_as_nat(fe.limbs), k) % p()  (proven above)
    // Both powers are non-negative, so int % and nat % give the same result
    // Therefore: spec_field_element(result) == (pow(spec_field_element(fe), k) as nat) % p() ✅
}

/// Lemma: When the input is zero, the invert result is zero
///
/// Strategy: Show that 0^11 = 0, therefore t3 = 0, therefore t21 = t20 * 0 = 0
pub proof fn lemma_invert_zero_case(
    self_fe: &FieldElement51,
    t3: &FieldElement51,
    t20: &FieldElement51,
    t21: &FieldElement51,
)
    requires
        spec_field_element(self_fe) == 0,
        // From pow22501 postcondition
        spec_field_element(t3) == (pow(spec_field_element(self_fe) as int, 11) as nat) % p(),
        // From mul postcondition
        spec_field_element(t21) == math_field_mul(spec_field_element(t20), spec_field_element(t3)),
    ensures
        spec_field_element(t21) == 0,
{
    assert(0nat % p() == 0) by {
        pow255_gt_19();  // Proves p() > 0 (since p = 2^255 - 19)
        lemma_mod_is_mod_recursive(0, p() as int);
    }

    // From requires: spec_field_element(t3) == (pow(0, 11) as nat) % p() == 0
    assert(spec_field_element(t3) == 0) by {
        assert(pow(0int, 11) == 0) by {
            lemma0_pow(11);  // vstd lemma: proves 0^k = 0 for k > 0
        }
    }

    // From mul postcondition: t21 = t20 * t3 = t20 * 0 = 0
    assert(spec_field_element(t21) == 0) by {
        assert(spec_field_element(t21) == math_field_mul(spec_field_element(t20), 0));
        assert((spec_field_element(t20) * 0) == 0);
    }
}

/// Lemma: Arithmetic fact about the exponent decomposition
///
/// Shows that: (2^250 - 1) * 2^5 + 11 = 2^255 - 21 = p - 2
/// where p = 2^255 - 19
pub proof fn lemma_invert_exponent_arithmetic()
    ensures
        (pow2(250) - 1) * pow2(5) == pow2(255) - 32,
        pow2(255) - 21 == p() - 2,
{
    assert((pow2(250) - 1) * pow2(5) == pow2(255) - 32) by {
        assert(pow2(250) * pow2(5) == pow2(255)) by {
            lemma_pow2_adds(250, 5);
        };
        assert(pow2(5) == 32) by {
            lemma2_to64();
        };
    }

    assert(pow2(255) - 21 == p() - 2) by {
        pow255_gt_19();
    }
}

/// Lemma: Connect field element postconditions to power expressions
///
/// This lemma bridges the gap between the postconditions from pow2k and mul
/// to the explicit power expression form needed for the inversion proof.
///
/// It establishes:
/// 1. t20 = x^(2^255 - 32) mod p (by chaining lifting, composition, and arithmetic lemmas)
/// 2. t21 = (x^(2^255 - 32) mod p * x^11 mod p) mod p (by expanding mul and substituting)
pub proof fn lemma_invert_power_chain(
    self_fe: &FieldElement51,
    t19: &FieldElement51,
    t20: &FieldElement51,
    t3: &FieldElement51,
    t21: &FieldElement51,
)
    requires
// From pow22501 postcondition

        spec_field_element(t19) == (pow(
            spec_field_element(self_fe) as int,
            (pow2(250) - 1) as nat,
        ) as nat) % p(),
        spec_field_element(t3) == (pow(spec_field_element(self_fe) as int, 11) as nat) % p(),
        // From pow2k postcondition (using limb-level form as provided by pow2k)
        u64_5_as_nat(t20.limbs) % p() == (pow(u64_5_as_nat(t19.limbs) as int, pow2(5)) as nat)
            % p(),
        // From mul postcondition
        spec_field_element(t21) == math_field_mul(spec_field_element(t20), spec_field_element(t3)),
    ensures
// Power expression form for t20

        spec_field_element(t20) == (pow(
            spec_field_element(self_fe) as int,
            (pow2(255) - 32) as nat,
        ) as nat) % p(),
        // Simple form for t21 using math_field_mul expansion
        spec_field_element(t21) == (spec_field_element(t20) * spec_field_element(t3)) % p(),
{
    // PART 1: Establish spec_field_element(t20) through the chain of lemmas
    // Chain: spec_field_element(t20) [lifting lemma]
    //     == (pow(spec_field_element(t19), 2^5) as nat) % p() [composition lemma]
    //     == (pow(x, (2^250 - 1) * 2^5) as nat) % p() [arithmetic]
    //     == (pow(x, 2^255 - 32) as nat) % p()
    // Step 1: Lift from limb-level to field-level using the lifting lemma
    assert(spec_field_element(t20) == (pow(spec_field_element(t19) as int, pow2(5)) as nat) % p())
        by {
        // pow2(5) > 0, required by the lifting lemma
        assert(pow2(5) > 0) by {
            lemma_pow2_pos(5);
        }
        // The lifting lemma derives field-level postcondition from pow2k's limb-level postcondition
        lemma_pow2k_to_field_element(t19, t20, pow2(5) as nat);
    }

    // Step 2: Apply composition lemma to combine powers
    let x = spec_field_element(self_fe);
    assert((pow(spec_field_element(t19) as int, pow2(5)) as nat) % p() == (pow(
        x as int,
        ((pow2(250) - 1) * pow2(5)) as nat,
    ) as nat) % p()) by {
        // Establish preconditions for the composition lemma
        assert((pow2(250) - 1) > 0) by {
            lemma_pow2_pos(250);
            assert(pow2(250) > 1) by {
                lemma2_to64();
                lemma_pow2_strictly_increases(0, 250);
            }
        }
        assert(pow2(5) > 0) by {
            lemma_pow2_pos(5);
        }
        assert(p() > 0) by {
            pow255_gt_19();
        }

        // Apply the composition lemma
        lemma_pow_mod_composition(x, (pow2(250) - 1) as nat, pow2(5) as nat, p());
    }

    // Step 3: Use arithmetic fact: (2^250 - 1) * 2^5 = 2^255 - 32
    assert((pow(x as int, ((pow2(250) - 1) * pow2(5)) as nat) as nat) % p() == (pow(
        x as int,
        (pow2(255) - 32) as nat,
    ) as nat) % p()) by {
        assert((pow2(250) - 1) * pow2(5) == pow2(255) - 32) by {
            lemma_invert_exponent_arithmetic();
        };
    }
}

/// Helper lemma: Multiplying x^(p-2) by x yields x^(p-1)
///
/// Proves that (x^(p-2) * x) % p = x^(p-1) % p in modular arithmetic.
/// This is a key step in applying Fermat's Little Theorem.
pub proof fn lemma_multiply_by_base_power_addition(
    x: nat,
    self_fe: &FieldElement51,
    t21: &FieldElement51,
)
    requires
        x == spec_field_element(self_fe),
        spec_field_element(t21) == (pow(x as int, (p() - 2) as nat) as nat) % p(),
    ensures
        (spec_field_element(t21) * x) % p() == (pow(x as int, (p() - 1) as nat) as nat) % p(),
{
    // First, show that x == (pow(x, 1) as nat) % p()
    // This holds because x = spec_field_element(self_fe) is already reduced: x < p()
    assert(x == (pow(x as int, 1) as nat) % p()) by {
        // pow(x, 1) = x
        assert(pow(x as int, 1) == x) by {
            lemma_pow1(x as int);
        }

        // Since x < p() (from spec_field_element definition), we have x % p() = x
        assert(x < p()) by {
            // spec_field_element(fe) = spec_field_element_as_nat(fe) % p()
            // By the fundamental property of modulo, any value n % m is in the range [0, m)
            assert(p() > 0) by {
                pow255_gt_19();
            }
            lemma_mod_bound(spec_field_element_as_nat(self_fe) as int, p() as int);
        }

        // For any n < m, we have n % m = n
        assert(x % p() == x) by {
            lemma_small_mod(x, p());
        }
    }

    // Prove p() > 2 (required for valid exponent p-2)
    assert(p() > 2) by {
        p_gt_2();
    }

    // Apply modular power addition: (x^(p-2) % p) * (x^1 % p) % p == x^(p-1) % p
    assert((spec_field_element(t21) * x) % p() == (pow(x as int, (p() - 1) as nat) as nat) % p())
        by {
        // spec_field_element(t21) == (pow(x, p-2) as nat) % p() (from requires)
        // x == (pow(x, 1) as nat) % p() (proven above)
        // Therefore: t21 * x == ((pow(x, p-2) as nat) % p()) * ((pow(x, 1) as nat) % p())
        // Simplify the exponent: (p - 2) + 1 = p - 1
        assert(((p() - 2) + 1) as nat == (p() - 1) as nat);

        // Apply lemma_modular_power_addition
        lemma_modular_power_addition(x, (p() - 2) as nat, 1, p());
    }
}

/// Lemma: The computed value is the multiplicative inverse (non-zero case)
///
/// Uses Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p) for non-zero a
/// Therefore: a^(p-2) * a ≡ 1 (mod p)
pub proof fn lemma_invert_is_multiplicative_inverse(
    self_fe: &FieldElement51,
    t19: &FieldElement51,
    t20: &FieldElement51,
    t3: &FieldElement51,
    t21: &FieldElement51,
)
    requires
        spec_field_element(self_fe) != 0,
        // From pow22501 postcondition
        spec_field_element(t19) == (pow(
            spec_field_element(self_fe) as int,
            (pow2(250) - 1) as nat,
        ) as nat) % p(),
        spec_field_element(t3) == (pow(spec_field_element(self_fe) as int, 11) as nat) % p(),
        // From pow2k postcondition (using u64_5_as_nat form as that's what pow2k provides)
        u64_5_as_nat(t20.limbs) % p() == (pow(u64_5_as_nat(t19.limbs) as int, pow2(5)) as nat)
            % p(),
        // From mul postcondition
        spec_field_element(t21) == math_field_mul(spec_field_element(t20), spec_field_element(t3)),
    ensures
        (spec_field_element(t21) * spec_field_element(self_fe)) % p() == 1,
{
    let x = spec_field_element(self_fe);

    // ========================================================================
    // PART 1: Prove the exponent chain - show that t21 = x^(p-2) mod p
    // ========================================================================

    // Step 1: Establish that t21 = x^(2^255 - 21) % p by composing the power operations
    let pow_exp_t20 = (pow(x as int, (pow2(255) - 32) as nat) as nat) % p();
    let pow_exp_t3 = (pow(x as int, 11) as nat) % p();

    // Show that t21 = (x^(2^255 - 32) * x^11) % p = x^(2^255 - 21) % p
    assert(spec_field_element(t21) == (pow(x as int, (pow2(255) - 21) as nat) as nat) % p()) by {
        // First, express t21 as product of powers
        assert(spec_field_element(t21) == (pow_exp_t20 * pow_exp_t3) % p()) by {
            lemma_invert_power_chain(self_fe, t19, t20, t3, t21);
        }

        // Prove precondition: (2^255 - 32) > 0
        assert((pow2(255) - 32) > 0) by {
            assert(pow2(5) == 32) by {
                lemma2_to64();
            }
            lemma_pow2_strictly_increases(5, 255);
        }

        // Apply power addition: (x^a % p) * (x^b % p) % p = x^(a+b) % p
        // This gives us: t21 = x^((2^255 - 32) + 11) % p
        assert(spec_field_element(t21) == (pow(x as int, ((pow2(255) - 32) + 11) as nat) as nat)
            % p()) by {
            lemma_modular_power_addition(x, (pow2(255) - 32) as nat, 11, p());
        }

        // Simplify the exponent: (2^255 - 32) + 11 = 2^255 - 21
        assert(((pow2(255) - 32) + 11) as nat == (pow2(255) - 21) as nat);
    }

    // Step 2: Show that 2^255 - 21 = p - 2
    assert(spec_field_element(t21) == (pow(x as int, (p() - 2) as nat) as nat) % p()) by {
        // The exponent arithmetic lemma proves: 2^255 - 21 = p() - 2
        assert(pow2(255) - 21 == p() - 2) by {
            lemma_invert_exponent_arithmetic();
        }
    }

    // ========================================================================
    // PART 2: Apply Fermat's Little Theorem to prove (t21 * x) % p = 1
    // ========================================================================

    // We've shown: t21 = x^(p-2) % p
    // Now prove: (x^(p-2) * x) % p = x^(p-1) % p = 1

    // Step 1: Use power addition to get x^(p-1)
    assert((spec_field_element(t21) * x) % p() == (pow(x as int, (p() - 1) as nat) as nat) % p())
        by {
        lemma_multiply_by_base_power_addition(x, self_fe, t21);
    }

    // Step 2: Apply Fermat's Little Theorem: x^(p-1) ≡ 1 (mod p) for non-zero x
    assert((spec_field_element(t21) * x) % p() == 1) by {
        assert((pow(x as int, (p() - 1) as nat) as nat) % p() == 1) by {
            // Prove the precondition: x % p() != 0
            assert(x % p() != 0) by {
                // x < p() and x != 0, therefore x % p() = x != 0
                assert(x < p()) by {
                    assert(p() > 0) by {
                        pow255_gt_19();
                    }
                    lemma_mod_bound(spec_field_element_as_nat(self_fe) as int, p() as int);
                }

                assert(x % p() == x) by {
                    lemma_small_mod(x, p());
                }
            }

            // Apply Fermat's Little Theorem for p()
            lemma_fermat_for_p(x);
        }
    }
}

/// Lemma: The computed value equals math_field_inv
///
/// Shows that spec_field_element(t21) satisfies the definition of math_field_inv
pub proof fn lemma_invert_equals_math_field_inv(self_fe: &FieldElement51, t21: &FieldElement51)
    requires
// When x != 0, t21 is the multiplicative inverse

        spec_field_element(self_fe) != 0 ==> (spec_field_element(t21) * spec_field_element(self_fe))
            % p() == 1,
        // When x == 0, t21 is zero
        spec_field_element(self_fe) == 0 ==> spec_field_element(t21) == 0,
    ensures
        spec_field_element(t21) == math_field_inv(spec_field_element(self_fe)),
{
    let x = spec_field_element(self_fe);
    let t21_val = spec_field_element(t21);

    if x != 0 {
        // For non-zero x, prove that t21_val is the unique multiplicative inverse
        // by showing it satisfies the defining properties and using uniqueness
        // Establish that x is in the valid range and x % p() == x
        assert(x % p() == x) by {
            assert(x < p()) by {
                assert(p() > 0) by {
                    pow255_gt_19();
                }
                lemma_mod_bound(spec_field_element_as_nat(self_fe) as int, p() as int);
            }
            lemma_small_mod(x, p());
        }

        // Since x != 0 and x % p() == x, we have x % p() != 0
        assert(x % p() != 0);

        // Establish that t21_val is in the valid range
        assert(t21_val < p()) by {
            assert(p() > 0) by {
                pow255_gt_19();
            }
            lemma_mod_bound(spec_field_element_as_nat(t21) as int, p() as int);
        }

        // Show that t21_val satisfies the inverse property: ((x % p()) * t21_val) % p() == 1
        assert(((x % p()) * t21_val) % p() == 1) by {
            // From requires: (t21_val * x) % p() == 1
            // Since x % p() == x, we can substitute
            assert((x * t21_val) == (t21_val * x)) by (nonlinear_arith);
            assert(((x % p()) * t21_val) == (x * t21_val));
        }

        // Both t21_val and math_field_inv(x) satisfy:
        // 1. They are < p()
        // 2. ((x % p()) * w) % p() == 1
        // By uniqueness, they must be equal
        assert(t21_val == math_field_inv(x)) by {
            field_inv_property(x);
            field_inv_unique(x, t21_val);
        }
    } else {
        // For x == 0, show that both t21_val and math_field_inv(0) are 0
        assert(t21_val == math_field_inv(x)) by {
            // t21_val == 0 from requires (when x == 0)
            // math_field_inv(0) == 0 by convention
            assert(math_field_inv(0) == 0) by {
                field_inv_zero();
            }
        }
    }
}

/// Main lemma: Correctness of the invert implementation
///
/// Ties together all the smaller lemmas to prove the complete specification
pub proof fn lemma_invert_correctness(
    self_fe: &FieldElement51,
    t19: &FieldElement51,
    t3: &FieldElement51,
    t20: &FieldElement51,
    t21: &FieldElement51,
)
    requires
// Postconditions from pow22501

        spec_field_element(t19) == (pow(
            spec_field_element(self_fe) as int,
            (pow2(250) - 1) as nat,
        ) as nat) % p(),
        spec_field_element(t3) == (pow(spec_field_element(self_fe) as int, 11) as nat) % p(),
        // Postcondition from pow2k(5) - using the actual form from pow2k
        u64_5_as_nat(t20.limbs) % p() == (pow(u64_5_as_nat(t19.limbs) as int, pow2(5)) as nat)
            % p(),
        // Postcondition from mul
        spec_field_element(t21) == math_field_mul(spec_field_element(t20), spec_field_element(t3)),
    ensures
// If self is non-zero, t21 is the multiplicative inverse

        spec_field_element(self_fe) != 0 ==> (spec_field_element(t21) * spec_field_element(self_fe))
            % p() == 1,
        // If self is zero, t21 is zero
        spec_field_element(self_fe) == 0 ==> spec_field_element(t21) == 0,
        // t21 equals math_field_inv
        spec_field_element(t21) == math_field_inv(spec_field_element(self_fe)),
{
    // Case 1: When self is zero, prove that t21 is zero
    if spec_field_element(self_fe) == 0 {
        assert(spec_field_element(t21) == 0) by {
            lemma_invert_zero_case(self_fe, t3, t20, t21);
        }
    }
    // Case 2: When self is non-zero, prove that t21 is the multiplicative inverse

    if spec_field_element(self_fe) != 0 {
        assert((spec_field_element(t21) * spec_field_element(self_fe)) % p() == 1) by {
            lemma_invert_exponent_arithmetic();
            lemma_invert_is_multiplicative_inverse(self_fe, t19, t20, t3, t21);
        }
    }
    // Prove that t21 equals the mathematical field inverse

    assert(spec_field_element(t21) == math_field_inv(spec_field_element(self_fe))) by {
        lemma_invert_equals_math_field_inv(self_fe, t21);
    }
}

} // verus!
