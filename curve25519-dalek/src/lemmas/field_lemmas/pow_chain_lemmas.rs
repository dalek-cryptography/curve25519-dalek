//! Helper lemmas for proving exponentiation chains like x^(2^k-1)
//!
//! These lemmas capture the repeated proof patterns in pow22501 and similar
//! exponentiation proofs. They eliminate duplication by providing reusable
//! proof components that can be instantiated with different parameters.
//!
//! ## Main Lemmas
//!
//! - `lemma_prove_pow2k_step`: Proves (x^(2^m-1))^(2^k) = x^((2^m-1)*2^k)
//! - `lemma_prove_geometric_mul_step`: Proves x^((2^m-1)*2^n) * x^(2^n-1) = x^(2^(m+n)-1)
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
use crate::specs::field_specs_u64::*;

verus! {

pub proof fn lemma_prove_pow2k_step(
    base: int,
    val_in: nat,
    val_out: nat,
    exp_in: nat,
    exp_power: nat,
)
    requires
        base >= 0,
        p() > 0,
        exp_power > 0,
        val_in % p() == pow(base, exp_in) as nat % p(),
        val_out % p() == pow(val_in as int, exp_power) as nat % p(),
    ensures
        val_out % p() == pow(base, (exp_in * exp_power) as nat) as nat % p(),
{
    // Prove pow(base, exp_in) >= 0 to bridge nat and int modulo
    assert(pow(base, exp_in) >= 0) by {
        lemma_pow_nonnegative(base, exp_in);
    }

    // Use power congruence: if a ≡ b (mod p), then a^n ≡ b^n (mod p)
    assert(val_in as int % (p() as int) == pow(base, exp_in) % (p() as int));
    assert((pow(val_in as int, exp_power) % (p() as int)) as nat == (pow(
        pow(base, exp_in),
        exp_power,
    ) % (p() as int)) as nat) by {
        lemma_pow_mod_congruent(val_in as int, pow(base, exp_in), exp_power, p() as int);
    }

    // Apply power-of-power rule: (x^a)^b = x^(a*b)
    assert(pow(pow(base, exp_in), exp_power) == pow(base, exp_in * exp_power)) by {
        lemma_pow_multiplies(base, exp_in, exp_power);
    }

    // Prove pow(base, exp_in * exp_power) >= 0
    assert(pow(base, exp_in * exp_power) >= 0) by {
        lemma_pow_nonnegative(base, exp_in * exp_power);
    }

    // Prove pow(val_in as int, exp_power) >= 0 to bridge the conversion
    assert(pow(val_in as int, exp_power) >= 0) by {
        if val_in > 0 {
            lemma_pow_positive(val_in as int, exp_power);
        } else {
            // val_in == 0, so pow(0, exp_power) == 0
            lemma0_pow(exp_power);
        }
    }

    // Chain the equalities to prove the postcondition
    // val_out % p() == pow(val_in as int, exp_power) as nat % p() (from precondition)
    // Now we can convert: pow(val_in as int, exp_power) as nat % p() == (pow(val_in as int, exp_power) % (p() as int)) as nat
    assert(val_out % p() == (pow(val_in as int, exp_power) % (p() as int)) as nat);

    // (pow(val_in as int, exp_power) % (p() as int)) as nat == (pow(pow(base, exp_in), exp_power) % (p() as int)) as nat (proved above)
    // pow(pow(base, exp_in), exp_power) == pow(base, exp_in * exp_power) (proved above)
    // Therefore: (pow(base, exp_in * exp_power) % (p() as int)) as nat == pow(base, (exp_in * exp_power) as nat) as nat % p()

    assert((pow(base, exp_in * exp_power) % (p() as int)) as nat == pow(
        base,
        (exp_in * exp_power) as nat,
    ) as nat % p());
    assert(val_out % p() == pow(base, (exp_in * exp_power) as nat) as nat % p());
}

pub proof fn lemma_prove_geometric_mul_step(
    base: int,
    val_a: nat,
    val_b: nat,
    val_result: nat,
    exp_a: nat,
    exp_b: nat,
)
    requires
        base >= 0,
        p() > 0,
        val_a % p() == pow(base, exp_a) as nat % p(),
        val_b % p() == pow(base, exp_b) as nat % p(),
        val_result % p() == (val_a * val_b) % p(),
    ensures
        val_result % p() == pow(base, (exp_a + exp_b) as nat) as nat % p(),
{
    // Prove pow(base, exp_a) >= 0 and pow(base, exp_b) >= 0
    assert(pow(base, exp_a) >= 0) by {
        lemma_pow_nonnegative(base, exp_a);
    }
    assert(pow(base, exp_b) >= 0) by {
        lemma_pow_nonnegative(base, exp_b);
    }

    // Use modular multiplication property
    assert(val_result % p() == ((val_a % p()) * (val_b % p())) % p()) by {
        lemma_mul_mod_noop_general(val_a as int, val_b as int, p() as int);
    }

    // Substitute known values
    assert(val_result % p() == ((pow(base, exp_a) as nat % p()) * (pow(base, exp_b) as nat % p()))
        % p());

    // Remove inner mods
    assert(val_result % p() == (pow(base, exp_a) as nat * pow(base, exp_b) as nat) % p()) by {
        lemma_mul_mod_noop_general(
            pow(base, exp_a) as nat as int,
            pow(base, exp_b) as nat as int,
            p() as int,
        );
    }

    // Apply power addition rule: x^a * x^b = x^(a+b)
    assert(pow(base, exp_a) * pow(base, exp_b) == pow(base, exp_a + exp_b)) by {
        lemma_pow_adds(base, exp_a, exp_b);
    }

    // Prove pow(base, exp_a + exp_b) >= 0
    assert(pow(base, exp_a + exp_b) >= 0) by {
        lemma_pow_nonnegative(base, exp_a + exp_b);
    }

    // Chain the equalities to prove the postcondition
    // val_result % p() == (val_a * val_b) % p() (from precondition)
    // We proved: val_result % p() == (pow(base, exp_a) as nat * pow(base, exp_b) as nat) % p()
    // We proved: pow(base, exp_a) * pow(base, exp_b) == pow(base, exp_a + exp_b)
    // Therefore: val_result % p() == pow(base, (exp_a + exp_b) as nat) as nat % p()

    assert((pow(base, exp_a + exp_b) % (p() as int)) as nat == pow(
        base,
        (exp_a + exp_b) as nat,
    ) as nat % p());
    assert(val_result % p() == (pow(base, exp_a) as nat * pow(base, exp_b) as nat) % p());
    assert((pow(base, exp_a) as nat * pow(base, exp_b) as nat) == (pow(base, exp_a) * pow(
        base,
        exp_b,
    )) as nat);
    assert(val_result % p() == pow(base, (exp_a + exp_b) as nat) as nat % p());
}

} // verus!
