#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use super::axioms::axiom_elligator_nonzero_intermediates;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::constants_lemmas::lemma_sqrt_ad_minus_one_nonzero;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::field_algebra_lemmas::lemma_nonzero_product;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;
use vstd::prelude::*;

verus! {

/// The Elligator completed point has nonzero Z and T denominators.
///
/// Z = N_t · √(ad−1) ≠ 0: N_t ≠ 0 (axiom) ∧ √(ad−1) ≠ 0 (proven)
///   ⟹ product ≠ 0 (no zero divisors in GF(p)).
/// T = 1 + s² ≠ 0: from axiom_elligator_nonzero_intermediates.
///
/// Reference: [RISTRETTO] section 4.3.4; Hamburg, "Decaf" section 4
/// Runtime validation: `test_elligator_nonzero_denominators` (200+ inputs)
pub proof fn lemma_elligator_nonzero_denominators(
    z_completed: nat,
    t_completed: nat,
    r_0: nat,
    s_nat: nat,
    n_t_nat: nat,
    d_val_nat: nat,
)
    requires
        s_nat < p(),
        n_t_nat < p(),
        t_completed == field_add(1, field_square(s_nat)),
        z_completed == field_mul(n_t_nat, spec_sqrt_ad_minus_one()),
        (s_nat, n_t_nat, d_val_nat) == elligator_intermediates(r_0),
    ensures
        z_completed != 0,
        t_completed != 0,
{
    assert(n_t_nat % p() != 0 && t_completed != 0) by {
        axiom_elligator_nonzero_intermediates(r_0, s_nat, n_t_nat, d_val_nat);
    };
    assert(z_completed != 0) by {
        lemma_sqrt_ad_minus_one_nonzero();
        lemma_nonzero_product(n_t_nat, spec_sqrt_ad_minus_one());
    };
}

} // verus!
