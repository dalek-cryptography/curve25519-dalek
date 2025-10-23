use crate::backend::serial::u64::field::FieldElement51;
use crate::backend::serial::u64::field_lemmas::field_core::*;
use crate::backend::serial::u64::subtle_assumes;
use crate::constants;
use subtle::Choice;

use vstd::prelude::*;

verus! {

pub open spec fn field_element_as_nat(fe: &FieldElement51) -> nat {
    as_nat(fe.limbs)
}

/// Spec-level view of FieldElement51::as_bytes()
/// Returns the canonical byte representation of the field element
/// VERIFICATION NOTE: placeholder implementation for now
pub open spec fn field_element_as_bytes(fe: &FieldElement51) -> Seq<u8> {
    Seq::new(32, |i: int| 0u8)
}

/// Spec function: two field elements are inverses if their product is 1 (mod p)
pub open spec fn is_inverse_field(a: &FieldElement51, b: &FieldElement51) -> bool {
    (field_element_as_nat(a) * field_element_as_nat(b)) % p() == 1
}

/// Spec function: field element is inverse of a natural number (mod p)
pub open spec fn is_inverse_field_of_nat(fe: &FieldElement51, n: nat) -> bool {
    (field_element_as_nat(fe) * n) % p() == 1
}

/// Spec function to compute product of all field elements in a sequence (mod p)
/// Returns the natural number representation
pub open spec fn product_of_fields(fields: Seq<FieldElement51>) -> nat
    decreases fields.len(),
{
    if fields.len() == 0 {
        1
    } else {
        (product_of_fields(fields.skip(1)) * field_element_as_nat(&fields[0])) % p()
    }
}

/// Spec function: b is a square root of a (mod p), i.e., b^2 = a (mod p)
pub open spec fn is_square_of(a: &FieldElement51, b: &FieldElement51) -> bool {
    (field_element_as_nat(b) * field_element_as_nat(b)) % p() == field_element_as_nat(a) % p()
}

/// Spec function: b^2 * v = u (mod p)
pub open spec fn is_sqrt_ratio(u: &FieldElement51, v: &FieldElement51, r: &FieldElement51) -> bool {
    (field_element_as_nat(r) * field_element_as_nat(r) * field_element_as_nat(v)) % p()
        == field_element_as_nat(u) % p()
}

// Square-ness mod p (spec-only).
pub open spec fn is_square_mod_p(a: nat) -> bool {
    exists|y: nat| (#[trigger] (y * y) % p()) == (a % p())
}

// Spec: there exists a modular inverse of v (when v != 0).
pub open spec fn has_inv_mod_p(v: nat) -> bool {
    v % p() != 0 ==> exists|w: nat| (#[trigger] (v * w) % p()) == 1
}

// Spec: witness-based inverse predicate (lets callers quantify the inverse).
pub open spec fn is_inv_witness(v: nat, w: nat) -> bool {
    ((v % p()) * (w % p())) % p() == 1
}

// Postcondition for FieldElement::sqrt_ratio_i(u, v).
pub(crate) open spec fn sqrt_ratio_i_post(
    u: &FieldElement51,
    v: &FieldElement51,
    choice: Choice,
    r: &FieldElement51,
) -> bool {
    let u_nat = field_element_as_nat(u) % p();
    let v_nat = field_element_as_nat(v) % p();
    let r_nat = field_element_as_nat(r) % p();
    let i_nat = field_element_as_nat(&constants::SQRT_M1) % p();

    // Case analysis exactly as in the docstring:
    // - (1, +sqrt(u/v)) if v != 0 and u/v is square
    // - (1, 0)          if u == 0
    // - (0, 0)          if v == 0 && u != 0
    // - (0, +sqrt(i*u/v)) otherwise
    if u_nat == 0 {
        // When u == 0, we return (1, 0)
        subtle_assumes::choice_is_true(choice) && r_nat == 0
    } else if v_nat == 0 {
        // When v == 0 and u != 0, we return (0, 0)
        !subtle_assumes::choice_is_true(choice) && r_nat == 0
    } else {
        // v != 0: reason via an inverse witness w with v*w == 1 (mod p)
        exists|w: nat|
            is_inv_witness(v_nat, w) && {
                let uv = (u_nat * w) % p();
                if is_square_mod_p(uv) {
                    // square branch: choice = 1 and r^2 == u/v
                    subtle_assumes::choice_is_true(choice) && ((r_nat * r_nat) % p() == uv)
                } else {
                    // nonsquare branch: choice = 0 and r^2 == i*u/v
                    !subtle_assumes::choice_is_true(choice) && ((r_nat * r_nat) % p() == (i_nat
                        * uv) % p())
                }
            }
    }
}

} // verus!
