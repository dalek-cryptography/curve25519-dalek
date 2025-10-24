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

pub open spec fn field_element_as_bytes(fe: &FieldElement51) -> Seq<u8> {
    // Step 1: Basic reduction to ensure h < 2*p
    let limbs = spec_reduce(fe.limbs);

    // Step 2: Compute q (quotient) to detect if limbs >= p
    // q = 0 if h < p, q = 1 if h >= p
    // This works because h >= p <==> h + 19 >= 2^255
    let q0 = ((limbs[0] + 19) as u64) >> 51;
    let q1 = ((limbs[1] + q0) as u64) >> 51;
    let q2 = ((limbs[2] + q1) as u64) >> 51;
    let q3 = ((limbs[3] + q2) as u64) >> 51;
    let q = ((limbs[4] + q3) as u64) >> 51;

    // Step 3: Compute r = h - pq = h + 19q - 2^255q
    // Add 19*q to limbs[0]
    let limbs0_adj = (limbs[0] + 19 * q) as u64;

    // Step 4: Propagate carries and mask to 51 bits (this subtracts 2^255q implicitly)
    let limbs1_adj = (limbs[1] + (limbs0_adj >> 51)) as u64;
    let limbs0_canon = (limbs0_adj & mask51) as u64;
    let limbs2_adj = (limbs[2] + (limbs1_adj >> 51)) as u64;
    let limbs1_canon = (limbs1_adj & mask51) as u64;
    let limbs3_adj = (limbs[3] + (limbs2_adj >> 51)) as u64;
    let limbs2_canon = (limbs2_adj & mask51) as u64;
    let limbs4_adj = (limbs[4] + (limbs3_adj >> 51)) as u64;
    let limbs3_canon = (limbs3_adj & mask51) as u64;
    // Discard carry from limbs[4], which subtracts 2^255q
    let limbs4_canon = (limbs4_adj & mask51) as u64;

    // Step 5: Pack canonical limbs into 32 bytes (little-endian)
    Seq::new(
        32,
        |i: int|
            if i == 0 {
                limbs0_canon as u8
            } else if i == 1 {
                (limbs0_canon >> 8) as u8
            } else if i == 2 {
                (limbs0_canon >> 16) as u8
            } else if i == 3 {
                (limbs0_canon >> 24) as u8
            } else if i == 4 {
                (limbs0_canon >> 32) as u8
            } else if i == 5 {
                (limbs0_canon >> 40) as u8
            } else if i == 6 {
                ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8
            } else if i == 7 {
                (limbs1_canon >> 5) as u8
            } else if i == 8 {
                (limbs1_canon >> 13) as u8
            } else if i == 9 {
                (limbs1_canon >> 21) as u8
            } else if i == 10 {
                (limbs1_canon >> 29) as u8
            } else if i == 11 {
                (limbs1_canon >> 37) as u8
            } else if i == 12 {
                ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8
            } else if i == 13 {
                (limbs2_canon >> 2) as u8
            } else if i == 14 {
                (limbs2_canon >> 10) as u8
            } else if i == 15 {
                (limbs2_canon >> 18) as u8
            } else if i == 16 {
                (limbs2_canon >> 26) as u8
            } else if i == 17 {
                (limbs2_canon >> 34) as u8
            } else if i == 18 {
                (limbs2_canon >> 42) as u8
            } else if i == 19 {
                ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8
            } else if i == 20 {
                (limbs3_canon >> 7) as u8
            } else if i == 21 {
                (limbs3_canon >> 15) as u8
            } else if i == 22 {
                (limbs3_canon >> 23) as u8
            } else if i == 23 {
                (limbs3_canon >> 31) as u8
            } else if i == 24 {
                (limbs3_canon >> 39) as u8
            } else if i == 25 {
                ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8
            } else if i == 26 {
                (limbs4_canon >> 4) as u8
            } else if i == 27 {
                (limbs4_canon >> 12) as u8
            } else if i == 28 {
                (limbs4_canon >> 20) as u8
            } else if i == 29 {
                (limbs4_canon >> 28) as u8
            } else if i == 30 {
                (limbs4_canon >> 36) as u8
            } else   /* i == 31 */
            {
                (limbs4_canon >> 44) as u8
            },
    )
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
