#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

use vstd::prelude::*;

verus! {

/// Spec function for field addition: (a + b) mod p
pub open spec fn spec_field_add(a: &FieldElement51, b: &FieldElement51) -> nat {
    (field_element(a) + field_element(b)) % p()
}

/// Spec predicate: all limbs are bounded by a given bit limit
pub open spec fn limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe.limbs[i] < (1u64 << bit_limit)
}

/// Spec function: result of limb-wise addition (what add_spec returns)
pub open spec fn spec_add_limbs(a: &FieldElement51, b: &FieldElement51) -> FieldElement51 {
    FieldElement51 {
        limbs: [
            (a.limbs[0] + b.limbs[0]) as u64,
            (a.limbs[1] + b.limbs[1]) as u64,
            (a.limbs[2] + b.limbs[2]) as u64,
            (a.limbs[3] + b.limbs[3]) as u64,
            (a.limbs[4] + b.limbs[4]) as u64,
        ],
    }
}

/// Spec function: result of limb-wise subtraction with reduction (what sub_spec returns)
/// Adds multiples of p to avoid underflow, then reduces
pub open spec fn spec_sub_limbs(a: &FieldElement51, b: &FieldElement51) -> FieldElement51 {
    FieldElement51 {
        limbs: spec_reduce(
            [
                ((a.limbs[0] + 36028797018963664u64) - b.limbs[0]) as u64,
                ((a.limbs[1] + 36028797018963952u64) - b.limbs[1]) as u64,
                ((a.limbs[2] + 36028797018963952u64) - b.limbs[2]) as u64,
                ((a.limbs[3] + 36028797018963952u64) - b.limbs[3]) as u64,
                ((a.limbs[4] + 36028797018963952u64) - b.limbs[4]) as u64,
            ],
        ),
    }
}

pub open spec fn field_element_as_nat(fe: &FieldElement51) -> nat {
    as_nat(fe.limbs)
}

/// Returns the canonical mathematical value of a field element in [0, p)
/// where p = 2^255 - 19
pub open spec fn field_element(fe: &FieldElement51) -> nat {
    field_element_as_nat(fe) % p()
}

/// Returns the canonical mathematical value when creating a field element from bytes.
/// The bytes are interpreted as a little-endian integer with the high bit of byte[31] ignored.
/// The result is the canonical value in [0, p) where p = 2^255 - 19.
pub open spec fn field_element_from_bytes(bytes: &[u8; 32]) -> nat {
    (as_nat_32_u8(bytes) % pow2(255)) % p()
}

/// Spec function: Get the sign bit of a field element
/// In Curve25519, the sign bit is the least significant bit of the canonical representation
pub open spec fn field_element_sign_bit(fe: &FieldElement51) -> u8 {
    ((field_element(fe) % p()) % 2) as u8
}

// Spec-level field operations on natural numbers (mod p)
/// Spec-level field addition
pub open spec fn field_add(a: nat, b: nat) -> nat {
    (a + b) % p()
}

/// Spec-level field subtraction
pub open spec fn field_sub(a: nat, b: nat) -> nat {
    (((a % p()) + p()) - (b % p())) as nat % p()
}

/// Spec-level field multiplication
pub open spec fn field_mul(a: nat, b: nat) -> nat {
    (a * b) % p()
}

/// Spec-level field negation
pub open spec fn field_neg(a: nat) -> nat {
    (p() - (a % p())) as nat % p()
}

/// Spec-level field squaring
pub open spec fn field_square(a: nat) -> nat {
    (a * a) % p()
}

/// Spec-level field inversion: returns w such that (a * w) % p == 1
/// We use `choose` to pick the unique inverse that exists for non-zero field elements
pub open spec fn field_inv(a: nat) -> nat
    recommends
        a % p() != 0,
{
    choose|w: nat| w < p() && #[trigger] ((a % p()) * w) % p() == 1
}

/// Axiom: For non-zero field elements, the inverse exists and satisfies the inverse property
pub proof fn field_inv_axiom(a: nat)
    requires
        a % p() != 0,
    ensures
        field_inv(a) < p(),
        ((a % p()) * field_inv(a)) % p() == 1,
{
    admit();  // This would be proven from field theory or assumed as axiom
}

/// Spec function for FieldElement::from_bytes
/// Takes a 32-byte array and produces a FieldElement51
/// The high bit of byte[31] is ignored, giving a 255-bit value
pub open spec fn fe51_from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
    // Mimic the implementation in field_verus.rs:from_bytes
    // Load 8-byte chunks at specified offsets and mask to 51-bit limbs
    let low_51_bit_mask = mask51;

    FieldElement51 {
        limbs: [
        // load bits [  0, 64), mask to 51 bits

            (load8_at_spec(bytes, 0) as u64) & low_51_bit_mask,
            // load bits [ 48,112), shift right by 3, mask to 51 bits
            ((load8_at_spec(bytes, 6) as u64) >> 3) & low_51_bit_mask,
            // load bits [ 96,160), shift right by 6, mask to 51 bits
            ((load8_at_spec(bytes, 12) as u64) >> 6) & low_51_bit_mask,
            // load bits [152,216), shift right by 1, mask to 51 bits
            ((load8_at_spec(bytes, 19) as u64) >> 1) & low_51_bit_mask,
            // load bits [192,256), shift right by 12, mask to 51 bits (this ignores high bit)
            ((load8_at_spec(bytes, 24) as u64) >> 12) & low_51_bit_mask,
        ],
    }
}

pub open spec fn fe51_to_bytes(fe: &FieldElement51) -> Seq<u8> {
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
    seq![
        limbs0_canon as u8,
        (limbs0_canon >> 8) as u8,
        (limbs0_canon >> 16) as u8,
        (limbs0_canon >> 24) as u8,
        (limbs0_canon >> 32) as u8,
        (limbs0_canon >> 40) as u8,
        ((limbs0_canon >> 48) | (limbs1_canon << 3)) as u8,
        (limbs1_canon >> 5) as u8,
        (limbs1_canon >> 13) as u8,
        (limbs1_canon >> 21) as u8,
        (limbs1_canon >> 29) as u8,
        (limbs1_canon >> 37) as u8,
        ((limbs1_canon >> 45) | (limbs2_canon << 6)) as u8,
        (limbs2_canon >> 2) as u8,
        (limbs2_canon >> 10) as u8,
        (limbs2_canon >> 18) as u8,
        (limbs2_canon >> 26) as u8,
        (limbs2_canon >> 34) as u8,
        (limbs2_canon >> 42) as u8,
        ((limbs2_canon >> 50) | (limbs3_canon << 1)) as u8,
        (limbs3_canon >> 7) as u8,
        (limbs3_canon >> 15) as u8,
        (limbs3_canon >> 23) as u8,
        (limbs3_canon >> 31) as u8,
        (limbs3_canon >> 39) as u8,
        ((limbs3_canon >> 47) | (limbs4_canon << 4)) as u8,
        (limbs4_canon >> 4) as u8,
        (limbs4_canon >> 12) as u8,
        (limbs4_canon >> 20) as u8,
        (limbs4_canon >> 28) as u8,
        (limbs4_canon >> 36) as u8,
        (limbs4_canon >> 44) as u8,
    ]
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

/// Spec function: r^2 * v = i*u (mod p), where i = sqrt(-1)
/// Used for the nonsquare case in sqrt_ratio_i
pub open spec fn is_sqrt_ratio_times_i(
    u: &FieldElement51,
    v: &FieldElement51,
    r: &FieldElement51,
) -> bool {
    (field_element_as_nat(r) * field_element_as_nat(r) * field_element_as_nat(v)) % p() == (
    field_element_as_nat(&constants::SQRT_M1) * field_element_as_nat(u)) % p()
}

// Square-ness mod p (spec-only).
pub open spec fn is_square_mod_p(a: nat) -> bool {
    exists|y: nat| (#[trigger] (y * y) % p()) == (a % p())
}

// Spec: there exists a modular inverse of v (when v != 0).
pub open spec fn has_inv_mod_p(v: nat) -> bool {
    v % p() != 0 && exists|w: nat| (#[trigger] (v * w) % p()) == 1
}

// Spec: witness-based inverse predicate (lets callers quantify the inverse).
pub open spec fn is_inv_witness(v: nat, w: nat) -> bool {
    ((v % p()) * (w % p())) % p() == 1
}

} // verus!
