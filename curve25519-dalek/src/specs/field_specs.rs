#[allow(unused_imports)]
use super::core_specs::*;
#[allow(unused_imports)]
use super::field_specs_u64::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::field::FieldElement51;
#[allow(unused_imports)]
use crate::constants;
#[allow(unused_imports)]
use crate::lemmas::common_lemmas::number_theory_lemmas::*;
#[allow(unused_imports)]
use crate::specs::primality_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

use vstd::prelude::*;

verus! {

/// Spec predicate: all limbs are bounded by a given bit limit
pub open spec fn fe51_limbs_bounded(fe: &FieldElement51, bit_limit: u64) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe.limbs[i] < (1u64 << bit_limit)
}

/// Spec predicate: sum of limbs are bounded by a given bit limit
pub open spec fn sum_of_limbs_bounded(
    fe1: &FieldElement51,
    fe2: &FieldElement51,
    bound: u64,
) -> bool {
    forall|i: int| 0 <= i < 5 ==> fe1.limbs[i] + fe2.limbs[i] < bound
}

/// Spec function: result of limb-wise addition (what add_spec returns)
pub open spec fn spec_add_fe51_limbs(a: &FieldElement51, b: &FieldElement51) -> FieldElement51 {
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

pub open spec fn spec_field_element_as_nat(fe: &FieldElement51) -> nat {
    u64_5_as_nat(fe.limbs)
}

/// Returns the canonical mathematical value of a field element in [0, p)
/// where p = 2^255 - 19
pub open spec fn spec_field_element(fe: &FieldElement51) -> nat {
    spec_field_element_as_nat(fe) % p()
}

/// Returns the canonical mathematical value when creating a field element from bytes.
/// The bytes are interpreted as a little-endian integer with the high bit of byte[31] ignored.
/// The result is the canonical value in [0, p) where p = 2^255 - 19.
pub open spec fn spec_field_element_from_bytes(bytes: &[u8; 32]) -> nat {
    (u8_32_as_nat(bytes) % pow2(255)) % p()
}

/// Spec function: Get the sign bit of a field element
/// In Curve25519, the sign bit is the least significant bit of the canonical representation
pub open spec fn spec_field_element_sign_bit(fe: &FieldElement51) -> u8 {
    ((spec_field_element(fe) % p()) % 2) as u8
}

// Spec-level field operations on natural numbers (mod p)
/// Math-level field addition
pub open spec fn math_field_add(a: nat, b: nat) -> nat {
    (a + b) % p()
}

/// Math-level field subtraction
pub open spec fn math_field_sub(a: nat, b: nat) -> nat {
    (((a % p()) + p()) - (b % p())) as nat % p()
}

/// Math-level field multiplication
pub open spec fn math_field_mul(a: nat, b: nat) -> nat {
    (a * b) % p()
}

/// Math-level field negation
pub open spec fn math_field_neg(a: nat) -> nat {
    (p() - (a % p())) as nat % p()
}

/// Math-level field squaring
pub open spec fn math_field_square(a: nat) -> nat {
    (a * a) % p()
}

/// Math-level field inversion: returns w such that (a * w) % p == 1
///
/// For non-zero elements (a % p() != 0), this returns the unique multiplicative
/// inverse modulo p. By convention, when a % p() == 0, this returns 0.
///
/// The existence of inverses for non-zero elements is guaranteed by field_inv_property,
/// which relies on p being prime.
pub open spec fn math_field_inv(a: nat) -> nat {
    if a % p() == 0 {
        0  // Convention: inverse of 0 is defined as 0

    } else {
        spec_mod_inverse(a, p())
    }
}

/// Theorem: For non-zero field elements, the inverse exists and satisfies the inverse property
///
/// Proven constructively: gcd(a%p, p) = 1 by primality, then Bezout gives the witness.
pub proof fn field_inv_property(a: nat)
    requires
        a % p() != 0,
    ensures
        math_field_inv(a) < p(),
        ((a % p()) * math_field_inv(a)) % p() == 1,
{
    assert(p() > 1) by {
        pow255_gt_19();
    }
    axiom_p_is_prime();
    lemma_gcd_with_prime(a, p());
    lemma_mod_inverse_correct(a, p());

    // lemma_mod_inverse_correct ensures (a * spec_mod_inverse(a, p())) % p() == 1
    // We need ((a % p()) * spec_mod_inverse(a, p())) % p() == 1
    let inv = spec_mod_inverse(a, p());
    assert(((a % p()) * inv) % p() == 1) by {
        lemma_mul_mod_noop_left(a as int, inv as int, p() as int);
    };
}

/// Helper lemma: If a*w ≡ 1 (mod p) and a*z ≡ 1 (mod p), and both w,z < p, then w = z
///
/// This is the core uniqueness property of multiplicative inverses in modular arithmetic.
/// The proof follows the standard field theory argument:
///   w = w * 1 = w * (a * z) = (w * a) * z = 1 * z = z
proof fn lemma_inverse_unique_core(a: nat, w: nat, z: nat, p: nat)
    requires
        p > 0,
        a % p != 0,
        w < p,
        z < p,
        (a * w) % p == 1,
        (a * z) % p == 1,
    ensures
        w == z,
{
    // Step 1: Since w < p and z < p, they are their own remainders mod p
    assert(w % p == w) by {
        lemma_small_mod(w, p);
    };
    assert(z % p == z) by {
        lemma_small_mod(z, p);
    };

    // Step 2: Compute (a * w * z) % p by multiplying first equation by z
    // From (a * w) % p == 1, we get ((a * w) % p * z) % p == z
    assert((a * w * z) % p == z) by {
        lemma_mul_mod_noop_general((a * w) as int, z as int, p as int);
        // This gives us: ((a * w) % p * z) % p == (a * w * z) % p
        assert(((a * w) % p * z) % p == (a * w * z) % p);
        // Since (a * w) % p == 1, we have: (1 * z) % p == (a * w * z) % p
        assert(((a * w) % p * z) % p == (1 * z) % p);
        // And (1 * z) % p == z since z < p
        assert((1 * z) % p == z);
    };

    // Step 3: Compute (a * z * w) % p by multiplying second equation by w
    // From (a * z) % p == 1, we get ((a * z) % p * w) % p == w
    assert((a * z * w) % p == w) by {
        lemma_mul_mod_noop_general((a * z) as int, w as int, p as int);
        // This gives us: ((a * z) % p * w) % p == (a * z * w) % p
        assert(((a * z) % p * w) % p == (a * z * w) % p);
        // Since (a * z) % p == 1, we have: (1 * w) % p == (a * z * w) % p
        assert(((a * z) % p * w) % p == (1 * w) % p);
        // And (1 * w) % p == w since w < p
        assert((1 * w) % p == w);
    };

    // Step 4: Show a * w * z == a * z * w by commutativity
    assert(a * w * z == a * z * w) by {
        lemma_mul_is_associative(a as int, w as int, z as int);
        lemma_mul_is_associative(a as int, z as int, w as int);
        // a * w * z = a * (w * z) = a * (z * w) = a * z * w
        assert(a * w * z == a * (w * z));
        assert(w * z == z * w);
        assert(a * (w * z) == a * (z * w));
        assert(a * (z * w) == a * z * w);
    };

    // Step 5: Conclude w == z
    // We have: z == (a * w * z) % p == (a * z * w) % p == w
    assert(w == z);
}

/// Theorem: Uniqueness of multiplicative inverse
///
/// If a value w satisfies the inverse property for a, then w equals math_field_inv(a).
/// This captures the uniqueness of the multiplicative inverse in a field.
///
/// Proof: Standard field theory argument using modular arithmetic:
/// w = w * 1 = w * (a * z) = (w * a) * z = 1 * z = z, where z = math_field_inv(a)
///
/// Note: This theorem only requires modular arithmetic properties; it does NOT
/// require p to be prime (though the existence from field_inv_property does).
pub proof fn field_inv_unique(a: nat, w: nat)
    requires
        a % p() != 0,
        w < p(),
        ((a % p()) * w) % p() == 1,
    ensures
        w == math_field_inv(a),
{
    let a_red = a % p();
    let z = math_field_inv(a);

    // Establish that z satisfies the inverse property
    field_inv_property(a);

    // Show a_red < p()
    assert(a_red < p()) by {
        lemma_mod_bound(a as int, p() as int);
    };
    // Show a_red % p() == a_red, which means a_red is in canonical form
    assert(a_red % p() == a_red) by {
        lemma_small_mod(a_red, p());
    };
    // Apply the core uniqueness lemma
    // Both w and z are inverses of a_red in the canonical range [0, p)
    lemma_inverse_unique_core(a_red, w, z, p());
}

/// Theorem: By convention, math_field_inv(0) returns 0
///
/// This is proven directly from the definition of math_field_inv.
/// When the input is 0 (which has no multiplicative inverse),
/// we conventionally define the result to be 0.
pub proof fn field_inv_zero()
    ensures
        math_field_inv(0nat) == 0,
{
    // Proof: By definition of math_field_inv, when a % p() == 0, it returns 0
    assert(p() > 0) by {
        pow255_gt_19();
    };

    // Since p() > 0, we have 0 % p() == 0
    assert(0nat % p() == 0);

    // By the if-branch in math_field_inv's definition: math_field_inv(0) == 0
}

/// Lemma: Fermat's Little Theorem applied to p() = 2^255 - 19
///
/// For any non-zero element x in the field ℤ/p()ℤ, we have x^(p-1) ≡ 1 (mod p).
/// This is a fundamental property of prime fields and the basis for computing
/// multiplicative inverses as x^(p-2) (since x * x^(p-2) = x^(p-1) ≡ 1).
///
/// This lemma is proven by:
/// 1. Invoking axiom_p_is_prime() to establish that p() is prime
/// 2. Applying the general lemma_fermat_little_theorem with p()
///
/// The general Fermat's Little Theorem is still admitted (requires group theory),
/// but this specific application to p() is now a proven lemma rather than an axiom.
pub proof fn lemma_fermat_for_p(x: nat)
    requires
        x % p() != 0,
    ensures
        (pow(x as int, (p() - 1) as nat) as nat) % p() == 1,
{
    axiom_p_is_prime();
    lemma_fermat_little_theorem(x, p());
}

/// Check if a value is a quadratic residue (square) modulo p
pub open spec fn math_is_square(a: nat) -> bool {
    exists|y: nat| (#[trigger] (y * y) % p()) == (a % p())
}

/// Compute a square root modulo p (if it exists)
/// Returns some y such that y^2 ≡ a (mod p)
/// The result is unspecified if a is not a quadratic residue
/// Note result is not unique
pub open spec fn math_sqrt(a: nat) -> nat
    recommends
        math_is_square(a),
{
    choose|y: nat| y < p() && #[trigger] ((y * y) % p()) == (a % p())
}

/// Spec function for FieldElement::from_bytes
/// Takes a 32-byte array and produces a FieldElement51
/// The high bit of byte[31] is ignored, giving a 255-bit value
pub open spec fn spec_fe51_from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
    // Mimic the implementation in field_verus.rs:from_bytes
    // Load 8-byte chunks at specified offsets and mask to 51-bit limbs
    let low_51_bit_mask = mask51;

    FieldElement51 {
        limbs: [
        // load bits [  0, 64), mask to 51 bits

            (spec_load8_at(bytes, 0) as u64) & low_51_bit_mask,
            // load bits [ 48,112), shift right by 3, mask to 51 bits
            ((spec_load8_at(bytes, 6) as u64) >> 3) & low_51_bit_mask,
            // load bits [ 96,160), shift right by 6, mask to 51 bits
            ((spec_load8_at(bytes, 12) as u64) >> 6) & low_51_bit_mask,
            // load bits [152,216), shift right by 1, mask to 51 bits
            ((spec_load8_at(bytes, 19) as u64) >> 1) & low_51_bit_mask,
            // load bits [192,256), shift right by 12, mask to 51 bits (this ignores high bit)
            ((spec_load8_at(bytes, 24) as u64) >> 12) & low_51_bit_mask,
        ],
    }
}

pub open spec fn spec_fe51_to_bytes(fe: &FieldElement51) -> Seq<u8> {
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
    (spec_field_element(a) * spec_field_element(b)) % p() == 1
}

/// Spec function: field element is inverse of a natural number (mod p)
pub open spec fn is_inverse_field_of_nat(fe: &FieldElement51, n: nat) -> bool {
    (spec_field_element(fe) * n) % p() == 1
}

/// Spec function to compute product of all field elements in a sequence (mod p)
/// Returns the natural number representation
pub open spec fn spec_product_of_field_elems(fields: Seq<FieldElement51>) -> nat
    decreases fields.len(),
{
    if fields.len() == 0 {
        1
    } else {
        (spec_product_of_field_elems(fields.skip(1)) * spec_field_element(&fields[0])) % p()
    }
}

/// Spec function: b is a square root of a (mod p), i.e., b^2 = a (mod p)
pub open spec fn is_square_of(a: &FieldElement51, b: &FieldElement51) -> bool {
    (spec_field_element(b) * spec_field_element(b)) % p() == spec_field_element(a) % p()
}

/// Spec function: b^2 * v = u (mod p)
pub open spec fn is_sqrt_ratio(u: &FieldElement51, v: &FieldElement51, r: &FieldElement51) -> bool {
    (spec_field_element(r) * spec_field_element(r) * spec_field_element(v)) % p()
        == spec_field_element(u)
}

/// Spec function: r^2 * v = i*u (mod p), where i = sqrt(-1)
/// Used for the nonsquare case in sqrt_ratio_i
pub open spec fn is_sqrt_ratio_times_i(
    u: &FieldElement51,
    v: &FieldElement51,
    r: &FieldElement51,
) -> bool {
    (spec_field_element(r) * spec_field_element(r) * spec_field_element(v)) % p() == (
    spec_field_element(&constants::SQRT_M1) * spec_field_element(u)) % p()
}

/// Spec function: r² * v = u (mod p) — math version operating on nat values
/// This is the mathematical equivalent of is_sqrt_ratio but without FieldElement wrappers.
/// Use this when working with mathematical values directly in lemmas.
pub open spec fn math_is_sqrt_ratio(u: nat, v: nat, r: nat) -> bool {
    (r * r * v) % p() == u
}

/// Spec function: r² * v = i*u (mod p) — math version operating on nat values
/// Used for the nonsquare case in sqrt_ratio_i.
/// This is the mathematical equivalent of is_sqrt_ratio_times_i.
pub open spec fn math_is_sqrt_ratio_times_i(u: nat, v: nat, r: nat) -> bool {
    (r * r * v) % p() == (spec_sqrt_m1() * u) % p()
}

/// Spec function capturing sqrt_ratio_i math correctness postconditions.
///
/// This encapsulates the four mathematical postconditions of sqrt_ratio_i:
/// 1. When u = 0: returns (true, 0)
/// 2. When v = 0 and u ≠ 0: returns (false, 0)
/// 3. When success and v ≠ 0: r² · v ≡ u (mod p)
/// 4. When failure and v ≠ 0 and u ≠ 0: r² · v ≡ i·u (mod p)
pub open spec fn spec_sqrt_ratio_i_math_post(u: nat, v: nat, success: bool, r: nat) -> bool {
    // When u = 0: always return (true, 0)
    ((u == 0) ==> (success && r == 0))
        &&
    // When v = 0 but u ≠ 0: return (false, 0) [division by zero case]
    ((v == 0 && u != 0) ==> (!success && r == 0))
        &&
    // When successful and v ≠ 0: r² * v ≡ u (mod p)
    ((success && v != 0) ==> math_is_sqrt_ratio(u, v, r))
        &&
    // When unsuccessful and v ≠ 0 and u ≠ 0: r² * v ≡ i*u (mod p)
    ((!success && v != 0 && u != 0) ==> math_is_sqrt_ratio_times_i(u, v, r))
}

/// Spec function capturing sqrt_ratio_i boundedness postconditions.
///
/// The result r is:
/// - Reduced modulo p (r < p)
/// - The "non-negative" square root (even, i.e., LSB = 0)
pub open spec fn spec_sqrt_ratio_i_bounded_post(r: nat) -> bool {
    r < p() && r % 2 == 0
}

/// Complete spec function for sqrt_ratio_i postconditions.
///
/// Combines math correctness and boundedness postconditions.
/// Use this in lemmas instead of listing all postconditions separately.
pub open spec fn spec_sqrt_ratio_i_post(u: nat, v: nat, success: bool, r: nat) -> bool {
    spec_sqrt_ratio_i_math_post(u, v, success, r) && spec_sqrt_ratio_i_bounded_post(r)
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

/// The mathematical value of SQRT_M1 (sqrt(-1) mod p)
/// This is the 4th root of unity i such that i² = -1 (mod p)
pub open spec fn spec_sqrt_m1() -> nat {
    spec_field_element(&constants::SQRT_M1)
}

} // verus!
