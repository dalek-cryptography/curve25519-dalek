// field.rs
#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

// ADAPTED CODE LINES: X.0 globally replaced with X.limbs

verus! {


/* MANUALLY moved outside and made explicit */
// LOW_51_BIT_MASK: u64 = (1u64 << 51) -1; originally
pub const LOW_51_BIT_MASK: u64 = 2251799813685247u64; // 2^51  -1

// Basic properties of LOW_51_BIT_MASK:
// - It's the value of low_bits_mask (spec function defined in vstd and used in its lemmas)
// - it's less than 2^51
pub proof fn l51_bit_mask_lt()
    ensures
        LOW_51_BIT_MASK == low_bits_mask(51),
        LOW_51_BIT_MASK < (1u64 << 51) as nat,
{
    lemma2_to64_rest();
    assert(LOW_51_BIT_MASK < (1u64 << 51) as nat) by (compute);
}

// Auxiliary lemma for multiplication (of nat!)
pub proof fn mul_lt(a1:nat, b1:nat, a2:nat, b2:nat)
    requires
        a1 < b1,
        a2 < b2,
    ensures
        a1 * a2 < b1 * b2,
{
    if (a2 == 0) {
        assert(b1 * b2 > 0) by {
            // a * b != 0 <==> a != 0 /\ b != 0
            lemma_mul_nonzero(b1 as int, b2 as int);
        }
    }
    else {
        // a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2
        lemma_mul_strict_inequality(a1 as int, b1  as int, a2 as int);
        // a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1
        lemma_mul_strict_inequality(a2 as int, b2 as int, b1 as int);
    }
}

// Auxiliary lemma for exponentiation
pub proof fn pow2_le_max64(k: nat)
    requires
        k < 64,
    ensures
        pow2(k) <= u64::MAX
    {
        lemma2_to64();
        lemma2_to64_rest();
    }

// Specialization of lemma_u64_shl_is_mul for x = 1
pub proof fn shift_is_pow2(k: nat)
    requires
        k < 64,
    ensures
        (1u64 << k) == pow2(k)
{
    pow2_le_max64(k);
    lemma_u64_shl_is_mul(1u64, k as u64);
}

// Masking with low_bits_mask(k) gives a value bounded by 2^k
pub proof fn masked_lt(v: u64)
    ensures
        v & LOW_51_BIT_MASK < (1u64 << 51),
{
    assert (v & 2251799813685247u64 < (1u64 << 51)) by (bit_vector);
}

// right-shifting a u64 gives at most 2^13 - 1
pub proof fn shifted_lt(v: u64)
    ensures
        v >> 51 < 1u64 << 13
{
    shift_is_pow2(13);
    lemma_u64_shr_is_div(u64::MAX, 51);
    lemma_u64_shr_is_div(v, 51);
    lemma_pow2_pos(51);
    lemma_div_is_ordered(v as int, u64::MAX as int, pow2(51) as int);
    assert(u64::MAX >> 51 < 1u64 << 13) by (compute);
}

pub open spec fn p() -> nat {
    (pow2(255) - 19) as nat
}

// Proof that 2^255 > 19
pub proof fn pow255_gt_19()
    ensures
        pow2(255) > 19
{
    lemma2_to64(); // 2^5
    lemma_pow2_strictly_increases(5, 255);
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat(limbs: [u64; 5]) -> nat {
    (limbs[0] as nat) +
    pow2(51) * (limbs[1] as nat) +
    pow2(102) * (limbs[2] as nat) +
    pow2(153) * (limbs[3] as nat) +
    pow2(204) * (limbs[4] as nat)
}

// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
pub open spec fn as_nat_32_u8(limbs: [u8; 32]) -> nat {
    // Verus error: `core::iter::range::impl&%15::fold` is not supported
    // we write them out manually
    (limbs[0] as nat) +
    pow2( 1 * 8) * (limbs[ 1] as nat) +
    pow2( 2 * 8) * (limbs[ 2] as nat) +
    pow2( 3 * 8) * (limbs[ 3] as nat) +
    pow2( 4 * 8) * (limbs[ 4] as nat) +
    pow2( 5 * 8) * (limbs[ 5] as nat) +
    pow2( 6 * 8) * (limbs[ 6] as nat) +
    pow2( 7 * 8) * (limbs[ 7] as nat) +
    pow2( 8 * 8) * (limbs[ 8] as nat) +
    pow2( 9 * 8) * (limbs[ 9] as nat) +
    pow2(10 * 8) * (limbs[10] as nat) +
    pow2(11 * 8) * (limbs[11] as nat) +
    pow2(12 * 8) * (limbs[12] as nat) +
    pow2(13 * 8) * (limbs[13] as nat) +
    pow2(14 * 8) * (limbs[14] as nat) +
    pow2(15 * 8) * (limbs[15] as nat) +
    pow2(16 * 8) * (limbs[16] as nat) +
    pow2(17 * 8) * (limbs[17] as nat) +
    pow2(18 * 8) * (limbs[18] as nat) +
    pow2(19 * 8) * (limbs[19] as nat) +
    pow2(20 * 8) * (limbs[20] as nat) +
    pow2(21 * 8) * (limbs[21] as nat) +
    pow2(22 * 8) * (limbs[22] as nat) +
    pow2(23 * 8) * (limbs[23] as nat) +
    pow2(24 * 8) * (limbs[24] as nat) +
    pow2(25 * 8) * (limbs[25] as nat) +
    pow2(26 * 8) * (limbs[26] as nat) +
    pow2(27 * 8) * (limbs[27] as nat) +
    pow2(28 * 8) * (limbs[28] as nat) +
    pow2(29 * 8) * (limbs[29] as nat) +
    pow2(30 * 8) * (limbs[30] as nat) +
    pow2(31 * 8) * (limbs[31] as nat)
}

// Lemma: If a > b pointwise, then as_nat(a - b) = as_nat(a) - as_nat(b)
pub proof fn lemma_as_nat_sub(a: [u64;5], b: [u64;5])
    requires
        forall |i:int| 0 <= i < 5 ==> b[i] < a[i]
    ensures
        as_nat([
            (a[0] - b[0]) as u64,
            (a[1] - b[1]) as u64,
            (a[2] - b[2]) as u64,
            (a[3] - b[3]) as u64,
            (a[4] - b[4]) as u64
        ]) == as_nat(a) - as_nat(b)
{
    let c: [u64;5] = [
        (a[0] - b[0]) as u64,
        (a[1] - b[1]) as u64,
        (a[2] - b[2]) as u64,
        (a[3] - b[3]) as u64,
        (a[4] - b[4]) as u64
    ];
    // distribute pow2
    assert( as_nat(c) ==
        (a[0] - b[0]) +
        pow2(51) * a[1] - pow2(51) * b[1] +
        pow2(102) * a[2] - pow2(102) * b[2] +
        pow2(153) * a[3] - pow2(153) * b[3] +
        pow2(204) * a[4] - pow2(204) * b[4]
    ) by {
        lemma_mul_is_distributive_sub(pow2(51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_sub(pow2(102) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_sub(pow2(153) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_sub(pow2(204) as int, a[4] as int, b[4] as int);
    }
}

// Auxiliary lemma; shift is division (for 51 fixed)
pub proof fn lemma_shift(ai: u64, v: u64)
    requires
        ai == v >> 51
    ensures
        ai == (v as nat) / pow2(51)
{
    lemma_u64_shr_is_div(v, 51);
}

// Auxiliary lemma; mask is mod (for 51 fixed)
pub proof fn lemma_mask(bi: u64, v: u64)
    requires
        bi == v & LOW_51_BIT_MASK
    ensures
        bi == v % (pow2(51) as u64)
{
    l51_bit_mask_lt();
    lemma_u64_low_bits_mask_is_mod(v, 51);
}

// Combination of the above lemmas, and the basic div/mod property that a = d * (a/d) + a % d
pub proof fn lemma_div_and_mod(ai:u64, bi: u64, v: u64)
    requires
        ai == v >> 51,
        bi == v & LOW_51_BIT_MASK
    ensures
        ai == (v as nat) / pow2(51),
        bi == v % (pow2(51) as u64),
        v == ai * pow2(51) + bi
{
    lemma_shift(ai, v);
    lemma_mask(bi, v);
    lemma_pow2_pos(51); // pow2(51) != 0
    assert(pow2(51) <= u64::MAX) by {
        lemma2_to64_rest();
    }
    lemma_fundamental_div_mod(v as int, pow2(51) as int);
}

// Rewriting lemma; 2^((t + 1) * 51) * x = 2^(t*51) * (2^51 * x)
// Parenthesis placement matters here
pub proof fn lemma_two_factoring(k : nat, ai: u64)
    ensures
        pow2(k + 51) * ai == pow2(k) * (pow2(51) * ai)
{
    lemma_pow2_adds(k, 51);
    lemma_mul_is_associative(pow2(k) as int, pow2(51) as int, ai as int);
}

pub open spec fn spec_reduce(limbs: [u64; 5]) -> (r: [u64; 5]) {
    let r = [
        ((limbs[0] & LOW_51_BIT_MASK) + (limbs[4] >> 51) * 19) as u64,
        ((limbs[1] & LOW_51_BIT_MASK) + (limbs[0] >> 51)) as u64,
        ((limbs[2] & LOW_51_BIT_MASK) + (limbs[1] >> 51)) as u64,
        ((limbs[3] & LOW_51_BIT_MASK) + (limbs[2] >> 51)) as u64,
        ((limbs[4] & LOW_51_BIT_MASK) + (limbs[3] >> 51)) as u64,
    ];
    r
}

// Each component of spec_reduce is bounded.
// The reason we _don't_ write
// ensures forall |i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52)
// is that the solver treats `spec_reduce`` above as symbolic and does _not_ instantiate e.g.
// ((limbs[4] & LOW_51_BIT_MASK) + (limbs[3] >> 51)) as u64 < (1u64 << 52)
pub proof fn lemma_boundaries(limbs: [u64; 5])
    ensures
        ((limbs[0] & LOW_51_BIT_MASK) + (limbs[4] >> 51) * 19) < (1u64 << 52),
        ((limbs[1] & LOW_51_BIT_MASK) + (limbs[0] >> 51)) < (1u64 << 52),
        ((limbs[2] & LOW_51_BIT_MASK) + (limbs[1] >> 51)) < (1u64 << 52),
        ((limbs[3] & LOW_51_BIT_MASK) + (limbs[2] >> 51)) < (1u64 << 52),
        ((limbs[4] & LOW_51_BIT_MASK) + (limbs[3] >> 51)) < (1u64 << 52)

{
    // \A i. limbs[i] < 2^13
    shifted_lt(limbs[0]);
    shifted_lt(limbs[1]);
    shifted_lt(limbs[2]);
    shifted_lt(limbs[3]);
    shifted_lt(limbs[4]);

    // \A i. limbs[i] & LOW_51_BIT_MASK < 2^51
    masked_lt(limbs[0]);
    masked_lt(limbs[1]);
    masked_lt(limbs[2]);
    masked_lt(limbs[3]);
    masked_lt(limbs[4]);

    // Since 19 < 2^5 and (limbs[4] >> 51) < 2^13, their product is less than 2^18
    assert((limbs[4] >> 51) * 19 < (1u64 << 18) as nat) by {
        assert(19 < (1u64 << 5)) by (bit_vector);
        shift_is_pow2(5);
        shift_is_pow2(13);
        shift_is_pow2(18);
        lemma_pow2_adds(13, 5);
        // If (limbs[4] >> 51) < 2^13 and 19 < 2^5 then their product is less than 2^18
        mul_lt((limbs[4] >> 51) as nat, (1u64 << 13) as nat, 19nat, (1u64 << 5) as nat);
    }

    // The final values (limbs[i] += cX) are all bounded by 2^51 + eps, for eps \in {2^18, 2^13}.
    assert(((1u64 << 18)) + (1u64 << 51) < (1u64 << 52)) by (bit_vector);
    assert(((1u64 << 13)) + (1u64 << 51) < (1u64 << 52)) by (bit_vector);

    // In summary, they're all bounded by 2^52
    // The solver can prove this automatically
}

pub proof fn lemma_reduce(limbs: [u64; 5])
    ensures
        forall|i: int| 0 <= i < 5 ==> spec_reduce(limbs)[i] < (1u64 << 52),
        // Suppose l = (l0, l1, l2, l3, l4) are the input limbs.
        // They represent a number
        // e(l) =  l0 + l1 * 2^51 + l2 * 2^102 + l3 * 2^153 + l4 * 2^204
        // in Z_p, for p = 2^255 - 19
        // reduce(l) returns v = (v0, v1, v2, v3, v4), such that
        // v0 = 19 * a4 + b0
        // v1 =      a0 + b1
        // v2 =      a1 + b2
        // v3 =      a2 + b3
        // v4 =      a3 + b4
        // where ai = li >> 51 and bi = li & LOW_51_BIT_MASK
        // we can reformulate this as ai = li / 2^51 (flooring division) and bi = li % 2^51
        // Using the following identity connecting integer division and remainder:
        // x = y * (x / y) + x % y
        // we can see that li = ai * 2^51 + bi
        // Plugging the above identities into the equations for v, we can observe that
        // e(v) = e(l) - p * (l4 >> 51)
        // IOW, e(reduce(l)) = e(l) (mod p)
        // additionally, if all limbs are below 2^51, reduce(l) = l
        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (spec_reduce(limbs) =~= limbs),
        as_nat(spec_reduce(limbs)) == as_nat(limbs) - p() * (limbs[4] >> 51)
{

    // -----
    // reduce identity for small limbs

    // Can't seem to reference r within this proof block, we reconstruct it here
    let rr: [u64; 5] = spec_reduce(limbs);

    assert((forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) ==> (rr =~= limbs)) by {
        if (forall|i: int| 0 <= i < 5 ==> #[trigger] limbs[i] < (1u64 << 51)) {
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] & LOW_51_BIT_MASK == limbs[i] by {
                l51_bit_mask_lt(); // LOW_51_BIT_MASK = low_bits_mask(51)
                shift_is_pow2(51);
                lemma_u64_low_bits_mask_is_mod(limbs[i], 51);
                lemma_small_mod(limbs[i] as nat, pow2(51));
            }
            assert forall|i: int| 0 <= i < 5 implies #[trigger] limbs[i] >> 51 == 0 by {
                l51_bit_mask_lt(); // LOW_51_BIT_MASK = low_bits_mask(51)
                shift_is_pow2(51);
                lemma_u64_shr_is_div(limbs[i], 51);
                lemma_basic_div(limbs[i] as int, pow2(51) as int);
            }
        }
    }

    // -- as_nat identity

    // ai = limbs[i] / 2^52
    let a0 = (limbs[0] >> 51);
    let a1 = (limbs[1] >> 51);
    let a2 = (limbs[2] >> 51);
    let a3 = (limbs[3] >> 51);
    let a4 = (limbs[4] >> 51);

    // bi = limbs[i] % 2^52
    let b0 = (limbs[0] & LOW_51_BIT_MASK);
    let b1 = (limbs[1] & LOW_51_BIT_MASK);
    let b2 = (limbs[2] & LOW_51_BIT_MASK);
    let b3 = (limbs[3] & LOW_51_BIT_MASK);
    let b4 = (limbs[4] & LOW_51_BIT_MASK);

    lemma_boundaries(limbs);

    // distribute
    assert(as_nat(rr) ==
        19 *  a4 + b0 +
        pow2(51) * a0 + pow2(51) * b1 +
        pow2(102) * a1 + pow2(102) * b2 +
        pow2(153) * a2 + pow2(153) * b3 +
        pow2(204) * a3 + pow2(204) * b4
    ) by {
        lemma_mul_is_distributive_add(pow2(51) as int, a0 as int, b1 as int);
        lemma_mul_is_distributive_add(pow2(102) as int, a1 as int, b2 as int);
        lemma_mul_is_distributive_add(pow2(153) as int, a2 as int, b3 as int);
        lemma_mul_is_distributive_add(pow2(204) as int, a3 as int, b4 as int);
    }

    // factor out
    assert(as_nat(rr) ==
        19 *  a4 + b0 +
        pow2(51) * a0 + pow2(51) * b1 +
        pow2(51) * (pow2(51) * a1) + pow2(102) * b2 +
        pow2(102) * (pow2(51) * a2) + pow2(153) * b3 +
        pow2(153) * (pow2(51) * a3) + pow2(204) * b4
    ) by {
        lemma_two_factoring(51, a1);
        lemma_two_factoring(102, a2);
        lemma_two_factoring(153, a3);
    }

    // change groupings
    assert(as_nat(rr) ==
        (b0 + pow2(51) * a0) +
        pow2(51) * (b1 + pow2(51) * a1) +
        pow2(102) * (b2 + pow2(51) * a2) +
        pow2(153) * (b3 + pow2(51) * a3) +
        pow2(204) * b4 + 19 * a4
    ) by {
        lemma_mul_is_distributive_add(pow2(51) as int, pow2(51) * a1 as int, b1 as int);
        lemma_mul_is_distributive_add(pow2(102) as int, pow2(51) * a2 as int, b2 as int);
        lemma_mul_is_distributive_add(pow2(153) as int, pow2(51) * a3 as int, b3 as int);
    }

    // invoke div/mod identity
    assert(as_nat(rr) ==
        limbs[0] +
        pow2(51) * limbs[1] +
        pow2(102) * limbs[2] +
        pow2(153) * limbs[3] +
        pow2(204) * b4 + 19 * a4
    ) by {
        lemma_div_and_mod(a0, b0, limbs[0]);
        lemma_div_and_mod(a1, b1, limbs[1]);
        lemma_div_and_mod(a2, b2, limbs[2]);
        lemma_div_and_mod(a3, b3, limbs[3]);
    }

    // Add missing limbs[4] parts
    assert(as_nat(rr) ==
        limbs[0] +
        pow2(51) * limbs[1] +
        pow2(102) * limbs[2] +
        pow2(153) * limbs[3] +
        pow2(204) * limbs[4] - pow2(204) * (pow2(51) * a4 ) + 19 * a4
    ) by {
        lemma_div_and_mod(a4, b4, limbs[4]);
        assert(pow2(204) * limbs[4] == pow2(204) * b4 + pow2(204)* (pow2(51) * a4)) by {
            lemma_mul_is_distributive_add(pow2(204) as int, pow2(51) * a4 as int, b4 as int);
        }
    }

    // The solver can collect components of as_nat(limbs) automatically:
    // as_nat(rr) == as_nat(limbs) - pow2(204) * (pow2(51) * a4 ) + 19 * a4
    // ... as well as pull in minus
    // as_nat(rr) == as_nat(limbs) - (pow2(204) * (pow2(51) * a4 ) - 19 * a4)

    // collect components of p() * a4
    assert(pow2(204) * (pow2(51) * a4) - 19 * a4 == p() * a4) by {
        lemma_mul_is_associative(pow2(204) as int, pow2(51) as int, a4 as int);
        lemma_pow2_adds(204, 51);
        lemma_mul_is_distributive_sub_other_way(a4 as int, pow2(255) as int, 19 );
        pow255_gt_19(); // we need to prove 2^255 - 19 doesn't underflow
    }
}

pub proof fn lemma_add_then_shift(a: u64, b: u64)
    requires
        a < (1u64 << 52),
        b < (1u64 << 52)
    ensures
        (a + b) < (1u64 << 53),
        ((a + b) as u64 >> 51) < 4
{
    lemma2_to64_rest();
    assert((a + b) < 1u64 << 53) by {
        assert((1u64 << 52) + (1u64 << 52) == 1u64 << 53) by (compute);
    }
    assert(1u64 << 53 == (1u64 << 51) * 4) by (bit_vector);
    // 0 < b  /\ a < b * c => a/b < c
    lemma_multiply_divide_lt((a + b) as int, (1u64 << 51) as int, 4int);
    shift_is_pow2(51);
    shift_is_pow2(53);
    assert((a + b) as u64 >> 51 == (a + b) as u64 / (pow2(51) as u64)) by {
        lemma_u64_shr_is_div((a + b) as u64, 51);
    }
    assert(pow2(53) / pow2(51) == 4) by {
        lemma_pow2_subtracts(51, 53);
    }
}

/* MANUALLY moved outside, named return value */
const fn load8_at(input: &[u8], i: usize) -> (r: u64)
    requires
        i + 7 < input.len(),
    ensures
        0 <= r <= (u64::MAX as nat),
{
        (input[i] as u64)
    | ((input[i + 1] as u64) << 8)
    | ((input[i + 2] as u64) << 16)
    | ((input[i + 3] as u64) << 24)
    | ((input[i + 4] as u64) << 32)
    | ((input[i + 5] as u64) << 40)
    | ((input[i + 6] as u64) << 48)
    | ((input[i + 7] as u64) << 56)
}

/* MANUALLY moved outside */
#[inline(always)]
fn m(x: u64, y: u64) -> (r: u128)
    requires
        (x as nat) * (y as nat) < (u128::MAX as nat),
    ensures
        (r as nat) == (x as nat) * (y as nat),
{
    (x as u128) * (y as u128)
}

pub struct FieldElement51 {
    // ADAPTED CODE LINE: we give a name to the field: "limbs"
    pub limbs: [u64; 5],
}

impl FieldElement51 {
    pub(crate) const fn from_limbs(limbs: [u64; 5]) -> FieldElement51 {
        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs}
    }

    // Modified to use direct struct
    pub const ZERO: FieldElement51 = FieldElement51{limbs: [0, 0, 0, 0, 0]};
    pub const ONE: FieldElement51 = FieldElement51{limbs: [1, 0, 0, 0, 0]};
    pub const MINUS_ONE: FieldElement51 = FieldElement51{limbs: [
        2251799813685228,
        2251799813685247,
        2251799813685247,
        2251799813685247,
        2251799813685247,
    ]};

    /// Invert the sign of this field element
    pub fn negate(&mut self)
        requires
            forall|i: int| 0 <= i < 5 ==> old(self).limbs[i] < (1u64 << 51),
        ensures
            forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 52),
            // Assume we start with l = (l0, l1, l2, l3, l4).
            // Using c0 = 2^51 - 19 and c = 2^51 - 1, we can see that
            // ( 36028797018963664u64 - l0,
            //   36028797018963952u64 - l1,
            //   36028797018963952u64 - l2,
            //   36028797018963952u64 - l3,
            //   36028797018963952u64 - l4 )
            // is just 16 * (c0, c, c, c, c) - l (in vector notation)
            // Further, as_nat((c0, c, c, c, c)) = p, so
            // as_nat(16 * (c0, c, c, c, c) - l) is 16p - as_nat(l)
            // We know as_nat(reduce(v)) = as_nat(v) - p * (v4 >> 51) for any v.
            // This gives us the identity
            // as_nat(negate(l)) = as_nat(reduce(16 * (c0, c, c, c, c) - l))
            //                   = 16p - as_nat(l) - p * ((16c - l4) >> 51)
            // Note that (16c - l4) >> 51 is either 14 or 15, in either case < 16.
            as_nat(self.limbs) == 16 * p() - as_nat(old(self).limbs) - p() * ((36028797018963952u64 - old(self).limbs[4]) as u64 >> 51)
            // Reducing mod p, this implies `as_nat(self.limbs) == - as_nat(old(self).limbs)`
    {
        proof {
            let c0 = (pow2(51) - 19);
            let c  = (pow2(51) - 1);
            lemma2_to64_rest(); // get pow2(51)
            // solver knows 36028797018963664u64 == 16 * c0
            // solver knows 36028797018963952u64 == 16 * c;

            assert forall |i: int| 0 <= i < 5 implies old(self).limbs[i] < 16 * c0 by {
                shift_is_pow2(51);
            }

            // Introduce 16p as a vector
            let v = [(16 * c0) as u64,(16 * c) as u64,(16 * c) as u64,(16 * c) as u64,(16 * c) as u64];

            assert(as_nat(v) == 16 * p()) by {
                // by definition of as_nat
                assert( as_nat(v) ==
                    16 * c0 +
                    pow2(51) * (16 * c) +
                    pow2(102) * (16 * c) +
                    pow2(153) * (16 * c) +
                    pow2(204) * (16 * c)
                );

                // solver can reorder factors and pull out 16 on its own
                // ...

                // Write out `c`s and sum up powers
                assert( p() ==
                    c0 +
                    pow2(51) * c +
                    pow2(102) * c +
                    pow2(153) * c +
                    pow2(204) * c
                ) by {
                    lemma_pow2_adds(51, 51);
                    lemma_pow2_adds(51, 102);
                    lemma_pow2_adds(51, 153);
                    lemma_pow2_adds(51, 204);
                }
            }

            let l0 = old(self).limbs[0];
            let l1 = old(self).limbs[1];
            let l2 = old(self).limbs[2];
            let l3 = old(self).limbs[3];
            let l4 = old(self).limbs[4];

            assert(as_nat([
                (16 * c0 - l0) as u64,
                (16 * c - l1) as u64,
                (16 * c - l2) as u64,
                (16 * c - l3) as u64,
                (16 * c - l4) as u64,
                ]) == as_nat(v) - as_nat(old(self).limbs)
            ) by {
                lemma_as_nat_sub(v, old(self).limbs);
            }
        }
        // See commentary in the Sub impl: (copied below)
            // To avoid underflow, first add a multiple of p.
            // Choose 16*p = p << 4 to be larger than 54-bit _rhs.
            //
            // If we could statically track the bitlengths of the limbs
            // of every FieldElement51, we could choose a multiple of p
            // just bigger than _rhs and avoid having to do a reduction.
            //
            // Since we don't yet have type-level integers to do this, we
            // have to add an explicit reduction call here.
        // Note on "magic numbers":
        // 36028797018963664u64 = 2^55 - 304 = 16 * (2^51 - 19)
        // 36028797018963952u64 = 2^55 - 16 =  16 * (2^51 - 1)
        let neg = FieldElement51::reduce([
            36028797018963664u64 - self.limbs[0],
            36028797018963952u64 - self.limbs[1],
            36028797018963952u64 - self.limbs[2],
            36028797018963952u64 - self.limbs[3],
            36028797018963952u64 - self.limbs[4],
        ]);
        self.limbs = neg.limbs;
    }

    /// Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).
    #[inline(always)]
    fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)
        ensures
            r.limbs == spec_reduce(limbs),
            forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
            (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
            as_nat(r.limbs) == as_nat(limbs) - p() * (limbs[4] >> 51)
    {
        proof {
            lemma_boundaries(limbs);
            lemma_reduce(limbs);
        }

        // Since the input limbs are bounded by 2^64, the biggest
        // carry-out is bounded by 2^13.
        //
        // The biggest carry-in is c4 * 19, resulting in
        //
        // 2^51 + 19*2^13 < 2^51.0000000001
        //
        // Because we don't need to canonicalize, only to reduce the
        // limb sizes, it's OK to do a "weak reduction", where we
        // compute the carry-outs in parallel.

        let c0 = limbs[0] >> 51;
        let c1 = limbs[1] >> 51;
        let c2 = limbs[2] >> 51;
        let c3 = limbs[3] >> 51;
        let c4 = limbs[4] >> 51;

        limbs[0] &= LOW_51_BIT_MASK;
        limbs[1] &= LOW_51_BIT_MASK;
        limbs[2] &= LOW_51_BIT_MASK;
        limbs[3] &= LOW_51_BIT_MASK;
        limbs[4] &= LOW_51_BIT_MASK;

        limbs[0] += c4 * 19;
        limbs[1] += c0;
        limbs[2] += c1;
        limbs[3] += c2;
        limbs[4] += c3;

        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs}
    }

    /// Load a `FieldElement51` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    ///
    #[rustfmt::skip] // keep alignment of bit shifts
    pub const fn from_bytes(bytes: &[u8; 32]) -> (r: FieldElement51)
        ensures
            true
            // TODO:
            // as_nat(r.limbs) =?= as_nat_32_u8(bytes)
    {
        proof {
            l51_bit_mask_lt() // No over/underflow in the below let-def
        }
        let low_51_bit_mask = (1u64 << 51) - 1;
        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{ limbs:
        // load bits [  0, 64), no shift
        [  load8_at(bytes,  0)        & low_51_bit_mask
        // load bits [ 48,112), shift to [ 51,112)
        , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
        // load bits [ 96,160), shift to [102,160)
        , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
        // load bits [152,216), shift to [153,216)
        , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
        // load bits [192,256), shift to [204,112)
        , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
        ]}
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    #[rustfmt::skip] // keep alignment of s[*] calculations
    #[allow(clippy::wrong_self_convention)]
    pub fn to_bytes(self) -> (r: [u8; 32])
        ensures
            true // No overflow
            // TODO:
            // as_nat(self.limbs) =?= as_nat_32_u8(r),
            // canonical encoding
            // forall|i: int| 0 <= i < 5 ==> r[i] < (1u64 << 51)
    {
        proof {
            let l = spec_reduce(self.limbs);
            lemma_reduce(self.limbs);

            let q0 = (l[0] + 19) as u64 >> 51;
            let q1 = (l[1] + q0) as u64 >> 51;
            let q2 = (l[2] + q1) as u64 >> 51;
            let q3 = (l[3] + q2) as u64 >> 51;
            let q4 = (l[4] + q3) as u64 >> 51;

            assert(19 < (1u64 << 52)) by (bit_vector);
            lemma_add_then_shift(l[0], 19);
            lemma_add_then_shift(l[1], q0);
            lemma_add_then_shift(l[2], q1);
            lemma_add_then_shift(l[3], q2);
            lemma_add_then_shift(l[4], q3);

            let l0 = (l[0] + 19 * q4) as u64;
            let l1 = (l[1] + (l0 >> 51)) as u64;
            let l2 = (l[2] + (l1 >> 51)) as u64;
            let l3 = (l[3] + (l2 >> 51)) as u64;
            let l4 = (l[3] + (l3 >> 51)) as u64;

            assert( 19 * q4 < 1u64 << 7) by {
                // Explicit values for pow2(k) for k < 64
                lemma2_to64();
                shift_is_pow2(5); // now we know 19 < 1u64 << 5 for free
                shift_is_pow2(2);
                shift_is_pow2(7);
                lemma_pow2_adds(5, 2);
            }
            assert(((1u64 << 7)) + (1u64 << 52) < (1u64 << 53)) by (bit_vector);
            assert(((1u64 << 13)) + (1u64 << 52) < (1u64 << 53)) by (bit_vector);
            shifted_lt(l0);
            shifted_lt(l1);
            shifted_lt(l2);
            shifted_lt(l3);

            l51_bit_mask_lt();

            // TODO
            // let rr = [
            //     l0 & LOW_51_BIT_MASK,
            //     l1 & LOW_51_BIT_MASK,
            //     l2 & LOW_51_BIT_MASK,
            //     l3 & LOW_51_BIT_MASK,
            //     l4 & LOW_51_BIT_MASK
            // ];

            // let r = [
            //     rr[0]                           as u8,
            //     (rr[0] >>  8)                    as u8,
            //     (rr[0] >> 16)                    as u8,
            //     (rr[0] >> 24)                    as u8,
            //     (rr[0] >> 32)                    as u8,
            //     (rr[0] >> 40)                    as u8,
            //     ((rr[0] >> 48) | (rr[1] << 3)) as u8,
            //     (rr[1] >>  5)                    as u8,
            //     (rr[1] >> 13)                    as u8,
            //     (rr[1] >> 21)                    as u8,
            //     (rr[1] >> 29)                    as u8,
            //     (rr[1] >> 37)                    as u8,
            //     ((rr[1] >> 45) | (rr[2] << 6)) as u8,
            //     (rr[2] >>  2)                    as u8,
            //     (rr[2] >> 10)                    as u8,
            //     (rr[2] >> 18)                    as u8,
            //     (rr[2] >> 26)                    as u8,
            //     (rr[2] >> 34)                    as u8,
            //     (rr[2] >> 42)                    as u8,
            //     ((rr[2] >> 50) | (rr[3] << 1)) as u8,
            //     (rr[3] >>  7)                    as u8,
            //     (rr[3] >> 15)                    as u8,
            //     (rr[3] >> 23)                    as u8,
            //     (rr[3] >> 31)                    as u8,
            //     (rr[3] >> 39)                    as u8,
            //     ((rr[3] >> 47) | (rr[4] << 4)) as u8,
            //     (rr[4] >>  4)                    as u8,
            //     (rr[4] >> 12)                    as u8,
            //     (rr[4] >> 20)                    as u8,
            //     (rr[4] >> 28)                    as u8,
            //     (rr[4] >> 36)                    as u8,
            //     (rr[4] >> 44)                    as u8
            // ];

        }
        // Let h = limbs[0] + limbs[1]*2^51 + ... + limbs[4]*2^204.
        //
        // Write h = pq + r with 0 <= r < p.
        //
        // We want to compute r = h mod p.
        //
        // If h < 2*p = 2^256 - 38,
        // then q = 0 or 1,
        //
        // with q = 0 when h < p
        //  and q = 1 when h >= p.
        //
        // Notice that h >= p <==> h + 19 >= p + 19 <==> h + 19 >= 2^255.
        // Therefore q can be computed as the carry bit of h + 19.

        // First, reduce the limbs to ensure h < 2*p.
        let mut limbs = FieldElement51::reduce(self.limbs).limbs;

        let mut q = (limbs[0] + 19) >> 51;
        q = (limbs[1] + q) >> 51;
        q = (limbs[2] + q) >> 51;
        q = (limbs[3] + q) >> 51;
        q = (limbs[4] + q) >> 51;

        // Now we can compute r as r = h - pq = r - (2^255-19)q = r + 19q - 2^255q

        limbs[0] += 19 * q;

        // Now carry the result to compute r + 19q ...
        let low_51_bit_mask = (1u64 << 51) - 1;
        limbs[1] += limbs[0] >> 51;
        limbs[0] &= low_51_bit_mask;
        limbs[2] += limbs[1] >> 51;
        limbs[1] &= low_51_bit_mask;
        limbs[3] += limbs[2] >> 51;
        limbs[2] &= low_51_bit_mask;
        limbs[4] += limbs[3] >> 51;
        limbs[3] &= low_51_bit_mask;
        // ... but instead of carrying (limbs[4] >> 51) = 2^255q
        // into another limb, discard it, subtracting the value
        limbs[4] &= low_51_bit_mask;

        // Now arrange the bits of the limbs.
        let mut s = [0u8;32];
        s[ 0] =   limbs[0]                           as u8;
        s[ 1] =  (limbs[0] >>  8)                    as u8;
        s[ 2] =  (limbs[0] >> 16)                    as u8;
        s[ 3] =  (limbs[0] >> 24)                    as u8;
        s[ 4] =  (limbs[0] >> 32)                    as u8;
        s[ 5] =  (limbs[0] >> 40)                    as u8;
        s[ 6] = ((limbs[0] >> 48) | (limbs[1] << 3)) as u8;
        s[ 7] =  (limbs[1] >>  5)                    as u8;
        s[ 8] =  (limbs[1] >> 13)                    as u8;
        s[ 9] =  (limbs[1] >> 21)                    as u8;
        s[10] =  (limbs[1] >> 29)                    as u8;
        s[11] =  (limbs[1] >> 37)                    as u8;
        s[12] = ((limbs[1] >> 45) | (limbs[2] << 6)) as u8;
        s[13] =  (limbs[2] >>  2)                    as u8;
        s[14] =  (limbs[2] >> 10)                    as u8;
        s[15] =  (limbs[2] >> 18)                    as u8;
        s[16] =  (limbs[2] >> 26)                    as u8;
        s[17] =  (limbs[2] >> 34)                    as u8;
        s[18] =  (limbs[2] >> 42)                    as u8;
        s[19] = ((limbs[2] >> 50) | (limbs[3] << 1)) as u8;
        s[20] =  (limbs[3] >>  7)                    as u8;
        s[21] =  (limbs[3] >> 15)                    as u8;
        s[22] =  (limbs[3] >> 23)                    as u8;
        s[23] =  (limbs[3] >> 31)                    as u8;
        s[24] =  (limbs[3] >> 39)                    as u8;
        s[25] = ((limbs[3] >> 47) | (limbs[4] << 4)) as u8;
        s[26] =  (limbs[4] >>  4)                    as u8;
        s[27] =  (limbs[4] >> 12)                    as u8;
        s[28] =  (limbs[4] >> 20)                    as u8;
        s[29] =  (limbs[4] >> 28)                    as u8;
        s[30] =  (limbs[4] >> 36)                    as u8;
        s[31] =  (limbs[4] >> 44)                    as u8;

        // High bit should be zero.
        // DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
        // debug_assert!((s[31] & 0b1000_0000u8) == 0u8);

        s
    }

    /// Given `k > 0`, return `self^(2^k)`.
    #[rustfmt::skip] // keep alignment of c* calculations
    pub fn pow2k(&self, mut k: u32) -> (r: FieldElement51)
        ensures
            true
    {
        // DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
        // debug_assert!( k > 0 );


        let mut a: [u64; 5] = self.limbs;

        loop
            invariant
                true
            decreases k
        {
            proof {
                assume(false);
            }
            // Precondition: assume input limbs a[i] are bounded as
            //
            // a[i] < 2^(51 + b)
            //
            // where b is a real parameter measuring the "bit excess" of the limbs.

            // Precomputation: 64-bit multiply by 19.
            //
            // This fits into a u64 whenever 51 + b + lg(19) < 64.
            //
            // Since 51 + b + lg(19) < 51 + 4.25 + b
            //                       = 55.25 + b,
            // this fits if b < 8.75.
            let a3_19 = 19 * a[3];
            let a4_19 = 19 * a[4];

            // Multiply to get 128-bit coefficients of output.
            //
            // The 128-bit multiplications by 2 turn into 1 slr + 1 slrd each,
            // which doesn't seem any better or worse than doing them as precomputations
            // on the 64-bit inputs.
            let     c0: u128 = m(a[0],  a[0]) + 2*( m(a[1], a4_19) + m(a[2], a3_19) );
            let mut c1: u128 = m(a[3], a3_19) + 2*( m(a[0],  a[1]) + m(a[2], a4_19) );
            let mut c2: u128 = m(a[1],  a[1]) + 2*( m(a[0],  a[2]) + m(a[4], a3_19) );
            let mut c3: u128 = m(a[4], a4_19) + 2*( m(a[0],  a[3]) + m(a[1],  a[2]) );
            let mut c4: u128 = m(a[2],  a[2]) + 2*( m(a[0],  a[4]) + m(a[1],  a[3]) );

            // Same bound as in multiply:
            //    c[i] < 2^(102 + 2*b) * (1+i + (4-i)*19)
            //         < 2^(102 + lg(1 + 4*19) + 2*b)
            //         < 2^(108.27 + 2*b)
            //
            // The carry (c[i] >> 51) fits into a u64 when
            //    108.27 + 2*b - 51 < 64
            //    2*b < 6.73
            //    b < 3.365.
            //
            // So we require b < 3 to ensure this fits.
            // DISABLED DUE TO NO VERUS SUPPORT FOR PANICS
            // debug_assert!(a[0] < (1 << 54));
            // debug_assert!(a[1] < (1 << 54));
            // debug_assert!(a[2] < (1 << 54));
            // debug_assert!(a[3] < (1 << 54));
            // debug_assert!(a[4] < (1 << 54));

            // const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1; // already defined

            // Casting to u64 and back tells the compiler that the carry is bounded by 2^64, so
            // that the addition is a u128 + u64 rather than u128 + u128.
            c1 += ((c0 >> 51) as u64) as u128;
            a[0] = (c0 as u64) & LOW_51_BIT_MASK;

            c2 += ((c1 >> 51) as u64) as u128;
            a[1] = (c1 as u64) & LOW_51_BIT_MASK;

            c3 += ((c2 >> 51) as u64) as u128;
            a[2] = (c2 as u64) & LOW_51_BIT_MASK;

            c4 += ((c3 >> 51) as u64) as u128;
            a[3] = (c3 as u64) & LOW_51_BIT_MASK;

            let carry: u64 = (c4 >> 51) as u64;
            a[4] = (c4 as u64) & LOW_51_BIT_MASK;

            // To see that this does not overflow, we need a[0] + carry * 19 < 2^64.
            //
            // c4 < a2^2 + 2*a0*a4 + 2*a1*a3 + (carry from c3)
            //    < 2^(102 + 2*b + lg(5)) + 2^64.
            //
            // When b < 3 we get
            //
            // c4 < 2^110.33  so that carry < 2^59.33
            //
            // so that
            //
            // a[0] + carry * 19 < 2^51 + 19 * 2^59.33 < 2^63.58
            //
            // and there is no overflow.
            a[0] += carry * 19;

            // Now a[1] < 2^51 + 2^(64 -51) = 2^51 + 2^13 < 2^(51 + epsilon).
            a[1] += a[0] >> 51;
            a[0] &= LOW_51_BIT_MASK;

            // Now all a[i] < 2^(51 + epsilon) and a = self^(2^k).

            k -= 1;
            if k == 0 {
                break;
            }
        }

        // ADAPTED CODE LINE: limbs is now a named field
        FieldElement51{limbs: a}
    }

    /// Returns the square of this field element.
    pub fn square(&self) -> FieldElement51 {
        self.pow2k(1)
    }

    /// Returns 2 times the square of this field element.
    pub fn square2(&self) -> (r: FieldElement51)
        ensures
            true
    {
        let mut square = self.pow2k(1);
        for i in 0..5 {
            proof {
                assume(false);
            }
            square.limbs[i] *= 2;
        }

        square
    }
}

fn main()
{}

}
