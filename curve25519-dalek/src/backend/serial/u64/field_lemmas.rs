#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::common_verus::*;

// Lemmas and spec functions only used in field_verus.rs
// A lemma should be in this file instead of `common_verus` if:
//  - It references some constant prominent in `field_verus` (e.g. 51 for bit operations, 2^255 -19)
//  - It defines or reasons about a spec function relevant only to `field_verus`
verus! {

// p = 2^255 - 19
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

// Specialization for b = 51
pub proof fn lemma_two_factoring_51(k : nat, ai: u64)
    ensures
        pow2(k + 51) * ai == pow2(k) * (pow2(51) * ai)
{
    lemma_two_factoring(k, 51, ai);
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
        broadcast use lemma_mul_is_distributive_sub;
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

// >> preserves [<=]. Unfortunately, these operations are u128 and
// we need lemma_u128_shr_is_div.
pub proof fn lemma_shr_51_le(a: u128, b: u128)
    requires
        a <= b
    ensures
        (a >> 51) <= (b >> 51)
{
    lemma_pow2_pos(51);
    lemma2_to64_rest(); // pow2(51) value
    lemma_u128_shr_is_div(a, 51);
    lemma_u128_shr_is_div(b, 51);
    lemma_div_is_ordered(a as int, b as int, 51);
}

// Corollary of above, using the identity (a << x) >> x == a for u64::MAX
pub proof fn lemma_shr_51_fits_u64(a: u128)
    requires
        a <= (u64::MAX as u128) << 51
    ensures
        (a >> 51) <= (u64::MAX as u128)

{
    assert(((u64::MAX as u128) << 51) >> 51 == (u64::MAX as u128)) by (compute);
    lemma_shr_51_le(a, (u64::MAX as u128) << 51);
}

// Auxiliary datatype lemma
// Should work for any k <= 64, but the proofs are convoluted and we can't use BV
// (x as u64) = x % 2^64, so x = 2^64 * (x / 2^64) + (x as u64). Thus
// (x as u64) % 2^k = (x as u64) % 2^k, because 2^k | 2^64 * (...) for k <= 64
pub proof fn lemma_cast_then_mod_51(x: u128)
    ensures
        (x as u64) % (pow2(51) as u64) == x % (pow2(51) as u128)
{
    lemma2_to64_rest(); // pow2(51 | 64)
    assert( (x as u64) % 0x8000000000000 == x % 0x8000000000000) by (bit_vector);
}

// Explicit and mod-p identities for squaring as_nat conversion
pub proof fn as_nat_squared(v: [u64; 5])
    ensures
        as_nat(v) * as_nat(v) ==
        pow2(8 * 51) * (v[4] * v[4]) +
        pow2(7 * 51) * (2 * (v[3] * v[4])) +
        pow2(6 * 51) * (v[3] * v[3] + 2 * (v[2] * v[4])) +
        pow2(5 * 51) * (2 * (v[2] * v[3]) + 2 * (v[1] * v[4])) +
        pow2(4 * 51) * (v[2] * v[2] + 2 * (v[1] * v[3]) + 2 * (v[0] * v[4])) +
        pow2(3 * 51) * (2 * (v[1] * v[2]) + 2 * (v[0] * v[3])) +
        pow2(2 * 51) * (v[1] * v[1] + 2 * (v[0] * v[2])) +
        pow2(1 * 51) * (2 * (v[0] * v[1])) +
                       (v[0] * v[0]),
        // and the mod equality
        (as_nat(v) * as_nat(v)) % p() ==
        (
            pow2(4 * 51) * (v[2] * v[2] + 2 * (v[1] * v[3]) + 2 * (v[0] * v[4])) +
            pow2(3 * 51) * (2 * (v[1] *  v[2]) + 2 * (v[0] *  v[3]) + 19 * (v[4] * v[4])) +
            pow2(2 * 51) * (v[1] * v[1] + 2 * (v[0] *  v[2]) + 19 * (2 * (v[3] * v[4]))) +
            pow2(1 * 51) * (2 * (v[0] *  v[1]) + 19 * (v[3] * v[3] + 2 * (v[2] * v[4]))) +
                           (v[0] *  v[0] + 19 * (2 * (v[2] * v[3]) + 2 * (v[1] * v[4])))
        ) as nat % p()
{
    let v0 = v[0];
    let v1 = v[1];
    let v2 = v[2];
    let v3 = v[3];
    let v4 = v[4];

    let s1 = pow2(1 * 51);
    let s2 = pow2(2 * 51);
    let s3 = pow2(3 * 51);
    let s4 = pow2(4 * 51);
    let s5 = pow2(5 * 51);
    let s6 = pow2(6 * 51);
    let s7 = pow2(7 * 51);
    let s8 = pow2(8 * 51);

    assert(s1 * s1 == s2) by {
        lemma_pow2_adds(51, 51)
    }
    assert(s1 * s2 == s2 * s1 == s3) by {
        lemma_pow2_adds(51, 102)
    }
    assert(s1 * s3 == s3 * s1 == s4) by {
        lemma_pow2_adds(51, 153)
    }
    assert(s1 * s4 == s4 * s1 == s5) by {
        lemma_pow2_adds(51, 204)
    }
    assert(s2 * s2 ==s4) by {
        lemma_pow2_adds(102, 102)
    }
    assert(s2 * s3 == s3 * s2 == s5) by {
        lemma_pow2_adds(102, 153)
    }
    assert(s2 * s4 == s4 * s2 == s6) by {
        lemma_pow2_adds(102, 204)
    }
    assert(s3 * s3 == s6) by {
        lemma_pow2_adds(153, 153)
    }
    assert(s3 * s4 == s4 * s3 == s7) by {
        lemma_pow2_adds(153, 204)
    }
    assert(s4 * s4 == s8) by {
        lemma_pow2_adds(204, 204)
    }

    assert(as_nat(v) * as_nat(v) ==
        v0 * as_nat(v) +
        (s1 * v1) * as_nat(v) +
        (s2 * v2) * as_nat(v) +
        (s3 * v3) * as_nat(v) +
        (s4 * v4) * as_nat(v)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    // because of the sheer number of possible associativity/distributivity groupings we have
    // to help the solver along by intermittently asserting chunks
    assert(v0 * as_nat(v) ==
        v0 * v0 +
        v0 * (s1 * v1) +
        v0 * (s2 * v2) +
        v0 * (s3 * v3) +
        v0 * (s4 * v4)
        ==
        s4 * (v0 * v4) +
        s3 * (v0 * v3) +
        s2 * (v0 * v2) +
        s1 * (v0 * v1) +
        v0 * v0
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    assert((s1 * v1) * as_nat(v) ==
        s5 * (v1 * v4) +
        s4 * (v1 * v3) +
        s3 * (v1 * v2) +
        s2 * (v1 * v1) +
        s1 * (v0 * v1)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    assert((s2 * v2) * as_nat(v) ==
        s6 * (v2 * v4) +
        s5 * (v2 * v3) +
        s4 * (v2 * v2) +
        s3 * (v1 * v2) +
        s2 * (v0 * v2)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    assert((s3 * v3) * as_nat(v) ==
        s7 * (v3 * v4) +
        s6 * (v3 * v3) +
        s5 * (v2 * v3) +
        s4 * (v1 * v3) +
        s3 * (v0 * v3)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    assert((s4 * v4) * as_nat(v) ==
        s8 * (v4 * v4) +
        s7 * (v3 * v4) +
        s6 * (v2 * v4) +
        s5 * (v1 * v4) +
        s4 * (v0 * v4)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    // we now mash them all together
    assert(as_nat(v) * as_nat(v) ==
        s8 * (v4 * v4) +
        s7 * (2 * (v3 * v4)) +
        s6 * (v3 * v3 + 2 * (v2 * v4)) +
        s5 * (2 * (v2 * v3) + 2 * (v1 * v4)) +
        s4 * (v2 * v2 + 2 * (v1 * v3) + 2 * (v0 * v4)) +
        s3 * (2 * (v1 * v2) + 2 * (v0 * v3)) +
        s2 * (v1 * v1 + 2 * (v0 * v2)) +
        s1 * (2 * (v0 * v1)) +
             (v0 * v0)
    ) by {
        broadcast use lemma_mul_is_associative;
        broadcast use lemma_mul_is_distributive_add;
        assert(v0 * v1 + v0 * v1 == 2 * (v0 * v1));
        assert(v0 * v2 + v0 * v2 == 2 * (v0 * v2));
        assert(v0 * v3 + v0 * v3 == 2 * (v0 * v3));
        assert(v0 * v4 + v0 * v4 == 2 * (v0 * v4));
        assert(v1 * v2 + v1 * v2 == 2 * (v1 * v2));
        assert(v1 * v3 + v1 * v3 == 2 * (v1 * v3));
        assert(v1 * v4 + v1 * v4 == 2 * (v1 * v4));
        assert(v2 * v3 + v2 * v3 == 2 * (v2 * v3));
        assert(v2 * v4 + v2 * v4 == 2 * (v2 * v4));
        assert(v3 * v4 + v3 * v4 == 2 * (v3 * v4));
    }

    // This is the explicit version, now we can take everything mod p

    // p well defined
    pow255_gt_19();

    // By definition, p = s^5 - 19
    // equivalently,
    // s^5 = (p + 19)
    // s^6 = s * (p + 19)
    // s^7 = s^2 * (p + 19)
    // s^8 = s^3 * (p + 19)
    assert(s5 == (p() + 19));

    // we pack together terms to slim down expressions;

    let c0_base = v0 *  v0;
    let c0_x19 = 2 * (v2 * v3) + 2 * (v1 * v4);
    let c0 = c0_base + 19 * c0_x19;

    let c1_base = 2 * (v0 *  v1);
    let c1_x19 = v3 * v3 + 2 * (v2 * v4);
    let c1 = c1_base + 19 * c1_x19;

    let c2_base = v1 * v1 + 2 * (v0 *  v2);
    let c2_x19 = 2 * (v3 * v4);
    let c2 = c2_base + 19 * c2_x19;

    let c3_base = 2 * (v1 *  v2) + 2 * (v0 *  v3);
    let c3_x19 = v4 * v4;
    let c3 = c3_base + 19 * c3_x19;

    let c4 = v2 *  v2 + 2 * (v1 *  v3) + 2 * (v0 *  v4);

    // group in preparation for the substitution
    assert(as_nat(v) * as_nat(v) ==
        s4 * c4 +
        s3 * (s5 * c3_x19 + c3_base) +
        s2 * (s5 * c2_x19 + c2_base) +
        s1 * (s5 * c1_x19 + c1_base) +
             (s5 * c0_x19 + c0_base)
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        broadcast use lemma_mul_is_associative;
    }

    // Next we use the identity s5 = p + 19
    assert(s5 * c3_x19 + c3_base == p() * c3_x19 + c3) by {
        lemma_mul_is_distributive_add(c3_x19 as int, p() as int, 19);
    }

    assert(s5 * c2_x19 + c2_base == p() * c2_x19 + c2) by {
        lemma_mul_is_distributive_add(c2_x19 as int, p() as int, 19);
    }

    assert(s5 * c1_x19 + c1_base == p() * c1_x19 + c1) by {
        lemma_mul_is_distributive_add(c1_x19 as int, p() as int, 19);
    }

    assert(s5 * c0_x19 + c0_base == p() * c0_x19 + c0) by {
        lemma_mul_is_distributive_add(c0_x19 as int, p() as int, 19);
    }

    // in summary, we can reorder and regroup terms to get X * p() + Y
    assert(as_nat(v) * as_nat(v) ==
        p() * ( s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19 ) +
        (
            s4 * c4 +
            s3 * c3 +
            s2 * c2 +
            s1 * c1 +
                 c0
        )
    ) by {
        broadcast use lemma_mul_is_distributive_add;
        // we don't broadcast assoc, too many trigger matches
        lemma_mul_is_associative(s3 as int, p() as int, c3_x19 as int);
        lemma_mul_is_associative(s2 as int, p() as int, c2_x19 as int);
        lemma_mul_is_associative(s1 as int, p() as int, c1_x19 as int);
        lemma_mul_is_associative(p() as int, s3 as int, c3_x19 as int);
        lemma_mul_is_associative(p() as int, s2 as int, c2_x19 as int);
        lemma_mul_is_associative(p() as int, s1 as int, c1_x19 as int);
    }


    let k = ( s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19 );
    let sum = (
            s4 * c4 +
            s3 * c3 +
            s2 * c2 +
            s1 * c1 +
                 c0
        );

    assert(as_nat(v) * as_nat(v) == k * p() + sum);
    assert(k * p() + sum == (k as nat) * p() + (sum as nat));

    // Now, we simply move to mod p

    assert((as_nat(v) * as_nat(v)) % p() == ((k as nat) * p() + (sum as nat)) % p() );
    assert(
        ((k as nat) * p() + (sum as nat)) % p() ==
        (sum as nat) % p()
    ) by {
        lemma_mod_sum_factor(k as int, sum as int, p() as int);
    }

    // sanity check
    assert(s4 * c4 == pow2(4 * 51) * (v[2] * v[2] + 2 * (v[1] * v[3]) + 2 * (v[0] * v[4])));
    assert(s3 * c3 == pow2(3 * 51) * (2 * (v[1] *  v[2]) + 2 * (v[0] *  v[3]) + 19 * (v[4] * v[4])));
    assert(s2 * c2 == pow2(2 * 51) * (v[1] * v[1] + 2 * (v[0] *  v[2]) + 19 * (2 * (v[3] * v[4]))));
    assert(s1 * c1 == pow2(1 * 51) * (2 * (v[0] *  v[1]) + 19 * (v[3] * v[3] + 2 * (v[2] * v[4]))));
    assert(c0 == (v[0] *  v[0] + 19 * (2 * (v[2] * v[3]) + 2 * (v[1] * v[4]))));
}

pub proof fn as_nat_k(a: [u64;5], k: u64)
    requires
        forall |i:int| 0 <= i < 5 ==> (k * a[i]) <= u64::MAX
    ensures
        as_nat([
            (k * a[0]) as u64,
            (k * a[1]) as u64,
            (k * a[2]) as u64,
            (k * a[3]) as u64,
            (k * a[4]) as u64
            ]) == k * as_nat(a)
{
    let ka = [
            (k * a[0]) as u64,
            (k * a[1]) as u64,
            (k * a[2]) as u64,
            (k * a[3]) as u64,
            (k * a[4]) as u64
            ];
    lemma_mul_is_associative(pow2( 51) as int, a[1] as int, k as int);
    lemma_mul_is_associative(pow2(102) as int, a[2] as int, k as int);
    lemma_mul_is_associative(pow2(153) as int, a[3] as int, k as int);
    lemma_mul_is_associative(pow2(204) as int, a[4] as int, k as int);

    assert(as_nat(ka) ==
        k * a[0] +
        k * (pow2( 51) * a[1]) +
        k * (pow2(102) * a[2]) +
        k * (pow2(153) * a[3]) +
        k * (pow2(204) * a[4])
    );
    broadcast use lemma_mul_is_distributive_add;
}

// Auxiliary lemma for reordering terms in the pow2k proof
pub proof fn lemma_reorder_mul(a: int, b: int)
    ensures
        2 * (a * (19 * b)) == 19 * (2 * (a * b))
{
    // 2*( a * (19 * b)) = (2 * a) * (19 * b)
    lemma_mul_is_associative(2, a, 19 * b);
    // (2 * a) * (19 * b) = (19 * b) * (2 * a) = 19 * (b * (2 * a))
    lemma_mul_is_associative(19, b, 2 * a);
    // (b * (2 * a)) = (b * (a * 2)) = 2 * (a * b)
    lemma_mul_is_associative(b, a, 2);
}

// dummy, so we can call `verus`
fn main() {}

}
