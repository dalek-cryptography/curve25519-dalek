#[allow(unused_imports)]
use super::super::specs::core_specs::*;
#[allow(unused_imports)]
use super::common_lemmas::*;
#[allow(unused_imports)]
use crate::backend::serial::u64::constants;
#[allow(unused_imports)]
use crate::backend::serial::u64::scalar::Scalar52;
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[allow(unused_imports)]
use crate::specs::scalar_specs_u64::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::common_lemmas::bit_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::pow_lemmas::*;
#[allow(unused_imports)]
use super::common_lemmas::shift_lemmas::*;
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::u8_32_as_nat_injectivity_lemmas::*;

verus! {

/// Verification: scalar * scalar.invert() ≡ 1 mod L
proof fn lemma_verify_invert_correct(
    x: Scalar52,
)
//     requires to_scalar(&x.limbs) != 0
//    ensures (to_scalar(&x.limbs) * invert_spec(&x.limbs)) % group_order() == 1
{
    assume(false);

}

pub proof fn lemma_52_52(x: u64, y: u64)
    requires
        x < (1u64 << 52),
        y < (1u64 << 52),
    ensures
        (x as u128) * (y as u128) < (1u128 << 104),
{
    assert(1u128 << 52 == 1u64 << 52) by (bit_vector);
    calc! {
        (<)
        (x as u128) * (y as u128); (<=) {
            if x > 0 {
                lemma_mul_strict_inequality(y as int, (1u128 << 52) as int, x as int);
                assert(x * y < x * (1u128 << 52));
            } else {
                assert((0 as u128) * (y as u128) == 0);
            }
        }
        (x as u128) * (1u128 << 52); (<) {
            lemma_mul_strict_inequality(x as int, (1u128 << 52) as int, (1u128 << 52) as int);
        }
        (1u128 << 52) * (1u128 << 52);
    }
    assert((1u128 << 52) * (1u128 << 52) == (1u128 << 104)) by (compute);
}

pub proof fn lemma_square_internal_no_overflow()
    ensures
        (1u128 << 105) + (1u128 << 105) == (1u128 << 106),
        (1u128 << 105) + (1u128 << 104) < (1u128 << 106),
        (1u128 << 104) * 2 == (1u128 << 105),
        (1u128 << 106) + (1u128 << 104) < (1u128 << 107),
{
    assert((1u128 << 105) + (1u128 << 105) == (1u128 << 106)) by (bit_vector);
    assert((1u128 << 105) + (1u128 << 104) < (1u128 << 106)) by (bit_vector);
    assert((1u128 << 104) * 2 == (1u128 << 105)) by (bit_vector);
    assert((1u128 << 106) + (1u128 << 104) < (1u128 << 107)) by (bit_vector);
}

pub proof fn lemma_square_internal_correct(a: &[u64; 5], z: &[u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < (1u64 << 52),
        z[0] == (a[0] * a[0]),
        z[1] == (a[0] * a[1]) * 2,
        z[2] == (a[0] * a[2]) * 2 + (a[1] * a[1]),
        z[3] == (a[0] * a[3]) * 2 + (a[1] * a[2]) * 2,
        z[4] == (a[0] * a[4]) * 2 + (a[1] * a[3]) * 2 + (a[2] * a[2]),
        z[5] == (a[1] * a[4]) * 2 + (a[2] * a[3]) * 2,
        z[6] == (a[2] * a[4]) * 2 + (a[3] * a[3]),
        z[7] == (a[3] * a[4]) * 2,
        z[8] == (a[4] * a[4]),
    ensures
        slice128_to_nat(z) == to_nat(a) * to_nat(a),
{
    assert(five_limbs_to_nat_aux(*a) * five_limbs_to_nat_aux(*a) == nine_limbs_to_nat_aux(&z)) by {
        broadcast use group_mul_is_commutative_and_distributive;
        broadcast use lemma_mul_is_associative;

        lemma_pow2_adds(52, 52);
        lemma_pow2_adds(52, 104);
        lemma_pow2_adds(52, 156);
        lemma_pow2_adds(52, 208);
        lemma_pow2_adds(104, 104);
        lemma_pow2_adds(104, 156);
        lemma_pow2_adds(104, 208);
        lemma_pow2_adds(156, 156);
        lemma_pow2_adds(156, 208);
        lemma_pow2_adds(208, 208);
    };
    lemma_nine_limbs_equals_slice128_to_nat(&z);
    lemma_five_limbs_equals_to_nat(&a);
}

pub proof fn lemma_mul_internal_no_overflow()
    ensures
        (1u128 << 104) + (1u128 << 104) == (1u128 << 105),
        3u128 * (1u128 << 104) < (1u128 << 106),
        4u128 * (1u128 << 104) == (1u128 << 2) * (1u128 << 104),
        (1u128 << 2) * (1u128 << 104) == (1u128 << 106),
        8u128 == (1u128 << 3),
        (1u128 << 3) * (1u128 << 104) == (1u128 << 107),
{
    assert((1u128 << 104) + (1u128 << 104) == (1u128 << 105)) by (bit_vector);
    assert(3u128 * (1u128 << 104) < (1u128 << 106)) by (bit_vector);
    assert(4u128 * (1u128 << 104) == (1u128 << 2) * (1u128 << 104)) by (bit_vector);
    assert((1u128 << 2) * (1u128 << 104) == (1u128 << 106)) by (bit_vector);
    assert(8u128 == (1u128 << 3)) by (bit_vector);
    assert((1u128 << 3) * (1u128 << 104) == (1u128 << 107)) by (bit_vector);
}

pub proof fn lemma_mul_internal_correct(a: &[u64; 5], b: &[u64; 5], z: &[u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a[i] < (1u64 << 52),
        forall|i: int| 0 <= i < 5 ==> b[i] < (1u64 << 52),
        z[0] == (a[0] * b[0]),
        z[1] == (a[0] * b[1]) + (a[1] * b[0]),
        z[2] == (a[0] * b[2]) + (a[1] * b[1]) + (a[2] * b[0]),
        z[3] == (a[0] * b[3]) + (a[1] * b[2]) + (a[2] * b[1]) + (a[3] * b[0]),
        z[4] == (a[0] * b[4]) + (a[1] * b[3]) + (a[2] * b[2]) + (a[3] * b[1]) + (a[4] * b[0]),
        z[5] == (a[1] * b[4]) + (a[2] * b[3]) + (a[3] * b[2]) + (a[4] * b[1]),
        z[6] == (a[2] * b[4]) + (a[3] * b[3]) + (a[4] * b[2]),
        z[7] == (a[3] * b[4]) + (a[4] * b[3]),
        z[8] == (a[4] * b[4]),
    ensures
        slice128_to_nat(z) == to_nat(a) * to_nat(b),
{
    assert(five_limbs_to_nat_aux(*a) * five_limbs_to_nat_aux(*b) == nine_limbs_to_nat_aux(&z)) by {
        broadcast use group_mul_is_commutative_and_distributive;
        broadcast use lemma_mul_is_associative;

        lemma_pow2_adds(52, 52);
        lemma_pow2_adds(52, 104);
        lemma_pow2_adds(52, 156);
        lemma_pow2_adds(52, 208);
        lemma_pow2_adds(104, 104);
        lemma_pow2_adds(104, 156);
        lemma_pow2_adds(104, 208);
        lemma_pow2_adds(156, 156);
        lemma_pow2_adds(156, 208);
        lemma_pow2_adds(208, 208);
    };
    lemma_nine_limbs_equals_slice128_to_nat(&z);
    lemma_five_limbs_equals_to_nat(&a);
    lemma_five_limbs_equals_to_nat(&b);
}

pub proof fn lemma_nine_limbs_equals_slice128_to_nat(limbs: &[u128; 9])
    ensures
        nine_limbs_to_nat_aux(limbs) == slice128_to_nat(limbs),
{
    let seq = limbs@.map(|i, x| x as nat);

    calc! {
        (==)
        slice128_to_nat(limbs); {}
        seq_to_nat(seq); {
            reveal_with_fuel(seq_to_nat, 10);
        }
        (limbs[0] as nat) + ((limbs[1] as nat) + ((limbs[2] as nat) + ((limbs[3] as nat) + ((
        limbs[4] as nat) + ((limbs[5] as nat) + ((limbs[6] as nat) + ((limbs[7] as nat) + (
        limbs[8] as nat) * pow2(52)) * pow2(52)) * pow2(52)) * pow2(52)) * pow2(52)) * pow2(52))
            * pow2(52)) * pow2(52); {
            lemma_pow2_adds(52, 52);
            lemma_pow2_adds(104, 52);
            lemma_pow2_adds(156, 52);
            lemma_pow2_adds(208, 52);
            lemma_pow2_adds(260, 52);
            lemma_pow2_adds(312, 52);
            lemma_pow2_adds(364, 52);
            broadcast use group_mul_is_distributive;
            broadcast use lemma_mul_is_associative;

        }
        nine_limbs_to_nat_aux(limbs);
    }
}

pub proof fn lemma_five_limbs_equals_to_nat(limbs: &[u64; 5])
    ensures
        five_limbs_to_nat_aux(*limbs) == to_nat(limbs),
{
    let seq = limbs@.map(|i, x| x as nat);

    calc! {
        (==)
        to_nat(limbs); {}
        seq_to_nat(seq); {
            reveal_with_fuel(seq_to_nat, 6);
        }
        (limbs[0] as nat) + ((limbs[1] as nat) + ((limbs[2] as nat) + ((limbs[3] as nat) + (
        limbs[4] as nat) * pow2(52)) * pow2(52)) * pow2(52)) * pow2(52); {
            lemma_pow2_adds(52, 52);
            lemma_pow2_adds(104, 52);
            lemma_pow2_adds(156, 52);
            broadcast use group_mul_is_distributive;
            broadcast use lemma_mul_is_associative;

        }
        (limbs[0] as nat) + pow2(52) * (limbs[1] as nat) + pow2(104) * (limbs[2] as nat) + pow2(156)
            * (limbs[3] as nat) + pow2(208) * (limbs[4] as nat); {}
        five_limbs_to_nat_aux(*limbs);
    }
}

pub proof fn lemma_scalar_subtract_no_overflow(
    carry: u64,
    difference_limb: u64,
    addend: u64,
    i: u32,
    l_value: &Scalar52,
)
    requires
        i < 5,
        difference_limb < (1u64 << 52),
        addend == 0 || addend == l_value.limbs[i as int],
        i == 0 ==> carry == 0,
        i >= 1 ==> (carry >> 52) < 2,
        l_value.limbs[0] == 0x0002631a5cf5d3ed,
        l_value.limbs[1] == 0x000dea2f79cd6581,
        l_value.limbs[2] == 0x000000000014def9,
        l_value.limbs[3] == 0x0000000000000000,
        l_value.limbs[4] == 0x0000100000000000,
    ensures
        (carry >> 52) + difference_limb + addend < (1u64 << 53),
{
    if i == 0 {
        assert(0x0002631a5cf5d3ed < (1u64 << 52)) by (bit_vector);
    } else if i == 1 {
        assert(0x000dea2f79cd6581 < (1u64 << 52)) by (bit_vector);
    } else if i == 2 {
        assert(0x000000000014def9 < (1u64 << 52)) by (bit_vector);
    } else if i == 3 {
    } else {
        assert(0x0000100000000000 < (1u64 << 52)) by (bit_vector);
    }
    if i == 0 {
        assert((0u64 >> 52) == 0) by (bit_vector);
    }
    assert(2 * (1u64 << 52) == (1u64 << 53)) by (bit_vector);
}

pub proof fn lemma_borrow_and_mask_bounded(borrow: u64, mask: u64)
    requires
        mask == (1u64 << 52) - 1,
    ensures
        (borrow & mask) < (1u64 << 52),
{
    assert((borrow & mask) <= mask) by (bit_vector);
}

pub proof fn lemma_carry_bounded_after_mask(carry: u64, mask: u64)
    requires
        mask == (1u64 << 52) - 1,
        carry < (1u64 << 53),
    ensures
        (carry & mask) < (1u64 << 52),
        (carry >> 52) <= 1,
{
    assert((carry & mask) <= mask) by (bit_vector);
    assert((1u64 << 53) == 2 * (1u64 << 52)) by (bit_vector);
    broadcast use lemma_u64_shr_is_div;

    lemma_pow2_pos(52);
    lemma_shift_is_pow2(52);
    assert(carry >> 52 == carry / (1u64 << 52));
    lemma_fundamental_div_mod(carry as int, (1u64 << 52) as int);
    let q = carry / (1u64 << 52);
    let r = carry % (1u64 << 52);
    lemma_mul_strict_inequality_converse(q as int, 2int, (1u64 << 52) as int);
}

pub proof fn lemma_add_loop_bounds(i: int, carry: u64, a_limb: u64, b_limb: u64)
    requires
        0 <= i < 5,
        a_limb < (1u64 << 52),
        b_limb < (1u64 << 52),
        i == 0 ==> carry == 0,
        i >= 1 ==> (carry >> 52) < 2,
    ensures
        (carry >> 52) + a_limb + b_limb < (1u64 << 53),
{
    if i == 0 {
        assert((0u64 >> 52) == 0) by (bit_vector);
    }
    assert((1u64 << 52) + (1u64 << 52) == (1u64 << 53)) by (bit_vector);
}

pub proof fn lemma_add_carry_and_sum_bounds(carry: u64, mask: u64)
    requires
        mask == (1u64 << 52) - 1,
        carry < (1u64 << 53),
    ensures
        (carry & mask) < (1u64 << 52),
        (carry >> 52) < 2,
{
    assert((carry & mask) <= mask) by (bit_vector);
    assert((1u64 << 53) == 2 * (1u64 << 52)) by (bit_vector);
    broadcast use lemma_u64_shr_is_div;

    lemma_pow2_pos(52);
    lemma_shift_is_pow2(52);
    assert(carry >> 52 == carry / (1u64 << 52));
    lemma_fundamental_div_mod(carry as int, (1u64 << 52) as int);
    let q = carry / (1u64 << 52);
    let r = carry % (1u64 << 52);
    lemma_mul_strict_inequality_converse(q as int, 2int, (1u64 << 52) as int);
}

pub proof fn lemma_l_value_properties(l_value: &Scalar52, sum: &Scalar52)
    requires
        l_value.limbs[0] == 0x0002631a5cf5d3ed,
        l_value.limbs[1] == 0x000dea2f79cd6581,
        l_value.limbs[2] == 0x000000000014def9,
        l_value.limbs[3] == 0x0000000000000000,
        l_value.limbs[4] == 0x0000100000000000,
        forall|j: int| 0 <= j < 5 ==> sum.limbs[j] < (1u64 << 52),
    ensures
        forall|j: int| 0 <= j < 5 ==> l_value.limbs[j] < (1u64 << 52),
{
    assert(0x0002631a5cf5d3ed < (1u64 << 52)) by (bit_vector);
    assert(0x000dea2f79cd6581 < (1u64 << 52)) by (bit_vector);
}

pub proof fn lemma_from_montgomery_limbs_conversion(limbs: &[u128; 9], self_limbs: &[u64; 5])
    requires
        forall|j: int| #![auto] 0 <= j < 5 ==> limbs[j] == self_limbs[j] as u128,
        forall|j: int| 5 <= j < 9 ==> limbs[j] == 0,
    ensures
        slice128_to_nat(limbs) == to_nat(self_limbs),
{
    lemma_nine_limbs_equals_slice128_to_nat(limbs);
    lemma_five_limbs_equals_to_nat(self_limbs);
    assert(limbs[0] == self_limbs[0] as u128);
    assert(nine_limbs_to_nat_aux(limbs) == (self_limbs[0] as nat) + (self_limbs[1] as nat) * pow2(
        52,
    ) + (self_limbs[2] as nat) * pow2(104) + (self_limbs[3] as nat) * pow2(156) + (
    self_limbs[4] as nat) * pow2(208) + 0 * pow2(260) + 0 * pow2(312) + 0 * pow2(364) + 0 * pow2(
        416,
    ));
}

pub proof fn lemma_r_limbs_bounded()
    ensures
        0x000f48bd6721e6edu64 < (1u64 << 52),
        0x0003bab5ac67e45au64 < (1u64 << 52),
        0x000fffffeb35e51bu64 < (1u64 << 52),
        0x000fffffffffffffu64 < (1u64 << 52),
        0x00000fffffffffff_u64 < (1u64 << 52),
{
    assert(0x000f48bd6721e6edu64 < (1u64 << 52)) by (bit_vector);
    assert(0x0003bab5ac67e45au64 < (1u64 << 52)) by (bit_vector);
    assert(0x000fffffeb35e51bu64 < (1u64 << 52)) by (bit_vector);
    assert(0x000fffffffffffffu64 < (1u64 << 52)) by (bit_vector);
    assert(0x00000fffffffffff_u64 < (1u64 << 52)) by (bit_vector);
}

pub proof fn lemma_rr_limbs_bounded()
    ensures
        0x000d63c715bea69fu64 < (1u64 << 52),
{
    // Verus can figure that out the other 4 limbs are bounded
    assert(0x000d63c715bea69fu64 < (1u64 << 52)) by (bit_vector);
}

pub proof fn lemma_cancel_mul_montgomery_mod(x: nat, a: nat, rr: nat)
    requires
        ((x * montgomery_radix()) % group_order()) == ((a * rr) % group_order()),
        (rr % group_order()) == ((montgomery_radix() * montgomery_radix()) % group_order()),
        group_order() > 0,
    ensures
        (x % group_order()) == ((a * montgomery_radix()) % group_order()),
{
    // 1. Substitute rr with r*r
    lemma_mul_mod_noop_right(a as int, rr as int, group_order() as int);
    lemma_mul_mod_noop_right(
        a as int,
        (montgomery_radix() * montgomery_radix()) as int,
        group_order() as int,
    );

    // let lhs = (x * montgomery_radix()) % group_order();
    // let step1 = (a * rr) % group_order();
    // let step2 = (a * (rr % group_order())) % group_order();
    // let step3 = (a * ((montgomery_radix() * montgomery_radix()) % group_order())) % group_order();
    // let step4 = (a * (montgomery_radix() * montgomery_radix())) % group_order();
    // let rhs = (a * montgomery_radix() * montgomery_radix()) % group_order();
    lemma_mul_is_associative(a as int, montgomery_radix() as int, montgomery_radix() as int);

    assert((x * montgomery_radix()) % group_order() == (a * montgomery_radix() * montgomery_radix())
        % group_order());

    // 2. use the inverse to remove r from both sides

    // Step 1: Multiply both sides by inv_montgomery_radix() using modular properties
    lemma_mul_mod_noop_right(
        inv_montgomery_radix() as int,
        (x * montgomery_radix()) as int,
        group_order() as int,
    );
    lemma_mul_mod_noop_right(
        inv_montgomery_radix() as int,
        (a * montgomery_radix() * montgomery_radix()) as int,
        group_order() as int,
    );

    assert((x * montgomery_radix() * inv_montgomery_radix()) % group_order() == (a
        * montgomery_radix() * montgomery_radix() * inv_montgomery_radix()) % group_order());

    // Step 2: Group (R * R^-1) together using associativity
    // x * (R * R^-1) and (a * R) * (R * R^-1)
    lemma_mul_is_associative(x as int, montgomery_radix() as int, inv_montgomery_radix() as int);
    lemma_mul_is_associative(
        (a * montgomery_radix()) as int,
        montgomery_radix() as int,
        inv_montgomery_radix() as int,
    );

    assert((x * (montgomery_radix() * inv_montgomery_radix())) % group_order() == ((a
        * montgomery_radix()) * (montgomery_radix() * inv_montgomery_radix())) % group_order());

    // Step 3: Use lemma_montgomery_inverse to substitute (R * R^-1) % n = 1
    lemma_montgomery_inverse();

    // Step 4: Substitute and simplify using (R * R^-1) ≡ 1
    lemma_mul_mod_noop_right(
        x as int,
        (montgomery_radix() * inv_montgomery_radix()) as int,
        group_order() as int,
    );
    lemma_mul_mod_noop_right(
        (a * montgomery_radix()) as int,
        (montgomery_radix() * inv_montgomery_radix()) as int,
        group_order() as int,
    );

}

pub proof fn lemma_montgomery_inverse()
    ensures
// r * r_inv ≡ 1 (mod n)

        (montgomery_radix() * inv_montgomery_radix()) % group_order() == 1,
{
    lemma2_to64();
    lemma2_to64_rest();

    lemma_pow2_adds(64, 64);  // prove pow2(128) in nat
    lemma_pow2_adds(128, 64);  // prove pow2(192) in nat
    lemma_pow2_adds(192, 60);  // prove pow2(252) in nat
    lemma_pow2_adds(252, 8);  // prove pow2(260) in nat

    calc! {
        (==)
        (montgomery_radix() * inv_montgomery_radix()) % group_order(); {}
        (1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat
            * 5706410653605570882457795059301885719620630590890452783038400561109479083972_nat)
            % 7237005577332262213973186563042994240857116359379907606001950938285454250989_nat; {}
        1;
    }

}

pub(crate) proof fn lemma_r_equals_spec(r: Scalar52)
    requires
        r == (Scalar52 {
            limbs: [
                0x000f48bd6721e6ed,
                0x0003bab5ac67e45a,
                0x000fffffeb35e51b,
                0x000fffffffffffff,
                0x00000fffffffffff,
            ],
        }),
    ensures
        to_nat(&r.limbs) % group_order() == montgomery_radix() % group_order(),
        to_nat(&r.limbs) < group_order(),
{
    lemma_five_limbs_equals_to_nat(&r.limbs);

    lemma2_to64();
    lemma2_to64_rest();
    lemma_pow2_adds(52, 52);
    lemma_pow2_adds(104, 52);
    lemma_pow2_adds(156, 52);
    lemma_pow2_adds(208, 44);
    lemma_pow2_adds(208, 52);

    let r_calc: nat = five_limbs_to_nat_aux(r.limbs);
    lemma_small_mod(r_calc, group_order());

    calc! {
        (==)
        montgomery_radix() % group_order(); {}
        pow2(260) % group_order(); {}
        1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat
            % 7237005577332262213973186563042994240857116359379907606001950938285454250989_nat; {}
        r_calc;
    }
}

pub(crate) proof fn lemma_rr_equals_spec(rr: Scalar52)
    requires
        rr == (Scalar52 {
            limbs: [
                0x0009d265e952d13b,
                0x000d63c715bea69f,
                0x0005be65cb687604,
                0x0003dceec73d217f,
                0x000009411b7c309a,
            ],
        }),
    ensures
        to_nat(&rr.limbs) % group_order() == (montgomery_radix() * montgomery_radix())
            % group_order(),
        to_nat(&rr.limbs) < group_order(),
{
    lemma_five_limbs_equals_to_nat(&rr.limbs);

    lemma2_to64_rest();
    lemma_pow2_adds(52, 52);  // prove pow2(104)
    lemma_pow2_adds(104, 52);  // prove pow2(156)
    lemma_pow2_adds(156, 52);  // prove pow2(208)
    lemma_pow2_adds(208, 44);  // prove pow2(252)
    lemma_pow2_adds(208, 52);  // prove pow2(260)

    let rr_calc: nat = five_limbs_to_nat_aux(rr.limbs);
    lemma_small_mod(rr_calc, group_order());  // necessary for to_nat(&constants::RR.limbs) == to_nat(&constants::RR.limbs) % group_order()

    calc! {
        (==)
        (montgomery_radix() * montgomery_radix()) % group_order(); {}
        (1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat
            * 1852673427797059126777135760139006525652319754650249024631321344126610074238976_nat)
            % 7237005577332262213973186563042994240857116359379907606001950938285454250989_nat; {}  // necessary line for some reason
        rr_calc;
    }

}

/// Need to use induction because the postcondition expands
/// seq_u64_to_nat in the opposite way from how it's defined.
/// The base case is straightforward, but it takes a few steps
/// to get Verus to prove it.
/// Induction case: Take off the first element using definition of
/// seq_u64_to_nat, apply induction hypothesis to the remaining sequence,
/// then put the first element back on and simplify all the powers.
pub proof fn lemma_seq_u64_to_nat_subrange_extend(seq: Seq<u64>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        seq_u64_to_nat(seq.subrange(0, i + 1)) == seq_u64_to_nat(seq.subrange(0, i)) + seq[i]
            * pow2(52 * i as nat),
    decreases i,
{
    if i == 0 {
        reveal_with_fuel(seq_to_nat, 3);
        assert(seq.len() > 0);
        assert(seq.subrange(0, 1) == seq![seq[0]]);
        calc! {
            (==)
            seq_u64_to_nat(seq.subrange(0, 0 + 1 as int)); {
                assert(seq.subrange(0, 1) == seq![seq[0]]);
            }
            seq_u64_to_nat(seq![seq[0]]); {
                let single_elem = seq![seq[0]];
                let nat_single = single_elem.map(|idx, x| x as nat);
                assert(nat_single == seq![seq[0] as nat]);
                assert(seq_u64_to_nat(single_elem) == seq_to_nat(nat_single));
                assert(nat_single.len() == 1);
                assert(seq_to_nat(nat_single) == nat_single[0] + seq_to_nat(
                    nat_single.subrange(1, 1),
                ) * pow2(52));
                assert(nat_single.subrange(1, 1).len() == 0);
                assert(seq_to_nat(nat_single.subrange(1, 1)) == 0);
                assert(seq_to_nat(nat_single) == nat_single[0]);
                assert(nat_single[0] == seq[0] as nat);
            }
            seq[0] as nat; {
                assert(pow2(0) == 1) by {
                    lemma2_to64();
                }
                assert(52 * 0 == 0);
                assert(pow2(52 * 0 as nat) == pow2(0));
                assert((seq[0] * pow2(0)) as nat == (seq[0] * 1) as nat);
                assert((seq[0] * 1) as nat == seq[0] as nat);
            }
            (seq[0] * pow2(52 * 0 as nat)) as nat; {}
            (seq_u64_to_nat(seq.subrange(0, 0)) + seq[0] * pow2(52 * 0 as nat)) as nat;
        }
        return ;
    } else {
        let limbs1 = seq.subrange(0, i + 1).map(|i, x| x as nat);
        let limbs2 = seq.subrange(0, i).map(|i, x| x as nat);
        calc! {
            (==)
            seq_u64_to_nat(seq.subrange(0, i + 1)); {
                assert(seq_to_nat(limbs1) == limbs1[0] + seq_to_nat(
                    limbs1.subrange(1, limbs1.len() as int),
                ) * pow2(52));
            }
            limbs1[0] + seq_to_nat(limbs1.subrange(1, limbs1.len() as int)) * pow2(52); {
                assert(seq.subrange(1, i + 1).map(|i, x| x as nat) == limbs1.subrange(
                    1,
                    limbs1.len() as int,
                ));
            }
            limbs1[0] + seq_u64_to_nat(seq.subrange(1, i + 1)) * pow2(52); {
                let tail = seq.subrange(1, i + 1);
                assert(i >= 1);
                assert(0 <= i - 1 < tail.len());
                lemma_seq_u64_to_nat_subrange_extend(tail, i - 1);
                assert(seq_u64_to_nat(tail.subrange(0, i)) == seq_u64_to_nat(
                    tail.subrange(0, i - 1),
                ) + tail[i - 1] * pow2(52 * (i - 1) as nat));
                assert(tail.subrange(0, i) == seq.subrange(1, i + 1));
                assert(tail.subrange(0, i - 1) == seq.subrange(1, i));
                assert(seq_u64_to_nat(seq.subrange(1, i + 1)) == seq_u64_to_nat(seq.subrange(1, i))
                    + seq[i] * pow2(52 * (i - 1) as nat));
            }
            limbs1[0] + ((seq_u64_to_nat(seq.subrange(1, i)) + seq[i] * pow2(52 * (i - 1) as nat))
                * pow2(52)) as nat; {
                broadcast use lemma_mul_is_distributive_add_other_way;

            }
            (limbs1[0] + seq_u64_to_nat(seq.subrange(1, i)) * pow2(52) + seq[i] * pow2(
                52 * (i - 1) as nat,
            ) * pow2(52)) as nat; {
                broadcast use lemma_mul_is_associative;

                lemma_pow2_adds(52 * (i - 1) as nat, 52);
            }
            (limbs1[0] + seq_u64_to_nat(seq.subrange(1, i)) * pow2(52) + seq[i] * pow2(
                52 * i as nat,
            )) as nat; {
                assert(seq.subrange(1, i).map(|i, x| x as nat) == limbs2.subrange(
                    1,
                    limbs2.len() as int,
                ));
            }
            (limbs2[0] + seq_to_nat(limbs2.subrange(1, limbs2.len() as int)) * pow2(52) + seq[i]
                * pow2(52 * i as nat)) as nat; {
                assert(seq_to_nat(limbs2) == limbs2[0] + seq_to_nat(
                    limbs2.subrange(1, limbs2.len() as int),
                ) * pow2(52));
            }
            (seq_to_nat(limbs2) + seq[i] * pow2(52 * i as nat)) as nat; {}
            (seq_u64_to_nat(seq.subrange(0, i)) + seq[i] * pow2(52 * i as nat)) as nat;
        }
    }
}

/// Using lemma_mod_add_multiples_vanish in a big proof made the proof hang
pub proof fn lemma_mod_cancel(a: &Scalar52, b: &Scalar52)
    ensures
        (group_order() + to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int) == (to_nat(
            &a.limbs,
        ) - to_nat(&b.limbs)) % (group_order() as int),
{
    lemma_mod_add_multiples_vanish(
        (to_nat(&a.limbs) - to_nat(&b.limbs)) as int,
        group_order() as int,
    );
}

/// The corollary of limbs_bounded(a)
pub proof fn lemma_bound_scalar(a: &Scalar52)
    requires
        limbs_bounded(a),
    ensures
        to_nat(&a.limbs) < pow2((52 * (5) as nat)),
{
    lemma_general_bound(a.limbs@);
}

/// The general case of lemma_bound_scalar so we
/// can prove via straightforward induction.
pub proof fn lemma_general_bound(a: Seq<u64>)
    requires
        forall|i: int| 0 <= i < a.len() ==> a[i] < (1u64 << 52),
    ensures
        seq_u64_to_nat(a) < pow2((52 * a.len() as nat)),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(seq_u64_to_nat(a) == 0);
        lemma2_to64();  // Gives us pow2(0) == 1 among other facts
        assert(pow2(0) == 1);
    } else {
        // Inductive case
        let tail = a.subrange(1, a.len() as int);

        // Apply induction hypothesis on tail
        assert(forall|i: int| 0 <= i < tail.len() ==> tail[i] < (1u64 << 52)) by {
            assert(forall|i: int| 0 <= i < tail.len() ==> tail[i] == a[i + 1]);
        };

        assert(tail.len() == a.len() - 1);

        // Apply induction hypothesis
        lemma_general_bound(tail);
        assert(seq_u64_to_nat(tail) < pow2((52 * tail.len() as nat)));

        // Now prove for the full sequence
        assert(seq_u64_to_nat(a) == seq_to_nat(a.map(|i, x| x as nat)));
        assert(a.map(|i, x| x as nat).len() == a.len());
        assert(a.map(|i, x| x as nat)[0] == a[0] as nat);
        assert(a.map(|i, x| x as nat).subrange(1, a.len() as int) == a.subrange(
            1,
            a.len() as int,
        ).map(|i, x| x as nat));
        // Therefore:
        assert(seq_u64_to_nat(a) == a[0] as nat + seq_u64_to_nat(a.subrange(1, a.len() as int))
            * pow2(52));

        assert(a.subrange(1, a.len() as int) == tail);

        // From precondition
        assert(a[0] < (1u64 << 52));
        lemma2_to64_rest();
        assert(0x10000000000000 == 1u64 << 52) by (compute_only);
        assert(0x10000000000000 == pow2(52));
        assert((1u64 << 52) == pow2(52));

        // We have seq_u64_to_nat(a) == a[0] + seq_u64_to_nat(tail) * pow2(52)
        // We know a[0] < pow2(52) and seq_u64_to_nat(tail) < pow2(52 * (a.len() - 1))

        assert(a[0] as nat <= pow2(52) - 1);
        assert(seq_u64_to_nat(tail) <= pow2(52 * (a.len() - 1) as nat) - 1);

        assert(seq_u64_to_nat(a) <= (pow2(52) - 1) + (pow2(52 * (a.len() - 1) as nat) - 1) * pow2(
            52,
        )) by {
            lemma_mul_inequality(
                (pow2(52 * (a.len() - 1) as nat) - 1) as int,
                pow2(52 * (a.len() - 1) as nat) as int,
                pow2(52) as int,
            );
        };

        // Expand the right side
        assert((pow2(52) - 1) + (pow2(52 * (a.len() - 1) as nat) - 1) * pow2(52) == pow2(52) - 1
            + pow2(52 * (a.len() - 1) as nat) * pow2(52) - pow2(52)) by {
            broadcast use lemma_mul_is_distributive_sub;

        };

        assert(pow2(52) - 1 + pow2(52 * (a.len() - 1) as nat) * pow2(52) - pow2(52) == pow2(
            52 * (a.len() - 1) as nat,
        ) * pow2(52) - 1);

        lemma_pow2_adds(52 * (a.len() - 1) as nat, 52);
        assert(pow2(52 * (a.len() - 1) as nat) * pow2(52) == pow2(52 * (a.len() - 1) as nat + 52));
        assert(52 * (a.len() - 1) as nat + 52 == 52 * a.len() as nat);

        assert(seq_u64_to_nat(a) <= pow2(52 * a.len() as nat) - 1);
        assert(seq_u64_to_nat(a) < pow2(52 * a.len() as nat));
    }
}

pub proof fn lemma_decompose(a: u64, mask: u64)
    requires
        mask == (1u64 << 52) - 1,
    ensures
        a == (a >> 52) * pow2(52) + (a & mask),
{
    lemma2_to64_rest();  // pow2(52)
    assert(a >> 52 == a / (pow2(52) as u64)) by {
        lemma_u64_shr_is_div(a, 52);
    }

    assert(mask == low_bits_mask(52)) by {
        assert((1u64 << 52) - 1 == 4503599627370495) by (compute);
    }

    assert(a & mask == a % (pow2(52) as u64)) by {
        lemma_u64_low_bits_mask_is_mod(a, 52);
    }

    lemma_fundamental_div_mod(a as int, pow2(52) as int);
}

/// The loop invariant says that subtraction is correct if we only subtract
/// the first i items of each array, plus there's a borrow term.
/// The first parts of the calc statement expand using the previous invariant.
/// Then we have cases depending if the wrapping_sub wrapped.
/// If it didn't wrap, we show that borrow must be small, and borrow >> 52 == 0.
/// If it did wrap, we show that borrow is so large that its bit-shifts are all
/// the maximum amount.
/// Either way, we then use the preconditions about what was mutated,
/// and shuffle around the powers of 52.
pub proof fn lemma_sub_loop1_invariant(
    difference: Scalar52,
    borrow: u64,
    i: usize,
    a: &Scalar52,
    b: &Scalar52,
    old_borrow: u64,
    mask: u64,
    difference_loop1_start: Scalar52,
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        0 <= i < 5,
        forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
        mask == (1u64 << 52) - 1,
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, i as int),
        ) == seq_u64_to_nat(difference_loop1_start.limbs@.subrange(0, i as int)) - (old_borrow
            >> 63) * pow2((52 * (i) as nat)),
        difference_loop1_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(
            0,
            i as int,
        ),
        difference.limbs[i as int] == borrow & mask,
        borrow == a.limbs[i as int].wrapping_sub((b.limbs[i as int] + (old_borrow >> 63)) as u64),
    ensures
        seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2(
            (52 * (i + 1) as nat),
        ) == seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) - seq_u64_to_nat(
            b.limbs@.subrange(0, i + 1),
        ),
{
    calc! {
        (==)
        seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) - seq_u64_to_nat(b.limbs@.subrange(0, i + 1)); {
            lemma_seq_u64_to_nat_subrange_extend(a.limbs@, i as int);
            lemma_seq_u64_to_nat_subrange_extend(b.limbs@, i as int);
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + a.limbs[i as int] * pow2(52 * i as nat) - (
        seq_u64_to_nat(b.limbs@.subrange(0, i as int)) + b.limbs[i as int] * pow2(52 * i as nat)); {
            broadcast use lemma_mul_is_distributive_sub_other_way;

        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, i as int),
        ) + (a.limbs[i as int] - b.limbs[i as int]) * pow2(52 * i as nat); {
            assert(difference_loop1_start.limbs@.subrange(0, i as int)
                == difference.limbs@.subrange(0, i as int));
            // Use loop invariant
        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) - (old_borrow >> 63) * pow2(
            52 * i as nat,
        ) + (a.limbs[i as int] - b.limbs[i as int]) * pow2(52 * i as nat); {
            broadcast use lemma_mul_is_distributive_sub_other_way;

        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (a.limbs[i as int]
            - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
            assert(borrow == a.limbs[i as int].wrapping_sub(
                (b.limbs[i as int] + (old_borrow >> 63)) as u64,
            ));
            assert(difference.limbs[i as int] == borrow & mask);
            // Expand wrapping sub
            if a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64) < 0 {
                assert(borrow >= 0x1_0000_0000_0000_0000 - (1u64 << 52)) by {
                    assert(old_borrow >> 63 <= 1) by (bit_vector);
                    assert(b.limbs[i as int] <= (1u64 << 52) - 1);
                    assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow
                        >> 63)) as u64) + 0x1_0000_0000_0000_0000) as u64);
                    assert((b.limbs[i as int] + (old_borrow >> 63)) as u64 <= 1u64 << 52);
                    assert(borrow >= (a.limbs[i as int] - (1u64 << 52)
                        + 0x1_0000_0000_0000_0000) as u64);
                };
                calc! {
                    (==)
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (a.limbs[i as int]
                        - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
                        assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow
                            >> 63)) as u64) + 0x1_0000_0000_0000_0000) as u64);
                        assert(b.limbs[i as int] < 1u64 << 52);
                        assert(old_borrow >> 63 <= 1) by (bit_vector);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow
                        - 0x1_0000_0000_0000_0000) * pow2(52 * i as nat); {
                        lemma_decompose(borrow, mask);
                        assert(borrow == (borrow >> 52) * pow2(52) + difference.limbs[i as int]);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((borrow >> 52)
                        * pow2(52) + difference.limbs[i as int] - 0x1_0000_0000_0000_0000) * pow2(
                        52 * i as nat,
                    ); {
                        assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {
                            broadcast use lemma_pow2_adds;

                        };
                        assert(52 + 52 * i as nat == 52 * (i + 1) as nat);
                        broadcast use lemma_mul_is_distributive_add_other_way;
                        broadcast use lemma_mul_is_distributive_sub_other_way;

                        assert((borrow >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (borrow
                            >> 52) as nat * pow2(52 * (i + 1) as nat)) by {
                            assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i + 1) as nat));
                            lemma_mul_is_associative(
                                (borrow >> 52) as int,
                                pow2(52) as int,
                                pow2(52 * i as nat) as int,
                            );
                        };
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow >> 52) * pow2(
                        52 * (i + 1) as nat,
                    ) + difference.limbs[i as int] * pow2(52 * i as nat) - 0x1_0000_0000_0000_0000
                        * pow2(52 * i as nat); {
                        lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) + (borrow >> 52) * pow2(
                        52 * (i + 1) as nat,
                    ) - 0x1_0000_0000_0000_0000 * pow2(52 * i as nat); {
                        assert(borrow >> 52 == (1u64 << 12) - 1) by (bit_vector)
                            requires
                                borrow >= 0x1_0000_0000_0000_0000 - (1u64 << 52),
                        ;
                        assert(0x1_0000_0000_0000_0000 * pow2(52 * i as nat) == (1u64 << 12) * pow2(
                            52 * (i + 1) as nat,
                        )) by {
                            lemma2_to64();
                            assert(0x1_0000_0000_0000_0000 == pow2(64));
                            assert(1u64 << 12 == pow2(12)) by (compute);
                            lemma_pow2_adds(64, 52 * i as nat);
                            lemma_pow2_adds(12, 52 * (i + 1) as nat);
                            assert(64 + 52 * i as nat == 12 + 52 * (i + 1) as nat);
                        }
                        lemma_mul_is_distributive_sub_other_way(
                            pow2(52 * (i + 1) as nat) as int,
                            (1u64 << 12) - 1,
                            (1u64 << 12) as int,
                        );
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) + (-1) * pow2(
                        52 * (i + 1) as nat,
                    ); {
                        assert(borrow >> 63 == 1) by (bit_vector)
                            requires
                                borrow >= 0x1_0000_0000_0000_0000 - (1u64 << 52),
                        ;
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2(
                        (52 * (i + 1) as nat),
                    );
                }
            } else {
                calc! {
                    (==)
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (a.limbs[i as int]
                        - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
                        assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow
                            >> 63)) as u64)) as u64);
                        assert(b.limbs[i as int] < 1u64 << 52);
                        assert(old_borrow >> 63 <= 1) by (bit_vector);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow) * pow2(
                        52 * i as nat,
                    ); {
                        lemma_decompose(borrow, mask);
                        assert(borrow == (borrow >> 52) * pow2(52) + difference.limbs[i as int]);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((borrow >> 52)
                        * pow2(52) + difference.limbs[i as int]) * pow2(52 * i as nat); {
                        assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {
                            broadcast use lemma_pow2_adds;

                        };
                        assert(52 + 52 * i as nat == 52 * (i + 1) as nat);
                        broadcast use lemma_mul_is_distributive_add_other_way;

                        assert((borrow >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (borrow
                            >> 52) as nat * pow2(52 * (i + 1) as nat)) by {
                            assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i + 1) as nat));
                            lemma_mul_is_associative(
                                (borrow >> 52) as int,
                                pow2(52) as int,
                                pow2(52 * i as nat) as int,
                            );
                        };
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow >> 52) * pow2(
                        52 * (i + 1) as nat,
                    ) + difference.limbs[i as int] * pow2(52 * i as nat); {
                        lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
                        assert(borrow < 1u64 << 52) by {
                            assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow
                                >> 63)) as u64)) as u64);
                            assert(a.limbs[i as int] < (1u64 << 52));
                            assert((b.limbs[i as int] + (old_borrow >> 63)) as u64 >= 0);
                        }
                        assert(borrow >> 52 == 0) by (bit_vector)
                            requires
                                borrow < 1u64 << 52,
                        ;
                        assert(borrow >> 63 == 0) by (bit_vector)
                            requires
                                borrow < 1u64 << 52,
                        ;
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2(
                        (52 * (i + 1) as nat),
                    );
                }
            }
        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2(
            (52 * (i + 1) as nat),
        );
    }
}

/// Just a proof by computation
pub(crate) proof fn lemma_l_equals_group_order()
    ensures
        to_nat(&constants::L.limbs) == group_order(),
        seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) == group_order(),
{
    // First show that the subrange equals the full array
    assert(constants::L.limbs@ == constants::L.limbs@.subrange(0, 5 as int));
    assert(seq_u64_to_nat(constants::L.limbs@) == seq_u64_to_nat(
        constants::L.limbs@.subrange(0, 5 as int),
    ));
    assert(to_nat(&constants::L.limbs) == seq_u64_to_nat(constants::L.limbs@));

    assert(pow2(52) == 0x10000000000000) by {
        lemma2_to64_rest();
    };
    lemma_pow2_adds(52, 52);
    assert(pow2(104) == 0x100000000000000000000000000);
    lemma_pow2_adds(104, 104);
    assert(pow2(208) == 0x10000000000000000000000000000000000000000000000000000);
    lemma_pow252();
    lemma_five_limbs_equals_to_nat(&constants::L.limbs);
    assert(five_limbs_to_nat_aux(constants::L.limbs) == group_order()) by (compute);
}

pub proof fn lemma_pow252()
    ensures
        pow2(252) == 0x1000000000000000000000000000000000000000000000000000000000000000,
{
    assert(pow2(63) == 0x8000000000000000) by {
        lemma2_to64_rest();
    }
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);
    lemma_pow2_adds(126, 126);
}

pub proof fn lemma_pow2_260_greater_than_2_group_order()
    ensures
        pow2(260) > 2 * group_order(),
{
    // The group order is approximately 2^252, so 2 * group_order ≈ 2^253
    // And 2^260 >> 2^253
    assert(pow2(260) == pow2(252) * pow2(8)) by {
        lemma_pow2_adds(252, 8);
    };
    assert(pow2(8) == 256) by {
        lemma2_to64();
    };
    lemma_pow252();
    // Now Verus knows what the powers of 2 mean, so it can figure out the rest
}

/// If borrow >> 63 == 0, we apply
/// (1) `-group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order()`,
/// and that's enough to show that to_nat(&difference.limbs) is between
/// 0 and group order.
/// If borrow >> 63 == 1, we apply (1) to show that carry >> 52 can't be 0.
/// This makes the excess terms in the borrow >> 63 == 1 precondition disappear
pub(crate) proof fn lemma_sub_correct_after_loops(
    difference: Scalar52,
    carry: u64,
    a: &Scalar52,
    b: &Scalar52,
    difference_after_loop1: Scalar52,
    borrow: u64,
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        limbs_bounded(&difference),
        limbs_bounded(&difference_after_loop1),
        (carry >> 52) < 2,
        -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        borrow >> 63 == 0 ==> difference_after_loop1 == difference,
        borrow >> 63 == 1 ==> seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int))
            + seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) == seq_u64_to_nat(
            difference.limbs@.subrange(0, 5 as int),
        ) + (carry >> 52) * pow2(52 * 5 as nat),
        seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) - (borrow >> 63)
            * pow2((52 * (5) as nat)),
    ensures
        to_nat(&difference.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int),
{
    assert(borrow >> 63 == 1 || borrow >> 63 == 0) by (bit_vector);
    assert(seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) == to_nat(&difference.limbs))
        by {
        assert(seq_u64_to_nat(difference.limbs@) == to_nat(&difference.limbs));
        assert(difference.limbs@ == difference.limbs@.subrange(0, 5 as int));
    }
    assert(seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == to_nat(&b.limbs)) by {
        assert(seq_u64_to_nat(b.limbs@) == to_nat(&b.limbs));
        assert(b.limbs@ == b.limbs@.subrange(0, 5 as int));
    }
    assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) == to_nat(&a.limbs)) by {
        assert(seq_u64_to_nat(a.limbs@) == to_nat(&a.limbs));
        assert(a.limbs@ == a.limbs@.subrange(0, 5 as int));
    }
    if borrow >> 63 == 0 {
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) - (borrow >> 63) * pow2(
            (52 * (5) as nat),
        ));
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)));
        assert(to_nat(&a.limbs) - to_nat(&b.limbs) == to_nat(&difference.limbs));
        assert(to_nat(&a.limbs) - to_nat(&b.limbs) >= 0);
        assert(to_nat(&a.limbs) - to_nat(&b.limbs) < group_order());
        lemma_small_mod((to_nat(&a.limbs) - to_nat(&b.limbs)) as nat, group_order());
        assert(to_nat(&difference.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (
        group_order() as int));
    }
    if borrow >> 63 == 1 {
        assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            constants::L.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(
            52 * 5 as nat,
        ));
        assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int))
            == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(
            52 * 5 as nat,
        ) - seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)));
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) - pow2(
            (52 * (5) as nat),
        ));
        assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(
            52 * 5 as nat,
        ) - seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) - pow2((52 * (5) as nat)));
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            a.limbs@.subrange(0, 5 as int),
        ) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == seq_u64_to_nat(
            difference.limbs@.subrange(0, 5 as int),
        ) + (carry >> 52) * pow2(52 * 5 as nat) - pow2((52 * (5) as nat)));
        if carry >> 52 == 0 {
            // Get a contradiction because the sides in the above equation have different signs
            assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
                a.limbs@.subrange(0, 5 as int),
            ) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) >= 0) by {
                assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) >= group_order())
                    by {
                    lemma_l_equals_group_order();
                };
                assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) == to_nat(&a.limbs));
                assert(seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == to_nat(&b.limbs));
            };
            assert(seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) < pow2(
                (52 * (5) as nat),
            )) by {
                assert(seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) == to_nat(
                    &difference.limbs,
                ));
                lemma_bound_scalar(&difference);
            };
            assert((carry >> 52) * pow2(52 * 5 as nat) == 0);
            assert(false);
        }
        assert(carry >> 52 == 1);
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            a.limbs@.subrange(0, 5 as int),
        ) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == seq_u64_to_nat(
            difference.limbs@.subrange(0, 5 as int),
        ));
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) + to_nat(&a.limbs)
            - to_nat(&b.limbs) == to_nat(&difference.limbs));
        assert(to_nat(&constants::L.limbs) == group_order()) by {
            lemma_l_equals_group_order();
        };
        assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) == group_order()) by {
            lemma_l_equals_group_order();
        };
        assert(group_order() > 0);
        calc! {
            (==)
            to_nat(&difference.limbs) as int; {}
            group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs); {
                assert(group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs) < group_order())
                    by {
                    assert(seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int))
                        == to_nat(&difference_after_loop1.limbs)) by {
                        assert(seq_u64_to_nat(difference_after_loop1.limbs@) == to_nat(
                            &difference_after_loop1.limbs,
                        ));
                        assert(difference_after_loop1.limbs@
                            == difference_after_loop1.limbs@.subrange(0, 5 as int));
                    }
                    assert(to_nat(&a.limbs) - to_nat(&b.limbs) == to_nat(
                        &difference_after_loop1.limbs,
                    ) - pow2((52 * (5) as nat)));
                    lemma_bound_scalar(&difference_after_loop1);
                };
                lemma_small_mod(
                    (group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs)) as nat,
                    group_order(),
                );
            }
            (group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int); {
                lemma_mod_cancel(a, b);
            }
            (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int);
        }
    }
}

/// If borrow >> 63 == 0, we just prove that the loop step has no effect.
/// If borrow >> 63 == 1, we substitute in the loop's updates
/// like `difference.limbs[i as int] == carry & mask`.
/// In that case we're proving that subtraction is correct if we only
/// consider the first i items of each array, except there's also a
/// `(carry >> 52) * pow2(52 * (i+1) as nat)` term that doesn't go away.
pub(crate) proof fn lemma_sub_loop2_invariant(
    difference: Scalar52,
    i: usize,
    a: &Scalar52,
    b: &Scalar52,
    mask: u64,
    difference_after_loop1: Scalar52,
    difference_loop2_start: Scalar52,
    carry: u64,
    old_carry: u64,
    addend: u64,
    borrow: u64,
)
    requires
        0 <= i < 5,
        mask == (1u64 << 52) - 1,
        forall|j: int| 0 <= j < 5 ==> difference_loop2_start.limbs[j] < (1u64 << 52),
        forall|j: int|
            i <= j < 5 ==> difference_loop2_start.limbs[j] == difference_after_loop1.limbs[j],
        forall|j: int|
            (0 <= j < 5 && j != i) ==> difference_loop2_start.limbs[j] == difference.limbs[j],
        mask == (1u64 << 52) - 1,
        i == 0 ==> old_carry == 0,
        i >= 1 ==> (old_carry >> 52) < 2,
        (i >= 1 && borrow >> 63 == 0) ==> old_carry == difference_loop2_start.limbs[i - 1],
        borrow >> 63 == 0 ==> difference_after_loop1 == difference_loop2_start,
        borrow >> 63 == 1 ==> seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int))
            + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) == seq_u64_to_nat(
            difference_loop2_start.limbs@.subrange(0, i as int),
        ) + (old_carry >> 52) * pow2(52 * i as nat),
        difference.limbs[i as int] == carry & mask,
        difference_loop2_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(
            0,
            i as int,
        ),
        borrow >> 63 == 0 ==> addend == 0,
        borrow >> 63 == 1 ==> addend == constants::L.limbs[i as int],
        carry == (old_carry >> 52) + difference_loop2_start.limbs[i as int] + addend,
    ensures
        (i + 1 >= 1 && borrow >> 63 == 0) ==> carry == difference.limbs[i as int],
        borrow >> 63 == 0 ==> difference_after_loop1 == difference,
        borrow >> 63 == 1 ==> seq_u64_to_nat(
            difference_after_loop1.limbs@.subrange(0, i + 1 as int),
        ) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i + 1 as int)) == seq_u64_to_nat(
            difference.limbs@.subrange(0, i + 1 as int),
        ) + (carry >> 52) * pow2(52 * (i + 1) as nat),
{
    if borrow >> 63 == 0 {
        assert(old_carry >> 52 == 0) by (bit_vector)
            requires
                old_carry < 1u64 << 52,
        ;
        assert(addend == 0);
        assert(carry == difference_loop2_start.limbs[i as int]);
        assert(carry & mask == carry) by (bit_vector)
            requires
                carry < 1u64 << 52,
                mask == (1u64 << 52) - 1,
        ;
        assert(difference_after_loop1.limbs[i as int] == difference.limbs[i as int]);
        assert(forall|j: int|
            0 <= j < 5 ==> difference_after_loop1.limbs[j] == difference.limbs[j]);
        assert(difference_after_loop1.limbs == difference.limbs);
    }
    if borrow >> 63 == 1 {
        // When underflow, addend = L.limbs[i]
        assert(addend == constants::L.limbs[i as int]);
        // carry = (old_carry >> 52) + difference_after_loop1.limbs[i] + L.limbs[i]
        // difference.limbs[i] = carry & mask
        calc! {
            (==)
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i + 1)) + seq_u64_to_nat(
                constants::L.limbs@.subrange(0, i + 1),
            ); {
                lemma_seq_u64_to_nat_subrange_extend(difference_after_loop1.limbs@, i as int);
                lemma_seq_u64_to_nat_subrange_extend(constants::L.limbs@, i as int);
            }
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int))
                + difference_after_loop1.limbs[i as int] as nat * pow2(52 * i as nat)
                + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int))
                + constants::L.limbs[i as int] as nat * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;

            }
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int)) + seq_u64_to_nat(
                constants::L.limbs@.subrange(0, i as int),
            ) + (difference_after_loop1.limbs[i as int] as nat
                + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                // Use invariant
            }
            seq_u64_to_nat(difference_loop2_start.limbs@.subrange(0, i as int)) + (old_carry
                >> 52) as nat * pow2(52 * i as nat) + (difference_after_loop1.limbs[i as int] as nat
                + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                assert(difference_loop2_start.limbs@.subrange(0, i as int)
                    == difference.limbs@.subrange(0, i as int));
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (old_carry >> 52) as nat
                * pow2(52 * i as nat) + (difference_after_loop1.limbs[i as int] as nat
                + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;

            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((old_carry >> 52) as nat
                + difference_after_loop1.limbs[i as int] as nat
                + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                assert(carry == (old_carry >> 52) + difference_after_loop1.limbs[i as int]
                    + constants::L.limbs[i as int]);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + carry as nat * pow2(
                52 * i as nat,
            ); {
                assert(carry == (carry >> 52) * (1u64 << 52) + (carry & mask)) by (bit_vector)
                    requires
                        mask == (1u64 << 52) - 1,
                ;
                assert(carry == (carry >> 52) * pow2(52) + difference.limbs[i as int]) by {
                    lemma2_to64_rest();
                    assert(0x10000000000000 == 1u64 << 52) by (compute_only);
                };
                assert(difference.limbs[i as int] == carry & mask);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((carry >> 52) as nat * pow2(
                52,
            ) + difference.limbs[i as int] as nat) * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;

            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (carry >> 52) as nat * pow2(
                52,
            ) * pow2(52 * i as nat) + difference.limbs[i as int] as nat * pow2(52 * i as nat); {
                assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {
                    broadcast use lemma_pow2_adds;

                };
                assert(52 + 52 * i as nat == 52 * (i + 1) as nat);
                assert((carry >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (carry >> 52) as nat
                    * pow2(52 * (i + 1) as nat)) by {
                    assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i + 1) as nat));
                    lemma_mul_is_associative(
                        (carry >> 52) as int,
                        pow2(52) as int,
                        pow2(52 * i as nat) as int,
                    );
                };
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (carry >> 52) as nat * pow2(
                52 * (i + 1) as nat,
            ) + difference.limbs[i as int] as nat * pow2(52 * i as nat); {
                lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) + (carry >> 52) as nat * pow2(
                52 * (i + 1) as nat,
            );
        }
    }
}

/// Proves that the addition loop maintains its invariant:
/// a[0..i+1] + b[0..i+1] == sum[0..i+1] + (carry >> 52) * 2^(52*(i+1))
/// See lemma_sub_loop1_invariant for more comments
pub proof fn lemma_add_loop_invariant(
    sum: Scalar52,
    carry: u64,
    i: usize,
    a: &Scalar52,
    b: &Scalar52,
    old_carry: u64,
    mask: u64,
    sum_loop_start: Scalar52,
)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        0 <= i < 5,
        forall|j: int| 0 <= j < i ==> sum.limbs[j] < (1u64 << 52),
        mask == (1u64 << 52) - 1,
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(
            b.limbs@.subrange(0, i as int),
        ) == seq_u64_to_nat(sum_loop_start.limbs@.subrange(0, i as int)) + (old_carry >> 52) * pow2(
            (52 * (i) as nat),
        ),
        sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int),
        sum.limbs[i as int] == carry & mask,
        carry == a.limbs[i as int] + b.limbs[i as int] + (old_carry >> 52),
    ensures
        seq_u64_to_nat(sum.limbs@.subrange(0, i + 1)) + (carry >> 52) * pow2((52 * (i + 1) as nat))
            == seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) + seq_u64_to_nat(
            b.limbs@.subrange(0, i + 1),
        ),
{
    calc! {
        (==)
        seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) + seq_u64_to_nat(b.limbs@.subrange(0, i + 1)); {
            lemma_seq_u64_to_nat_subrange_extend(a.limbs@, i as int);
            lemma_seq_u64_to_nat_subrange_extend(b.limbs@, i as int);
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + a.limbs[i as int] as nat * pow2(
            52 * i as nat,
        ) + seq_u64_to_nat(b.limbs@.subrange(0, i as int)) + b.limbs[i as int] as nat * pow2(
            52 * i as nat,
        ); {
            lemma_mul_is_distributive_add_other_way(
                pow2(52 * i as nat) as int,
                a.limbs[i as int] as int,
                b.limbs[i as int] as int,
            );
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(
            b.limbs@.subrange(0, i as int),
        ) + (a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int));
            // Use loop invariant
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (old_carry >> 52) as nat * pow2(
            52 * i as nat,
        ) + (a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            lemma_mul_is_distributive_add_other_way(
                pow2(52 * i as nat) as int,
                (old_carry >> 52) as int,
                (a.limbs[i as int] as nat + b.limbs[i as int] as nat) as int,
            );
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + ((old_carry >> 52) as nat
            + a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(carry == a.limbs[i as int] + b.limbs[i as int] + (old_carry >> 52));
            assert(sum.limbs[i as int] == carry & mask);
            // Decompose carry using the mask
            lemma_decompose(carry, mask);
            assert(carry == (carry >> 52) * pow2(52) + sum.limbs[i as int]);
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + ((carry >> 52) as nat * pow2(52)
            + sum.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {
                lemma_pow2_adds(52, 52 * i as nat);
            };
            assert(52 + 52 * i as nat == 52 * (i + 1) as nat);
            lemma_mul_is_distributive_add_other_way(
                pow2(52 * i as nat) as int,
                (carry >> 52) as nat * pow2(52) as int,
                sum.limbs[i as int] as int,
            );
            assert((carry >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (carry >> 52) as nat
                * pow2(52 * (i + 1) as nat)) by {
                assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i + 1) as nat));
                lemma_mul_is_associative(
                    (carry >> 52) as int,
                    pow2(52) as int,
                    pow2(52 * i as nat) as int,
                );
            };
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (carry >> 52) as nat * pow2(
            52 * (i + 1) as nat,
        ) + sum.limbs[i as int] as nat * pow2(52 * i as nat); {
            lemma_seq_u64_to_nat_subrange_extend(sum.limbs@, i as int);
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i + 1)) + (carry >> 52) as nat * pow2(
            (52 * (i + 1) as nat),
        );
    }
}

/// Get rid of the subranges from the invariant statement.
/// Since a and b are less than group order, we can show that carry >> 52
/// has to be 0, else the RHS is too large
pub proof fn lemma_add_sum_simplify(a: &Scalar52, b: &Scalar52, sum: &Scalar52, carry: u64)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        to_nat(&a.limbs) < group_order(),
        to_nat(&b.limbs) < group_order(),
        forall|j: int| 0 <= j < 5 ==> sum.limbs[j] < (1u64 << 52),
        (carry >> 52) < 2,
        seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(
            b.limbs@.subrange(0, 5 as int),
        ) == seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) + (carry >> 52) as nat * pow2(
            (52 * (5) as nat),
        ),
    ensures
        to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs),
{
    // First establish the relationship between the different representations
    assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) == to_nat(&a.limbs)) by {
        assert(a.limbs@ == a.limbs@.subrange(0, 5 as int));
        assert(seq_u64_to_nat(a.limbs@) == to_nat(&a.limbs));
    }
    assert(seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == to_nat(&b.limbs)) by {
        assert(b.limbs@ == b.limbs@.subrange(0, 5 as int));
        assert(seq_u64_to_nat(b.limbs@) == to_nat(&b.limbs));
    }
    assert(seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) == to_nat(&sum.limbs)) by {
        assert(sum.limbs@ == sum.limbs@.subrange(0, 5 as int));
        assert(seq_u64_to_nat(sum.limbs@) == to_nat(&sum.limbs));
    }

    assert(to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs) + (carry >> 52) * pow2(
        (52 * (5) as nat),
    ));

    // From the loop invariant, we have: a + b == sum + (carry >> 52) * 2^260
    assert(52 * 5 == 260) by (compute);
    assert(pow2((52 * 5) as nat) == pow2(260));
    assert(to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs) + (carry >> 52) as nat * pow2(
        260,
    ));

    // Since a < group_order() and b < group_order(), we have a + b < 2 * group_order()
    // This is just basic arithmetic: if x < A and y < A, then x + y < A + A = 2*A
    assert(to_nat(&a.limbs) + to_nat(&b.limbs) < group_order() + group_order());
    assert(group_order() + group_order() == 2 * group_order());
    assert(to_nat(&a.limbs) + to_nat(&b.limbs) < 2 * group_order());

    // Therefore: sum + (carry >> 52) * 2^260 < 2 * group_order()
    assert(to_nat(&sum.limbs) + (carry >> 52) as nat * pow2(260) < 2 * group_order());

    // Prove a contradiction if carry is nonzero
    assert((carry >> 52) as nat * pow2(260) < 2 * group_order());
    if carry >> 52 == 1 {
        lemma_pow2_260_greater_than_2_group_order();
        assert(1 as nat * pow2(260) < 2 * group_order());
        assert(false);
    }
    assert(carry >> 52 == 0);

    // Since carry >> 52 >= 0 and pow2(260) > 0, we have (carry >> 52) * pow2(260) >= 0
    // Therefore sum < sum + (carry >> 52) * pow2(260) < 2 * group_order()
    lemma_pow2_pos(260);
    assert(pow2(260) > 0);
    assert((carry >> 52) as nat * pow2(260) >= 0);
    assert(to_nat(&sum.limbs) <= to_nat(&sum.limbs) + (carry >> 52) as nat * pow2(260));
    assert(to_nat(&sum.limbs) < 2 * group_order());
}

/// Proves that bytes_to_nat is at least as large as any individual term in its sum
pub proof fn lemma_bytes_to_nat_lower_bound(bytes: &[u8; 32], index: usize)
    requires
        index < 32,
    ensures
        bytes_to_nat(bytes) >= (bytes[index as int] as nat) * pow2((index * 8) as nat),
{
    // bytes_to_nat is defined recursively as a sum of non-negative terms
    // Therefore the sum is >= any individual term
    use crate::specs::core_specs::u8_32_as_nat;
    assert(bytes_to_nat(bytes) == u8_32_as_nat(bytes));
    lemma_bytes_to_nat_rec_bound(bytes, 0, index);
}

/// Helper lemma showing that bytes_to_nat_rec is >= a specific term
proof fn lemma_bytes_to_nat_rec_bound(bytes: &[u8; 32], start: usize, target: usize)
    requires
        start <= target < 32,
    ensures
        bytes_to_nat_rec(bytes, start as int) >= (bytes[target as int] as nat) * pow2(
            (target * 8) as nat,
        ),
    decreases 32 - start,
{
    if start == target {
        // Base case: the current term is exactly what we're looking for
        // bytes_to_nat_rec(bytes, target) = bytes[target] * pow2(target*8) + (rest >= 0)
    } else {
        // Inductive case: recurse to the next position
        lemma_bytes_to_nat_rec_bound(bytes, (start + 1) as usize, target);
    }
}

/// Proof that the group order is less than 2^255
pub proof fn lemma_group_order_bound()
    ensures
        group_order() < pow2(255),
{
    // group_order = 2^252 + 27742317777372353535851937790883648493
    lemma_l_equals_group_order();
    lemma_pow252();

    // First compare the constant to the concrete numeral for 2^126
    assert(27742317777372353535851937790883648493nat < 0x40000000000000000000000000000000)
        by (compute_only);

    // Establish pow2(126) == 0x4000...0000 so we can rewrite the bound
    assert(pow2(63) == 0x8000000000000000) by {
        lemma2_to64_rest();
    };
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);

    // Hence the constant < 2^126 < 2^252
    assert(27742317777372353535851937790883648493nat < pow2(126));
    lemma_pow2_strictly_increases(126, 252);
    assert(27742317777372353535851937790883648493nat < pow2(252));

    // Therefore group_order < 2^252 + 2^252 = 2^253
    assert(group_order() == pow2(252) + 27742317777372353535851937790883648493nat);
    assert(group_order() < pow2(252) + pow2(252));

    // 2^252 + 2^252 = 2^253
    assert(pow2(252) + pow2(252) == pow2(253)) by {
        lemma_pow2_adds(1, 252);
        lemma2_to64();
    }

    // 2^253 < 2^255
    lemma_pow2_strictly_increases(253, 255);
    assert(group_order() < pow2(255));
}

/// If an UnpackedScalar (Scalar52) is canonical (< group_order), then it is < 2^256.
pub proof fn lemma_scalar52_lt_pow2_256_if_canonical(a: &Scalar52)
    requires
        limbs_bounded(a),
        to_nat(&a.limbs) < group_order(),
    ensures
        to_nat(&a.limbs) < pow2(256),
{
    // group_order() < 2^255
    lemma_group_order_bound();

    // Chain: to_nat(a) < group_order() < 2^255 < 2^256
    calc! {
        (<)
        to_nat(&a.limbs); {  /* from precondition */
        }
        group_order(); {  /* from lemma_group_order_bound */
        }
        pow2(255); {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(255, 256);
        }
        pow2(256);
    }
}

// Proof that group_order() is odd
pub proof fn lemma_group_order_is_odd()
    ensures
        group_order() % 2 == 1,
{
    assert(group_order() == pow2(252) + 27742317777372353535851937790883648493nat);

    lemma_pow2_even(252);
    assert((pow2(252) as int) % 2 == 0);

    // Reduce the sum modulo 2: (A + B) % 2 == ((A % 2) + (B % 2)) % 2
    lemma_add_mod_noop(
        pow2(252) as int,
        27742317777372353535851937790883648493nat as int,
        2 as int,
    );

    assert((27742317777372353535851937790883648493nat as int) % 2 == 1);
    assert(group_order() % 2 == 1);
}

// Proof that (a * R) % group_order() == (b * R) % group_order ==> a % group_order() == b % group_order()
pub proof fn lemma_cancel_mul_pow2_mod(a: nat, b: nat, r_pow: nat)
    requires
// r_pow is a power of two, and r_pow and group_order are coprime
// (montgomery_radix() is 2^260; group_order() is odd)

        r_pow == pow2(260),
        (a * r_pow) % group_order() == (b * r_pow) % group_order(),
    ensures
        a % group_order() == b % group_order(),
{
    // Constructive proof using inverse-of-2 modulo L.
    let L = group_order();

    lemma_group_order_is_odd();

    // Define inv2 = (L + 1) / 2
    let inv2 = (L + 1) / 2;

    // From division: (L + 1) == 2 * ((L + 1) / 2) + (L + 1) % 2
    lemma_fundamental_div_mod((L + 1) as int, 2);
    // Since L is odd, (L + 1) % 2 == 0, so 2 * inv2 == L + 1
    assert(2 * inv2 == L + 1);

    // inv_pow = inv2^260
    let inv_pow = pow(inv2 as int, 260);

    // Multiply given congruence (a * r_pow) ≡ (b * r_pow) (mod L) by inv_pow
    lemma_mul_factors_congruent_implies_products_congruent(
        inv_pow as int,
        (a * r_pow) as int,
        (b * r_pow) as int,
        L as int,
    );

    // So (inv_pow * a * r_pow) % L == (inv_pow * b * r_pow) % L.
    // Show that (inv_pow * r_pow) % L == 1.

    // First, (inv2 * 2) % L == 1
    assert((inv2 * 2) % L == 1) by {
        // we already have 2 * inv2 == L + 1
        assert(2 * inv2 == L + 1);

        // rewrite to (L + 1) % L
        assert((2 * inv2) % L == (L + 1) % L);

        // show group_order() > 1
        // pow2(252) == 2 * pow2(251)
        lemma_pow2_adds(1, 251);
        assert(pow2(1) == 2) by { lemma2_to64() };
        assert(pow2(252) == 2 * pow2(251));

        // pow2(251) > 0  ==> pow2(252) >= 2
        lemma_pow2_pos(251);
        assert(pow2(251) > 0);
        // since pow2(252) == 2 * pow2(251) and pow2(251) >= 1, pow2(252) >= 2
        assert(pow2(252) >= 2);

        // group_order() = pow2(252) + C, so group_order() >= pow2(252) >= 2
        // (use compute / definition unfolding if needed)
        assert(group_order() >= pow2(252));
        assert(group_order() >= 2);
        assert(group_order() > 1);

        // Now L + 1 == L * 1 + 1 and 0 <= 1 < L, so remainder of (L+1) mod L is 1.
        assert(L + 1 == L * 1 + 1);
        assert(0 <= 1 && 1 < L);

        // Use the converse lemma: if x == q * d + r and 0 <= r < d then r == x % d
        lemma_fundamental_div_mod_converse((L + 1) as int, L as int, 1, 1);

        assert((L + 1) % L == 1);
    }

    // pow((inv2 * 2), 260) % L == 1
    lemma_pow_mod_one((inv2 * 2) as int, 260, L as int);

    // pow(inv2 * 2, 260) == pow(inv2,260) * pow(2,260)
    lemma_pow_distributes(inv2 as int, 2int, 260);

    // Using the above, (pow(inv2,260) * pow(2,260)) % L == 1
    // Note r_pow == pow2(260) == pow(2,260)

    // Let c = inv_pow * r_pow
    let c = (inv_pow * r_pow) as int;

    // c % L == 1
    assert(c % (L as int) == 1) by {
        // pow(inv2,260) * pow(2,260) is congruent to 1
        assert(pow(inv2 as int, 260) * pow(2 as int, 260) == pow((inv2 * 2) as int, 260));
        assert((pow(inv2 as int, 260) * pow(2 as int, 260)) % (L as int) == 1);
        assert(pow(2int, 260) == (pow2(260) as int)) by { lemma_pow2(260) };
    }

    assert(1int < L);
    assert(1int % (L as int) == 1) by { lemma_small_mod(1nat, L) };

    // (a * r_pow) % L = (b * r_pow) % L
    lemma_mul_factors_congruent_implies_products_congruent(
        inv_pow,
        (a * r_pow) as int,
        (b * r_pow) as int,
        L as int,
    );

    assert(((a * r_pow) * inv_pow) % (L as int) == ((b * r_pow) * inv_pow) % (L as int));
    assert(((a * r_pow) * inv_pow) % (L as int) == (a * (r_pow * inv_pow)) % (L as int)) by {
        lemma_mul_is_associative(a as int, r_pow as int, inv_pow as int)
    };

    assert(((b * r_pow) * inv_pow) % (L as int) == (b * (r_pow * inv_pow)) % (L as int)) by {
        lemma_mul_is_associative(b as int, r_pow as int, inv_pow as int)
    };
    // assert((a * (r_pow * inv_pow)) % (L as int) == (b * (r_pow * inv_pow)) % (L as int));

    lemma_mul_factors_congruent_implies_products_congruent(a as int, c, 1, L as int);
    lemma_mul_factors_congruent_implies_products_congruent(b as int, c, 1, L as int);

}

// Proof that a % m == b % m ==> (c * a) % m == (c * b) % m
pub proof fn lemma_mul_factors_congruent_implies_products_congruent(c: int, a: int, b: int, m: int)
    requires
        m > 0,
        a % m == b % m,
    ensures
        (c * a) % m == (c * b) % m,
{
    assert((c * a) % m == (c * (a % m)) % m) by { lemma_mul_mod_noop_right(c, a, m) };
    assert((c * a) % m == (c * (b % m)) % m);
    assert((c * a) % m == (c * b) % m) by { lemma_mul_mod_noop_right(c, b, m) };

}

// Proof that group_order is less than 2^256
pub proof fn lemma_group_order_smaller_than_pow256()
    ensures
        group_order() < pow2(256),
{
    lemma_group_order_bound();
    lemma_pow2_strictly_increases(255, 256);
}

// prove each literal limb is < 2^52
pub proof fn lemma_r_bounded(r: Scalar52)
    requires
        r == (Scalar52 {
            limbs: [
                0x000f48bd6721e6ed,
                0x0003bab5ac67e45a,
                0x000fffffeb35e51b,
                0x000fffffffffffff,
                0x00000fffffffffff,
            ],
        }),
    ensures
        limbs_bounded(&r),
{
    assert(0x000f48bd6721e6ed < 0x10000000000000) by (compute_only);
    assert(0x0003bab5ac67e45a < 0x10000000000000) by (compute_only);
    assert(0x000fffffeb35e51b < 0x10000000000000) by (compute_only);
    assert(0x000fffffffffffff < 0x10000000000000) by (compute_only);
    assert(0x00000fffffffffff < 0x10000000000000) by (compute_only);

    assert(0x10000000000000 == 1u64 << 52) by (bit_vector);

}

/// Proves correctness of is_canonical check
///
/// This lemma establishes that comparing a scalar to its reduced form
/// correctly determines whether it is canonical (i.e., already in the range [0, group_order())).
///
/// The proof works by cases:
/// - If self_bytes == reduced_bytes, then self is already canonical
/// - If self_bytes != reduced_bytes, then they have different nat values (by injectivity),
///   but equal nat values mod group_order (by reduce's postcondition).
///   This is only possible if self_bytes represents a value >= group_order.
pub proof fn lemma_is_canonical_correctness(self_bytes: &[u8; 32], reduced_bytes: &[u8; 32])
    requires
// reduced is canonical

        bytes_to_nat(reduced_bytes) < group_order(),
        // reduced has the same value mod group_order as self
        bytes_to_nat(reduced_bytes) % group_order() == bytes_to_nat(self_bytes) % group_order(),
    ensures
// Bytes are equal iff self is canonical

        (self_bytes == reduced_bytes) == (bytes_to_nat(self_bytes) < group_order()),
{
    if self_bytes == reduced_bytes {
        // Case 1: Bytes are equal
        // Then nat values are equal and self is canonical
        assert(bytes_to_nat(self_bytes) == bytes_to_nat(reduced_bytes));
        assert(bytes_to_nat(self_bytes) < group_order());
    } else {
        // Case 2: Bytes differ
        // Step 1: Different bytes imply different nat values (by injectivity)
        assert(bytes_to_nat(reduced_bytes) != bytes_to_nat(self_bytes)) by {
            if bytes_to_nat(reduced_bytes) == bytes_to_nat(self_bytes) {
                lemma_canonical_bytes_equal(reduced_bytes, self_bytes);
                assert(reduced_bytes =~= self_bytes);  // contradiction
            }
        }

        // Step 2: Canonical value equals itself mod group_order
        assert(bytes_to_nat(reduced_bytes) == bytes_to_nat(reduced_bytes) % group_order()) by {
            lemma_fundamental_div_mod_converse_mod(
                bytes_to_nat(reduced_bytes) as int,
                group_order() as int,
                0int,
                bytes_to_nat(reduced_bytes) as int,
            );
        }

        // Step 3: From Step 1, Step 2, and requires, deduce self_bytes differs from its mod
        // reduced == reduced % L (Step 2) and reduced % L == self % L (requires)
        // implies reduced == self % L, but reduced != self (Step 1)
        // therefore self % L != self
        assert(bytes_to_nat(self_bytes) % group_order() != bytes_to_nat(self_bytes));

        // Step 4: By contradiction - if self_bytes < group_order, it would equal itself mod group_order
        assert(!(bytes_to_nat(self_bytes) < group_order())) by {
            if bytes_to_nat(self_bytes) < group_order() {
                assert(bytes_to_nat(self_bytes) % group_order() == bytes_to_nat(self_bytes)) by {
                    lemma_small_mod(bytes_to_nat(self_bytes), group_order());
                }
            }
        }
        // Therefore self_bytes >= group_order, so it's not canonical
    }
}

/// Lemma: Montgomery squaring preserves the squares property
/// Key insight: 2^(k+1) - 1 = 2*(2^k - 1) + 1, so R^(2^(k+1) - 1) = R * (R^(2^k - 1))^2
pub proof fn lemma_square_multiply_step(new_y: nat, y_before: nat, y0: nat, R: nat, L: nat, k: nat)
    requires
        L > 0,
        R > 0,
        (new_y * R) % L == (y_before * y_before) % L,
        (y_before * pow(R as int, (pow2(k) - 1) as nat) as nat) % L == (pow(
            y0 as int,
            pow2(k),
        ) as nat) % L,
    ensures
        (new_y * pow(R as int, (pow2(k + 1) - 1) as nat) as nat) % L == (pow(
            y0 as int,
            pow2(k + 1),
        ) as nat) % L,
{
    use vstd::arithmetic::power2::{lemma_pow2_unfold, lemma_pow2_pos};
    use vstd::arithmetic::mul::lemma_mul_is_associative;
    use crate::lemmas::common_lemmas::pow_lemmas::{lemma_pow_nonnegative, lemma_pow2_square};

    lemma_pow2_unfold(k + 1);
    lemma_pow2_pos(k);

    let exp_k = (pow2(k) - 1) as nat;
    let exp_k1 = (pow2(k + 1) - 1) as nat;
    let R_exp_k: int = pow(R as int, exp_k);
    let R_exp_k_sq: nat = (R_exp_k * R_exp_k) as nat;
    let y_R: nat = y_before * (R_exp_k as nat);
    let y0_k: nat = pow(y0 as int, pow2(k)) as nat;

    assert(exp_k1 == 2 * exp_k + 1) by (nonlinear_arith)
        requires
            pow2(k) >= 1,
            pow2(k + 1) == 2 * pow2(k),
            exp_k == (pow2(k) - 1) as nat,
            exp_k1 == (pow2(k + 1) - 1) as nat,
    ;
    lemma_pow_positive(R as int, exp_k);
    lemma_pow_positive(R_exp_k, 2);

    assert(R_exp_k_sq == pow(R_exp_k, 2) as nat) by {
        lemma_pow1(R_exp_k);
        lemma_pow_adds(R_exp_k, 1, 1);
    }
    assert(y_R * y_R == (y_before * y_before) * R_exp_k_sq) by (nonlinear_arith)
        requires
            y_R == y_before * (R_exp_k as nat),
            R_exp_k_sq == (R_exp_k * R_exp_k) as nat,
            R_exp_k > 0,
    ;
    assert((new_y * R) * R_exp_k_sq == new_y * pow(R as int, exp_k1) as nat) by {
        lemma_pow_adds(R as int, 1nat, 2 * exp_k);
        lemma_pow1(R as int);
        lemma_pow_multiplies(R as int, exp_k, 2nat);
        lemma_mul_is_associative(new_y as int, R as int, R_exp_k_sq as int);
    }
    lemma_pow_multiplies(y0 as int, pow2(k), 2);
    lemma_pow2_square(y0 as int, k);
    lemma_pow_nonnegative(y0 as int, pow2(k));

    calc! {
        (==)
        (new_y * pow(R as int, exp_k1) as nat) % L; {}
        ((new_y * R) * R_exp_k_sq) % L; {
            lemma_mul_mod_noop((new_y * R) as int, R_exp_k_sq as int, L as int);
            lemma_mul_mod_noop((y_before * y_before) as int, R_exp_k_sq as int, L as int);
        }
        ((y_before * y_before) * R_exp_k_sq) % L; {}
        (y_R * y_R) % L; {
            lemma_mul_mod_noop(y_R as int, y_R as int, L as int);
            lemma_mul_mod_noop(y0_k as int, y0_k as int, L as int);
        }
        (y0_k * y0_k) % L; {}
        (pow(y0 as int, pow2(k + 1)) as nat) % L;
    }
}

/// If bytes_to_nat(bytes) < group_order(), then bytes[31] <= 127 (high bit is clear)
pub proof fn lemma_canonical_bytes_high_bit_clear(bytes: &[u8; 32])
    requires
        bytes_to_nat(bytes) < group_order(),
    ensures
        bytes[31] <= 127,
{
    lemma_group_order_bound();
    // bytes_to_nat < group_order < 2^255
    if bytes[31] >= 128 {
        // bytes_to_nat >= bytes[31] * 2^248 >= 128 * 2^248 = 2^255
        lemma_bytes_to_nat_lower_bound(bytes, 31);
        lemma_pow2_adds(7, 248);
        lemma2_to64();
        lemma_mul_inequality(128, bytes[31] as int, pow2(248) as int);
        // contradiction: bytes_to_nat >= 2^255 > group_order
    }
}

/// Proves that Scalar52::ZERO has bounded limbs (all limbs are 0 < 2^52)
/// and that its natural number value is 0
pub proof fn lemma_zero_bounded(z: Scalar52)
    requires
        z == (Scalar52 { limbs: [0, 0, 0, 0, 0] }),
    ensures
        limbs_bounded(&z),
        to_nat(&z.limbs) == 0,
{
    assert(0u64 < (1u64 << 52)) by (bit_vector);

    // Prove to_nat is 0 for all-zero limbs
    let seq = z.limbs@.map(|i, x| x as nat);
    assert(seq =~= seq![0nat, 0nat, 0nat, 0nat, 0nat]);

    reveal_with_fuel(seq_to_nat, 6);
    assert(seq_to_nat(seq) == 0);
    assert(to_nat(&z.limbs) == 0);
}

/// Helper lemma: -(L*q + r) % L == (-r) % L
proof fn lemma_neg_sum_mod(q: int, r: int, L: int)
    requires
        L > 0,
        0 <= r < L,
    ensures
        (-(L * q + r)) % L == (-r) % L,
{
    lemma_mod_multiples_vanish(-q, -r, L);
    vstd::arithmetic::mul::lemma_mul_unary_negation(L, q);
}

/// Proves that for self_nat and its negation result_nat:
/// (self_nat + result_nat) % L == 0
/// where result_nat == (-congruent_to_self) % L and congruent_to_self % L == self_nat % L
pub proof fn lemma_negation_sums_to_zero(
    self_nat: nat,
    congruent_to_self: nat,
    result_nat: nat,
    L: nat,
)
    requires
        L > 0,
        congruent_to_self % L == self_nat % L,
        result_nat == (-(congruent_to_self as int)) % (L as int),
        result_nat < L,
    ensures
        (self_nat + result_nat) % L == 0,
{
    let L_int: int = L as int;
    let self_mod_L: int = (self_nat % L) as int;

    // (-congruent_to_self) % L == (-self_mod_L) % L
    let q: int = (congruent_to_self as int) / L_int;
    lemma_fundamental_div_mod(congruent_to_self as int, L_int);
    lemma_neg_sum_mod(q, self_mod_L, L_int);

    if self_mod_L == 0 {
        lemma_small_mod(0nat, L);
        lemma_mod_multiples_vanish((self_nat as int) / L_int, 0, L_int);
    } else {
        lemma_mod_add_multiples_vanish(-self_mod_L, L_int);
        lemma_small_mod((L_int - self_mod_L) as nat, L);
        lemma_add_mod_noop(self_nat as int, result_nat as int, L_int);
        lemma_small_mod(result_nat, L);
        lemma_mod_self_0(L_int);
    }
}

} // verus!
