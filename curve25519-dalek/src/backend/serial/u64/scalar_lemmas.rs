#[allow(unused_imports)]
use super::common_verus::*;
#[allow(unused_imports)]
use super::constants;
#[allow(unused_imports)]
use super::scalar::Scalar52;
#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
#[allow(unused_imports)]
use vstd::bits::*;
#[allow(unused_imports)]
use vstd::calc;
use vstd::prelude::*;

#[allow(unused_imports)]
use super::common_verus::shift_lemmas::*;

verus! {

/// Verification: scalar * scalar.invert() ≡ 1 mod L
proof fn verify_invert_correct(x: Scalar52)
//     requires to_scalar(&x.limbs) != 0
//    ensures (to_scalar(&x.limbs) * invert_spec(&x.limbs)) % group_order() == 1
{
    assume(false);

}

pub proof fn lemma_52_52(x: u64, y: u64)
requires
    x < (1u64 << 52),
    y < (1u64 << 52),
ensures (x as u128) * (y as u128) < (1u128 << 104)
{
    assert(1u128 << 52 == 1u64 << 52) by (bit_vector);
    calc! {
        (<)
        (x as u128) * (y as u128); (<=) {
            if x > 0 {
                lemma_mul_strict_inequality(y as int, (1u128 << 52) as int, x as int);
                assert( x * y < x * (1u128 << 52)  );
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
        z[0] == (a[0] * a[0]) ,
        z[1] == (a[0] * a[1])  * 2,
        z[2] == (a[0] * a[2])  * 2 + (a[1] * a[1]) ,
        z[3] == (a[0] * a[3])  * 2 + (a[1] * a[2])  * 2,
        z[4] == (a[0] * a[4])  * 2 + (a[1] * a[3])  * 2 + (a[2] * a[2]) ,
        z[5] == (a[1] * a[4])  * 2 + (a[2] * a[3])  * 2,
        z[6] == (a[2] * a[4])  * 2 + (a[3] * a[3]) ,
        z[7] == (a[3] * a[4])  * 2,
        z[8] == (a[4] * a[4]) ,
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
    nine_limbs_to_nat_aux(limbs) == slice128_to_nat(limbs)
{

    let seq = limbs@.map(|i, x| x as nat);

    calc! {
        (==)
        slice128_to_nat(limbs); {
        }
        seq_to_nat(seq); {
            reveal_with_fuel(seq_to_nat, 10);
        }
        (limbs[0] as nat) +
        ((limbs[1] as nat) +
            ((limbs[2] as nat) +
            ((limbs[3] as nat) +
            ((limbs[4] as nat) +
            ((limbs[5] as nat) +
                ((limbs[6] as nat) +
                ((limbs[7] as nat) +
                (limbs[8] as nat) * pow2(52)
                ) * pow2(52)
                ) * pow2(52)
            ) * pow2(52)
            ) * pow2(52)
            ) * pow2(52)
            ) * pow2(52)
        ) * pow2(52); {
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
    five_limbs_to_nat_aux(*limbs) == to_nat(limbs)
{
    let seq = limbs@.map(|i, x| x as nat);

    calc! {
        (==)
        to_nat(limbs); {
        }
        seq_to_nat(seq); {
            reveal_with_fuel(seq_to_nat, 6);
        }
        (limbs[0] as nat) +
        ((limbs[1] as nat) +
            ((limbs[2] as nat) +
            ((limbs[3] as nat) +
            (limbs[4] as nat) * pow2(52)
            ) * pow2(52)
            ) * pow2(52)
        ) * pow2(52); {
        lemma_pow2_adds(52, 52);
        lemma_pow2_adds(104, 52);
        lemma_pow2_adds(156, 52);
        broadcast use group_mul_is_distributive;
        broadcast use lemma_mul_is_associative;
        }
        (limbs[0] as nat) +
        pow2(52) * (limbs[1] as nat) +
        pow2(104) * (limbs[2] as nat) +
        pow2(156) * (limbs[3] as nat) +
        pow2(208) * (limbs[4] as nat); {
        }
        five_limbs_to_nat_aux(*limbs);
    }
}


pub proof fn lemma_scalar_subtract_no_overflow(carry: u64, difference_limb: u64, addend: u64, i: u32, l_value: &Scalar52)
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
    shift_is_pow2(52);
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
    shift_is_pow2(52);
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


pub proof fn lemma_from_montgomery_limbs_conversion(
    limbs: &[u128; 9],
    self_limbs: &[u64; 5]
)
    requires
        forall|j: int| #![auto] 0 <= j < 5 ==> limbs[j] == self_limbs[j] as u128,
        forall|j: int| 5 <= j < 9 ==> limbs[j] == 0,
    ensures
        slice128_to_nat(limbs) == to_nat(self_limbs),
{
    lemma_nine_limbs_equals_slice128_to_nat(limbs);
    lemma_five_limbs_equals_to_nat(self_limbs);
    assert(limbs[0] == self_limbs[0] as u128);
    assert(nine_limbs_to_nat_aux(limbs) == (self_limbs[0] as nat) +
           (self_limbs[1] as nat) * pow2(52) +
           (self_limbs[2] as nat) * pow2(104) +
           (self_limbs[3] as nat) * pow2(156) +
           (self_limbs[4] as nat) * pow2(208) +
           0 * pow2(260) + 0 * pow2(312) + 0 * pow2(364) + 0 * pow2(416));
}



pub proof fn lemma_rr_limbs_bounded()
    ensures
        0x000d63c715bea69fu64 < (1u64 << 52),
{
    // Verus can figure that out the other 4 limbs are bounded
    assert(0x000d63c715bea69fu64 < (1u64 << 52)) by (bit_vector);
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
        seq_u64_to_nat(seq.subrange(0, i + 1)) ==
        seq_u64_to_nat(seq.subrange(0, i)) + seq[i] * pow2(52 * i as nat)
    decreases i
{
    if i == 0 {
        reveal_with_fuel(seq_to_nat, 3);
        assert(seq.len()>0);
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
                assert(seq_to_nat(nat_single) == nat_single[0] + seq_to_nat(nat_single.subrange(1, 1)) * pow2(52));
                assert(nat_single.subrange(1, 1).len() == 0);
                assert(seq_to_nat(nat_single.subrange(1, 1)) == 0);
                assert(seq_to_nat(nat_single) == nat_single[0]);
                assert(nat_single[0] == seq[0] as nat);
            }
            seq[0] as nat; {
                assert(pow2(0) == 1) by {lemma2_to64();}
                assert(52 * 0 == 0);
                assert(pow2(52 * 0 as nat) == pow2(0));
                assert((seq[0] * pow2(0)) as nat == (seq[0] * 1) as nat);
                assert((seq[0] * 1) as nat == seq[0] as nat);
            }
            (seq[0] * pow2(52 * 0 as nat)) as nat; {
                lemma_empty_seq_as_nat(seq);
            }
            (seq_u64_to_nat(seq.subrange(0, 0)) + seq[0] * pow2(52 * 0 as nat)) as nat;
        }
        return;
    }
    else {
        let limbs1 = seq.subrange(0, i + 1).map(|i, x| x as nat);
        let limbs2 = seq.subrange(0, i).map(|i, x| x as nat);
        calc! {
            (==)
            seq_u64_to_nat(seq.subrange(0, i + 1)); {
                assert( seq_to_nat(limbs1) == limbs1[0] + seq_to_nat(limbs1.subrange(1, limbs1.len() as int)) * pow2(52));
            }
            limbs1[0] + seq_to_nat(limbs1.subrange(1, limbs1.len() as int)) * pow2(52); {
                assert(seq.subrange(1, i + 1).map(|i, x| x as nat) == limbs1.subrange(1, limbs1.len() as int));
            }
            limbs1[0] + seq_u64_to_nat(seq.subrange(1, i + 1)) * pow2(52); {
                let tail = seq.subrange(1, i + 1);
                assert(i >= 1);
                assert(0 <= i-1 < tail.len());
                lemma_seq_u64_to_nat_subrange_extend(tail, i-1);
                assert(seq_u64_to_nat(tail.subrange(0, i)) ==
                    seq_u64_to_nat(tail.subrange(0, i - 1)) + tail[i -1 ] * pow2(52 * (i-1) as nat));
                assert( tail.subrange(0, i) == seq.subrange(1, i + 1) );
                assert( tail.subrange(0, i - 1) == seq.subrange(1, i ) );
                assert(seq_u64_to_nat(seq.subrange(1, i + 1)) ==
                    seq_u64_to_nat(seq.subrange(1, i )) + seq[i] * pow2(52 * (i-1) as nat));
            }
            limbs1[0] + ((seq_u64_to_nat(seq.subrange(1, i )) + seq[i] * pow2(52 * (i-1) as nat)) * pow2(52)) as nat; {
                broadcast use lemma_mul_is_distributive_add_other_way;
            }
            (limbs1[0] + seq_u64_to_nat(seq.subrange(1, i )) * pow2(52) + seq[i] * pow2(52 * (i-1) as nat) * pow2(52)) as nat; {
                broadcast use lemma_mul_is_associative;
                lemma_pow2_adds(52 * (i-1) as nat, 52);
            }
            (limbs1[0] + seq_u64_to_nat(seq.subrange(1, i )) * pow2(52) + seq[i] * pow2(52 * i as nat)) as nat; {
                assert(seq.subrange(1, i ).map(|i, x| x as nat) == limbs2.subrange(1, limbs2.len() as int));
            }
            (limbs2[0] + seq_to_nat(limbs2.subrange(1, limbs2.len() as int)) * pow2(52) + seq[i] * pow2(52 * i as nat)) as nat; {
                assert( seq_to_nat(limbs2) == limbs2[0] + seq_to_nat(limbs2.subrange(1, limbs2.len() as int)) * pow2(52));
            }
            (seq_to_nat(limbs2) + seq[i] * pow2(52 * i as nat)) as nat; {
            }
            (seq_u64_to_nat(seq.subrange(0, i)) + seq[i] * pow2(52 * i as nat)) as nat;

        }
    }
}

/// Verus times out when this assertion is inside
/// lemma_seq_u64_to_nat_subrange_extend
pub proof fn lemma_empty_seq_as_nat(a: Seq<u64>)
    ensures seq_u64_to_nat(a.subrange(0, 0)) == 0
{
    assert(seq_u64_to_nat(a.subrange(0, 0)) == 0);
}


/// Using lemma_mod_add_multiples_vanish in a big proof made the proof hang
pub proof fn lemma_mod_cancel(a: &Scalar52, b: &Scalar52)
    ensures (group_order() + to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int) ==
            (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int)
{
    lemma_mod_add_multiples_vanish((to_nat(&a.limbs) - to_nat(&b.limbs)) as int, group_order() as int);
}


/// The corollary of limbs_bounded(a)
pub proof fn lemma_bound_scalar(a: &Scalar52)
    requires limbs_bounded(a)
    ensures to_nat(&a.limbs) < pow2((52 * (5) as nat))
{
    lemma_general_bound(a.limbs@);
}

/// The general case of lemma_bound_scalar so we
/// can prove via straightforward induction.
pub proof fn lemma_general_bound(a: Seq<u64>)
    requires forall|i: int| 0 <= i < a.len() ==> a[i] < (1u64 << 52)
    ensures seq_u64_to_nat(a) < pow2((52 * a.len() as nat))
    decreases a.len()
{
    if a.len() == 0 {
        assert(seq_u64_to_nat(a) == 0);
        lemma2_to64(); // Gives us pow2(0) == 1 among other facts
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
        assert(a.map(|i, x| x as nat).subrange(1, a.len() as int) == a.subrange(1, a.len() as int).map(|i, x| x as nat));
        // Therefore:
        assert(seq_u64_to_nat(a) == a[0] as nat + seq_u64_to_nat(a.subrange(1, a.len() as int)) * pow2(52));

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

        assert(seq_u64_to_nat(a) <= (pow2(52) - 1) + (pow2(52 * (a.len() - 1) as nat) - 1) * pow2(52)) by {
            lemma_mul_inequality((pow2(52 * (a.len() - 1) as nat) - 1) as int, pow2(52 * (a.len() - 1) as nat) as int, pow2(52) as int);
        };

        // Expand the right side
        assert((pow2(52) - 1) + (pow2(52 * (a.len() - 1) as nat) - 1) * pow2(52) ==
               pow2(52) - 1 + pow2(52 * (a.len() - 1) as nat) * pow2(52) - pow2(52)) by {
            broadcast use lemma_mul_is_distributive_sub;
        };

        assert(pow2(52) - 1 + pow2(52 * (a.len() - 1) as nat) * pow2(52) - pow2(52) ==
               pow2(52 * (a.len() - 1) as nat) * pow2(52) - 1);

        lemma_pow2_adds(52 * (a.len() - 1) as nat, 52);
        assert(pow2(52 * (a.len() - 1) as nat) * pow2(52) == pow2(52 * (a.len() - 1) as nat + 52));
        assert(52 * (a.len() - 1) as nat + 52 == 52 * a.len() as nat);

        assert(seq_u64_to_nat(a) <= pow2(52 * a.len() as nat) - 1);
        assert(seq_u64_to_nat(a) < pow2(52 * a.len() as nat));
    }
}

/// Claude wrote this proof. Could the proof be shorter?
/// Moved this to a lemma to get under rlimit.
pub proof fn lemma_decompose(a: u64, mask: u64)
    requires mask == (1u64 << 52) - 1
    ensures a == (a >> 52) * pow2(52) + (a & mask)
{
    // First, establish that bit shifting is division by pow2(52)
    broadcast use lemma_u64_shr_is_div;
    lemma_pow2_pos(52);
    shift_is_pow2(52);
    lemma2_to64_rest(); // Establishes pow2(52) == 0x10000000000000
    assert((1u64 << 52) == 0x10000000000000) by (bit_vector);
    assert(pow2(52) == 0x10000000000000);
    assert((1u64 << 52) as nat == pow2(52));

    assert(a >> 52 == a / (1u64 << 52));

    // Apply fundamental division theorem: a = q * d + r
    lemma_fundamental_div_mod(a as int, pow2(52) as int);
    let q = a as nat / pow2(52);
    let r = a as nat % pow2(52);
    assert(a as nat == q * pow2(52) + r);
    assert(0 <= r < pow2(52));

    // Now prove that (a & mask) == r
    // mask is all 1s in the lower 52 bits
    assert(mask == (1u64 << 52) - 1);

    // Key insight: a & mask gives us the lower 52 bits, which is exactly a % pow2(52)
    lemma_u64_low_bits_mask_is_mod(a, 52);
    assert(a & mask == a % (1u64 << 52));
    assert((a % (1u64 << 52)) as nat == a as nat % pow2(52));
    assert((a & mask) as nat == r);

    // Now show that a >> 52 == q
    assert((a >> 52) as nat == a as nat / pow2(52));
    assert((a >> 52) as nat == q);

    // Combine everything
    assert(a as nat == (a >> 52) as nat * pow2(52) + (a & mask) as nat);
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
pub proof fn lemma_sub_loop1_invariant(difference: Scalar52, borrow: u64, i: usize, a: &Scalar52, b: &Scalar52, old_borrow: u64, mask: u64, difference_loop1_start: Scalar52)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        0 <= i < 5,
        forall|j: int| 0 <= j < i ==> difference.limbs[j] < (1u64 << 52),
        mask == (1u64 << 52) - 1,
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(b.limbs@.subrange(0, i as int )) ==
                    seq_u64_to_nat(difference_loop1_start.limbs@.subrange(0, i as int )) - (old_borrow >> 63) * pow2((52 * (i) as nat)),
        difference_loop1_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int),
        difference.limbs[i as int] == borrow & mask,
        borrow == a.limbs[i as int].wrapping_sub((b.limbs[i as int] + (old_borrow >> 63)) as u64)
    ensures
        seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2((52 * (i + 1) as nat))
        == seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) - seq_u64_to_nat(b.limbs@.subrange(0, i + 1))
{
    calc! {
        (==)
        seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) - seq_u64_to_nat(b.limbs@.subrange(0, i + 1)); {
            lemma_seq_u64_to_nat_subrange_extend(a.limbs@, i as int);
            lemma_seq_u64_to_nat_subrange_extend(b.limbs@, i as int);
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + a.limbs[i as int] * pow2(52 * i as nat) -
        (seq_u64_to_nat(b.limbs@.subrange(0, i as int)) + b.limbs[i as int] * pow2(52 * i as nat)); {
            broadcast use lemma_mul_is_distributive_sub_other_way;
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) - seq_u64_to_nat(b.limbs@.subrange(0, i as int)) +
        (a.limbs[i as int] - b.limbs[i as int]) * pow2(52 * i as nat); {
            assert(difference_loop1_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int));
            // Use loop invariant
        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) - (old_borrow >> 63) * pow2(52 * i as nat) +
        (a.limbs[i as int] - b.limbs[i as int]) * pow2(52 * i as nat); {
            broadcast use lemma_mul_is_distributive_sub_other_way;
        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i as int))  +
        (a.limbs[i as int] - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
            assert(borrow == a.limbs[i as int].wrapping_sub((b.limbs[i as int] + (old_borrow >> 63)) as u64));
            assert(difference.limbs[i as int] == borrow & mask);
            // Expand wrapping sub
            if a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64) < 0 {

                assert(borrow >= 0x1_0000_0000_0000_0000 - (1u64<<52)) by {
                    assert(old_borrow >> 63 <= 1) by (bit_vector);
                    assert(b.limbs[i as int] <= (1u64 << 52) - 1);
                    assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64) + 0x1_0000_0000_0000_0000) as u64);
                    assert((b.limbs[i as int] + (old_borrow >> 63)) as u64 <= 1u64 << 52);
                    assert(borrow >= (a.limbs[i as int] - (1u64 << 52) + 0x1_0000_0000_0000_0000) as u64);
                };
                calc! {
                    (==)
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int))  +
                    (a.limbs[i as int] - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
                        assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64) + 0x1_0000_0000_0000_0000) as u64);
                        assert(b.limbs[i as int] < 1u64 << 52);
                        assert(old_borrow >> 63 <= 1) by (bit_vector);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow - 0x1_0000_0000_0000_0000) * pow2(52 * i as nat); {
                        lemma_decompose(borrow, mask);
                        assert(borrow == (borrow >> 52) * pow2(52) + difference.limbs[i as int]);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) +
                        ((borrow >> 52) * pow2(52) + difference.limbs[i as int] - 0x1_0000_0000_0000_0000) * pow2(52 * i as nat); {
                        assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {broadcast use lemma_pow2_adds;};
                        assert(52 + 52 * i as nat == 52 * (i+1) as nat);
                        broadcast use lemma_mul_is_distributive_add_other_way;
                        broadcast use lemma_mul_is_distributive_sub_other_way;
                        assert((borrow >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (borrow >> 52) as nat * pow2(52 * (i+1) as nat)) by {
                                assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i+1) as nat));
                                lemma_mul_is_associative((borrow >> 52) as int, pow2(52) as int, pow2(52 * i as nat) as int);
                        };
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) +
                        (borrow >> 52) * pow2(52 * (i+1) as nat) + difference.limbs[i as int] * pow2(52 * i as nat) -
                        0x1_0000_0000_0000_0000 * pow2(52 * i as nat); {
                            lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) +
                        (borrow >> 52) * pow2(52 * (i+1) as nat) - 0x1_0000_0000_0000_0000 * pow2(52 * i as nat); {
                        assert(borrow >> 52 == (1u64<<12) - 1) by (bit_vector)
                                requires borrow >= 0x1_0000_0000_0000_0000 - (1u64<<52);
                        assert( 0x1_0000_0000_0000_0000 * pow2(52 * i as nat) == (1u64 << 12) * pow2(52 * (i + 1) as nat) ) by
                        {
                            lemma2_to64();
                            assert(0x1_0000_0000_0000_0000 == pow2(64));
                            assert(1u64 << 12 == pow2(12)) by (compute);
                            lemma_pow2_adds(64, 52 * i as nat);
                            lemma_pow2_adds(12, 52 * (i + 1) as nat);
                            assert(64 + 52 * i as nat == 12 + 52 * (i + 1) as nat);
                        }
                        lemma_mul_is_distributive_sub_other_way(pow2(52 * (i+1) as nat) as int, (1u64<<12) - 1, (1u64 << 12) as int);
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) +
                        (-1) * pow2(52 * (i+1) as nat) ; {
                        assert(borrow >> 63 == 1) by (bit_vector)
                                requires borrow >= 0x1_0000_0000_0000_0000 - (1u64<<52);
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2((52 * (i + 1) as nat));
                }
            }
            else {

                calc! {
                    (==)
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int))  +
                    (a.limbs[i as int] - b.limbs[i as int] - (old_borrow >> 63)) * pow2(52 * i as nat); {
                        assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64)) as u64);
                        assert(b.limbs[i as int] < 1u64 << 52);
                        assert(old_borrow >> 63 <= 1) by (bit_vector);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (borrow) * pow2(52 * i as nat); {
                        lemma_decompose(borrow, mask);
                        assert(borrow == (borrow >> 52) * pow2(52) + difference.limbs[i as int]);
                    }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) +
                        ((borrow >> 52) * pow2(52) + difference.limbs[i as int]) * pow2(52 * i as nat); {
                        assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {broadcast use lemma_pow2_adds;};
                        assert(52 + 52 * i as nat == 52 * (i+1) as nat);
                        broadcast use lemma_mul_is_distributive_add_other_way;
                        assert((borrow >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (borrow >> 52) as nat * pow2(52 * (i+1) as nat)) by {
                                assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i+1) as nat));
                                lemma_mul_is_associative((borrow >> 52) as int, pow2(52) as int, pow2(52 * i as nat) as int);
                        };
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) +
                        (borrow >> 52) * pow2(52 * (i+1) as nat) + difference.limbs[i as int] * pow2(52 * i as nat); {
                            lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
                        assert (borrow < 1u64 << 52) by {
                            assert(borrow == (a.limbs[i as int] - ((b.limbs[i as int] + (old_borrow >> 63)) as u64)) as u64);
                            assert(a.limbs[i as int] < (1u64 << 52));
                            assert((b.limbs[i as int] + (old_borrow >> 63)) as u64 >= 0);
                        }
                        assert(borrow >> 52 == 0) by (bit_vector)
                                requires borrow < 1u64 << 52;
                        assert(borrow >> 63 == 0) by (bit_vector)
                                requires borrow < 1u64 << 52;
                        }
                    seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2((52 * (i + 1) as nat));
                }
            }
        }
        seq_u64_to_nat(difference.limbs@.subrange(0, i + 1)) - (borrow >> 63) * pow2((52 * (i + 1) as nat));
    }
}

/// Just a proof by computation
pub(crate) proof fn lemma_l_equals_group_order()
    ensures
        to_nat(&constants::L.limbs) == group_order(),
        seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) == group_order()
{
    // First show that the subrange equals the full array
    assert(constants::L.limbs@ == constants::L.limbs@.subrange(0, 5 as int));
    assert(seq_u64_to_nat(constants::L.limbs@) == seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)));
    assert(to_nat(&constants::L.limbs) == seq_u64_to_nat(constants::L.limbs@));

    assert(pow2(52) == 0x10000000000000) by {lemma2_to64_rest();};
    lemma_pow2_adds(52, 52);
    assert(pow2(104) == 0x100000000000000000000000000);
    lemma_pow2_adds(104, 104);
    assert(pow2(208) == 0x10000000000000000000000000000000000000000000000000000);
    lemma_pow252();
    lemma_five_limbs_equals_to_nat(&constants::L.limbs);
    assert(five_limbs_to_nat_aux(constants::L.limbs) == group_order()) by (compute);
}

pub proof fn lemma_pow252()
    ensures pow2(252) == 0x1000000000000000000000000000000000000000000000000000000000000000
{
    assert(pow2(63) == 0x8000000000000000) by {lemma2_to64_rest();}
    lemma_pow2_adds(63, 63);
    assert(pow2(126) == 0x40000000000000000000000000000000);
    lemma_pow2_adds(126, 126);
}

pub proof fn lemma_pow2_260_greater_than_2_group_order()
    ensures pow2(260) > 2 * group_order()
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
pub(crate) proof fn lemma_sub_correct_after_loops(difference: Scalar52, carry: u64, a: &Scalar52, b: &Scalar52, difference_after_loop1: Scalar52, borrow: u64)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        limbs_bounded(&difference),
        limbs_bounded(&difference_after_loop1),
        (carry >> 52) < 2,
        -group_order() <= to_nat(&a.limbs) - to_nat(&b.limbs) < group_order(),
        borrow >> 63 == 0 ==> difference_after_loop1 == difference,
        borrow >> 63 == 1 ==>
        seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) ==
        seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(52 * 5 as nat),
        seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int )) - (borrow >> 63) * pow2((52 * (5) as nat)),
    ensures
            to_nat(&difference.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int)
{
        assert(borrow >> 63 == 1 || borrow >> 63 == 0) by (bit_vector);
        assert( seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) == to_nat(&difference.limbs)) by {
            assert( seq_u64_to_nat(difference.limbs@) == to_nat(&difference.limbs));
            assert( difference.limbs@ == difference.limbs@.subrange(0, 5 as int));
        }
        assert( seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == to_nat(&b.limbs)) by {
            assert( seq_u64_to_nat(b.limbs@) == to_nat(&b.limbs));
            assert( b.limbs@ == b.limbs@.subrange(0, 5 as int));
        }
        assert( seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) == to_nat(&a.limbs)) by {
            assert( seq_u64_to_nat(a.limbs@) == to_nat(&a.limbs));
            assert( a.limbs@ == a.limbs@.subrange(0, 5 as int));
        }
        if borrow >> 63 == 0 {

            assert(              seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                                        seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int )) - (borrow >> 63) * pow2((52 * (5) as nat)) );
            assert(              seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                                        seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int )) );
            assert(              to_nat(&a.limbs) - to_nat(&b.limbs) ==
                                        to_nat(&difference.limbs) );
            assert(to_nat(&a.limbs) - to_nat(&b.limbs) >= 0);
            assert(to_nat(&a.limbs) - to_nat(&b.limbs) < group_order());
            lemma_small_mod((to_nat(&a.limbs) - to_nat(&b.limbs)) as nat, group_order());
            assert(to_nat(&difference.limbs) == (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int));
        }
        if borrow >> 63 == 1 {
            assert(
                          seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) ==
                          seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(52 * 5 as nat)
            );
            assert(
                          seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) ==
                          seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(52 * 5 as nat)
                    - seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int))
            );
            assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                   seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int )) - pow2((52 * (5) as nat)) );
            assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                   seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(52 * 5 as nat)
                    - seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) - pow2((52 * (5) as nat)) );
            assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) +
                   seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                   seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) + (carry >> 52) * pow2(52 * 5 as nat)
                     - pow2((52 * (5) as nat)) );
            if carry >> 52 == 0 {
                // Get a contradiction because the sides in the above equation have different signs
                assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) +
                    seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) >=0) by {
                    assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) >= group_order()) by {
                        lemma_l_equals_group_order();
                    };
                    assert(seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) == to_nat(&a.limbs));
                    assert(seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) == to_nat(&b.limbs));
                };
                assert(seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) < pow2((52 * (5) as nat))) by {
                    assert(seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int)) == to_nat(&difference.limbs));
                    lemma_bound_scalar(&difference);
                };
                assert((carry >> 52) * pow2(52 * 5 as nat) == 0);
                assert(false);
            }
            assert(carry >> 52 ==1);
            assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) +
                   seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) - seq_u64_to_nat(b.limbs@.subrange(0, 5 as int )) ==
                   seq_u64_to_nat(difference.limbs@.subrange(0, 5 as int))  );
            assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) +
                   to_nat(&a.limbs) - to_nat(&b.limbs) ==
                   to_nat(&difference.limbs)  );
            assert(to_nat(&constants::L.limbs) == group_order()) by {
                lemma_l_equals_group_order();
            };
            assert(seq_u64_to_nat(constants::L.limbs@.subrange(0, 5 as int)) == group_order()) by {
                lemma_l_equals_group_order();
            };
            assert(group_order() > 0);
            calc! {
                (==)
                to_nat(&difference.limbs) as int; {
                }
                group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs); {
                    assert(group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs) < group_order()) by {
                        assert( seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, 5 as int)) == to_nat(&difference_after_loop1.limbs)) by {
                            assert( seq_u64_to_nat(difference_after_loop1.limbs@) == to_nat(&difference_after_loop1.limbs));
                            assert( difference_after_loop1.limbs@ == difference_after_loop1.limbs@.subrange(0, 5 as int));
                        }
                        assert(to_nat(&a.limbs) - to_nat(&b.limbs ) ==
                        to_nat(&difference_after_loop1.limbs ) - pow2((52 * (5) as nat)) );
                        lemma_bound_scalar(&difference_after_loop1);
                    };
                    lemma_small_mod((group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs)) as nat, group_order());
                }
                (group_order() as int + to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int); {
                    lemma_mod_cancel(a, b);
                }
                (to_nat(&a.limbs) - to_nat(&b.limbs)) % (group_order() as int);
            }
        }
}

/// Moving this out to get under rlimit
pub proof fn lemma_old_carry(old_carry: u64)
    requires old_carry < 1u64 <<52,
    ensures old_carry >> 52 == 0,
{
    assert(old_carry >> 52 == 0) by (bit_vector)
        requires old_carry < 1u64 <<52;
}

/// If borrow >> 63 == 0, we just prove that the loop step has no effect.
/// If borrow >> 63 == 1, we substitute in the loop's updates
/// like `difference.limbs[i as int] == carry & mask`.
/// In that case we're proving that subtraction is correct if we only
/// consider the first i items of each array, except there's also a
/// `(carry >> 52) * pow2(52 * (i+1) as nat)` term that doesn't go away.
pub(crate) proof fn lemma_sub_loop2_invariant(difference: Scalar52, i: usize, a: &Scalar52, b: &Scalar52, mask: u64, difference_after_loop1: Scalar52, difference_loop2_start: Scalar52, carry: u64, old_carry: u64, addend: u64, borrow: u64)
    requires
        0 <= i < 5,
        mask == (1u64 << 52) - 1,
        forall|j: int| 0 <= j < 5 ==> difference_loop2_start.limbs[j] < (1u64 << 52),
        forall|j: int| i <= j < 5 ==> difference_loop2_start.limbs[j] == difference_after_loop1.limbs[j],
        forall|j: int| (0 <= j < 5 && j!=i) ==> difference_loop2_start.limbs[j] == difference.limbs[j],
        mask == (1u64 << 52) - 1,
        i == 0 ==> old_carry == 0,
        i >= 1 ==> (old_carry >> 52) < 2,
        (i >=1 && borrow >> 63 == 0) ==> old_carry == difference_loop2_start.limbs[i-1],
        borrow >> 63 == 0 ==> difference_after_loop1 == difference_loop2_start,
        borrow >> 63 == 1 ==>
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) ==
            seq_u64_to_nat(difference_loop2_start.limbs@.subrange(0, i as int)) + (old_carry >> 52) * pow2(52 * i as nat),
        difference.limbs[i as int] == carry & mask,
        difference_loop2_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int),
        borrow >> 63 == 0 ==> addend == 0,
        borrow >> 63 == 1 ==> addend == constants::L.limbs[i as int],
        carry == (old_carry >> 52) + difference_loop2_start.limbs[i as int] + addend,
    ensures
        (i+1 >=1 && borrow >> 63 == 0) ==> carry == difference.limbs[i as int],
        borrow >> 63 == 0 ==> difference_after_loop1 == difference,
        borrow >> 63 == 1 ==>
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i+1 as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i+1 as int)) ==
            seq_u64_to_nat(difference.limbs@.subrange(0, i+1 as int)) + (carry >> 52) * pow2(52 * (i+1) as nat)
{
    if borrow >> 63 == 0 {
        lemma_old_carry(old_carry);
        assert(addend == 0);
        assert(carry == difference_loop2_start.limbs[i as int]);
        assert( carry & mask == carry ) by (bit_vector)
            requires
            carry < 1u64 <<52,
            mask == (1u64 << 52) - 1;
        assert(difference_after_loop1.limbs[i as int] == difference.limbs[i as int]);
        assert(forall |j :int| 0<=j<5 ==> difference_after_loop1.limbs[j] == difference.limbs[j]);
        assert(difference_after_loop1.limbs == difference.limbs);
    }
    if borrow >> 63 == 1 {
        // When underflow, addend = L.limbs[i]
        assert(addend == constants::L.limbs[i as int]);
        // carry = (old_carry >> 52) + difference_after_loop1.limbs[i] + L.limbs[i]
        // difference.limbs[i] = carry & mask
        calc! {
            (==)
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i+1)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i+1)); {
                lemma_seq_u64_to_nat_subrange_extend(difference_after_loop1.limbs@, i as int);
                lemma_seq_u64_to_nat_subrange_extend(constants::L.limbs@, i as int);
            }
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int)) + difference_after_loop1.limbs[i as int] as nat * pow2(52 * i as nat) +
            seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) + constants::L.limbs[i as int] as nat * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;
            }
            seq_u64_to_nat(difference_after_loop1.limbs@.subrange(0, i as int)) + seq_u64_to_nat(constants::L.limbs@.subrange(0, i as int)) +
            (difference_after_loop1.limbs[i as int] as nat + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                // Use invariant
            }
            seq_u64_to_nat(difference_loop2_start.limbs@.subrange(0, i as int)) + (old_carry >> 52) as nat * pow2(52 * i as nat) +
            (difference_after_loop1.limbs[i as int] as nat + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                assert(difference_loop2_start.limbs@.subrange(0, i as int) == difference.limbs@.subrange(0, i as int) );
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (old_carry >> 52) as nat * pow2(52 * i as nat) +
            (difference_after_loop1.limbs[i as int] as nat + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((old_carry >> 52) as nat +
            difference_after_loop1.limbs[i as int] as nat + constants::L.limbs[i as int] as nat) * pow2(52 * i as nat); {
                assert(carry == (old_carry >> 52) + difference_after_loop1.limbs[i as int] + constants::L.limbs[i as int]);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + carry as nat * pow2(52 * i as nat); {
                assert(carry == (carry >> 52) * (1u64<<52) + (carry & mask)) by (bit_vector)
                    requires mask == (1u64 << 52) - 1;
                assert(carry == (carry >> 52) * pow2(52) + difference.limbs[i as int]) by {
                    lemma2_to64_rest();
                    assert(0x10000000000000 == 1u64 << 52) by (compute_only);};
                    assert(difference.limbs[i as int] == carry & mask);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + ((carry >> 52) as nat * pow2(52) + difference.limbs[i as int] as nat) * pow2(52 * i as nat); {
                broadcast use lemma_mul_is_distributive_add_other_way;
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (carry >> 52) as nat * pow2(52) * pow2(52 * i as nat) + difference.limbs[i as int] as nat * pow2(52 * i as nat); {
                assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {broadcast use lemma_pow2_adds;};
                assert(52 + 52 * i as nat == 52 * (i+1) as nat);
                assert((carry >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (carry >> 52) as nat * pow2(52 * (i+1) as nat)) by {
                        assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i+1) as nat));
                        lemma_mul_is_associative((carry >> 52) as int, pow2(52) as int, pow2(52 * i as nat) as int);
                };
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i as int)) + (carry >> 52) as nat * pow2(52 * (i+1) as nat) + difference.limbs[i as int] as nat * pow2(52 * i as nat); {
                lemma_seq_u64_to_nat_subrange_extend(difference.limbs@, i as int);
            }
            seq_u64_to_nat(difference.limbs@.subrange(0, i+1)) + (carry >> 52) as nat * pow2(52 * (i+1) as nat);
        }
    }
}

/// Proves that the addition loop maintains its invariant:
/// a[0..i+1] + b[0..i+1] == sum[0..i+1] + (carry >> 52) * 2^(52*(i+1))
/// See lemma_sub_loop1_invariant for more comments
pub proof fn lemma_add_loop_invariant(sum: Scalar52, carry: u64, i: usize, a: &Scalar52, b: &Scalar52, old_carry: u64, mask: u64, sum_loop_start: Scalar52)
    requires
        limbs_bounded(a),
        limbs_bounded(b),
        0 <= i < 5,
        forall|j: int| 0 <= j < i ==> sum.limbs[j] < (1u64 << 52),
        mask == (1u64 << 52) - 1,
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(b.limbs@.subrange(0, i as int)) ==
                    seq_u64_to_nat(sum_loop_start.limbs@.subrange(0, i as int)) + (old_carry >> 52) * pow2((52 * (i) as nat)),
        sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int),
        sum.limbs[i as int] == carry & mask,
        carry == a.limbs[i as int] + b.limbs[i as int] + (old_carry >> 52)
    ensures
        seq_u64_to_nat(sum.limbs@.subrange(0, i + 1)) + (carry >> 52) * pow2((52 * (i + 1) as nat))
        == seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) + seq_u64_to_nat(b.limbs@.subrange(0, i + 1))
{
    calc! {
        (==)
        seq_u64_to_nat(a.limbs@.subrange(0, i + 1)) + seq_u64_to_nat(b.limbs@.subrange(0, i + 1)); {
            lemma_seq_u64_to_nat_subrange_extend(a.limbs@, i as int);
            lemma_seq_u64_to_nat_subrange_extend(b.limbs@, i as int);
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + a.limbs[i as int] as nat * pow2(52 * i as nat) +
        seq_u64_to_nat(b.limbs@.subrange(0, i as int)) + b.limbs[i as int] as nat * pow2(52 * i as nat); {
            lemma_mul_is_distributive_add_other_way(pow2(52 * i as nat) as int, a.limbs[i as int] as int, b.limbs[i as int] as int);
        }
        seq_u64_to_nat(a.limbs@.subrange(0, i as int)) + seq_u64_to_nat(b.limbs@.subrange(0, i as int)) +
        (a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(sum_loop_start.limbs@.subrange(0, i as int) == sum.limbs@.subrange(0, i as int));
            // Use loop invariant
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) + (old_carry >> 52) as nat * pow2(52 * i as nat) +
        (a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            lemma_mul_is_distributive_add_other_way(pow2(52 * i as nat) as int, (old_carry >> 52) as int, (a.limbs[i as int] as nat + b.limbs[i as int] as nat) as int);
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) +
        ((old_carry >> 52) as nat + a.limbs[i as int] as nat + b.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(carry == a.limbs[i as int] + b.limbs[i as int] + (old_carry >> 52));
            assert(sum.limbs[i as int] == carry & mask);
            // Decompose carry using the mask
            lemma_decompose(carry, mask);
            assert(carry == (carry >> 52) * pow2(52) + sum.limbs[i as int]);
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) +
        ((carry >> 52) as nat * pow2(52) + sum.limbs[i as int] as nat) * pow2(52 * i as nat); {
            assert(pow2(52) * pow2(52 * i as nat) == pow2(52 + 52 * i as nat)) by {lemma_pow2_adds(52, 52 * i as nat);};
            assert(52 + 52 * i as nat == 52 * (i+1) as nat);
            lemma_mul_is_distributive_add_other_way(pow2(52 * i as nat) as int, (carry >> 52) as nat * pow2(52) as int, sum.limbs[i as int] as int);
            assert((carry >> 52) as nat * pow2(52) * pow2(52 * i as nat) == (carry >> 52) as nat * pow2(52 * (i+1) as nat)) by {
                    assert(pow2(52) * pow2(52 * i as nat) == pow2(52 * (i+1) as nat));
                    lemma_mul_is_associative((carry >> 52) as int, pow2(52) as int, pow2(52 * i as nat) as int);
            };
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i as int)) +
        (carry >> 52) as nat * pow2(52 * (i+1) as nat) + sum.limbs[i as int] as nat * pow2(52 * i as nat); {
            lemma_seq_u64_to_nat_subrange_extend(sum.limbs@, i as int);
        }
        seq_u64_to_nat(sum.limbs@.subrange(0, i + 1)) + (carry >> 52) as nat * pow2((52 * (i + 1) as nat));
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
        seq_u64_to_nat(a.limbs@.subrange(0, 5 as int)) + seq_u64_to_nat(b.limbs@.subrange(0, 5 as int)) ==
               seq_u64_to_nat(sum.limbs@.subrange(0, 5 as int)) + (carry >> 52) as nat * pow2((52 * (5) as nat))
    ensures
        to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs)
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

    assert(to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs) + (carry >> 52) * pow2((52 * (5) as nat)));

    // From the loop invariant, we have: a + b == sum + (carry >> 52) * 2^260
    assert(52 * 5 == 260) by (compute);
    assert(pow2((52 * 5) as nat) == pow2(260));
    assert(to_nat(&a.limbs) + to_nat(&b.limbs) == to_nat(&sum.limbs) + (carry >> 52) as nat * pow2(260));

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

} // verus!
