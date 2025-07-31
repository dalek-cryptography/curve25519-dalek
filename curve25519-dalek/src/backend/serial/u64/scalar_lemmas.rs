#[allow(unused_imports)]
use super::scalar_specs::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;
#[allow(unused_imports)]
use vstd::calc;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {


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


} // verus!
