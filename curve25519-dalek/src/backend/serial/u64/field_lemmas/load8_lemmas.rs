#![allow(unused)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {


pub proof fn bit_or_is_plus(a: u64, b: u8, k: nat)
    requires
        k + 16 <= 64,
        a < 1u64 << k
    ensures
        a | ((b as u64) << (k as u64)) == a + ((b as u64) << (k as u64))
{
    assume(false);
}


pub proof fn bit_or_is_plus_alt(a: u8, b: u8, k: nat)
    requires
        k + 16 <= 64
    ensures
        ((a as u64) << (k as u64)) | ((b as u64)) << (k + 8) as u64
        ==
        (pow2(k) * a + pow2(k + 8) * b)
{
    let a64 = a as u64;
    let b64 = b as u64;
    let k64 = k as u64;
    let k_8_64 = (k + 8) as u64;

    let a_shl = a64 << k64;
    let b_shl = b64 << k_8_64;

    assert( a_shl == pow2(k) * a ) by {
        assert(a64 as nat == a);
        u8_times_pow2_fits_u64(a, k);
        lemma_u64_shl_is_mul(a64, k64);
    }

    assert( b_shl == pow2(k + 8) * b ) by {
        assert(b64 as nat == b);
        u8_times_pow2_fits_u64(b, k + 8);
        lemma_u64_shl_is_mul(b64, k_8_64);
    }

    if (a == 0 || b == 0) {
        bitwise_or_r_zero_is_id((pow2(k) * a) as u64);
        bitwise_or_l_zero_is_id((pow2(k + 8) * b) as u64);

        assume(false);
    }
    else {
        assert(a_shl <= pow2(k + 8) - pow2(k) < pow2(k + 8)) by {
            pow2_mul_u8(a, k);
            // 2^k > 0
            lemma_pow2_pos(k);
        }
        assert(pow2(k + 8) <= b_shl <= pow2(k + 16) - pow2(k + 8)) by {
            mul_le(1, b as nat, pow2(k + 8), pow2(k + 8));
            pow2_mul_u8(b, k + 8);
        }

        assert(a_shl + b_shl <= u64::MAX) by {
            // 2^(k + 8) > 0
            assert(a_shl + b_shl <= (pow2(k + 16) - pow2(k)));
            assert(a_shl + b_shl <= (pow2(64) - pow2(0))) by {
                if (k + 16 < 64){
                    lemma_pow2_strictly_increases(k + 16, 64);
                }
                if (0 < k){
                    lemma_pow2_strictly_increases(0, k);
                }
                lemma_pow2_pos(0);
            }
            assert(pow2(64) - pow2(0) == u64::MAX) by {
                lemma2_to64();
                lemma2_to64_rest();
            }
        }

        let sum = (a_shl + b_shl) as u64;

        assert(a_shl | b_shl == sum) by {
            assume(false);
        }

    }
}

pub open spec fn load8_at_or_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k
{
    if (k == 0) {
        (input[i as int] as u64)
    }
    else {
        // k > 0
        load8_at_or_version_rec(input, i, (k - 1) as nat) | ((input[i + k] as u64) << k * 8)
    }
}

pub open spec fn load8_at_plus_version_rec(input: &[u8], i: usize, k: nat) -> u64
    decreases k
{
    if (k == 0) {
        (input[i as int] as u64)
    }
    else {
        // k > 0
        (load8_at_plus_version_rec(input, i, (k - 1) as nat) + ((input[i + k] as u64) << k * 8)) as u64
    }
}

pub proof fn load8_at_plus_version_rec_is_bounded(input: &[u8], i: usize, k: nat)
    requires
        k <= 7
    ensures
        load8_at_plus_version_rec(input, i, k) < pow2(8 * (k + 1))
    decreases k
{

    assert(u8::MAX < pow2(8)) by {
        lemma2_to64();
    }

    if (k == 0) {
        // just needs the the pre-if assert
    }
    else {
        // k > 0
        assert(load8_at_plus_version_rec(input, i, (k - 1) as nat) < pow2(8 * k)) by {
            load8_at_plus_version_rec_is_bounded(input, i, (k - 1) as nat);
        }

        assert((input[i + k] as u64) * pow2(8 * k) <= u64::MAX) by {
            assert(u64::MAX == pow2(64) - 1) by {
                lemma2_to64_rest();
            }
            assert((input[i + k] as u64) * pow2(8 * k) < pow2(64)) by {
                assert((input[i + k] as u64) * pow2(8 * k) < pow2(8) * pow2(8 * k)) by {
                    lemma_mul_strict_inequality(
                        input[i + k] as int,
                        pow2(8) as int,
                        pow2(8 * k) as int
                    );
                }
                if (k < 7) {
                    lemma_pow2_strictly_increases(8 * k, 56);
                }
                lemma_pow2_adds(8, 56);
            }
        }

        // lemma_pow2_pos(8);
        //     lemma_mul_strict_inequality(
        //         load8_at_plus_version_rec(input, i, (k -1) as nat) as nat,
        //         pow2(8 * k),
        //         pow2(8)
        //     );

        // lemma_pow2_adds(8 * k, 8);
    }
}

// pub proof fn load8_at_versions_equivalent(input: &[u8], i: usize, k: nat)
//     requires
//         k <= 7
//     ensures
//         load8_at_or_version_rec(input, i, k) == load8_at_plus_version_rec(input, i, k)
//     decreases k
// {
//     if (k == 0){
//         // trivial
//     }
//     else {
//         load8_at_versions_equivalent(input, i, (k - 1) as nat);
//         let prev = load8_at_plus_version_rec(input, i, (k - 1) as nat);
//         assert(prev < (1u64 << 8 * k));
//         bit_or_is_plus(prev, input[i + k], 8 * k);
//     }
// }


pub proof fn load8_at_spec_fits_u64(input: &[u8], i: usize)
    requires
        i + 7 < input.len()
    ensures
        load8_at_spec(input, i) <= u64::MAX
{
    lemma2_to64();
    lemma2_to64_rest();

    assert forall |j: nat| 0 <= j < 8 implies #[trigger] pow2(j * 8) * input[i + j] <= pow2((j + 1) * 8) - pow2(j * 8) by {
        // sanity check, holds for all u8
        assert(input[i + j] <= pow2(8) - 1);
        mul_le(pow2(j * 8), pow2(j * 8), input[i + j] as nat, (pow2(8) - 1) as nat);
        assert(pow2(j * 8) * (pow2(8) - 1) == pow2((j + 1) * 8) - pow2(j * 8)) by {
            lemma_mul_is_distributive_sub(pow2(j * 8) as int, pow2(8) as int, 1);
            lemma_pow2_adds(j * 8, 8);
        }

    }
}


pub proof fn load8_rshift3(input: &[u8], i: usize)
    requires
        i + 7 < input.len()
    ensures
        true
{
  assert(true);
}

fn main() {}

}
