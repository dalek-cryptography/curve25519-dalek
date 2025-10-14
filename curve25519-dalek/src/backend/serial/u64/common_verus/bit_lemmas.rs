#![allow(unused)]
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

use super::mask_lemmas::*;
use super::pow_lemmas::*;
use super::shift_lemmas::*;

verus! {

pub proof fn bitwise_or_r_zero_is_id(a: u64)
    ensures
        a | 0 == a
{
    assert( a | 0 == a) by (bit_vector);
}

pub proof fn bitwise_or_l_zero_is_id(a: u64)
    ensures
        0 | a == a
{
    assert( 0 | a == a) by (bit_vector);
}


pub proof fn bit_or_is_plus(a: u64, b: u64, k: u64)
    by (bit_vector)
    requires
        b <= (u64::MAX >> k),
        a < 1u64 << k,

    ensures
        a | (b << k) == a + (b << k)
{
}

pub proof fn lemma_bitops(a: u64, b: u64, c: u64)
    requires
        c < 64
    ensures
        (a | b) >> c == (a >> c) | (b >> c),
        (a | b) & (low_bits_mask(c as nat) as u64) == (a & (low_bits_mask(c as nat) as u64)) | (b & (low_bits_mask(c as nat) as u64))
{
    assert(low_bits_mask(c as nat) <= u64::MAX) by {
        low_bits_masks_fit_u64(c as nat);
    }
    assert((a | b) >> c == (a >> c) | (b >> c)) by (bit_vector);
    let lbm = (low_bits_mask(c as nat) as u64);
    assert((a | b) & lbm == (a & lbm) | (b & lbm)) by (bit_vector);
}

pub proof fn lemma_bitops_lifted(a: u64, b: u64, s: nat, k: nat)
    requires
        a < pow2(s),
        a + b * pow2(s) <= u64::MAX,
        s < 64,
        k < 64,
    ensures
        (a + b * pow2(s)) as nat / pow2(k) == (a as nat) / pow2(k) + (b * pow2(s)) as nat / pow2(k),
        (a + b * pow2(s)) as nat % pow2(k) == (a as nat) % pow2(k) + (b * pow2(s)) as nat % pow2(k),
{

    let pk = pow2(k);
    let pk64 = pk as u64;

    let ps = pow2(s);

    let s64 = s as u64;
    let k64 = k as u64;

    let x = a;
    let y = (b * ps) as u64;

    assert(0 < pow2(k) <= u64::MAX) by {
        lemma_pow2_pos(k);
        pow2_le_max64(k);
    }

    assert(b * ps == b << s64) by {
        lemma_u64_shl_is_mul(b, s as u64);
    }

    assert(b <= (u64::MAX >> s64)) by {
        assert(b * ps <= (u64::MAX)); // x + y <= C => y <= C for x,y >= 0
        assert((b << s64) >> s64 <= u64::MAX >> s64) by (bit_vector);
        assert( b == (b << s64) >> s64) by {
            left_right_shift(b, s64, s64);
            shl_zero_is_id(b);
        }
    }

    assert(x < 1u64 << s64) by {
        shift_is_pow2(s);
    }

    assert(x + y == x | y) by {
        bit_or_is_plus(a, b, s64);
    }

    let xory = x | y;
    let lbm = (low_bits_mask(k) as u64);

    assert(
        xory >> k64 == (x >> k64) | (y >> k64)
        &&
        xory & lbm == (x & lbm) | (y & lbm)
    ) by {
        lemma_bitops(x, y, k64);
    }

    assert((a + b * ps) as nat / pk == (a as nat) / pk + (b * ps) as nat / pk) by {
        assert( xory >> k64 == xory / pk64 ) by {
            lemma_u64_shr_is_div(xory, k64);
        }
        assert( x >> k64 == x / pk64 ) by {
            lemma_u64_shr_is_div(x, k64);
        }
        assert( y >> k64 == y / pk64 ) by {
            lemma_u64_shr_is_div(y, k64);
        }

        assert((x / pk64) | (y / pk64) == (x / pk64) + (y / pk64)) by {
            if (s >= k ){
                let d = (s64 - k64) as u64;
                assert(y / pk64 == (b << s64) >> k64);
                assert((b << s64) >> k64 == b << d) by {
                    left_right_shift(b, s64, k64);
                }

                assert(b <= u64::MAX >> d) by {
                    assert(b <= u64::MAX >> s64); // known
                    assert(u64::MAX >> s64 <= u64::MAX >> d) by {
                        shr_nonincreasing(u64::MAX, d as nat, s);
                    }
                }

                assert( x / pk64 < 1u64 << d) by {
                    assert(x < pow2(s)); // known
                    assert(x < pow2(d as nat) * pow2(k)) by {
                        lemma_pow2_adds(d as nat, k);
                    }
                    assert(pow2(k) > 0); // known

                    assert(x as nat / pow2(k) < pow2(d as nat)) by {
                        lemma_multiply_divide_lt(x as int, pow2(k) as int, pow2(d as nat) as int);
                    }

                    assert(pow2(d as nat) == 1u64 << d) by {
                        shift_is_pow2(d as nat);
                    }
                }

                assert((x / pk64) | (b << d) == (x / pk64) + (b << d)) by {
                    bit_or_is_plus(x / pk64, b, d);
                }
            }
            else {
                // s < k
                assert(x /pk64 == 0) by {
                    assert(pow2(s) < pow2(k)) by {
                        lemma_pow2_strictly_increases(s, k);
                    }
                    lemma_basic_div(x as int, pk64 as int);
                }

                assert( 0 | (y / pk64) == (y / pk64)) by {
                    bitwise_or_l_zero_is_id(y / pk64);
                }
            }

        }
    }

    assert((a + b * ps) as nat % pk == (a as nat) % pk + (b * ps) as nat % pk) by {
        assert( xory & lbm == xory % pk64 ) by {
            lemma_u64_low_bits_mask_is_mod(xory, k);
        }
        assert( x & lbm == x % pk64 ) by {
            lemma_u64_low_bits_mask_is_mod(x, k);
        }
        assert( y & lbm == y % pk64 ) by {
            lemma_u64_low_bits_mask_is_mod(y, k);
        }

        assert((x % pk64) | (y % pk64) == (x % pk64) + (y % pk64)) by {
            if (s >= k ){
                let d = (s - k) as nat;
                assert(y % pk64 == 0) by {
                    assert(y == pow2(k) * (b * pow2(d))) by {
                        lemma_pow2_adds(d, k);
                        lemma_mul_is_associative(b as int, pow2(d) as int, pow2(k) as int);
                        lemma_mul_is_commutative((b * pow2(d)) as int, pow2(k) as int);
                    }
                    assert(y as nat % pow2(k) == 0) by {
                        lemma_mod_multiples_basic((b * pow2(d)) as int, pow2(k) as int);
                    }
                }
                assert((x % pk64) | 0 == (x % pk64)) by {
                    bitwise_or_r_zero_is_id(x % pk64);
                }
            }

            else {
                // s < k
                let d = (k - s) as nat;
                let b_n = b as nat;

                assert(pow2(d) > 0) by {
                    lemma_pow2_pos(d);
                }

                assert( x & lbm < 1u64 << s64) by {
                    assert(x & lbm <= x) by (bit_vector);
                }

                assert(y % pk64 == (b_n % pow2(d)) * pow2(s)) by {
                    mask_pow2(b_n, s, k);
                }

                assert(b_n % pow2(d) <= b) by {
                    lemma_mod_decreases(b as nat, pow2(d) as nat);
                }

                assert((x & lbm) | ((b_n % pow2(d)) * pow2(s)) as u64 == (x & lbm) + ((b_n % pow2(d)) * pow2(s))) by {
                    assert(((b_n % pow2(d)) * pow2(s)) == (((b_n % pow2(d)) as u64) << s64)) by {
                        lemma_u64_shl_is_mul((b_n % pow2(d)) as u64, s64);
                    }
                    bit_or_is_plus(x & lbm, (b_n % pow2(d)) as u64, s64);
                }
            }
        }
    }
}

fn main() {}

}
