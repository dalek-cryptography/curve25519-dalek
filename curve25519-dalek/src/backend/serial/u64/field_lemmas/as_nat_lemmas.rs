#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_verus::div_mod_lemmas::*;
use super::super::common_verus::mul_lemmas::*;
use super::super::common_verus::pow_lemmas::*;
use super::field_core::*;

verus! {

// Lemma: If a > b pointwise, then as_nat(a - b) = as_nat(a) - as_nat(b)
pub proof fn lemma_as_nat_sub(a: [u64;5], b: [u64;5])
    requires
        forall |i:int| 0 <= i < 5 ==> b[i] <= a[i]
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
        lemma_mul_is_distributive_sub(pow2(1 * 51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_sub(pow2(2 * 51) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_sub(pow2(3 * 51) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_sub(pow2(4 * 51) as int, a[4] as int, b[4] as int);
    }
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
    assert(s2 * s2 == s4) by {
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
        // (x1 + x2 + x3 + x4 + x5) * n == x1 * n + x2 * n + x3 * n + x4 * n + x5 * n
        mul_5_terms(
            as_nat(v) as int,
            v0 as int,
            s1 * v1,
            s2 * v2,
            s3 * v3,
            s4 * v4
        );
    }

    // because of the sheer number of possible associativity/distributivity groupings we have
    // to help the solver along by intermittently asserting chunks
    assert(v0 * as_nat(v) ==
        s4 * (v0 * v4) +
        s3 * (v0 * v3) +
        s2 * (v0 * v2) +
        s1 * (v0 * v1) +
        v0 * v0
    ) by {
        mul_v0_and_reorder(
            v0 as int,
            s1 as int, v1 as int,
            s2 as int, v2 as int,
            s3 as int, v3 as int,
            s4 as int, v4 as int
        );
    }

    assert((s1 * v1) * as_nat(v) ==
        s5 * (v1 * v4) +
        s4 * (v1 * v3) +
        s3 * (v1 * v2) +
        s2 * (v1 * v1) +
        s1 * (v0 * v1)
    ) by {
        mul_si_vi_and_reorder(
            s1 as int, v1 as int,
            v0 as int,
            s1 as int, v1 as int,
            s2 as int, v2 as int,
            s3 as int, v3 as int,
            s4 as int, v4 as int
        )
    }

    assert((s2 * v2) * as_nat(v) ==
        s6 * (v2 * v4) +
        s5 * (v2 * v3) +
        s4 * (v2 * v2) +
        s3 * (v1 * v2) +
        s2 * (v0 * v2)
    ) by {
        mul_si_vi_and_reorder(
            s2 as int, v2 as int,
            v0 as int,
            s1 as int, v1 as int,
            s2 as int, v2 as int,
            s3 as int, v3 as int,
            s4 as int, v4 as int
        )
    }

    assert((s3 * v3) * as_nat(v) ==
        s7 * (v3 * v4) +
        s6 * (v3 * v3) +
        s5 * (v2 * v3) +
        s4 * (v1 * v3) +
        s3 * (v0 * v3)
    ) by {
        mul_si_vi_and_reorder(
            s3 as int, v3 as int,
            v0 as int,
            s1 as int, v1 as int,
            s2 as int, v2 as int,
            s3 as int, v3 as int,
            s4 as int, v4 as int
        )
    }

    assert((s4 * v4) * as_nat(v) ==
        s8 * (v4 * v4) +
        s7 * (v3 * v4) +
        s6 * (v2 * v4) +
        s5 * (v1 * v4) +
        s4 * (v0 * v4)
    ) by {
        mul_si_vi_and_reorder(
            s4 as int, v4 as int,
            v0 as int,
            s1 as int, v1 as int,
            s2 as int, v2 as int,
            s3 as int, v3 as int,
            s4 as int, v4 as int
        )
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
        // These assert(a + a = 2a) statements aren't strictly necessary, but they improve the solve time

        // s1 terms
        assert(
            s1 * (v0 * v1) + s1 * (v0 * v1)
            ==
            s1 * (2 * (v0 * v1))
        ) by {
            assert(v0 * v1 + v0 * v1 == 2 * (v0 * v1));
            lemma_mul_is_distributive_add(s1 as int, v0 * v1, v0 * v1);
        }

        // s2 terms
        assert(
            s2 * (v0 * v2) + s2 * (v1 * v1) + s2 * (v0 * v2)
            ==
            s2 * (v1 * v1 + 2 * (v0 * v2))
        ) by {
            assert(v0 * v2 + v0 * v2 == 2 * (v0 * v2));
            lemma_mul_is_distributive_add(s2 as int, v0 * v2, v0 * v2);
            lemma_mul_is_distributive_add(s2 as int, 2 * (v0 * v2), v1 * v1);
        }

        // s3 terms
        assert(
            s3 * (v0 * v3) + s3 * (v1 * v2) + s3 * (v1 * v2) + s3 * (v0 * v3)
            ==
            s3 * (2 * (v1 * v2) + 2 * (v0 * v3))
        ) by {
            assert(v1 * v2 + v1 * v2 == 2 * (v1 * v2));
            assert(v0 * v3 + v0 * v3 == 2 * (v0 * v3));
            lemma_mul_is_distributive_add(s3 as int, v1 * v2, v1 * v2);
            lemma_mul_is_distributive_add(s3 as int, v0 * v3, v0 * v3);
            lemma_mul_is_distributive_add(s3 as int, 2 * (v1 * v2), 2 * (v0 * v3));
        }

        // s4 terms
        assert(
            s4 * (v0 * v4) + s4 * (v1 * v3) + s4 * (v2 * v2) + s4 * (v1 * v3) + s4 * (v0 * v4)
            ==
            s4 * (v2 * v2 + 2 * (v1 * v3) + 2 * (v0 * v4))
        ) by {
            assert(v0 * v4 + v0 * v4 == 2 * (v0 * v4));
            assert(v1 * v3 + v1 * v3 == 2 * (v1 * v3));
            lemma_mul_is_distributive_add(s4 as int, v0 * v4, v0 * v4);
            lemma_mul_is_distributive_add(s4 as int, v1 * v3, v1 * v3);
            lemma_mul_is_distributive_add(s4 as int, v2 * v2, 2 * (v1 * v3));
            lemma_mul_is_distributive_add(s4 as int, v2 * v2 + 2 * (v1 * v3), 2 * (v0 * v4));
        }

        // s5 terms
        assert(
            s5 * (v1 * v4) + s5 * (v2 * v3) + s5 * (v2 * v3) + s5 * (v1 * v4)
            ==
            s5 * (2 * (v2 * v3) + 2 * (v1 * v4))
        ) by {
            assert(v1 * v4 + v1 * v4 == 2 * (v1 * v4));
            assert(v2 * v3 + v2 * v3 == 2 * (v2 * v3));
            lemma_mul_is_distributive_add(s5 as int, v1 * v4, v1 * v4);
            lemma_mul_is_distributive_add(s5 as int, v2 * v3, v2 * v3);
            lemma_mul_is_distributive_add(s5 as int, 2 * (v1 * v4), 2 * (v2 * v3));
        }

        // s6 terms
        assert(
            s6 * (v2 * v4) + s6 * (v3 * v3) + s6 * (v2 * v4)
            ==
            s6 * (v3 * v3 + 2 * (v2 * v4))
        ) by {
            assert(v2 * v4 + v2 * v4 == 2 * (v2 * v4));
            lemma_mul_is_distributive_add(s6 as int, v2 * v4, v2 * v4);
            lemma_mul_is_distributive_add(s6 as int, 2 * (v2 * v4), v3 * v3);
        }

        // s7 terms
        assert(
            s7 * (v3 * v4) + s7 * (v3 * v4)
            ==
            s7 * (2 * (v3 * v4))
        ) by {
            assert(v3 * v4 + v3 * v4 == 2 * (v3 * v4));
            lemma_mul_is_distributive_add(s7 as int, v3 * v4, v3 * v4);
        }
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
        // s3 terms
        assert(
            s8 * c3_x19 + s3 * c3_base
            ==
            s3 * (s5 * c3_x19 + c3_base)
        ) by {
            assert(s8 == (s3 * s5)) by {
                lemma_pow2_adds(3 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s3 as int, s5 as int, c3_x19);
            lemma_mul_is_distributive_add(s3 as int, s5 * c3_x19, c3_base)
        }

        // s2 terms
        assert(
            s7 * c2_x19 + s2 * c2_base
            ==
            s2 * (s5 * c2_x19 + c2_base)
        ) by {
            assert(s7 == (s2 * s5)) by {
                lemma_pow2_adds(2 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s2 as int, s5 as int, c2_x19);
            lemma_mul_is_distributive_add(s2 as int, s5 * c2_x19, c2_base)
        }

        // s1 terms
        assert(
            s6 * c1_x19 + s1 * c1_base
            ==
            s1 * (s5 * c1_x19 + c1_base)
        ) by {
            assert(s6 == (s1 * s5)) by {
                lemma_pow2_adds(1 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s1 as int, s5 as int, c1_x19);
            lemma_mul_is_distributive_add(s1 as int, s5 * c1_x19, c1_base)
        }
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
        lemma_mul_is_distributive_add(s3 as int, p() * c3_x19, c3 as int);
        lemma_mul_is_distributive_add(s2 as int, p() * c2_x19, c2 as int);
        lemma_mul_is_distributive_add(s1 as int, p() * c1_x19, c1 as int);

        assert(
            s3 * (p() * c3_x19) + s2 * (p() * c2_x19) + s1 * (p() * c1_x19) + p() * c0_x19
            ==
            p() * ( s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19 )
        ) by {
            lemma_mul_is_associative(s3 as int, c3_x19 as int, p() as int);
            lemma_mul_is_associative(s2 as int, c2_x19 as int, p() as int);
            lemma_mul_is_associative(s1 as int, c1_x19 as int, p() as int);

            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19, s2 * c2_x19);
            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19 + s2 * c2_x19, s1 * c1_x19);
            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19, c0_x19 as int);
        }
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

    assert(as_nat(ka) ==
        k * a[0] +
        k * (pow2( 51) * a[1]) +
        k * (pow2(102) * a[2]) +
        k * (pow2(153) * a[3]) +
        k * (pow2(204) * a[4])
    ) by {
        lemma_mul_is_associative(pow2( 51) as int, a[1] as int, k as int);
        lemma_mul_is_associative(pow2(102) as int, a[2] as int, k as int);
        lemma_mul_is_associative(pow2(153) as int, a[3] as int, k as int);
        lemma_mul_is_associative(pow2(204) as int, a[4] as int, k as int);
    }

    assert(
        k * a[0] +
        k * (pow2( 51) * a[1]) +
        k * (pow2(102) * a[2]) +
        k * (pow2(153) * a[3]) +
        k * (pow2(204) * a[4])
        ==
        k * (
            a[0] +
            (pow2( 51) * a[1]) +
            (pow2(102) * a[2]) +
            (pow2(153) * a[3]) +
            (pow2(204) * a[4])
        )
    ) by {
        lemma_mul_is_distributive_add(k as int, a[0] as int, pow2( 51) * a[1]);
        lemma_mul_is_distributive_add(k as int, a[0] + pow2( 51) * a[1], pow2(102) * a[2]);
        lemma_mul_is_distributive_add(k as int, a[0] + pow2( 51) * a[1] + pow2(102) * a[2], pow2(153) * a[3]);
        lemma_mul_is_distributive_add(k as int, a[0] + pow2( 51) * a[1] + pow2(102) * a[2] + pow2(153) * a[3], (pow2(204) * a[4]));
    }
}

fn main() {}

}
