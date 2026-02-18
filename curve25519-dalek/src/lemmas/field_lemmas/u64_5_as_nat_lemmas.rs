#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

use super::super::common_lemmas::div_mod_lemmas::*;
use super::super::common_lemmas::mul_lemmas::*;
use super::super::common_lemmas::pow_lemmas::*;

use crate::backend::serial::u64::field::FieldElement51;
use crate::specs::field_specs::*;
use crate::specs::field_specs_u64::*;

verus! {

// Lemma: Bridges from u64_5_as_nat postcondition to fe51_as_canonical_nat postcondition for power operations
pub proof fn lemma_bridge_pow_as_nat_to_spec(
    result: &FieldElement51,
    base: &FieldElement51,
    exp: nat,
)
    requires
        u64_5_as_nat(result.limbs) % p() == (pow(u64_5_as_nat(base.limbs) as int, exp) as nat)
            % p(),
    ensures
        fe51_as_canonical_nat(result) == (pow(fe51_as_canonical_nat(base) as int, exp) as nat)
            % p(),
{
    // Prove p() > 0
    pow255_gt_19();

    // By definition: fe51_as_canonical_nat(result) == u64_5_as_nat(result.limbs) % p()
    //                fe51_as_canonical_nat(base) == u64_5_as_nat(base.limbs) % p()
    // The solver should unfold these automatically

    // Apply lemma_pow_mod_noop: pow(b, e) % m == pow(b % m, e) % m
    lemma_pow_mod_noop(u64_5_as_nat(base.limbs) as int, exp, p() as int);

    // Let's use clear names for the key values
    let x = u64_5_as_nat(base.limbs);
    let y = fe51_as_canonical_nat(base);

    // y == x % p() by definition
    assert(y == x % p());

    // From lemma_pow_mod_noop, in int arithmetic:
    // pow(x as int, exp) % (p() as int) == pow((x % p()) as int, exp) % (p() as int)
    assert(pow(x as int, exp) % (p() as int) == pow((x % p()) as int, exp) % (p() as int));

    // Since y == x % p():
    assert(pow(x as int, exp) % (p() as int) == pow(y as int, exp) % (p() as int));

    assert(pow(x as int, exp) >= 0) by {
        lemma_pow_nonnegative(x as int, exp);
    }

    assert(pow(y as int, exp) >= 0) by {
        lemma_pow_nonnegative(y as int, exp);
    }

    // Now we have: pow(x, exp) % p() == pow(y, exp) % p()
    // With type conversions: (pow(x, exp) as nat) % p() == (pow(y, exp) as nat) % p()
    assert((pow(x as int, exp) as nat) % p() == (pow(y as int, exp) as nat) % p());
}

pub proof fn lemma_u64_5_as_nat_add(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> b[i] as nat + a[i] as nat <= u64::MAX,
    ensures
        u64_5_as_nat(
            [
                (a[0] + b[0]) as u64,
                (a[1] + b[1]) as u64,
                (a[2] + b[2]) as u64,
                (a[3] + b[3]) as u64,
                (a[4] + b[4]) as u64,
            ],
        ) == u64_5_as_nat(a) + u64_5_as_nat(b),
{
    let c: [u64; 5] = [
        (a[0] + b[0]) as u64,
        (a[1] + b[1]) as u64,
        (a[2] + b[2]) as u64,
        (a[3] + b[3]) as u64,
        (a[4] + b[4]) as u64,
    ];
    // distribute pow2
    assert(u64_5_as_nat(c) == (a[0] + b[0]) + pow2(51) * a[1] + pow2(51) * b[1] + pow2(102) * a[2]
        + pow2(102) * b[2] + pow2(153) * a[3] + pow2(153) * b[3] + pow2(204) * a[4] + pow2(204)
        * b[4]) by {
        lemma_mul_is_distributive_add(pow2(1 * 51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_add(pow2(2 * 51) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_add(pow2(3 * 51) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_add(pow2(4 * 51) as int, a[4] as int, b[4] as int);
    }
}

// Lemma: If a > b pointwise, then u64_5_as_nat(a - b) = u64_5_as_nat(a) - u64_5_as_nat(b)
pub proof fn lemma_u64_5_as_nat_sub(a: [u64; 5], b: [u64; 5])
    requires
        forall|i: int| 0 <= i < 5 ==> b[i] <= a[i],
    ensures
        u64_5_as_nat(
            [
                (a[0] - b[0]) as u64,
                (a[1] - b[1]) as u64,
                (a[2] - b[2]) as u64,
                (a[3] - b[3]) as u64,
                (a[4] - b[4]) as u64,
            ],
        ) == u64_5_as_nat(a) - u64_5_as_nat(b),
{
    let c: [u64; 5] = [
        (a[0] - b[0]) as u64,
        (a[1] - b[1]) as u64,
        (a[2] - b[2]) as u64,
        (a[3] - b[3]) as u64,
        (a[4] - b[4]) as u64,
    ];
    // distribute pow2
    assert(u64_5_as_nat(c) == (a[0] - b[0]) + pow2(51) * a[1] - pow2(51) * b[1] + pow2(102) * a[2]
        - pow2(102) * b[2] + pow2(153) * a[3] - pow2(153) * b[3] + pow2(204) * a[4] - pow2(204)
        * b[4]) by {
        lemma_mul_is_distributive_sub(pow2(1 * 51) as int, a[1] as int, b[1] as int);
        lemma_mul_is_distributive_sub(pow2(2 * 51) as int, a[2] as int, b[2] as int);
        lemma_mul_is_distributive_sub(pow2(3 * 51) as int, a[3] as int, b[3] as int);
        lemma_mul_is_distributive_sub(pow2(4 * 51) as int, a[4] as int, b[4] as int);
    }
}

pub proof fn lemma_u64_5_as_nat_k(a: [u64; 5], k: u64)
    requires
        forall|i: int| 0 <= i < 5 ==> (k * a[i]) <= u64::MAX,
    ensures
        u64_5_as_nat(
            [
                (k * a[0]) as u64,
                (k * a[1]) as u64,
                (k * a[2]) as u64,
                (k * a[3]) as u64,
                (k * a[4]) as u64,
            ],
        ) == k * u64_5_as_nat(a),
{
    let ka = [
        (k * a[0]) as u64,
        (k * a[1]) as u64,
        (k * a[2]) as u64,
        (k * a[3]) as u64,
        (k * a[4]) as u64,
    ];

    assert(u64_5_as_nat(ka) == k * a[0] + k * (pow2(51) * a[1]) + k * (pow2(102) * a[2]) + k * (
    pow2(153) * a[3]) + k * (pow2(204) * a[4])) by {
        lemma_mul_is_associative(pow2(51) as int, a[1] as int, k as int);
        lemma_mul_is_associative(pow2(102) as int, a[2] as int, k as int);
        lemma_mul_is_associative(pow2(153) as int, a[3] as int, k as int);
        lemma_mul_is_associative(pow2(204) as int, a[4] as int, k as int);
    }

    assert(k * a[0] + k * (pow2(51) * a[1]) + k * (pow2(102) * a[2]) + k * (pow2(153) * a[3]) + k
        * (pow2(204) * a[4]) == k * (a[0] + (pow2(51) * a[1]) + (pow2(102) * a[2]) + (pow2(153)
        * a[3]) + (pow2(204) * a[4]))) by {
        lemma_mul_is_distributive_add(k as int, a[0] as int, pow2(51) * a[1]);
        lemma_mul_is_distributive_add(k as int, a[0] + pow2(51) * a[1], pow2(102) * a[2]);
        lemma_mul_is_distributive_add(
            k as int,
            a[0] + pow2(51) * a[1] + pow2(102) * a[2],
            pow2(153) * a[3],
        );
        lemma_mul_is_distributive_add(
            k as int,
            a[0] + pow2(51) * a[1] + pow2(102) * a[2] + pow2(153) * a[3],
            (pow2(204) * a[4]),
        );
    }
}

#[verusfmt::skip]
pub proof fn lemma_u64_5_as_nat_product(a: [u64; 5], b: [u64; 5])
    ensures
        // Full polynomial expansion
        u64_5_as_nat(a) * u64_5_as_nat(b) ==
            pow2(8 * 51) * (a[4] * b[4]) +
            pow2(7 * 51) * (a[3] * b[4] + a[4] * b[3]) +
            pow2(6 * 51) * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2]) +
            pow2(5 * 51) * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]) +
            pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
            pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]) +
            pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0]) +
            pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0]) +
                           (a[0] * b[0]),
        // Mod-p reduction (using pow2(5*51) = p + 19)
        (u64_5_as_nat(a) * u64_5_as_nat(b)) % p() ==
            (
                pow2(4 * 51) * (a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0]) +
                pow2(3 * 51) * (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0] + 19 * (a[4] * b[4])) +
                pow2(2 * 51) * (a[0] * b[2] + a[1] * b[1] + a[2] * b[0] + 19 * (a[3] * b[4] + a[4] * b[3])) +
                pow2(1 * 51) * (a[0] * b[1] + a[1] * b[0] + 19 * (a[2] * b[4] + a[3] * b[3] + a[4] * b[2])) +
                               (a[0] * b[0] + 19 * (a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1]))
            ) as nat % p(),
{
    let a0 = a[0]; let a1 = a[1]; let a2 = a[2]; let a3 = a[3]; let a4 = a[4];
    let b0 = b[0]; let b1 = b[1]; let b2 = b[2]; let b3 = b[3]; let b4 = b[4];

    let s1 = pow2(1 * 51);
    let s2 = pow2(2 * 51);
    let s3 = pow2(3 * 51);
    let s4 = pow2(4 * 51);
    let s5 = pow2(5 * 51);
    let s6 = pow2(6 * 51);
    let s7 = pow2(7 * 51);
    let s8 = pow2(8 * 51);

    assert(s1 * s1 == s2) by { lemma_pow2_adds(51, 51) }
    assert(s1 * s2 == s2 * s1 == s3) by { lemma_pow2_adds(51, 102) }
    assert(s1 * s3 == s3 * s1 == s4) by { lemma_pow2_adds(51, 153) }
    assert(s1 * s4 == s4 * s1 == s5) by { lemma_pow2_adds(51, 204) }
    assert(s2 * s2 == s4) by { lemma_pow2_adds(102, 102) }
    assert(s2 * s3 == s3 * s2 == s5) by { lemma_pow2_adds(102, 153) }
    assert(s2 * s4 == s4 * s2 == s6) by { lemma_pow2_adds(102, 204) }
    assert(s3 * s3 == s6) by { lemma_pow2_adds(153, 153) }
    assert(s3 * s4 == s4 * s3 == s7) by { lemma_pow2_adds(153, 204) }
    assert(s4 * s4 == s8) by { lemma_pow2_adds(204, 204) }

    // Step 1: Distribute u64_5_as_nat(a) * u64_5_as_nat(b) into 5 rows
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == a0 * u64_5_as_nat(b) + (s1 * a1)
        * u64_5_as_nat(b) + (s2 * a2) * u64_5_as_nat(b) + (s3 * a3) * u64_5_as_nat(b) + (s4
        * a4) * u64_5_as_nat(b)) by {
        lemma_mul_distributive_5_terms(
            u64_5_as_nat(b) as int,
            a0 as int,
            s1 * a1,
            s2 * a2,
            s3 * a3,
            s4 * a4,
        );
    }

    // Step 2: Expand each row
    assert(a0 * u64_5_as_nat(b) == s4 * (a0 * b4) + s3 * (a0 * b3) + s2 * (a0 * b2) + s1 * (a0
        * b1) + a0 * b0) by {
        lemma_mul_w0_and_reorder(
            a0 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s1 * a1) * u64_5_as_nat(b) == s5 * (a1 * b4) + s4 * (a1 * b3) + s3 * (a1 * b2) + s2
        * (a1 * b1) + s1 * (a1 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s1 as int,
            a1 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s2 * a2) * u64_5_as_nat(b) == s6 * (a2 * b4) + s5 * (a2 * b3) + s4 * (a2 * b2) + s3
        * (a2 * b1) + s2 * (a2 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s2 as int,
            a2 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s3 * a3) * u64_5_as_nat(b) == s7 * (a3 * b4) + s6 * (a3 * b3) + s5 * (a3 * b2) + s4
        * (a3 * b1) + s3 * (a3 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s3 as int,
            a3 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    assert((s4 * a4) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a4 * b3) + s6 * (a4 * b2) + s5
        * (a4 * b1) + s4 * (a4 * b0)) by {
        lemma_mul_si_vi_and_reorder(
            s4 as int,
            a4 as int,
            b0 as int,
            s1 as int,
            b1 as int,
            s2 as int,
            b2 as int,
            s3 as int,
            b3 as int,
            s4 as int,
            b4 as int,
        );
    }

    // Step 3: Group by power
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s8 * (a4 * b4) + s7 * (a3 * b4 + a4 * b3) + s6
        * (a2 * b4 + a3 * b3 + a4 * b2) + s5 * (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + s4
        * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0) + s3 * (a0 * b3 + a1 * b2 + a2 * b1
        + a3 * b0) + s2 * (a0 * b2 + a1 * b1 + a2 * b0) + s1 * (a0 * b1 + a1 * b0) + (a0 * b0))
        by {
        // s1 terms
        assert(s1 * (a0 * b1) + s1 * (a1 * b0) == s1 * (a0 * b1 + a1 * b0)) by {
            lemma_mul_is_distributive_add(s1 as int, a0 * b1, a1 * b0);
        }
        // s2 terms
        assert(s2 * (a0 * b2) + s2 * (a1 * b1) + s2 * (a2 * b0) == s2 * (a0 * b2 + a1 * b1 + a2
            * b0)) by {
            lemma_mul_distributive_3_terms(s2 as int, a0 * b2, a1 * b1, a2 * b0);
        }
        // s3 terms
        assert(s3 * (a0 * b3) + s3 * (a1 * b2) + s3 * (a2 * b1) + s3 * (a3 * b0) == s3 * (a0
            * b3 + a1 * b2 + a2 * b1 + a3 * b0)) by {
            lemma_mul_distributive_4_terms(s3 as int, a0 * b3, a1 * b2, a2 * b1, a3 * b0);
        }
        // s4 terms
        assert(s4 * (a0 * b4) + s4 * (a1 * b3) + s4 * (a2 * b2) + s4 * (a3 * b1) + s4 * (a4
            * b0) == s4 * (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)) by {
            lemma_mul_distributive_5_terms(s4 as int, a0 * b4, a1 * b3, a2 * b2, a3 * b1, a4 * b0);
        }
        // s5 terms
        assert(s5 * (a1 * b4) + s5 * (a2 * b3) + s5 * (a3 * b2) + s5 * (a4 * b1) == s5 * (a1
            * b4 + a2 * b3 + a3 * b2 + a4 * b1)) by {
            lemma_mul_distributive_4_terms(s5 as int, a1 * b4, a2 * b3, a3 * b2, a4 * b1);
        }
        // s6 terms
        assert(s6 * (a2 * b4) + s6 * (a3 * b3) + s6 * (a4 * b2) == s6 * (a2 * b4 + a3 * b3 + a4
            * b2)) by {
            lemma_mul_distributive_3_terms(s6 as int, a2 * b4, a3 * b3, a4 * b2);
        }
        // s7 terms
        assert(s7 * (a3 * b4) + s7 * (a4 * b3) == s7 * (a3 * b4 + a4 * b3)) by {
            lemma_mul_is_distributive_add(s7 as int, a3 * b4, a4 * b3);
        }
    }

    // Step 4: Factor out s5 = p + 19 for high-order terms
    pow255_gt_19();
    assert(s5 == (p() + 19));

    let c0_x19 = a[1] * b[4] + a[2] * b[3] + a[3] * b[2] + a[4] * b[1];
    let c1_x19 = a[2] * b[4] + a[3] * b[3] + a[4] * b[2];
    let c2_x19 = a[3] * b[4] + a[4] * b[3];
    let c3_x19 = a[4] * b[4];

    let c0_base = a[0] * b[0];
    let c1_base = a[0] * b[1] + a[1] * b[0];
    let c2_base = a[0] * b[2] + a[1] * b[1] + a[2] * b[0];
    let c3_base = a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0];
    let c4 = a[0] * b[4] + a[1] * b[3] + a[2] * b[2] + a[3] * b[1] + a[4] * b[0];

    let c0 = c0_base + 19 * c0_x19;
    let c1 = c1_base + 19 * c1_x19;
    let c2 = c2_base + 19 * c2_x19;
    let c3 = c3_base + 19 * c3_x19;

    // Group in preparation for the s5 = p+19 substitution
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == s4 * c4 + s3 * (s5 * c3_x19 + c3_base) + s2
        * (s5 * c2_x19 + c2_base) + s1 * (s5 * c1_x19 + c1_base) + (s5 * c0_x19 + c0_base)) by {
        assert(s8 * c3_x19 + s3 * c3_base == s3 * (s5 * c3_x19 + c3_base)) by {
            assert(s8 == (s3 * s5)) by {
                lemma_pow2_adds(3 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s3 as int, s5 as int, c3_x19);
            lemma_mul_is_distributive_add(s3 as int, s5 * c3_x19, c3_base);
        }

        assert(s7 * c2_x19 + s2 * c2_base == s2 * (s5 * c2_x19 + c2_base)) by {
            assert(s7 == (s2 * s5)) by {
                lemma_pow2_adds(2 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s2 as int, s5 as int, c2_x19);
            lemma_mul_is_distributive_add(s2 as int, s5 * c2_x19, c2_base);
        }

        assert(s6 * c1_x19 + s1 * c1_base == s1 * (s5 * c1_x19 + c1_base)) by {
            assert(s6 == (s1 * s5)) by {
                lemma_pow2_adds(1 * 51, 5 * 51);
            }
            lemma_mul_is_associative(s1 as int, s5 as int, c1_x19);
            lemma_mul_is_distributive_add(s1 as int, s5 * c1_x19, c1_base);
        }
    }

    // Step 5: Substitute s5 = p + 19
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

    // Regroup: X * p() + Y
    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19
        + c0_x19) + (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0)) by {
        lemma_mul_is_distributive_add(s3 as int, p() * c3_x19, c3 as int);
        lemma_mul_is_distributive_add(s2 as int, p() * c2_x19, c2 as int);
        lemma_mul_is_distributive_add(s1 as int, p() * c1_x19, c1 as int);

        assert(s3 * (p() * c3_x19) + s2 * (p() * c2_x19) + s1 * (p() * c1_x19) + p() * c0_x19
            == p() * (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19)) by {
            lemma_mul_is_associative(s3 as int, c3_x19 as int, p() as int);
            lemma_mul_is_associative(s2 as int, c2_x19 as int, p() as int);
            lemma_mul_is_associative(s1 as int, c1_x19 as int, p() as int);

            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19, s2 * c2_x19);
            lemma_mul_is_distributive_add(p() as int, s3 * c3_x19 + s2 * c2_x19, s1 * c1_x19);
            lemma_mul_is_distributive_add(
                p() as int,
                s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19,
                c0_x19 as int,
            );
        }
    }

    // Step 6: Take mod p
    let k = (s3 * c3_x19 + s2 * c2_x19 + s1 * c1_x19 + c0_x19);
    let sum = (s4 * c4 + s3 * c3 + s2 * c2 + s1 * c1 + c0);

    assert(u64_5_as_nat(a) * u64_5_as_nat(b) == k * p() + sum);
    assert(k * p() + sum == (k as nat) * p() + (sum as nat));

    assert((u64_5_as_nat(a) * u64_5_as_nat(b)) % p() == ((k as nat) * p() + (sum as nat)) % p());
    assert(((k as nat) * p() + (sum as nat)) % p() == (sum as nat) % p()) by {
        lemma_mod_sum_factor(k as int, sum as int, p() as int);
    }
}

fn main() {
}

} // verus!
