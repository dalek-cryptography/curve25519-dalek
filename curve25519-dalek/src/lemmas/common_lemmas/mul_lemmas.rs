#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// Auxiliary lemma for multiplication (of nat!)
pub proof fn lemma_mul_lt(a1: nat, b1: nat, a2: nat, b2: nat)
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
    } else {
        // a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2
        lemma_mul_strict_inequality(a1 as int, b1 as int, a2 as int);
        // a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1
        lemma_mul_strict_inequality(a2 as int, b2 as int, b1 as int);
    }
}

pub proof fn lemma_mul_le(a1: nat, b1: nat, a2: nat, b2: nat)
    requires
        a1 <= b1,
        a2 <= b2,
    ensures
        a1 * a2 <= b1 * b2,
{
    // a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2
    lemma_mul_inequality(a1 as int, b1 as int, a2 as int);
    // a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1
    lemma_mul_inequality(a2 as int, b2 as int, b1 as int);
}

// m(_,_) multiplication is bounded by the product of the individual bounds
pub proof fn lemma_m(x: u64, y: u64, bx: u64, by: u64)
    requires
        x < bx,
        y < by,
    ensures
        (x as u128) * (y as u128) < (bx as u128) * (by as u128),
{
    lemma_mul_lt(x as nat, bx as nat, y as nat, by as nat);
}

pub proof fn lemma_mul_distributive_3_terms(n: int, x1: int, x2: int, x3: int)
    ensures
        n * (x1 + x2 + x3) == (x1 + x2 + x3) * n == n * x1 + n * x2 + n * x3,
{
    assert(n * (x1 + x2 + x3) == (x1 + x2 + x3) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3);
    }

    assert(n * (x1 + x2 + x3) == n * (x1 + x2) + n * x3) by {
        lemma_mul_is_distributive_add(n, x1 + x2, x3);
    }

    assert(n * (x1 + x2) == n * x1 + n * x2) by {
        lemma_mul_is_distributive_add(n, x1, x2);
    }
}

pub proof fn lemma_mul_distributive_4_terms(n: int, x1: int, x2: int, x3: int, x4: int)
    ensures
        n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n == n * x1 + n * x2 + n * x3 + n * x4,
{
    assert(n * (x1 + x2 + x3 + x4) == (x1 + x2 + x3 + x4) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4);
    }

    assert(n * (x1 + x2 + x3 + x4) == n * (x1 + x2 + x3) + n * x4) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3, x4);
    }

    assert(n * (x1 + x2 + x3) == n * x1 + n * x2 + n * x3) by {
        lemma_mul_distributive_3_terms(n, x1, x2, x3);
    }
}

pub proof fn lemma_mul_distributive_5_terms(n: int, x1: int, x2: int, x3: int, x4: int, x5: int)
    ensures
        n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n == n * x1 + n * x2 + n * x3 + n
            * x4 + n * x5,
{
    assert(n * (x1 + x2 + x3 + x4 + x5) == (x1 + x2 + x3 + x4 + x5) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5) == n * (x1 + x2 + x3 + x4) + n * x5) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4, x5);
    }

    assert(n * (x1 + x2 + x3 + x4) == n * x1 + n * x2 + n * x3 + n * x4) by {
        lemma_mul_distributive_4_terms(n, x1, x2, x3, x4);
    }
}

pub proof fn lemma_mul_distributive_6_terms(
    n: int,
    x1: int,
    x2: int,
    x3: int,
    x4: int,
    x5: int,
    x6: int,
)
    ensures
        n * (x1 + x2 + x3 + x4 + x5 + x6) == (x1 + x2 + x3 + x4 + x5 + x6) * n == n * x1 + n * x2
            + n * x3 + n * x4 + n * x5 + n * x6,
{
    assert(n * (x1 + x2 + x3 + x4 + x5 + x6) == (x1 + x2 + x3 + x4 + x5 + x6) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5 + x6);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5 + x6) == n * (x1 + x2 + x3 + x4 + x5) + n * x6) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4 + x5, x6);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5) == n * x1 + n * x2 + n * x3 + n * x4 + n * x5) by {
        lemma_mul_distributive_5_terms(n, x1, x2, x3, x4, x5);
    }
}

pub proof fn lemma_mul_distributive_7_terms(
    n: int,
    x1: int,
    x2: int,
    x3: int,
    x4: int,
    x5: int,
    x6: int,
    x7: int,
)
    ensures
        n * (x1 + x2 + x3 + x4 + x5 + x6 + x7) == (x1 + x2 + x3 + x4 + x5 + x6 + x7) * n == n * x1
            + n * x2 + n * x3 + n * x4 + n * x5 + n * x6 + n * x7,
{
    assert(n * (x1 + x2 + x3 + x4 + x5 + x6 + x7) == (x1 + x2 + x3 + x4 + x5 + x6 + x7) * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5 + x6 + x7);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5 + x6 + x7) == n * (x1 + x2 + x3 + x4 + x5 + x6) + n * x7)
        by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4 + x5 + x6, x7);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5 + x6) == n * x1 + n * x2 + n * x3 + n * x4 + n * x5 + n * x6)
        by {
        lemma_mul_distributive_6_terms(n, x1, x2, x3, x4, x5, x6);
    }
}

pub proof fn lemma_mul_distributive_8_terms(
    n: int,
    x1: int,
    x2: int,
    x3: int,
    x4: int,
    x5: int,
    x6: int,
    x7: int,
    x8: int,
)
    ensures
        n * (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) == (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) * n
            == n * x1 + n * x2 + n * x3 + n * x4 + n * x5 + n * x6 + n * x7 + n * x8,
{
    assert(n * (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) == (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8)
        * n) by {
        lemma_mul_is_commutative(n, x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) == n * (x1 + x2 + x3 + x4 + x5 + x6 + x7) + n
        * x8) by {
        lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4 + x5 + x6 + x7, x8);
    }

    assert(n * (x1 + x2 + x3 + x4 + x5 + x6 + x7) == n * x1 + n * x2 + n * x3 + n * x4 + n * x5 + n
        * x6 + n * x7) by {
        lemma_mul_distributive_7_terms(n, x1, x2, x3, x4, x5, x6, x7);
    }
}

pub proof fn lemma_mul_quad_prod(a1: int, b1: int, a2: int, b2: int)
    ensures
        (a1 * b1) * (a2 * b2) == (a1 * a2) * (b1 * b2),
{
    // commutativity is baked-in
    // (a1 * b1) * (a2 * b2) =  ((a1 * b1) * a2) * b2
    lemma_mul_is_associative(a1 * b1, a2, b2);
    // (a1 * b1) * a2 = a2 * (a1 * b1) = (a2 * a1) * b1
    lemma_mul_is_associative(a2, a1, b1);
    // ((a2 * a1) * b1) * b2 = (a2 * a1) * (b1 * b2)
    lemma_mul_is_associative(a2 * a1, b1, b2);
}

pub proof fn lemma_mul_commutative_8_terms(
    a0: int,
    b0: int,
    a1: int,
    b1: int,
    a2: int,
    b2: int,
    a3: int,
    b3: int,
    a4: int,
    b4: int,
    a5: int,
    b5: int,
    a6: int,
    b6: int,
    a7: int,
    b7: int,
)
    ensures
        a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 + a5 * b5 + a6 * b6 + a7 * b7 == b0 * a0
            + b1 * a1 + b2 * a2 + b3 * a3 + b4 * a4 + b5 * a5 + b6 * a6 + b7 * a7,
{
    lemma_mul_is_commutative(a0, b0);
    lemma_mul_is_commutative(a1, b1);
    lemma_mul_is_commutative(a2, b2);
    lemma_mul_is_commutative(a3, b3);
    lemma_mul_is_commutative(a4, b4);
    lemma_mul_is_commutative(a5, b5);
    lemma_mul_is_commutative(a6, b6);
    lemma_mul_is_commutative(a7, b7);
}

} // verus!
