#![allow(unused)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

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

pub proof fn mul_le(a1:nat, b1:nat, a2:nat, b2:nat)
    requires
        a1 <= b1,
        a2 <= b2,
    ensures
        a1 * a2 <= b1 * b2,
{
    // a1 < b1 /\ a2 > 0 ==> a1 * a2 < b1 * a2
    lemma_mul_inequality(a1 as int, b1  as int, a2 as int);
    // a2 < b2 /\ b2 > 0 ==> a2 * b1 < b2 * b1
    lemma_mul_inequality(a2 as int, b2 as int, b1 as int);
}

// m(_,_) multiplication is bounded by the product of the individual bounds
pub proof fn lemma_m(x: u64, y: u64, bx: u64, by: u64)
    requires
        x < bx,
        y < by
    ensures
        (x as u128) * (y as u128) < (bx as u128) * (by as u128)
{
    mul_lt(x as nat, bx as nat, y as nat, by as nat);
}

pub proof fn mul_5_terms(n: int, x1: int, x2: int, x3: int, x4: int, x5: int)
    ensures
        n * (x1 + x2 + x3 + x4 + x5) == n * x1 + n * x2 + n * x3 + n * x4 + n * x5
{
    // N * ((((x0 + x1) + x2) + x3) + x4) = N * (((x0 + x1) + x2) + x3) + N * x4
    lemma_mul_is_distributive_add(n, x1 + x2 + x3 + x4, x5);
    // N * (((x0 + x1) + x2) + x3) = N * ((x0 + x1) + x2) + N * x3
    lemma_mul_is_distributive_add(n, x1 + x2 + x3, x4);
    // N * ((x0 + x1) + x2) = N * (x0 + x1) + N * x2
    lemma_mul_is_distributive_add(n, x1 + x2, x3);
    // N * (x0 + x1) = N * x0 + N * x1
    lemma_mul_is_distributive_add(n, x1, x2);
}

pub proof fn mul_5_terms_other_way(n: int, x1: int, x2: int, x3: int, x4: int, x5: int)
    ensures
        (x1 + x2 + x3 + x4 + x5) * n == x1 * n + x2 * n + x3 * n + x4 * n + x5 * n
{
    // N * ((((x0 + x1) + x2) + x3) + x4) = N * (((x0 + x1) + x2) + x3) + N * x4
    lemma_mul_is_distributive_add_other_way(n, x1 + x2 + x3 + x4, x5);
    // N * (((x0 + x1) + x2) + x3) = N * ((x0 + x1) + x2) + N * x3
    lemma_mul_is_distributive_add_other_way(n, x1 + x2 + x3, x4);
    // N * ((x0 + x1) + x2) = N * (x0 + x1) + N * x2
    lemma_mul_is_distributive_add_other_way(n, x1 + x2, x3);
    // N * (x0 + x1) = N * x0 + N * x1
    lemma_mul_is_distributive_add_other_way(n, x1, x2);
}

pub proof fn mul_v0_and_reorder(
    v0: int,
    s1: int, v1: int,
    s2: int, v2: int,
    s3: int, v3: int,
    s4: int, v4: int
)
    ensures
        v0 * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) ==
        s4 * (v0 * v4) +
        s3 * (v0 * v3) +
        s2 * (v0 * v2) +
        s1 * (v0 * v1) +
             (v0 * v0)
{
    mul_5_terms(
        v0,
        v0,
        s1 * v1,
        s2 * v2,
        s3 * v3,
        s4 * v4
    );

    lemma_mul_is_associative(v0, v1, s1);
    lemma_mul_is_associative(v0, v2, s2);
    lemma_mul_is_associative(v0, v3, s3);
    lemma_mul_is_associative(v0, v4, s4);
}

pub proof fn mul_quad_prod(a1: int, b1: int, a2: int, b2: int)
    ensures
        (a1 * b1) * (a2 * b2) == (a1 * a2) * (b1 * b2)
{
    // commutativity is baked-in

    // (a1 * b1) * (a2 * b2) =  ((a1 * b1) * a2) * b2
    lemma_mul_is_associative(a1 * b1, a2, b2);
    // (a1 * b1) * a2 = a2 * (a1 * b1) = (a2 * a1) * b1
    lemma_mul_is_associative(a2, a1, b1);
    // ((a2 * a1) * b1) * b2 = (a2 * a1) * (b1 * b2)
    lemma_mul_is_associative(a2 * a1, b1, b2);
}

pub proof fn mul_si_vi_and_reorder(
    si: int, vi: int,
    v0: int,
    s1: int, v1: int,
    s2: int, v2: int,
    s3: int, v3: int,
    s4: int, v4: int
)
    ensures
        (si * vi) * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4) ==
        (si     ) * (vi * v0) +
        (si * s1) * (vi * v1) +
        (si * s2) * (vi * v2) +
        (si * s3) * (vi * v3) +
        (si * s4) * (vi * v4)
{
    // n * (x1 + x2 + x3 + x4 + x5) == n * x1 + n * x2 + n * x3 + n * x4 + n * x5
    mul_5_terms(
        si * vi,
        v0,
        s1 * v1,
        s2 * v2,
        s3 * v3,
        s4 * v4
    );

    assert(
        (si * vi) * (v0 + s1 * v1 + s2 * v2 + s3 * v3 + s4 * v4)
        ==
        (si * vi) * v0 +
        (si * vi) * (s1 * v1) +
        (si * vi) * (s2 * v2) +
        (si * vi) * (s3 * v3) +
        (si * vi) * (s4 * v4)
    );

    lemma_mul_is_associative(si, vi, v0);
    mul_quad_prod(si, vi, s1, v1);
    mul_quad_prod(si, vi, s2, v2);
    mul_quad_prod(si, vi, s3, v3);
    mul_quad_prod(si, vi, s4, v4);
}

fn main() {}
}
