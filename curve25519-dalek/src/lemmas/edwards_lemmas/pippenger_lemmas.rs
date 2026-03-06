//! # Pippenger bucket-method multiscalar multiplication — specs and proofs
//!
//! ## Mathematical background
//!
//! Given n scalars s\_i and n points P\_i on a twisted Edwards curve, compute
//! S = ∑\_{i=0}^{n-1} s\_i · P\_i.
//!
//! Each scalar is written in signed radix-2^w with dc digits d\_{i,j} ∈ \[−2^{w−1}, 2^{w−1}\]:
//! s\_i = ∑\_{j=0}^{dc-1} d\_{i,j} · 2^{w·j}.
//!
//! Swapping summation order:
//! S = ∑\_j 2^{w·j} · C\_j where C\_j = ∑\_i d\_{i,j} · P\_i ("column sum").
//!
//! The outer sum is evaluated by **Horner's rule** (right-to-left):
//! H(j) = 2^w · H(j+1) + C\_j, H(dc) = O ⟹ H(0) = S.
//!
//! Each column sum C\_j is computed by the **bucket method**:
//!
//! 1. Sort points into B = 2^{w−1} buckets by |d\_{i,j}|.
//! 2. Compute WBS = ∑\_{b=0}^{B-1} (b+1) · bucket\[b\] via the
//!    **intermediate-sum trick** (running\_sum), which avoids explicit scalar muls.
//! 3. Prove WBS = C\_j.
//!
//! ## Proof structure
//!
//! The main theorem is `lemma_pippenger_horner_correct`:
//! pippenger\_horner(pts, digs, 0, w, dc) = sum\_of\_scalar\_muls(scalars, points).
//!
//! It is proved by induction on n (number of points), using:
//!
//! - **`lemma_bucket_weighted_sum_equals_column_sum`** (induction on n):
//!   WBS(bucket\[0..B\], B) = C\_j. Each point contributes d·P to exactly one bucket,
//!   and the (b+1)-weighting recovers the signed scalar.
//!
//! - **`lemma_running_sum_equals_weighted`** (induction on B via helper spec):
//!   running\_sum(0, B) = WBS(B). The intermediate-sum trick computes the same
//!   weighted sum, proved by introducing `pippenger_weighted_from(b, B)` and
//!   showing both functions satisfy the same recurrence.
//!
//! - **`lemma_pippenger_single`**: Horner on a single point = signed scalar mul.
//! - **`lemma_pippenger_peel_last`**: Horner over n points = prefix(n−1) + single(n).
//!
//! All proofs are fully mechanised — no `admit()` remains in this module.
#![allow(non_snake_case)]
#![allow(unused_imports)]

use crate::backend::serial::curve_models::ProjectiveNielsPoint;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;

#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::*;

#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_small_mod;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;

use vstd::prelude::*;

verus! {

// =============================================================================
// Spec helpers: derive pts_affine, digits_seqs, dc from runtime arguments
// =============================================================================
// These spec functions extract the abstract mathematical views directly from
// the concrete scalars_points vector, eliminating the need for Ghost parameters
// in function signatures.  Each is the functional equivalent of what was
// previously carried as a Ghost<…> argument.
/// Affine (x, y) coordinates of each point, derived from the ProjectiveNielsPoint.
pub open spec fn sp_points_affine(sp: Seq<([i8; 64], ProjectiveNielsPoint)>) -> Seq<(nat, nat)> {
    Seq::new(sp.len(), |i: int| projective_niels_point_as_affine_edwards(sp[i].1))
}

/// Digit sequences for each scalar, derived from the [i8; 64] arrays.
pub open spec fn sp_digits_seqs(sp: Seq<([i8; 64], ProjectiveNielsPoint)>) -> Seq<Seq<i8>> {
    Seq::new(sp.len(), |i: int| sp[i].0@)
}

/// Number of digit columns, derived from the window width w.
pub open spec fn sp_digit_count(w: nat) -> nat {
    if w < 8 {
        ((256 + w as int - 1) / w as int) as nat
    } else {
        ((256 + w as int - 1) / w as int + 1) as nat
    }
}

// =============================================================================
// Spec: validity of Pippenger input data (scalars_points, pts_affine, digits)
// =============================================================================
/// Bundled validity predicate for the n-tuple of (scalar_digits, NielsPoint)
/// pairs that Pippenger operates on.  For each index k ∈ [0, n):
///
///  - digits are valid radix-2^w with dc digits
///  - the ProjectiveNielsPoint is valid and 54-bounded in all limbs
///  - its affine projection matches pts_affine[k]
///  - pts_affine[k] is canonical (< p)
///  - digits_seqs[k] = scalars_points[k].0.view()
pub open spec fn pippenger_input_valid(
    scalars_points: Seq<([i8; 64], ProjectiveNielsPoint)>,
    pts_affine: Seq<(nat, nat)>,
    digits_seqs: Seq<Seq<i8>>,
    w: nat,
    dc: nat,
) -> bool {
    let n = pts_affine.len() as int;
    &&& scalars_points.len() as int == n
    &&& digits_seqs.len() as int == n
    // Digit validity
    &&& forall|k: int|
        0 <= k < n ==> is_valid_radix_2w(
            &(#[trigger] scalars_points[k]).0,
            w,
            dc,
        )
    // Niels point validity + 54-bounded limbs
    &&& forall|k: int|
        0 <= k < n ==> is_valid_projective_niels_point((#[trigger] scalars_points[k]).1)
    &&& forall|k: int|
        0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points[k]).1.Y_plus_X, 54)
    &&& forall|k: int|
        0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points[k]).1.Y_minus_X, 54)
    &&& forall|k: int| 0 <= k < n ==> fe51_limbs_bounded(&(#[trigger] scalars_points[k]).1.Z, 54)
    &&& forall|k: int|
        0 <= k < n ==> fe51_limbs_bounded(
            &(#[trigger] scalars_points[k]).1.T2d,
            54,
        )
    // Affine correspondence: niels affine == pts_affine
    &&& forall|k: int|
        0 <= k < n ==> projective_niels_point_as_affine_edwards((#[trigger] scalars_points[k]).1)
            == pts_affine[k]
    // pts_affine are canonical
    &&& forall|k: int|
        0 <= k < n ==> (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1
            < p()
    // digits_seqs connection
    &&& forall|k: int| 0 <= k < n ==> (#[trigger] digits_seqs[k]) == scalars_points[k].0@
}

// =============================================================================
// Spec: bucket contents after processing n points at a given column
// =============================================================================
/// Contents of bucket b (0-indexed, representing digit value b+1)
/// after processing the first n points at digit column `col`:
///
///   bucket(b, n) =  ∑_{i : d_{i,col} = b+1}  P_i  −  ∑_{i : d_{i,col} = −(b+1)}  P_i
///
/// Recursive definition (peeling off the last point):
///   bucket(b, 0)  = O
///   bucket(b, n)  = bucket(b, n−1) + P_{n−1}    if d_{n−1,col} = b+1
///                  = bucket(b, n−1) − P_{n−1}    if d_{n−1,col} = −(b+1)
///                  = bucket(b, n−1)               otherwise
pub open spec fn pippenger_bucket_contents(
    points_affine: Seq<(nat, nat)>,
    all_digits: Seq<Seq<i8>>,
    col: int,
    n: int,
    b: int,
) -> (nat, nat)
    decreases n,
{
    if n <= 0 {
        edwards_identity()
    } else {
        let prev = pippenger_bucket_contents(points_affine, all_digits, col, n - 1, b);
        let d = all_digits[n - 1][col] as int;
        let pt = points_affine[n - 1];
        if d == (b + 1) {
            edwards_add(prev.0, prev.1, pt.0, pt.1)
        } else if d == -(b + 1) {
            edwards_sub(prev.0, prev.1, pt.0, pt.1)
        } else {
            prev
        }
    }
}

// =============================================================================
// Spec: weighted sum of buckets (what the intermediate-sum trick computes)
// =============================================================================
/// Weighted bucket sum:
///
///   WBS(B)  =  ∑_{b=0}^{B-1} (b+1) · bucket[b]
///
/// This is the mathematical quantity that Pippenger's bucket method computes
/// via the intermediate-sum trick (see `pippenger_running_sum`).
pub open spec fn pippenger_weighted_bucket_sum(
    buckets_affine: Seq<(nat, nat)>,
    num_buckets: int,
) -> (nat, nat)
    decreases num_buckets,
{
    if num_buckets <= 0 {
        edwards_identity()
    } else {
        let prev = pippenger_weighted_bucket_sum(buckets_affine, num_buckets - 1);
        let bucket = buckets_affine[num_buckets - 1];
        let weighted = edwards_scalar_mul(bucket, num_buckets as nat);
        edwards_add(prev.0, prev.1, weighted.0, weighted.1)
    }
}

// =============================================================================
// Spec: intermediate sum (suffix sum of buckets from b to B-1)
// =============================================================================
/// Intermediate sum — the suffix sum of buckets from index b up to B−1:
///
///   IS(b, B)  =  ∑_{j=b}^{B-1} bucket[j]
///
/// Defined top-down: IS(B−1, B) = bucket[B−1],
/// IS(b, B) = IS(b+1, B) + bucket[b].
pub open spec fn pippenger_intermediate_sum(buckets_affine: Seq<(nat, nat)>, b: int, B: int) -> (
    nat,
    nat,
)
    decreases B - b,
{
    if b >= B {
        edwards_identity()
    } else if b == B - 1 {
        buckets_affine[b]
    } else {
        let next = pippenger_intermediate_sum(buckets_affine, b + 1, B);
        edwards_add(next.0, next.1, buckets_affine[b].0, buckets_affine[b].1)
    }
}

// =============================================================================
// Spec: running sum of intermediate sums (the output of the bucket sum trick)
// =============================================================================
/// Running sum — the cumulative sum of intermediate sums:
///
///   RS(b, B)  =  ∑_{k=b}^{B-1} IS(k, B)
///
/// Defined by: RS(B−1, B) = bucket[B−1],
/// RS(b, B) = RS(b+1, B) + IS(b, B).
///
/// The key identity proved in this module is:  RS(0, B) = WBS(B).
pub open spec fn pippenger_running_sum(buckets_affine: Seq<(nat, nat)>, b: int, B: int) -> (
    nat,
    nat,
)
    decreases B - b,
{
    if b >= B {
        edwards_identity()
    } else if b == B - 1 {
        buckets_affine[b]
    } else {
        let rest = pippenger_running_sum(buckets_affine, b + 1, B);
        let inter = pippenger_intermediate_sum(buckets_affine, b, B);
        edwards_add(rest.0, rest.1, inter.0, inter.1)
    }
}

// =============================================================================
// Spec: Pippenger Horner accumulator (generalized from straus_ct_partial)
// =============================================================================
/// Horner accumulation over digit columns with window size w:
///
///   H(j)  =  2^w · H(j+1) + C_j,      H(dc) = O
///
/// where C_j = straus_column_sum(pts, digs, j, n) = ∑_i d_{i,j} · P_i.
///
/// At j = 0:  H(0) = ∑_{j=0}^{dc-1} 2^{w·j} · C_j = ∑_i s_i · P_i.
#[verifier::opaque]
pub open spec fn pippenger_horner(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    from_col: int,
    w: nat,
    digits_count: nat,
) -> (nat, nat)
    decreases digits_count as int - from_col,
{
    if from_col >= digits_count as int {
        edwards_identity()
    } else {
        let prev = pippenger_horner(points_affine, digits, from_col + 1, w, digits_count);
        let scaled = edwards_scalar_mul(prev, pow2(w));
        let col = straus_column_sum(points_affine, digits, from_col, points_affine.len() as int);
        edwards_add(scaled.0, scaled.1, col.0, col.1)
    }
}

// =============================================================================
// Lemma: Zero-points Horner is identity
// =============================================================================
/// When n = 0 (no points):  H(j) = O for all j.
pub proof fn lemma_pippenger_zero_points_from(
    pts: Seq<(nat, nat)>,
    digs: Seq<Seq<i8>>,
    j: int,
    w: nat,
    digits_count: nat,
)
    requires
        pts.len() == 0,
        digs.len() == 0,
        0 <= j <= digits_count as int,
    ensures
        pippenger_horner(pts, digs, j, w, digits_count) == edwards_identity(),
    decreases digits_count as int - j,
{
    reveal(pippenger_horner);
    if j >= digits_count as int {
    } else {
        assert(pippenger_horner(pts, digs, j + 1, w, digits_count) == edwards_identity()) by {
            lemma_pippenger_zero_points_from(pts, digs, j + 1, w, digits_count);
        }
        assert(edwards_scalar_mul(edwards_identity(), pow2(w)) == edwards_identity()) by {
            lemma_edwards_scalar_mul_identity(pow2(w));
        }
        let id = edwards_identity();
        assert(edwards_add(id.0, id.1, 0, 1) == id) by {
            p_gt_2();
            lemma_edwards_add_identity_right_canonical(id);
        }
    }
}

// =============================================================================
// Lemma: Single-point Horner = [reconstruct_radix_2w_from(d, w, j, dc)] * P
// =============================================================================
/// For a single point P with digit sequence d:
///
///   H({P}, {d}, j)  =  [r(d, w, j, dc)]_± · P
///
/// where r(d, w, j, dc) = ∑_{k=j}^{dc-1} d[k] · 2^{w·(k−j)} is the
/// signed scalar reconstructed from digits j onward.
/// Proof by induction on dc − j, using the Horner recurrence.
pub proof fn lemma_pippenger_single(P: (nat, nat), d: Seq<i8>, j: int, w: nat, digits_count: nat)
    requires
        d.len() >= digits_count as int,
        P.0 < p(),
        P.1 < p(),
        0 <= j <= digits_count as int,
        w >= 1,
    ensures
        pippenger_horner(seq![(P)], seq![(d)], j, w, digits_count) == edwards_scalar_mul_signed(
            P,
            reconstruct_radix_2w_from(d, w, j, digits_count),
        ),
    decreases digits_count as int - j,
{
    reveal(pippenger_horner);
    if j >= digits_count as int {
        // reconstruct_radix_2w_from(d, w, dc, dc) == 0
        // edwards_scalar_mul_signed(P, 0) == identity
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        // IH: pippenger_horner(seq![P], seq![d], j+1, w, dc) == [reconstruct_from(d, w, j+1, dc)]*P
        lemma_pippenger_single(P, d, j + 1, w, digits_count);
        let r_next = reconstruct_radix_2w_from(d, w, j + 1, digits_count);

        // [pow2(w)] * [r_next]*P == [pow2(w) * r_next]*P
        assert(edwards_scalar_mul(edwards_scalar_mul_signed(P, r_next), pow2(w))
            == edwards_scalar_mul_signed(P, r_next * (pow2(w) as int))) by {
            lemma_edwards_scalar_mul_signed_composition(P, r_next, pow2(w));
        }

        // column_sum(seq![P], seq![d], j, 1) == [d[j]]*P
        assert(straus_column_sum(seq![(P)], seq![(d)], j, 1) == edwards_scalar_mul_signed(
            P,
            d[j] as int,
        )) by {
            lemma_column_sum_single(P, d, j);
        }

        // [pow2(w)*r_next]*P + [d[j]]*P == [pow2(w)*r_next + d[j]]*P
        assert({
            let pa = edwards_scalar_mul_signed(P, pow2(w) as int * r_next);
            let pb = edwards_scalar_mul_signed(P, d[j] as int);
            edwards_add(pa.0, pa.1, pb.0, pb.1)
        } == edwards_scalar_mul_signed(P, pow2(w) as int * r_next + d[j] as int)) by {
            axiom_edwards_scalar_mul_signed_additive(P, pow2(w) as int * r_next, d[j] as int);
        }

        // pow2(w)*r_next + d[j] == reconstruct_radix_2w_from(d, w, j, dc)
        assert(d[j] as int + pow2(w) as int * r_next == reconstruct_radix_2w_from(
            d,
            w,
            j,
            digits_count,
        ));
    }
}

// =============================================================================
// Lemma: Pippenger peel-last (splitting off the last point)
// =============================================================================
/// Linearity of Horner in the point set:
///
///   H(pts[0..n], j)  =  H(pts[0..n−1], j)  +  H({pts[n−1]}, j)
///
/// Proof by induction on dc − j, using distributivity of scalar mul and
/// four-way reassociation of addition.
pub proof fn lemma_pippenger_peel_last(
    pts: Seq<(nat, nat)>,
    digs: Seq<Seq<i8>>,
    j: int,
    w: nat,
    digits_count: nat,
)
    requires
        pts.len() >= 1,
        digs.len() == pts.len(),
        0 <= j <= digits_count as int,
        forall|k: int| 0 <= k < digs.len() ==> (#[trigger] digs[k]).len() >= digits_count as int,
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        pippenger_horner(pts, digs, j, w, digits_count) == ({
            let prefix_result = pippenger_horner(
                pts.drop_last(),
                digs.drop_last(),
                j,
                w,
                digits_count,
            );
            let single_result = pippenger_horner(
                seq![(pts.last())],
                seq![(digs.last())],
                j,
                w,
                digits_count,
            );
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases digits_count as int - j,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let digs_prefix = digs.drop_last();
    let pts_single = seq![(pts.last())];
    let digs_single = seq![(digs.last())];

    reveal(pippenger_horner);
    if j >= digits_count as int {
        // Base case: all three terms are identity
        assert(edwards_add(
            edwards_identity().0,
            edwards_identity().1,
            edwards_identity().0,
            edwards_identity().1,
        ) == edwards_identity()) by {
            p_gt_2();
            lemma_edwards_add_identity_right_canonical(edwards_identity());
        }
    } else {
        let prev_full = pippenger_horner(pts, digs, j + 1, w, digits_count);
        let prev_prefix = pippenger_horner(pts_prefix, digs_prefix, j + 1, w, digits_count);
        let prev_single = pippenger_horner(pts_single, digs_single, j + 1, w, digits_count);
        let scaled_prefix = edwards_scalar_mul(prev_prefix, pow2(w));
        let scaled_single = edwards_scalar_mul(prev_single, pow2(w));
        let col_full = straus_column_sum(pts, digs, j, n);
        let col_prefix = straus_column_sum(pts_prefix, digs_prefix, j, (n - 1));
        let col_single = straus_column_sum(pts_single, digs_single, j, 1);

        // IH at j+1
        assert(prev_full == edwards_add(prev_prefix.0, prev_prefix.1, prev_single.0, prev_single.1))
            by {
            lemma_pippenger_peel_last(pts, digs, j + 1, w, digits_count);
        }
        // [pow2(w)] distributes over addition
        assert(edwards_scalar_mul(
            edwards_add(prev_prefix.0, prev_prefix.1, prev_single.0, prev_single.1),
            pow2(w),
        ) == edwards_add(scaled_prefix.0, scaled_prefix.1, scaled_single.0, scaled_single.1)) by {
            axiom_edwards_scalar_mul_distributive(prev_prefix, prev_single, pow2(w));
        }
        // Column sum splitting
        assert(straus_column_sum(pts, digs, j, n - 1) == col_prefix) by {
            lemma_column_sum_prefix_eq(pts, digs, pts_prefix, digs_prefix, j, n - 1);
        }
        assert(col_single == edwards_scalar_mul_signed(pts.last(), digs.last()[j] as int)) by {
            lemma_column_sum_single(pts.last(), digs.last(), j);
        }

        // Four-way reassociation: (A+B) + (C+D) = (A+C) + (B+D)
        let a = scaled_prefix;
        let b = scaled_single;
        let c = col_prefix;
        let d_val = col_single;
        let ab = edwards_add(a.0, a.1, b.0, b.1);
        let cd = edwards_add(c.0, c.1, d_val.0, d_val.1);
        let bd = edwards_add(b.0, b.1, d_val.0, d_val.1);
        let ac = edwards_add(a.0, a.1, c.0, c.1);

        assert(edwards_add(ab.0, ab.1, cd.0, cd.1) == edwards_add(ac.0, ac.1, bd.0, bd.1)) by {
            axiom_edwards_add_associative(a.0, a.1, b.0, b.1, cd.0, cd.1);
            axiom_edwards_add_associative(b.0, b.1, c.0, c.1, d_val.0, d_val.1);
            lemma_edwards_add_commutative(b.0, b.1, c.0, c.1);
            axiom_edwards_add_associative(c.0, c.1, b.0, b.1, d_val.0, d_val.1);
            axiom_edwards_add_associative(a.0, a.1, c.0, c.1, bd.0, bd.1);
        }
    }
}

// =============================================================================
// Lemma: reconstruct_radix_2w_from(d, w, 0, dc) == reconstruct_radix_2w(d.take(dc), w)
// =============================================================================
/// The "from" reconstruction starting at column 0 equals the standard
/// reconstruction on the truncated digit sequence: r(d, w, 0, dc) = R(d[0..dc], w).
pub proof fn lemma_reconstruct_radix_2w_from_equals_reconstruct(
    d: Seq<i8>,
    w: nat,
    digits_count: nat,
)
    requires
        d.len() >= digits_count as int,
    ensures
        reconstruct_radix_2w_from(d, w, 0, digits_count) == reconstruct_radix_2w(
            d.take(digits_count as int),
            w,
        ),
{
    assert(reconstruct_radix_2w_from(d, w, 0, digits_count) == reconstruct_radix_2w(
        d.subrange(0, digits_count as int),
        w,
    )) by {
        lemma_reconstruct_radix_2w_from_eq_helper(d, w, 0, digits_count);
    }
    assert(d.subrange(0, digits_count as int) =~= d.take(digits_count as int));
}

proof fn lemma_reconstruct_radix_2w_from_eq_helper(d: Seq<i8>, w: nat, k: int, digits_count: nat)
    requires
        d.len() >= digits_count as int,
        0 <= k <= digits_count as int,
    ensures
        reconstruct_radix_2w_from(d, w, k, digits_count) == reconstruct_radix_2w(
            d.subrange(k, digits_count as int),
            w,
        ),
    decreases digits_count as int - k,
{
    let sub = d.subrange(k, digits_count as int);
    if k >= digits_count as int {
    } else {
        lemma_reconstruct_radix_2w_from_eq_helper(d, w, k + 1, digits_count);
        let sub_next = d.subrange(k + 1, digits_count as int);
        assert forall|i: int| 0 <= i < sub.skip(1).len() implies #[trigger] sub.skip(1)[i]
            == sub_next[i] by {}
        assert(sub.skip(1) =~= sub_next);
    }
}

// =============================================================================
// Main Pippenger correctness theorem
// =============================================================================
/// The Pippenger Horner evaluation equals the multiscalar product:
///
///   H(pts, digs, 0, w, dc)  =  ∑_{i=0}^{n-1} s_i · P_i
///
/// where s_i = R(digs[i][0..dc], w) is the scalar reconstructed from digits.
/// Proof by induction on n, peeling off the last point at each step.
pub proof fn lemma_pippenger_horner_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    w: nat,
    digits_count: nat,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        digits.len() == scalars.len(),
        w >= 1,
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < digits.len() ==> {
                &&& (#[trigger] digits[k]).len() >= digits_count as int
                &&& reconstruct_radix_2w_from(digits[k], w, 0, digits_count) == scalar_as_nat(
                    &scalars[k],
                ) as int
            },
    ensures
        pippenger_horner(points_affine, digits, 0, w, digits_count) == sum_of_scalar_muls(
            scalars,
            points_ep,
        ),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        assert(pippenger_horner(points_affine, digits, 0, w, digits_count) == edwards_identity())
            by {
            lemma_pippenger_zero_points_from(points_affine, digits, 0, w, digits_count);
        }
    } else {
        let last = (n - 1) as int;
        let pts_prefix = points_affine.drop_last();
        let digs_prefix = digits.drop_last();
        let scalars_prefix = scalars.subrange(0, last);
        let points_prefix = points_ep.subrange(0, last);

        // Preconditions for prefix
        assert forall|k: int| 0 <= k < pts_prefix.len() implies #[trigger] pts_prefix[k]
            == edwards_point_as_affine(points_prefix[k]) by {
            assert(pts_prefix[k] == points_affine[k]);
            assert(points_prefix[k] == points_ep[k]);
        }
        assert forall|k: int| 0 <= k < digs_prefix.len() implies {
            &&& (#[trigger] digs_prefix[k]).len() >= digits_count as int
            &&& reconstruct_radix_2w_from(digs_prefix[k], w, 0, digits_count) == scalar_as_nat(
                &scalars_prefix[k],
            ) as int
        } by {
            assert(digs_prefix[k] == digits[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH: prefix is correct
        assert(pippenger_horner(pts_prefix, digs_prefix, 0, w, digits_count) == sum_of_scalar_muls(
            scalars_prefix,
            points_prefix,
        )) by {
            lemma_pippenger_horner_correct(
                scalars_prefix,
                points_prefix,
                pts_prefix,
                digs_prefix,
                w,
                digits_count,
            );
        }

        // Points are canonical
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            lemma_edwards_point_as_affine_canonical(points_ep[k]);
        }

        // Digits lengths for peel_last
        assert forall|k: int| 0 <= k < digits.len() implies (#[trigger] digits[k]).len()
            >= digits_count as int by {}

        // Split: pippenger_horner(pts, digs, 0) = prefix_result + single_result
        lemma_pippenger_peel_last(points_affine, digits, 0, w, digits_count);

        // Single point Horner = [scalar_last] * P_last
        let P_last = points_affine.last();
        let d_last = digits.last();
        assert(pippenger_horner(seq![(P_last)], seq![(d_last)], 0, w, digits_count)
            == edwards_scalar_mul_signed(
            P_last,
            reconstruct_radix_2w_from(d_last, w, 0, digits_count),
        )) by {
            lemma_pippenger_single(P_last, d_last, 0, w, digits_count);
        }

        // Connect signed to unsigned scalar_mul
        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct_radix_2w_from(d_last, w, 0, digits_count) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);
    }
}

// =============================================================================
// Helper spec: weighted sum of buckets from position b to B-1
// =============================================================================
/// Weighted sum starting from position b:
///
///   weighted_from(b, B)  =  ∑_{j=b}^{B-1} (j − b + 1) · bucket[j]
///
/// Defined by peeling off the *last* bucket (top-down recursion on B):
///
///   weighted_from(b, B)  =  weighted_from(b, B−1) + (B−b) · bucket[B−1]
///
/// At b = 0 this coincides with `pippenger_weighted_bucket_sum`:
///
///   weighted_from(0, B)  =  ∑_{j=0}^{B-1} (j+1) · bucket[j]  =  weighted_bucket_sum(B)
pub open spec fn pippenger_weighted_from(buckets: Seq<(nat, nat)>, b: int, B: int) -> (nat, nat)
    decreases B - b,
{
    if B <= b {
        edwards_identity()
    } else {
        let rest = pippenger_weighted_from(buckets, b, B - 1);
        let weight = (B - b) as nat;
        let weighted = edwards_scalar_mul(buckets[B - 1], weight);
        edwards_add(rest.0, rest.1, weighted.0, weighted.1)
    }
}

// =============================================================================
// Lemma: weighted_from(0, B) = weighted_bucket_sum(B)
// =============================================================================
/// Both specs compute ∑_{j=0}^{B-1} (j+1)·bucket[j] with the same top-down
/// recursion, so they agree by induction on B.
proof fn lemma_weighted_from_eq_weighted_bucket_sum(buckets: Seq<(nat, nat)>, B: int)
    requires
        B >= 0,
        buckets.len() >= B,
    ensures
        pippenger_weighted_from(buckets, 0, B) == pippenger_weighted_bucket_sum(buckets, B),
    decreases B,
{
    if B <= 0 {
    } else {
        assert(pippenger_weighted_from(buckets, 0, B - 1) == pippenger_weighted_bucket_sum(
            buckets,
            B - 1,
        )) by {
            lemma_weighted_from_eq_weighted_bucket_sum(buckets, B - 1);
        }
    }
}

// =============================================================================
// Lemma: intermediate_sum(b, B) = intermediate_sum(b, B-1) + bucket[B-1]
// =============================================================================
/// Extending the intermediate sum by one bucket from the top.
///
/// Mathematically: the suffix sum over [b..B) equals the suffix sum over [b..B-1)
/// plus the new top bucket.  Proof uses commutativity and associativity of addition.
proof fn lemma_intermediate_sum_extend(buckets: Seq<(nat, nat)>, b: int, B: int)
    requires
        0 <= b,
        b < B - 1,
        B <= buckets.len() as int,
    ensures
        pippenger_intermediate_sum(buckets, b, B) == {
            let prev = pippenger_intermediate_sum(buckets, b, B - 1);
            let top = buckets[B - 1];
            edwards_add(prev.0, prev.1, top.0, top.1)
        },
    decreases B - 1 - b,
{
    if b == B - 2 {
        // Help Z3 unfold intermediate_sum at base cases
        assert(pippenger_intermediate_sum(buckets, B - 1, B) == buckets[B - 1]);
        assert(pippenger_intermediate_sum(buckets, B - 2, B - 1) == buckets[B - 2]);
        assert(edwards_add(buckets[B - 1].0, buckets[B - 1].1, buckets[B - 2].0, buckets[B - 2].1)
            == edwards_add(buckets[B - 2].0, buckets[B - 2].1, buckets[B - 1].0, buckets[B - 1].1))
            by {
            lemma_edwards_add_commutative(
                buckets[B - 1].0,
                buckets[B - 1].1,
                buckets[B - 2].0,
                buckets[B - 2].1,
            );
        }
    } else {
        let A = pippenger_intermediate_sum(buckets, b + 1, B - 1);
        let C = buckets[B - 1];
        let D = buckets[b];

        // IH: IS(b+1, B) = add(IS(b+1, B-1), bucket[B-1])
        assert(pippenger_intermediate_sum(buckets, b + 1, B) == edwards_add(A.0, A.1, C.0, C.1))
            by {
            lemma_intermediate_sum_extend(buckets, b + 1, B);
        }

        // Rearrange: add(add(A, C), D) = add(add(A, D), C)
        assert(edwards_add(
            edwards_add(A.0, A.1, C.0, C.1).0,
            edwards_add(A.0, A.1, C.0, C.1).1,
            D.0,
            D.1,
        ) == edwards_add(
            edwards_add(A.0, A.1, D.0, D.1).0,
            edwards_add(A.0, A.1, D.0, D.1).1,
            C.0,
            C.1,
        )) by {
            axiom_edwards_add_associative(A.0, A.1, C.0, C.1, D.0, D.1);
            lemma_edwards_add_commutative(C.0, C.1, D.0, D.1);
            axiom_edwards_add_associative(A.0, A.1, D.0, D.1, C.0, C.1);
        }
    }
}

// =============================================================================
// Lemma: weighted_from(b, B) = weighted_from(b+1, B) + intermediate_sum(b, B)
// =============================================================================
/// The top-down weighted sum decomposes as: the (b+1)-weighted sum plus the
/// full suffix sum at b.  This is the "change of summation order" identity that
/// connects the top-down definition of weighted_from with the bottom-up
/// recursion of running_sum.
///
/// Mathematically:
///   ∑_{j=b}^{B-1} (j−b+1)·bucket[j]
///     = ∑_{j=b+1}^{B-1} (j−b)·bucket[j]  +  ∑_{j=b}^{B-1} bucket[j]
///
/// since for each j ≥ b+1: (j−b+1) = (j−b) + 1, and bucket[b] appears once.
proof fn lemma_weighted_from_decompose(buckets: Seq<(nat, nat)>, b: int, B: int)
    requires
        0 <= b,
        b < B,
        B <= buckets.len() as int,
        forall|j: int| 0 <= j < B ==> (#[trigger] buckets[j]).0 < p() && buckets[j].1 < p(),
    ensures
        pippenger_weighted_from(buckets, b, B) == {
            let w = pippenger_weighted_from(buckets, b + 1, B);
            let is = pippenger_intermediate_sum(buckets, b, B);
            edwards_add(w.0, w.1, is.0, is.1)
        },
    decreases B - b,
{
    if b == B - 1 {
        // Help Z3 unfold specs at base case
        assert(pippenger_weighted_from(buckets, b + 1, B) == edwards_identity());
        assert(pippenger_intermediate_sum(buckets, b, B) == buckets[b]);
        assert(pippenger_weighted_from(buckets, b, B - 1) == edwards_identity());
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        let W = pippenger_weighted_from(buckets, b + 1, B - 1);
        let IS_prev = pippenger_intermediate_sum(buckets, b, B - 1);
        let C = buckets[B - 1];
        let m = (B - b - 1) as nat;
        let mC = edwards_scalar_mul(C, m);
        let mC_plus_C = edwards_add(mC.0, mC.1, C.0, C.1);
        let W_plus_mC = edwards_add(W.0, W.1, mC.0, mC.1);
        let IS_prev_plus_C = edwards_add(IS_prev.0, IS_prev.1, C.0, C.1);

        // IH: weighted_from(b, B-1) = add(W, IS_prev)
        assert(pippenger_weighted_from(buckets, b, B - 1) == edwards_add(
            W.0,
            W.1,
            IS_prev.0,
            IS_prev.1,
        )) by {
            lemma_weighted_from_decompose(buckets, b, B - 1);
        }
        // IS(b, B) = add(IS_prev, C)
        assert(pippenger_intermediate_sum(buckets, b, B) == IS_prev_plus_C) by {
            lemma_intermediate_sum_extend(buckets, b, B);
        }
        // [(m+1)]*C = add([m]*C, C)
        assert(edwards_scalar_mul(C, (m + 1) as nat) == mC_plus_C) by {
            lemma_edwards_scalar_mul_succ(C, m);
        }

        // Unfold weighted_from(b, B) and weighted_from(b+1, B)
        assert(pippenger_weighted_from(buckets, b, B) == edwards_add(
            edwards_add(W.0, W.1, IS_prev.0, IS_prev.1).0,
            edwards_add(W.0, W.1, IS_prev.0, IS_prev.1).1,
            mC_plus_C.0,
            mC_plus_C.1,
        ));
        assert(pippenger_weighted_from(buckets, b + 1, B) == W_plus_mC);

        // Four-way reassociation: (W+IS_prev)+(mC+C) = (W+mC)+(IS_prev+C)
        assert(edwards_add(
            edwards_add(W.0, W.1, IS_prev.0, IS_prev.1).0,
            edwards_add(W.0, W.1, IS_prev.0, IS_prev.1).1,
            mC_plus_C.0,
            mC_plus_C.1,
        ) == edwards_add(W_plus_mC.0, W_plus_mC.1, IS_prev_plus_C.0, IS_prev_plus_C.1)) by {
            axiom_edwards_add_associative(W.0, W.1, IS_prev.0, IS_prev.1, mC_plus_C.0, mC_plus_C.1);
            axiom_edwards_add_associative(IS_prev.0, IS_prev.1, mC.0, mC.1, C.0, C.1);
            lemma_edwards_add_commutative(IS_prev.0, IS_prev.1, mC.0, mC.1);
            axiom_edwards_add_associative(mC.0, mC.1, IS_prev.0, IS_prev.1, C.0, C.1);
            axiom_edwards_add_associative(W.0, W.1, mC.0, mC.1, IS_prev_plus_C.0, IS_prev_plus_C.1);
        }
    }
}

// =============================================================================
// Lemma: running_sum(b, B) = weighted_from(b, B)
// =============================================================================
/// Both running_sum and weighted_from satisfy the same recurrence
///   f(b, B) = f(b+1, B) + intermediate_sum(b, B)
/// with the same base case (identity when b ≥ B), so they are equal.
///
/// The base case b = B−1 requires identity + bucket = bucket (canonical identity law).
proof fn lemma_running_sum_eq_weighted_from(buckets: Seq<(nat, nat)>, b: int, B: int)
    requires
        0 <= b,
        b <= B,
        B <= buckets.len() as int,
        forall|j: int| 0 <= j < B ==> (#[trigger] buckets[j]).0 < p() && buckets[j].1 < p(),
    ensures
        pippenger_running_sum(buckets, b, B) == pippenger_weighted_from(buckets, b, B),
    decreases B - b,
{
    if b >= B {
        // Both are identity
    } else if b == B - 1 {
        // Help Z3 unfold specs at base case
        assert(pippenger_running_sum(buckets, b, B) == buckets[b]);
        assert(pippenger_weighted_from(buckets, b, B - 1) == edwards_identity());
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_add(0, 1, buckets[b].0, buckets[b].1) == (
            buckets[b].0 % p(),
            buckets[b].1 % p(),
        )) by {
            p_gt_2();
            lemma_edwards_add_identity_left(buckets[b].0, buckets[b].1);
        }
        assert(buckets[b].0 % p() == buckets[b].0) by {
            lemma_small_mod(buckets[b].0, p());
        }
        assert(buckets[b].1 % p() == buckets[b].1) by {
            lemma_small_mod(buckets[b].1, p());
        }
    } else {
        // IH: running_sum(b+1, B) = weighted_from(b+1, B)
        assert(pippenger_running_sum(buckets, b + 1, B) == pippenger_weighted_from(
            buckets,
            b + 1,
            B,
        )) by {
            lemma_running_sum_eq_weighted_from(buckets, b + 1, B);
        }
        // Decompose: weighted_from(b, B) = add(weighted_from(b+1, B), IS(b, B))
        assert(pippenger_weighted_from(buckets, b, B) == {
            let w = pippenger_weighted_from(buckets, b + 1, B);
            let is = pippenger_intermediate_sum(buckets, b, B);
            edwards_add(w.0, w.1, is.0, is.1)
        }) by {
            lemma_weighted_from_decompose(buckets, b, B);
        }
    }
}

// =============================================================================
// Lemma: running_sum(0, B) = weighted_bucket_sum(B)  [was axiom]
// =============================================================================
/// The running-sum-of-intermediate-sums trick computes the weighted bucket sum.
///
/// Mathematically:  running_sum(0, B)  =  ∑_{b=0}^{B-1} IS(b, B)
///                                      =  ∑_{b=0}^{B-1} (b+1) · bucket[b]
///                                      =  weighted_bucket_sum(B)
///
/// The first equality is by definition of running_sum.
/// The second is the "swap summation order" identity: each bucket[j] appears
/// in IS(b, B) for every b ≤ j, hence (j+1) times total.
///
/// Proved via the helper spec weighted_from and three lemmas:
///   1. running_sum(b, B) = weighted_from(b, B)    [same recurrence]
///   2. weighted_from(0, B) = weighted_bucket_sum(B) [same top-down recursion]
pub proof fn lemma_running_sum_equals_weighted(buckets_affine: Seq<(nat, nat)>, B: int)
    requires
        B > 0,
        buckets_affine.len() == B,
        forall|j: int|
            0 <= j < B ==> (#[trigger] buckets_affine[j]).0 < p() && buckets_affine[j].1 < p(),
    ensures
        pippenger_running_sum(buckets_affine, 0, B) == pippenger_weighted_bucket_sum(
            buckets_affine,
            B,
        ),
{
    assert(pippenger_running_sum(buckets_affine, 0, B) == pippenger_weighted_from(
        buckets_affine,
        0,
        B,
    )) by {
        lemma_running_sum_eq_weighted_from(buckets_affine, 0, B);
    }
    assert(pippenger_weighted_from(buckets_affine, 0, B) == pippenger_weighted_bucket_sum(
        buckets_affine,
        B,
    )) by {
        lemma_weighted_from_eq_weighted_bucket_sum(buckets_affine, B);
    }
}

// =============================================================================
// Helper: if two sequences agree on [0..B), their weighted_bucket_sum agrees
// =============================================================================
/// Extensionality:  a[j] = b[j] for j ∈ [0, B)  ⟹  WBS(a, B) = WBS(b, B).
proof fn lemma_weighted_bucket_sum_agree(a: Seq<(nat, nat)>, b: Seq<(nat, nat)>, B: int)
    requires
        B >= 0,
        a.len() >= B,
        b.len() >= B,
        forall|j: int| 0 <= j < B ==> (#[trigger] a[j]) == b[j],
    ensures
        pippenger_weighted_bucket_sum(a, B) == pippenger_weighted_bucket_sum(b, B),
    decreases B,
{
    if B <= 0 {
    } else {
        assert(pippenger_weighted_bucket_sum(a, B - 1) == pippenger_weighted_bucket_sum(b, B - 1))
            by {
            lemma_weighted_bucket_sum_agree(a, b, B - 1);
        }
    }
}

// =============================================================================
// Helper: weighted_bucket_sum of all-identity buckets is identity
// =============================================================================
/// When every bucket is the identity point, the weighted sum is identity.
/// Uses: [n] · O = O  and  O + O = O.
proof fn lemma_weighted_bucket_sum_all_identity(buckets: Seq<(nat, nat)>, B: int)
    requires
        B >= 0,
        buckets.len() >= B,
        forall|j: int| 0 <= j < B ==> (#[trigger] buckets[j]) == edwards_identity(),
    ensures
        pippenger_weighted_bucket_sum(buckets, B) == edwards_identity(),
    decreases B,
{
    if B <= 0 {
    } else {
        assert(pippenger_weighted_bucket_sum(buckets, B - 1) == edwards_identity()) by {
            lemma_weighted_bucket_sum_all_identity(buckets, B - 1);
        }
        assert(edwards_scalar_mul(edwards_identity(), B as nat) == edwards_identity()) by {
            lemma_edwards_scalar_mul_identity(B as nat);
        }
        assert(edwards_add(
            edwards_identity().0,
            edwards_identity().1,
            edwards_identity().0,
            edwards_identity().1,
        ) == edwards_identity()) by {
            p_gt_2();
            lemma_edwards_add_identity_right_canonical(edwards_identity());
        }
    }
}

// =============================================================================
// Helper: weighted_bucket_sum when one bucket gets a point added
// =============================================================================
/// If `buckets_new` differs from `buckets_old` only at position `idx`, where
///   buckets_new[idx] = buckets_old[idx] + P,
/// then
///   WBS(buckets_new, B) = WBS(buckets_old, B) + [(idx+1)] · P
///
/// This is the key algebraic step: adding P to bucket idx changes the
/// weighted sum by exactly (idx+1)·P, because only the term for bucket idx
/// changes, and it changes by [(idx+1)]·P via the distributive law
///   [(idx+1)]·(A + P) = [(idx+1)]·A + [(idx+1)]·P.
proof fn lemma_weighted_bucket_sum_add_to_bucket(
    buckets_old: Seq<(nat, nat)>,
    buckets_new: Seq<(nat, nat)>,
    idx: int,
    P: (nat, nat),
    B: int,
)
    requires
        0 <= idx < B,
        B <= buckets_old.len() as int,
        B <= buckets_new.len() as int,
        buckets_new[idx] == edwards_add(buckets_old[idx].0, buckets_old[idx].1, P.0, P.1),
        forall|j: int| 0 <= j < B && j != idx ==> (#[trigger] buckets_new[j]) == buckets_old[j],
    ensures
        pippenger_weighted_bucket_sum(buckets_new, B) == {
            let prev = pippenger_weighted_bucket_sum(buckets_old, B);
            let delta = edwards_scalar_mul(P, (idx + 1) as nat);
            edwards_add(prev.0, prev.1, delta.0, delta.1)
        },
    decreases B,
{
    if idx == B - 1 {
        let wbs_prev = pippenger_weighted_bucket_sum(buckets_old, B - 1);
        let old_w = edwards_scalar_mul(buckets_old[B - 1], B as nat);
        let delta = edwards_scalar_mul(P, B as nat);

        // First B-1 buckets agree
        assert(pippenger_weighted_bucket_sum(buckets_new, B - 1) == pippenger_weighted_bucket_sum(
            buckets_old,
            B - 1,
        )) by {
            lemma_weighted_bucket_sum_agree(buckets_old, buckets_new, B - 1);
        }
        // [B]*(old[B-1] + P) = [B]*old[B-1] + [B]*P  (distributivity)
        assert(edwards_scalar_mul(
            edwards_add(buckets_old[B - 1].0, buckets_old[B - 1].1, P.0, P.1),
            B as nat,
        ) == edwards_add(old_w.0, old_w.1, delta.0, delta.1)) by {
            axiom_edwards_scalar_mul_distributive(buckets_old[B - 1], P, B as nat);
        }
        // Reassociate: WBS_old(B-1) + ([B]*old + [B]*P) = (WBS_old(B-1) + [B]*old) + [B]*P
        assert(edwards_add(
            wbs_prev.0,
            wbs_prev.1,
            edwards_add(old_w.0, old_w.1, delta.0, delta.1).0,
            edwards_add(old_w.0, old_w.1, delta.0, delta.1).1,
        ) == edwards_add(
            edwards_add(wbs_prev.0, wbs_prev.1, old_w.0, old_w.1).0,
            edwards_add(wbs_prev.0, wbs_prev.1, old_w.0, old_w.1).1,
            delta.0,
            delta.1,
        )) by {
            axiom_edwards_add_associative(
                wbs_prev.0,
                wbs_prev.1,
                old_w.0,
                old_w.1,
                delta.0,
                delta.1,
            );
        }
    } else {
        let wbs_prev = pippenger_weighted_bucket_sum(buckets_old, B - 1);
        let old_w = edwards_scalar_mul(buckets_old[B - 1], B as nat);
        let delta = edwards_scalar_mul(P, (idx + 1) as nat);

        // IH on first B-1 buckets
        assert(pippenger_weighted_bucket_sum(buckets_new, B - 1) == {
            let prev = pippenger_weighted_bucket_sum(buckets_old, B - 1);
            edwards_add(prev.0, prev.1, delta.0, delta.1)
        }) by {
            lemma_weighted_bucket_sum_add_to_bucket(buckets_old, buckets_new, idx, P, B - 1);
        }
        // Reassociate: (WBS_old(B-1) + delta) + [B]*old = (WBS_old(B-1) + [B]*old) + delta
        assert(edwards_add(
            edwards_add(wbs_prev.0, wbs_prev.1, delta.0, delta.1).0,
            edwards_add(wbs_prev.0, wbs_prev.1, delta.0, delta.1).1,
            old_w.0,
            old_w.1,
        ) == edwards_add(
            edwards_add(wbs_prev.0, wbs_prev.1, old_w.0, old_w.1).0,
            edwards_add(wbs_prev.0, wbs_prev.1, old_w.0, old_w.1).1,
            delta.0,
            delta.1,
        )) by {
            axiom_edwards_add_associative(
                wbs_prev.0,
                wbs_prev.1,
                delta.0,
                delta.1,
                old_w.0,
                old_w.1,
            );
            lemma_edwards_add_commutative(delta.0, delta.1, old_w.0, old_w.1);
            axiom_edwards_add_associative(
                wbs_prev.0,
                wbs_prev.1,
                old_w.0,
                old_w.1,
                delta.0,
                delta.1,
            );
        }
    }
}

// =============================================================================
// Lemma: Bucket weighted sum = column sum  [was axiom]
// =============================================================================
/// The weighted bucket sum equals the column sum (straus_column_sum).
///
/// Mathematically, define buckets after processing n points:
///   bucket[b](n) = ∑_{i : d_i = b+1} P_i  −  ∑_{i : d_i = −(b+1)} P_i
///
/// Then:
///   WBS(n)  =  ∑_{b=0}^{B-1} (b+1) · bucket[b](n)
///           =  ∑_{i=0}^{n-1} d_i · P_i                    (*)
///           =  straus_column_sum(pts, digs, col, n)
///
/// (*) holds because point P_i with digit d_i contributes (b+1)·P_i to bucket
///     b = |d_i|−1, with the correct sign.
///
/// Proof by induction on n.  The step uses `lemma_weighted_bucket_sum_add_to_bucket`:
/// adding P_n to bucket |d_n|−1 changes WBS by exactly d_n · P_n.
pub proof fn lemma_bucket_weighted_sum_equals_column_sum(
    points_affine: Seq<(nat, nat)>,
    all_digits: Seq<Seq<i8>>,
    col: int,
    n: int,
    num_buckets: int,
)
    requires
        0 <= col,
        0 <= n <= points_affine.len(),
        n <= all_digits.len(),
        num_buckets > 0,
        forall|k: int| 0 <= k < n ==> col < (#[trigger] all_digits[k]).len(),
        forall|k: int|
            0 <= k < n ==> -(num_buckets as int) <= ((#[trigger] all_digits[k])[col] as int) <= (
            num_buckets as int),
        forall|k: int|
            0 <= k < n ==> (#[trigger] points_affine[k]).0 < p() && points_affine[k].1 < p(),
    ensures
        ({
            let buckets = Seq::new(
                num_buckets as nat,
                |b: int| pippenger_bucket_contents(points_affine, all_digits, col, n, b),
            );
            pippenger_weighted_bucket_sum(buckets, num_buckets)
        }) == straus_column_sum(points_affine, all_digits, col, n),
    decreases n,
{
    let B = num_buckets;
    let buckets_n = Seq::new(
        B as nat,
        |b: int| pippenger_bucket_contents(points_affine, all_digits, col, n, b),
    );

    if n <= 0 {
        // All buckets are identity; WBS = identity = column_sum(0)
        assert forall|b: int| 0 <= b < B implies (#[trigger] buckets_n[b])
            == edwards_identity() by {};
        assert(pippenger_weighted_bucket_sum(buckets_n, B) == edwards_identity()) by {
            lemma_weighted_bucket_sum_all_identity(buckets_n, B);
        }
    } else {
        // IH at n-1
        let buckets_prev = Seq::new(
            B as nat,
            |b: int| pippenger_bucket_contents(points_affine, all_digits, col, n - 1, b),
        );
        assert(pippenger_weighted_bucket_sum(buckets_prev, num_buckets) == straus_column_sum(
            points_affine,
            all_digits,
            col,
            n - 1,
        )) by {
            lemma_bucket_weighted_sum_equals_column_sum(
                points_affine,
                all_digits,
                col,
                n - 1,
                num_buckets,
            );
        }

        let d = all_digits[n - 1][col] as int;
        let pt = points_affine[n - 1];

        if d > 0 {
            let idx = (d - 1) as int;

            assert forall|bb: int| 0 <= bb < B && bb != idx implies (#[trigger] buckets_n[bb])
                == buckets_prev[bb] by {};
            assert(buckets_n[idx] == edwards_add(
                buckets_prev[idx].0,
                buckets_prev[idx].1,
                pt.0,
                pt.1,
            ));

            assert(pippenger_weighted_bucket_sum(buckets_n, B) == {
                let prev = pippenger_weighted_bucket_sum(buckets_prev, B);
                let delta = edwards_scalar_mul(pt, (idx + 1) as nat);
                edwards_add(prev.0, prev.1, delta.0, delta.1)
            }) by {
                lemma_weighted_bucket_sum_add_to_bucket(buckets_prev, buckets_n, idx, pt, B);
            }
            reveal(edwards_scalar_mul_signed);
        } else if d < 0 {
            let idx = (-d - 1) as int;

            assert forall|bb: int| 0 <= bb < B && bb != idx implies (#[trigger] buckets_n[bb])
                == buckets_prev[bb] by {};

            let neg_pt = edwards_neg(pt);
            assert(buckets_n[idx] == edwards_sub(
                buckets_prev[idx].0,
                buckets_prev[idx].1,
                pt.0,
                pt.1,
            ));
            assert(buckets_n[idx] == edwards_add(
                buckets_prev[idx].0,
                buckets_prev[idx].1,
                neg_pt.0,
                neg_pt.1,
            ));

            assert(pippenger_weighted_bucket_sum(buckets_n, B) == {
                let prev = pippenger_weighted_bucket_sum(buckets_prev, B);
                let delta = edwards_scalar_mul(neg_pt, (idx + 1) as nat);
                edwards_add(prev.0, prev.1, delta.0, delta.1)
            }) by {
                lemma_weighted_bucket_sum_add_to_bucket(buckets_prev, buckets_n, idx, neg_pt, B);
            }
            assert(edwards_scalar_mul(edwards_neg(pt), (-d) as nat) == edwards_neg(
                edwards_scalar_mul(pt, (-d) as nat),
            )) by {
                lemma_scalar_mul_distributes_over_neg(pt, (-d) as nat);
            }
            reveal(edwards_scalar_mul_signed);
        } else {
            // d == 0: no buckets changed
            assert forall|bb: int| 0 <= bb < B implies (#[trigger] buckets_n[bb])
                == buckets_prev[bb] by {};
            assert(pippenger_weighted_bucket_sum(buckets_n, B) == pippenger_weighted_bucket_sum(
                buckets_prev,
                B,
            )) by {
                lemma_weighted_bucket_sum_agree(buckets_prev, buckets_n, B);
            }

            reveal(edwards_scalar_mul_signed);
            reveal_with_fuel(edwards_scalar_mul, 1);

            let cs = straus_column_sum(points_affine, all_digits, col, n - 1);
            assert(cs.0 < p() && cs.1 < p()) by {
                lemma_column_sum_canonical(points_affine, all_digits, col, n - 1);
            }
            assert(edwards_add(cs.0, cs.1, 0, 1) == cs) by {
                p_gt_2();
                lemma_edwards_add_identity_right_canonical(cs);
            }
        }
    }
}

} // verus!
