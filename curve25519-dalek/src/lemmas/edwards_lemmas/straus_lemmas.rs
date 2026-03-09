//! Lemmas for Straus (interleaved window) multiscalar multiplication.
//!
//! Proves correctness of both constant-time (CT) and variable-time (VT) Straus
//! evaluation: Q = s\_1 P\_1 + ... + s\_n P\_n via column-wise Horner recurrences.
//!
//! CT uses radix-16 signed digits d\_{k,j} with 64 positions (j = 0..63):
//!   H(64) = O,   H(j) = \[16\] H(j+1) + col(j, n)
//!
//! VT uses NAF(5) digits n\_{k,i} with 256 positions (i = 0..255):
//!   H(256) = O,  H(i) = \[2\] H(i+1) + col(i, n)
//!
//! where col(j, k) = sum\_{m=0}^{k-1} \[d\_{m,j}\] P\_m (column sum).
//!
//! ## Bundled validity predicates:
//! - `straus_vt_input_valid`: groups ~8 quantified VT loop invariants
//! - `straus_ct_input_valid`: groups ~8 quantified CT loop invariants
//!
//! ## Select lemmas:
//! - `lemma_select_is_signed_scalar_mul_projective`: LookupTable select -> \[x\] P
//! - `lemma_naf_select_is_signed_scalar_mul_projective`: NafLookupTable5 select -> \[d\] P
//!
//! ## Column sum / Horner lemmas:
//! - `lemma_column_sum_step`: col(j, k+1) = col(j, k) + \[d\_{k,j}\] P\_k
//! - `lemma_straus_ct_step`: H(j) = \[16\] H(j+1) + col(j, n)
//! - `lemma_straus_vt_step`: H(i) = \[2\] H(i+1) + col(i, n)
//!
//! ## Correctness theorems:
//! - `lemma_straus_ct_correct`: H\_ct(0) = sum\_of\_scalar\_muls(scalars, points)
//! - `lemma_straus_vt_correct`: H\_vt(0) = sum\_of\_scalar\_muls(scalars, points)
#![allow(non_snake_case)]

use crate::backend::serial::curve_models::{AffineNielsPoint, ProjectiveNielsPoint};
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::window::LookupTable;
use crate::window::NafLookupTable5;

#[cfg(verus_keep_ghost)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
use crate::specs::window_specs::*;

#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;

use vstd::prelude::*;

verus! {

// =============================================================================
// Straus multiscalar multiplication spec functions
// =============================================================================
/// Column sum: col(j, n) = sum_{k=0}^{n-1} [d_{k,j}] * P_k
///
/// Recursive over k (number of points summed).
/// Base case: col(j, 0) = O  (identity).
/// Step:      col(j, k+1) = col(j, k) + [d_{k,j}] * P_k
///
/// Shared by both CT (radix-16 digits) and VT (NAF digits).
pub open spec fn straus_column_sum(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    n: int,
) -> (nat, nat)
    decreases n,
{
    if n <= 0 {
        edwards_identity()
    } else {
        let prev = straus_column_sum(points_affine, digits, j, n - 1);
        let term = edwards_scalar_mul_signed(points_affine[n - 1], digits[n - 1][j] as int);
        edwards_add(prev.0, prev.1, term.0, term.1)
    }
}

/// CT Horner accumulator: H_ct(j) for j in [0, 64].
///
/// H_ct(64) = O
/// H_ct(j)  = [16] * H_ct(j+1) + col(j, n)    for j = 63..0
///
/// Result: H_ct(0) = sum_k s_k * P_k  (proved by lemma_straus_ct_correct).
#[verifier::opaque]
pub open spec fn straus_ct_partial(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    from_j: int,
) -> (nat, nat)
    decreases 64 - from_j,
{
    if from_j >= 64 {
        edwards_identity()
    } else {
        let prev = straus_ct_partial(points_affine, digits, from_j + 1);
        let scaled = edwards_scalar_mul(prev, 16);
        let col = straus_column_sum(points_affine, digits, from_j, points_affine.len() as int);
        edwards_add(scaled.0, scaled.1, col.0, col.1)
    }
}

/// VT Horner accumulator: H_vt(i) for i in [0, 256].
///
/// H_vt(256) = O
/// H_vt(i)   = [2] * H_vt(i+1) + col(i, n)    for i = 255..0
///
/// Result: H_vt(0) = sum_k s_k * P_k  (proved by lemma_straus_vt_correct).
#[verifier::opaque]
pub open spec fn straus_vt_partial(
    points_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
    from_i: int,
) -> (nat, nat)
    decreases 256 - from_i,
{
    if from_i >= 256 {
        edwards_identity()
    } else {
        let prev = straus_vt_partial(points_affine, nafs, from_i + 1);
        let doubled = edwards_double(prev.0, prev.1);
        let col = straus_column_sum(points_affine, nafs, from_i, points_affine.len() as int);
        edwards_add(doubled.0, doubled.1, col.0, col.1)
    }
}

/// Index-based Horner evaluation of radix-16 digits from position j:
///
///   R16(d, j) = sum_{i=j}^{63} d[i] * 16^{i-j}
///             = d[j] + 16 * R16(d, j+1)
///
/// R16(d, 64) = 0.   R16(d, 0) = reconstruct_radix_16(d).
pub open spec fn reconstruct_radix_16_from(digits: Seq<i8>, from_j: int) -> int
    decreases 64 - from_j,
{
    if from_j >= 64 || from_j < 0 {
        0
    } else {
        (digits[from_j] as int) + 16 * reconstruct_radix_16_from(digits, from_j + 1)
    }
}

/// Index-based Horner evaluation of NAF digits from position i:
///
///   RNAF(n, i) = sum_{k=i}^{255} n[k] * 2^{k-i}
///              = n[i] + 2 * RNAF(n, i+1)
///
/// RNAF(n, 256) = 0.   RNAF(n, 0) = reconstruct(n).
pub open spec fn reconstruct_naf_from(naf: Seq<i8>, from_i: int) -> int
    decreases 256 - from_i,
{
    if from_i >= 256 || from_i < 0 {
        0
    } else {
        (naf[from_i] as int) + 2 * reconstruct_naf_from(naf, from_i + 1)
    }
}

// =============================================================================
// Select lemma for LookupTable<ProjectiveNielsPoint>
// =============================================================================
/// LookupTable select correctness: select(x) decodes to [x]*P in affine.
///
/// For digit x in [-8, 8]:
///   x > 0:  table[x-1]            -> [x]*P
///   x = 0:  identity              -> O
///   x < 0:  negate(table[-x-1])   -> [x]*P
pub proof fn lemma_select_is_signed_scalar_mul_projective(
    table: [ProjectiveNielsPoint; 8],
    x: i8,
    result: ProjectiveNielsPoint,
    basepoint: (nat, nat),
)
    requires
        -8 <= x <= 8,
        // Table entries decode to multiples of basepoint
        forall|j: int|
            0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (j + 1) as nat),
        // select's postconditions:
        (x > 0 ==> result == table[(x - 1) as int]),
        (x == 0 ==> result == identity_projective_niels()),
        (x < 0 ==> result == negate_projective_niels(table[((-x) - 1) as int])),
    ensures
        projective_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            x as int,
        ),
{
    reveal(edwards_scalar_mul_signed);

    if x > 0 {
        let j = (x - 1) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == x as nat);
    } else if x == 0 {
        lemma_identity_projective_niels_is_identity();
        reveal_with_fuel(edwards_scalar_mul, 1);
        assert(edwards_scalar_mul(basepoint, 0) == edwards_identity());
    } else {
        // x < 0: result == negate_projective_niels(table[((-x) - 1) as int])
        let j = ((-x) - 1) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (j + 1) as nat,
        ));
        assert((j + 1) as nat == (-x) as nat);

        lemma_negate_projective_niels_is_edwards_neg(table[j]);
        assert(projective_niels_point_as_affine_edwards(negate_projective_niels(table[j]))
            == edwards_neg(edwards_scalar_mul(basepoint, (-x) as nat)));
    }
}

// =============================================================================
// Select lemma for NafLookupTable5<ProjectiveNielsPoint>
// =============================================================================
/// NafLookupTable5 select correctness: select/negate by NAF digit -> [d]*P.
///
/// NAF digits are odd and in (-16, 16):
///   d > 0:  table[d/2]           -> [d]*P
///   d < 0:  negate(table[-d/2])  -> [d]*P
///   d = 0:  not handled here (identity contribution in caller)
pub proof fn lemma_naf_select_is_signed_scalar_mul_projective(
    table: [ProjectiveNielsPoint; 8],
    digit: i8,
    result: ProjectiveNielsPoint,
    basepoint: (nat, nat),
    is_add: bool,  // true if digit > 0, false if digit < 0
)
    requires
        digit != 0,
        // NAF width-5 bounds: nonzero digits are odd and in (-16, 16)
        -16 < digit < 16,
        (digit as int) % 2 != 0,
        // Table validity: table[j] decodes to [(2j+1)]*P
        forall|j: int|
            0 <= j < 8 ==> projective_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (2 * j + 1) as nat),
        // For digit > 0: result = table[digit/2] (from select(digit as usize))
        is_add ==> digit > 0 && result == table[((digit as int) / 2) as int],
        // For digit < 0: result = negate(table[(-digit)/2]) (from select then negate)
        !is_add ==> digit < 0 && result == negate_projective_niels(
            table[(((-digit) as int) / 2) as int],
        ),
    ensures
        projective_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            digit as int,
        ),
{
    reveal(edwards_scalar_mul_signed);

    if is_add {
        // digit > 0, odd: result = table[digit/2]
        let j = ((digit as int) / 2) as int;
        assert(0 <= j < 8);
        // table[j] = [(2j+1)]*P and 2j+1 = digit (since digit is odd)
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (2 * j + 1) as nat,
        ));
        assert((2 * j + 1) as nat == digit as nat);
    } else {
        // digit < 0, odd: result = negate(table[(-digit)/2])
        let abs_digit = (-digit) as int;
        let j = (abs_digit / 2) as int;
        assert(0 <= j < 8);
        assert(projective_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
            basepoint,
            (2 * j + 1) as nat,
        ));
        assert((2 * j + 1) as nat == abs_digit as nat);

        lemma_negate_projective_niels_is_edwards_neg(table[j]);
        assert(projective_niels_point_as_affine_edwards(negate_projective_niels(table[j]))
            == edwards_neg(edwards_scalar_mul(basepoint, abs_digit as nat)));
    }
}

/// NafLookupTable8 affine select correctness: select by odd positive digit -> [d]*P.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_select_is_signed_scalar_mul_affine8(
    table: [AffineNielsPoint; 64],
    digit: i8,
    result: AffineNielsPoint,
    basepoint: (nat, nat),
)
    requires
        0 < digit < 128,
        (digit as int) % 2 != 0,
        forall|j: int|
            0 <= j < 64 ==> affine_niels_point_as_affine_edwards(#[trigger] table[j])
                == edwards_scalar_mul(basepoint, (2 * j + 1) as nat),
        result == table[((digit as int) / 2) as int],
    ensures
        affine_niels_point_as_affine_edwards(result) == edwards_scalar_mul_signed(
            basepoint,
            digit as int,
        ),
{
    reveal(edwards_scalar_mul_signed);
    let j = ((digit as int) / 2) as int;
    assert(0 <= j < 64);
    assert(affine_niels_point_as_affine_edwards(table[j]) == edwards_scalar_mul(
        basepoint,
        (2 * j + 1) as nat,
    ));
    assert((2 * j + 1) as nat == digit as nat);
}

// =============================================================================
// Straus CT step lemma (unfold opaque spec)
// =============================================================================
/// Unfold CT Horner: H(j) = [16] * H(j+1) + col(j, n)  for j < 64.
pub proof fn lemma_straus_ct_step(points_affine: Seq<(nat, nat)>, digits: Seq<Seq<i8>>, j: int)
    requires
        0 <= j < 64,
    ensures
        straus_ct_partial(points_affine, digits, j) == {
            let prev = straus_ct_partial(points_affine, digits, j + 1);
            let scaled = edwards_scalar_mul(prev, 16);
            let col = straus_column_sum(points_affine, digits, j, points_affine.len() as int);
            edwards_add(scaled.0, scaled.1, col.0, col.1)
        },
{
    reveal(straus_ct_partial);
}

/// CT base case: H(64) = O.
pub proof fn lemma_straus_ct_base(points_affine: Seq<(nat, nat)>, digits: Seq<Seq<i8>>)
    ensures
        straus_ct_partial(points_affine, digits, 64) == edwards_identity(),
{
    reveal(straus_ct_partial);
}

// =============================================================================
// Straus VT step lemma (unfold opaque spec)
// =============================================================================
/// Unfold VT Horner: H(i) = [2] * H(i+1) + col(i, n)  for i < 256.
pub proof fn lemma_straus_vt_step(points_affine: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        0 <= i < 256,
    ensures
        straus_vt_partial(points_affine, nafs, i) == {
            let prev = straus_vt_partial(points_affine, nafs, i + 1);
            let doubled = edwards_double(prev.0, prev.1);
            let col = straus_column_sum(points_affine, nafs, i, points_affine.len() as int);
            edwards_add(doubled.0, doubled.1, col.0, col.1)
        },
{
    reveal(straus_vt_partial);
}

/// VT base case: H(256) = O.
pub proof fn lemma_straus_vt_base(points_affine: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>)
    ensures
        straus_vt_partial(points_affine, nafs, 256) == edwards_identity(),
{
    reveal(straus_vt_partial);
}

/// Spec predicate: all digits in a Seq<i8> are in [-8, 8].
/// This is the Seq analog of `radix_16_all_bounded` which works on arrays.
pub open spec fn radix_16_all_bounded_seq(digits: Seq<i8>) -> bool {
    forall|k: int| 0 <= k < digits.len() ==> -8 <= #[trigger] digits[k] <= 8
}

// =============================================================================
// Bundled validity predicates for Straus loop invariants
// =============================================================================
/// Bundled validity predicate for the variable-time (VT) Straus loops.
///
/// Groups the quantified invariants shared by both the outer loop
/// (i = 255..0) and the inner loop (j = 0..n):
///   - Length consistency for all ghost/runtime sequences
///   - NAF validity (width 5)
///   - NafLookupTable5 validity and 54-bit limb bounds
///   - Ghost-runtime consistency (pts\_affine, unwrapped\_points, nafs\_seqs)
///   - Canonical affine coordinates (< p())
///
/// Note: scalar reconstruction (`reconstruct(nafs_seqs[k]) == scalar_as_nat(...)`)
/// is kept as a separate outer-loop invariant to avoid rlimit pressure in the
/// inner loop where it is not needed.
pub open spec fn straus_vt_input_valid(
    nafs_view: Seq<[i8; 256]>,
    lookup_tables_view: Seq<NafLookupTable5<ProjectiveNielsPoint>>,
    nafs_seqs: Seq<Seq<i8>>,
    pts_affine: Seq<(nat, nat)>,
    spec_scalars: Seq<Scalar>,
    spec_points: Seq<Option<EdwardsPoint>>,
    unwrapped_points: Seq<EdwardsPoint>,
    n: nat,
) -> bool {
    let n_int = n as int;
    // Length consistency
    &&& nafs_view.len() as int == n_int
    &&& lookup_tables_view.len() as int == n_int
    &&& nafs_seqs.len() as int == n_int
    &&& pts_affine.len() as int == n_int
    &&& n_int == spec_scalars.len()
    &&& n_int
        == spec_points.len()
    // NAF validity (reconstruction kept separate — see note above)
    &&& forall|k: int|
        0 <= k < n_int ==> is_valid_naf(
            #[trigger] nafs_seqs[k],
            5,
        )
    // Table validity + 54-bit limb bounds + per-entry validity
    &&& forall|k: int|
        0 <= k < n_int ==> {
            &&& is_valid_naf_lookup_table5_projective(
                (#[trigger] lookup_tables_view[k]).0,
                spec_points[k].unwrap(),
            )
            &&& naf_lookup_table5_projective_limbs_bounded(lookup_tables_view[k].0)
            &&& forall|j: int|
                0 <= j < 8 ==> is_valid_projective_niels_point(
                    #[trigger] lookup_tables_view[k].0[j],
                )
        }
        // Ghost-runtime consistency
    &&& forall|k: int|
        0 <= k < n_int ==> #[trigger] pts_affine[k] == edwards_point_as_affine(unwrapped_points[k])
    &&& forall|k: int| 0 <= k < n_int ==> #[trigger] unwrapped_points[k] == spec_points[k].unwrap()
    &&& forall|k: int|
        0 <= k < n_int ==> #[trigger] nafs_seqs[k]
            == nafs_view[k]@
    // Canonical affine coordinates (< p())
    &&& forall|k: int|
        0 <= k < n_int ==> (#[trigger] pts_affine[k]).0 < p() && pts_affine[k].1 < p()
}

/// Bundled validity predicate for the constant-time (CT) Straus loops.
///
/// Groups the quantified invariants shared by both the outer loop
/// (j = 63..0) and the inner loop (k = 0..n):
///   - Length consistency for all ghost/runtime sequences
///   - LookupTable validity (8 multiples) and 54-bit limb bounds
///   - Radix-16 digit bounds
///   - Ghost-runtime consistency (pts\_affine, digits\_seqs)
///
/// Note: `is_valid_radix_16` and `reconstruct_radix_16` are kept as separate
/// outer-loop invariants to avoid rlimit pressure in the inner loop.
pub open spec fn straus_ct_input_valid(
    scalar_digits_view: Seq<[i8; 64]>,
    lookup_tables_view: Seq<LookupTable<ProjectiveNielsPoint>>,
    digits_seqs: Seq<Seq<i8>>,
    pts_affine: Seq<(nat, nat)>,
    spec_scalars: Seq<Scalar>,
    spec_points: Seq<EdwardsPoint>,
    n: nat,
) -> bool {
    let n_int = n as int;
    // Length consistency
    &&& scalar_digits_view.len() as int == n_int
    &&& lookup_tables_view.len() as int == n_int
    &&& digits_seqs.len() as int == n_int
    &&& pts_affine.len() as int == n_int
    &&& n_int == spec_scalars.len()
    &&& n_int
        == spec_points.len()
    // Table validity + 54-bit limb bounds + per-entry projective niels validity
    &&& forall|k: int|
        0 <= k < n_int ==> {
            &&& is_valid_lookup_table_projective(
                (#[trigger] lookup_tables_view[k]).0,
                spec_points[k],
                8,
            )
            &&& lookup_table_projective_limbs_bounded(lookup_tables_view[k].0)
            &&& forall|j: int|
                0 <= j < 8 ==> is_valid_projective_niels_point(
                    #[trigger] lookup_tables_view[k].0[j],
                )
        }
        // Radix-16 digit bounds (validity + reconstruction kept separate — see note above)
    &&& forall|k: int|
        #![auto]
        0 <= k < n_int ==> radix_16_all_bounded(
            &#[trigger] scalar_digits_view[k],
        )
    // Ghost-runtime consistency
    &&& forall|k: int|
        0 <= k < n_int ==> #[trigger] pts_affine[k] == edwards_point_as_affine(spec_points[k])
    &&& forall|k: int| 0 <= k < n_int ==> #[trigger] digits_seqs[k] == scalar_digits_view[k]@
}

// =============================================================================
// NAF digit select preconditions
// =============================================================================
/// For a NAF digit d > 0 from a valid NAF(5), d is odd and d < 16.
/// This establishes the select preconditions: (d as usize) & 1 == 1 and (d as usize) < 16.
pub proof fn lemma_naf_digit_positive_select_preconditions(digit: i8)
    requires
        digit > 0,
        (digit as int) % 2 != 0,
        digit < 16,
    ensures
        (digit as usize) & 1usize == 1usize,
        (digit as usize) < 16,
{
    assert((digit as usize) < 16);
    assert((digit as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit > 0i8,
            digit < 16i8,
            (digit as int) % 2 != 0,
    ;
}

/// For a NAF digit d > 0 from a valid NAF(8), d is odd and d < 128.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_digit_positive_select_preconditions_width8(digit: i8)
    requires
        digit > 0,
        (digit as int) % 2 != 0,
        digit < 128,
    ensures
        (digit as usize) & 1usize == 1usize,
        (digit as usize) < 128usize,
{
    assert((digit as usize) < 128usize);
    assert((digit as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit > 0i8,
            (digit as int) % 2 != 0,
    ;
}

/// For a NAF digit d < 0 from a valid NAF(5), -d is odd and -d < 16.
/// This establishes the select preconditions for the negated digit.
pub proof fn lemma_naf_digit_negative_select_preconditions(digit: i8)
    requires
        digit < 0,
        (digit as int) % 2 != 0,
        digit > -16,
    ensures
        ((-digit) as usize) & 1usize == 1usize,
        ((-digit) as usize) < 16,
{
    assert(((-digit) as usize) < 16);
    assert(((-digit) as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit < 0i8,
            digit > -16i8,
            (digit as int) % 2 != 0,
    ;
}

/// For a NAF digit d < 0 from a valid NAF(8), -d is odd and -d < 128.
#[cfg(feature = "precomputed-tables")]
pub proof fn lemma_naf_digit_negative_select_preconditions_width8(digit: i8)
    requires
        digit < 0,
        (digit as int) % 2 != 0,
        digit > -128,
    ensures
        ((-digit) as usize) & 1usize == 1usize,
        ((-digit) as usize) < 128usize,
{
    assert(((-digit) as usize) < 128usize);
    assert(((-digit) as usize) & 1usize == 1usize) by (bit_vector)
        requires
            digit < 0i8,
            digit > -128i8,
            (digit as int) % 2 != 0,
    ;
}

// =============================================================================
// Affine coordinates are always canonical (< p())
// =============================================================================
/// edwards_point_as_affine returns coordinates < p() because field_mul
/// returns (a * b) % p() which is < p() for p() > 0.
pub proof fn lemma_edwards_point_as_affine_canonical(point: EdwardsPoint)
    ensures
        edwards_point_as_affine(point).0 < p(),
        edwards_point_as_affine(point).1 < p(),
{
    p_gt_2();
}

// =============================================================================
// Column sum produces canonical coordinates
// =============================================================================
/// col(j, n) is canonical: col(j, n).0 < p() and col(j, n).1 < p().
pub proof fn lemma_column_sum_canonical(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    n: int,
)
    requires
        n >= 0,
        n <= points_affine.len(),
        n <= digits.len(),
        0 <= j,
        forall|k: int| 0 <= k < n ==> j < (#[trigger] digits[k]).len(),
        forall|k: int|
            0 <= k < n ==> (#[trigger] points_affine[k]).0 < p() && points_affine[k].1 < p(),
    ensures
        straus_column_sum(points_affine, digits, j, n).0 < p(),
        straus_column_sum(points_affine, digits, j, n).1 < p(),
    decreases n,
{
    if n <= 0 {
        // identity = (0, 1), both < p()
        p_gt_2();
    } else {
        lemma_column_sum_canonical(points_affine, digits, j, n - 1);
        let prev = straus_column_sum(points_affine, digits, j, n - 1);
        // term is canonical because edwards_scalar_mul_signed returns canonical coords
        lemma_edwards_scalar_mul_signed_canonical(points_affine[n - 1], digits[n - 1][j] as int);
        // edwards_add of canonical inputs produces canonical output
        let term = edwards_scalar_mul_signed(points_affine[n - 1], digits[n - 1][j] as int);
        lemma_edwards_add_canonical(prev.0, prev.1, term.0, term.1);
    }
}

// =============================================================================
// Column sum step for zero digit (Equal case in VT inner loop)
// =============================================================================
/// Zero digit: col(j, k+1) = col(j, k) when d_{k,j} = 0.
/// Handles the Equal (no-op) case in the VT inner loop.
pub proof fn lemma_column_sum_step_zero_digit(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    k: int,
)
    requires
        0 <= k < points_affine.len(),
        0 <= k < digits.len(),
        0 <= j,
        j < digits[k].len(),
        digits[k][j] == 0,
        // column sum up to k is canonical
        straus_column_sum(points_affine, digits, j, k).0 < p(),
        straus_column_sum(points_affine, digits, j, k).1 < p(),
    ensures
        straus_column_sum(points_affine, digits, j, k + 1) == straus_column_sum(
            points_affine,
            digits,
            j,
            k,
        ),
{
    let col_k = straus_column_sum(points_affine, digits, j, k);
    let term = edwards_scalar_mul_signed(points_affine[k], 0int);
    // edwards_scalar_mul_signed(_, 0) == edwards_scalar_mul(_, 0) == identity
    reveal_with_fuel(edwards_scalar_mul, 1);
    assert(term == edwards_identity());
    assert(term == (0nat, 1nat));
    // edwards_add(col_k, identity) == col_k (when col_k is canonical)
    lemma_edwards_add_identity_right_canonical(col_k);
}

/// If every digit in column `j` is zero, the column sum is the identity.
pub proof fn lemma_column_sum_all_zero(
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
    j: int,
    n: int,
)
    requires
        0 <= n <= points_affine.len(),
        n <= digits.len(),
        0 <= j,
        forall|k: int| 0 <= k < n ==> j < (#[trigger] digits[k]).len(),
        forall|k: int|
            0 <= k < n ==> (#[trigger] points_affine[k]).0 < p() && points_affine[k].1 < p(),
        forall|k: int| 0 <= k < n ==> #[trigger] digits[k][j] == 0,
    ensures
        straus_column_sum(points_affine, digits, j, n) == edwards_identity(),
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_column_sum_all_zero(points_affine, digits, j, n - 1);
        lemma_column_sum_canonical(points_affine, digits, j, n - 1);
        lemma_column_sum_step_zero_digit(points_affine, digits, j, n - 1);
        assert(straus_column_sum(points_affine, digits, j, n - 1) == edwards_identity());
    }
}

/// If all digits strictly above `i` are zero, then `straus_vt_partial(i + 1)` is the identity.
pub proof fn lemma_straus_vt_zero_suffix(points_affine: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        0 <= i < 256,
        nafs.len() == points_affine.len(),
        forall|k: int| 0 <= k < nafs.len() ==> (#[trigger] nafs[k]).len() == 256,
        forall|k: int|
            0 <= k < points_affine.len() ==> (#[trigger] points_affine[k]).0 < p()
                && points_affine[k].1 < p(),
        forall|k: int, j: int| 0 <= k < nafs.len() && i < j < 256 ==> #[trigger] nafs[k][j] == 0,
    ensures
        straus_vt_partial(points_affine, nafs, i + 1) == edwards_identity(),
    decreases 255 - i,
{
    if i == 255 {
        lemma_straus_vt_base(points_affine, nafs);
    } else {
        lemma_straus_vt_step(points_affine, nafs, i + 1);
        lemma_straus_vt_zero_suffix(points_affine, nafs, i + 1);
        lemma_column_sum_all_zero(points_affine, nafs, i + 1, points_affine.len() as int);
        lemma_double_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(edwards_identity());
    }
}

// =============================================================================
// Column sum prefix independence
// =============================================================================
/// Prefix independence: col(j, n) depends only on pts[0..n) and digs[0..n).
/// If two sequences agree on [0..n), their column sums are equal.
pub proof fn lemma_column_sum_prefix_eq(
    pts1: Seq<(nat, nat)>,
    digs1: Seq<Seq<i8>>,
    pts2: Seq<(nat, nat)>,
    digs2: Seq<Seq<i8>>,
    j: int,
    n: int,
)
    requires
        n >= 0,
        n <= pts1.len(),
        n <= pts2.len(),
        n <= digs1.len(),
        n <= digs2.len(),
        forall|k: int| 0 <= k < n ==> #[trigger] pts1[k] == pts2[k],
        forall|k: int| 0 <= k < n ==> #[trigger] digs1[k] == digs2[k],
    ensures
        straus_column_sum(pts1, digs1, j, n) == straus_column_sum(pts2, digs2, j, n),
    decreases n,
{
    if n > 0 {
        lemma_column_sum_prefix_eq(pts1, digs1, pts2, digs2, j, n - 1);
        // At k = n-1: pts1[n-1] == pts2[n-1] and digs1[n-1] == digs2[n-1]
        // So the recursive step produces the same result
    }
}

// =============================================================================
// Column sum for single point equals signed scalar mul (when canonical)
// =============================================================================
/// Single-point column sum: col(j, 1) = [d_j] * P when P is canonical.
pub proof fn lemma_column_sum_single(P: (nat, nat), d: Seq<i8>, j: int)
    requires
        0 <= j < d.len(),
        P.0 < p(),
        P.1 < p(),
    ensures
        straus_column_sum(seq![(P)], seq![(d)], j, 1) == edwards_scalar_mul_signed(P, d[j] as int),
{
    let pts = seq![(P)];
    let digs = seq![(d)];
    // Verify indexing
    assert(pts[0] == P);
    assert(digs[0] == d);
    assert(digs[0][j] == d[j]);

    // column_sum(pts, digs, j, 1) by definition:
    //   prev = column_sum(pts, digs, j, 0) = identity
    //   term = edwards_scalar_mul_signed(pts[0], digs[0][j])
    //   result = edwards_add(prev, term) = edwards_add(identity, term)
    let prev = straus_column_sum(pts, digs, j, 0);
    assert(prev == edwards_identity());

    let term = edwards_scalar_mul_signed(P, d[j] as int);
    lemma_edwards_scalar_mul_signed_canonical(P, d[j] as int);

    // edwards_add(identity, term) = edwards_add(term, identity) = term
    let id = edwards_identity();
    lemma_edwards_add_commutative(id.0, id.1, term.0, term.1);
    lemma_edwards_add_identity_right_canonical(term);
}

// =============================================================================
// Single-point Horner CT: straus_ct_partial(seq![P], seq![d], j) == [reconstruct_from(d,j)]*P
// =============================================================================
/// Single-point CT Horner: H_ct(seq![P], seq![d], j) = [R(d, j)] * P
/// where R(d, j) = reconstruct_radix_16_from(d, j).
pub proof fn lemma_straus_ct_single(P: (nat, nat), d: Seq<i8>, j: int)
    requires
        d.len() == 64,
        P.0 < p(),
        P.1 < p(),
        0 <= j <= 64,
    ensures
        straus_ct_partial(seq![(P)], seq![(d)], j) == edwards_scalar_mul_signed(
            P,
            reconstruct_radix_16_from(d, j),
        ),
    decreases 64 - j,
{
    if j >= 64 {
        // Base: straus_ct_partial(..., 64) == identity
        lemma_straus_ct_base(seq![(P)], seq![(d)]);
        // reconstruct_radix_16_from(d, 64) == 0
        // edwards_scalar_mul_signed(P, 0) == identity
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        // Unfold straus_ct_partial one step
        lemma_straus_ct_step(seq![(P)], seq![(d)], j);
        // straus_ct_partial(seq![P], seq![d], j)
        //   == edwards_add([16]*straus_ct_partial(seq![P], seq![d], j+1), column_sum(seq![P], seq![d], j, 1))

        // IH: straus_ct_partial(seq![P], seq![d], j+1) == [reconstruct_from(d, j+1)]*P
        lemma_straus_ct_single(P, d, j + 1);
        let r_next = reconstruct_radix_16_from(d, j + 1);

        // [16] * [r_next]*P == [16 * r_next]*P
        lemma_edwards_scalar_mul_signed_composition(P, r_next, 16);

        // column_sum(seq![P], seq![d], j, 1) == [d[j]]*P
        lemma_column_sum_single(P, d, j);

        // [16*r_next]*P + [d[j]]*P == [16*r_next + d[j]]*P
        axiom_edwards_scalar_mul_signed_additive(P, 16 * r_next, d[j] as int);

        // 16*r_next + d[j] == reconstruct_radix_16_from(d, j)
        // (from definition: reconstruct_from(d, j) = d[j] + 16 * reconstruct_from(d, j+1))
        assert(d[j] as int + 16 * r_next == reconstruct_radix_16_from(d, j));
    }
}

// =============================================================================
// Straus CT partial peel-last: splitting off the last point
// =============================================================================
/// CT peel-last: H(pts, digs, j) = H(pts[..n-1], digs[..n-1], j) + H(seq![P_n], seq![d_n], j).
///
/// Splits the n-point Horner into (n-1)-point prefix + single last point.
/// Proof by induction on (64 - j), using [16]-distributivity and associativity.
pub proof fn lemma_straus_ct_partial_peel_last(pts: Seq<(nat, nat)>, digs: Seq<Seq<i8>>, j: int)
    requires
        pts.len() >= 1,
        digs.len() == pts.len(),
        0 <= j <= 64,
        // All digits have length 64
        forall|k: int| 0 <= k < digs.len() ==> (#[trigger] digs[k]).len() == 64,
        // All points are canonical
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        straus_ct_partial(pts, digs, j) == ({
            let prefix_result = straus_ct_partial(pts.drop_last(), digs.drop_last(), j);
            let single_result = straus_ct_partial(seq![(pts.last())], seq![(digs.last())], j);
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases 64 - j,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let digs_prefix = digs.drop_last();
    let pts_single = seq![(pts.last())];
    let digs_single = seq![(digs.last())];

    if j >= 64 {
        // Base case: all three terms are identity
        lemma_straus_ct_base(pts, digs);
        lemma_straus_ct_base(pts_prefix, digs_prefix);
        lemma_straus_ct_base(pts_single, digs_single);
        // edwards_add(identity, identity) == identity
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(edwards_identity());
    } else {
        // Unfold straus_ct_partial for all three
        lemma_straus_ct_step(pts, digs, j);
        lemma_straus_ct_step(pts_prefix, digs_prefix, j);
        lemma_straus_ct_step(pts_single, digs_single, j);

        // IH at j+1
        lemma_straus_ct_partial_peel_last(pts, digs, j + 1);

        let prev_full = straus_ct_partial(pts, digs, j + 1);
        let prev_prefix = straus_ct_partial(pts_prefix, digs_prefix, j + 1);
        let prev_single = straus_ct_partial(pts_single, digs_single, j + 1);

        // By IH: prev_full == edwards_add(prev_prefix, prev_single)
        // [16]*prev_full == [16]*edwards_add(prev_prefix, prev_single)
        //               == edwards_add([16]*prev_prefix, [16]*prev_single)  (distributivity)
        axiom_edwards_scalar_mul_distributive(prev_prefix, prev_single, 16);

        let scaled_prefix = edwards_scalar_mul(prev_prefix, 16);
        let scaled_single = edwards_scalar_mul(prev_single, 16);

        // column_sum(pts, digs, j, n) == edwards_add(column_sum(pts, digs, j, n-1), term)
        // And column_sum(pts, digs, j, n-1) == column_sum(pts_prefix, digs_prefix, j, n-1)
        let col_full = straus_column_sum(pts, digs, j, n);
        let col_prefix = straus_column_sum(pts_prefix, digs_prefix, j, (n - 1));
        let col_single = straus_column_sum(pts_single, digs_single, j, 1);

        // Prove column_sum prefix independence
        lemma_column_sum_prefix_eq(pts, digs, pts_prefix, digs_prefix, j, n - 1);
        // So: straus_column_sum(pts, digs, j, n-1) == col_prefix

        // column_sum for the single point
        lemma_column_sum_single(pts.last(), digs.last(), j);
        // col_single == [digs.last()[j]] * pts.last()

        // (A+B) + (C+D) = (A+C) + (B+D)
        lemma_edwards_add_four_way_swap(scaled_prefix, scaled_single, col_prefix, col_single);
    }
}

// =============================================================================
// Main CT correctness theorem
// =============================================================================
/// Main CT theorem: H_ct(0) = sum_of_scalar_muls(scalars, points).
///
/// Proof by induction on n: peel off last point, apply IH for prefix,
/// use single-point Horner for the last, combine via peel-last lemma.
pub proof fn lemma_straus_ct_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    digits: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        digits.len() == scalars.len(),
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < digits.len() ==> {
                &&& (#[trigger] digits[k]).len() == 64
                &&& radix_16_all_bounded_seq(digits[k])
                &&& reconstruct_radix_16(digits[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_ct_partial(points_affine, digits, 0) == sum_of_scalar_muls(scalars, points_ep),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        // Both sides are identity
        lemma_straus_ct_base(points_affine, digits);
        lemma_straus_ct_zero_points_from(points_affine, digits, 0);
    } else {
        // Inductive case: peel off last point
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
            &&& (#[trigger] digs_prefix[k]).len() == 64
            &&& radix_16_all_bounded_seq(digs_prefix[k])
            &&& reconstruct_radix_16(digs_prefix[k]) == scalar_as_nat(&scalars_prefix[k]) as int
        } by {
            assert(digs_prefix[k] == digits[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH: prefix is correct
        lemma_straus_ct_correct(scalars_prefix, points_prefix, pts_prefix, digs_prefix);

        // Points are canonical (from edwards_point_as_affine)
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            lemma_edwards_point_as_affine_canonical(points_ep[k]);
        }

        // Split: straus_ct_partial(pts, digs, 0) = prefix_result + single_result
        lemma_straus_ct_partial_peel_last(points_affine, digits, 0);

        // Single point Horner = [scalar_last] * P_last
        let P_last = points_affine.last();
        let d_last = digits.last();
        lemma_straus_ct_single(P_last, d_last, 0);
        // straus_ct_partial(seq![P_last], seq![d_last], 0) == [reconstruct_radix_16_from(d_last, 0)] * P_last

        // Connect reconstruct_radix_16_from(d, 0) to reconstruct_radix_16(d)
        lemma_reconstruct_radix_16_from_equals_reconstruct(d_last);
        // So: [reconstruct_radix_16(d_last)] * P_last == [scalar_as_nat(scalars[last])] * P_last

        // Connect signed to unsigned scalar_mul
        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct_radix_16(d_last) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);

        // Now combine: sum_of_scalar_muls(scalars, points_ep) decomposes as
        // edwards_add(sum_of_scalar_muls(prefix), [scalar_last]*P_last)
        // which matches our splitting.
    }
}

/// When n = 0: H_ct(j) = O for all j.
pub proof fn lemma_straus_ct_zero_points_from(pts: Seq<(nat, nat)>, digs: Seq<Seq<i8>>, j: int)
    requires
        pts.len() == 0,
        digs.len() == 0,
        0 <= j <= 64,
    ensures
        straus_ct_partial(pts, digs, j) == edwards_identity(),
    decreases 64 - j,
{
    if j >= 64 {
        lemma_straus_ct_base(pts, digs);
    } else {
        lemma_straus_ct_step(pts, digs, j);
        lemma_straus_ct_zero_points_from(pts, digs, j + 1);
        // straus_ct_partial(pts, digs, j) = [16]*identity + column_sum(pts, digs, j, 0)
        // column_sum(..., 0) = identity
        // [16]*identity = identity (scalar mul of identity)
        lemma_edwards_scalar_mul_identity(16);
        let id = edwards_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

// =============================================================================
// Helper: reconstruct_radix_16_from(d, 0) == reconstruct_radix_16(d) for len-64
// =============================================================================
pub proof fn lemma_reconstruct_radix_16_from_equals_reconstruct(d: Seq<i8>)
    requires
        d.len() == 64,
    ensures
        reconstruct_radix_16_from(d, 0) == reconstruct_radix_16(d),
{
    lemma_reconstruct_radix_16_from_eq_helper(d, 0);
    // Helper gives: reconstruct_radix_16_from(d, 0) == reconstruct_radix_2w(d.subrange(0, 64), 4)
    // Need: d.subrange(0, 64) == d
    assert(d.subrange(0, 64int) =~= d);
    // reconstruct_radix_16(d) == reconstruct_radix_2w(d, 4) by definition
}

proof fn lemma_reconstruct_radix_16_from_eq_helper(d: Seq<i8>, k: int)
    requires
        d.len() == 64,
        0 <= k <= 64,
    ensures
        reconstruct_radix_16_from(d, k) == reconstruct_radix_2w(d.subrange(k, 64int), 4),
    decreases 64 - k,
{
    let sub = d.subrange(k, 64int);
    if k >= 64 {
        assert(sub.len() == 0);
    } else {
        lemma_reconstruct_radix_16_from_eq_helper(d, k + 1);
        let sub_next = d.subrange(k + 1, 64int);
        assert(sub[0] == d[k]);
        assert(sub.len() == (64 - k));
        // Key: sub.skip(1) extensionally equals d.subrange(k+1, 64)
        assert forall|i: int| #![auto] 0 <= i < sub.skip(1).len() implies sub.skip(1)[i]
            == sub_next[i] by {
            assert(sub.skip(1)[i] == sub[i + 1]);
            assert(sub[i + 1] == d[k + 1 + i]);
            assert(sub_next[i] == d[k + 1 + i]);
        }
        assert(sub.skip(1) =~= sub_next);
        assert(pow2(4) == 16) by {
            vstd::arithmetic::power2::lemma2_to64();
        }
    }
}

/// Single-point VT Horner: H_vt(seq![P], seq![naf], i) = [R(naf, i)] * P
/// where R(naf, i) = reconstruct_naf_from(naf, i).
pub proof fn lemma_straus_vt_single(P: (nat, nat), naf: Seq<i8>, i: int)
    requires
        naf.len() == 256,
        P.0 < p(),
        P.1 < p(),
        0 <= i <= 256,
    ensures
        straus_vt_partial(seq![(P)], seq![(naf)], i) == edwards_scalar_mul_signed(
            P,
            reconstruct_naf_from(naf, i),
        ),
    decreases 256 - i,
{
    if i >= 256 {
        lemma_straus_vt_base(seq![(P)], seq![(naf)]);
        reveal(edwards_scalar_mul_signed);
        reveal_with_fuel(edwards_scalar_mul, 1);
    } else {
        lemma_straus_vt_step(seq![(P)], seq![(naf)], i);

        // IH at i+1
        lemma_straus_vt_single(P, naf, i + 1);
        let r_next = reconstruct_naf_from(naf, i + 1);

        // double([r_next]*P) = [2]*([r_next]*P) = [2*r_next]*P
        let prev_result = edwards_scalar_mul_signed(P, r_next);
        lemma_double_is_scalar_mul_2(prev_result);
        lemma_edwards_scalar_mul_signed_composition(P, r_next, 2);

        // column_sum(seq![P], seq![naf], i, 1) = [naf[i]]*P
        lemma_column_sum_single(P, naf, i);

        // [2*r_next]*P + [naf[i]]*P = [2*r_next + naf[i]]*P
        axiom_edwards_scalar_mul_signed_additive(P, 2 * r_next, naf[i] as int);

        // 2*r_next + naf[i] == reconstruct_naf_from(naf, i) by definition
        assert(naf[i] as int + 2 * r_next == reconstruct_naf_from(naf, i));
    }
}

/// VT peel-last: H(pts, nafs, i) = H(pts[..n-1], nafs[..n-1], i) + H(seq![P_n], seq![naf_n], i).
pub proof fn lemma_straus_vt_partial_peel_last(pts: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        pts.len() >= 1,
        nafs.len() == pts.len(),
        0 <= i <= 256,
        forall|k: int| 0 <= k < nafs.len() ==> (#[trigger] nafs[k]).len() == 256,
        forall|k: int| 0 <= k < pts.len() ==> (#[trigger] pts[k]).0 < p() && pts[k].1 < p(),
    ensures
        straus_vt_partial(pts, nafs, i) == ({
            let prefix_result = straus_vt_partial(pts.drop_last(), nafs.drop_last(), i);
            let single_result = straus_vt_partial(seq![(pts.last())], seq![(nafs.last())], i);
            edwards_add(prefix_result.0, prefix_result.1, single_result.0, single_result.1)
        }),
    decreases 256 - i,
{
    let n = pts.len() as int;
    let pts_prefix = pts.drop_last();
    let nafs_prefix = nafs.drop_last();
    let pts_single = seq![(pts.last())];
    let nafs_single = seq![(nafs.last())];

    if i >= 256 {
        lemma_straus_vt_base(pts, nafs);
        lemma_straus_vt_base(pts_prefix, nafs_prefix);
        lemma_straus_vt_base(pts_single, nafs_single);
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(edwards_identity());
    } else {
        lemma_straus_vt_step(pts, nafs, i);
        lemma_straus_vt_step(pts_prefix, nafs_prefix, i);
        lemma_straus_vt_step(pts_single, nafs_single, i);

        // IH at i+1
        lemma_straus_vt_partial_peel_last(pts, nafs, i + 1);

        let prev_full = straus_vt_partial(pts, nafs, i + 1);
        let prev_prefix = straus_vt_partial(pts_prefix, nafs_prefix, i + 1);
        let prev_single = straus_vt_partial(pts_single, nafs_single, i + 1);

        // By IH: prev_full == edwards_add(prev_prefix, prev_single)
        // double(prev_full) == double(edwards_add(prev_prefix, prev_single))
        //                   == edwards_add(double(prev_prefix), double(prev_single))
        lemma_double_distributes(prev_prefix, prev_single);

        let doubled_prefix = edwards_double(prev_prefix.0, prev_prefix.1);
        let doubled_single = edwards_double(prev_single.0, prev_single.1);

        // Column sum splitting (same as CT)
        let col_prefix = straus_column_sum(pts_prefix, nafs_prefix, i, (n - 1));
        let col_single = straus_column_sum(pts_single, nafs_single, i, 1);

        lemma_column_sum_prefix_eq(pts, nafs, pts_prefix, nafs_prefix, i, n - 1);
        lemma_column_sum_single(pts.last(), nafs.last(), i);

        // (A+B) + (C+D) = (A+C) + (B+D)
        lemma_edwards_add_four_way_swap(doubled_prefix, doubled_single, col_prefix, col_single);
    }
}

/// When n = 0: H_vt(i) = O for all i.
pub proof fn lemma_straus_vt_zero_points_from(pts: Seq<(nat, nat)>, nafs: Seq<Seq<i8>>, i: int)
    requires
        pts.len() == 0,
        nafs.len() == 0,
        0 <= i <= 256,
    ensures
        straus_vt_partial(pts, nafs, i) == edwards_identity(),
    decreases 256 - i,
{
    if i >= 256 {
        lemma_straus_vt_base(pts, nafs);
    } else {
        lemma_straus_vt_step(pts, nafs, i);
        lemma_straus_vt_zero_points_from(pts, nafs, i + 1);
        // double(identity) = identity
        lemma_double_identity();
        let id = edwards_identity();
        p_gt_2();
        lemma_edwards_add_identity_right_canonical(id);
    }
}

/// R(naf, 0) = reconstruct(naf) for len-256 NAFs.
pub proof fn lemma_reconstruct_naf_from_equals_reconstruct(naf: Seq<i8>)
    requires
        naf.len() == 256,
    ensures
        reconstruct_naf_from(naf, 0) == reconstruct(naf),
{
    lemma_reconstruct_naf_from_eq_helper(naf, 0);
    assert(naf.subrange(0, 256int) =~= naf);
}

proof fn lemma_reconstruct_naf_from_eq_helper(naf: Seq<i8>, k: int)
    requires
        naf.len() == 256,
        0 <= k <= 256,
    ensures
        reconstruct_naf_from(naf, k) == reconstruct(naf.subrange(k, 256int)),
    decreases 256 - k,
{
    let sub = naf.subrange(k, 256int);
    if k >= 256 {
        assert(sub.len() == 0);
    } else {
        lemma_reconstruct_naf_from_eq_helper(naf, k + 1);
        let sub_next = naf.subrange(k + 1, 256int);
        assert(sub[0] == naf[k]);
        assert(sub.len() == (256 - k));
        assert forall|j: int| #![auto] 0 <= j < sub.skip(1).len() implies sub.skip(1)[j]
            == sub_next[j] by {
            assert(sub.skip(1)[j] == sub[j + 1]);
            assert(sub[j + 1] == naf[k + 1 + j]);
            assert(sub_next[j] == naf[k + 1 + j]);
        }
        assert(sub.skip(1) =~= sub_next);
    }
}

/// Main VT theorem: H_vt(0) = sum_of_scalar_muls(scalars, points).
pub proof fn lemma_straus_vt_correct(
    scalars: Seq<Scalar>,
    points_ep: Seq<EdwardsPoint>,
    points_affine: Seq<(nat, nat)>,
    nafs: Seq<Seq<i8>>,
)
    requires
        scalars.len() == points_ep.len(),
        points_affine.len() == scalars.len(),
        nafs.len() == scalars.len(),
        forall|k: int|
            0 <= k < points_affine.len() ==> #[trigger] points_affine[k] == edwards_point_as_affine(
                points_ep[k],
            ),
        forall|k: int|
            0 <= k < nafs.len() ==> {
                &&& (#[trigger] nafs[k]).len() == 256
                &&& is_valid_naf(nafs[k], 5)
                &&& reconstruct(nafs[k]) == scalar_as_nat(&scalars[k]) as int
            },
    ensures
        straus_vt_partial(points_affine, nafs, 0) == sum_of_scalar_muls(scalars, points_ep),
    decreases scalars.len(),
{
    let n = scalars.len();

    if n == 0 {
        lemma_straus_vt_zero_points_from(points_affine, nafs, 0);
    } else {
        let last = (n - 1) as int;
        let pts_prefix = points_affine.drop_last();
        let nafs_prefix = nafs.drop_last();
        let scalars_prefix = scalars.subrange(0, last);
        let points_prefix = points_ep.subrange(0, last);

        // Preconditions for prefix
        assert forall|k: int| 0 <= k < pts_prefix.len() implies #[trigger] pts_prefix[k]
            == edwards_point_as_affine(points_prefix[k]) by {
            assert(pts_prefix[k] == points_affine[k]);
            assert(points_prefix[k] == points_ep[k]);
        }
        assert forall|k: int| 0 <= k < nafs_prefix.len() implies {
            &&& (#[trigger] nafs_prefix[k]).len() == 256
            &&& is_valid_naf(nafs_prefix[k], 5)
            &&& reconstruct(nafs_prefix[k]) == scalar_as_nat(&scalars_prefix[k]) as int
        } by {
            assert(nafs_prefix[k] == nafs[k]);
            assert(scalars_prefix[k] == scalars[k]);
        }

        // IH
        lemma_straus_vt_correct(scalars_prefix, points_prefix, pts_prefix, nafs_prefix);

        // Points are canonical
        assert forall|k: int| 0 <= k < points_affine.len() implies (#[trigger] points_affine[k]).0
            < p() && points_affine[k].1 < p() by {
            p_gt_2();
        }

        // Split
        lemma_straus_vt_partial_peel_last(points_affine, nafs, 0);

        // Single point Horner = scalar_mul
        let P_last = points_affine.last();
        let naf_last = nafs.last();
        lemma_straus_vt_single(P_last, naf_last, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(naf_last);

        let scalar_nat = scalar_as_nat(&scalars[last]);
        assert(reconstruct(naf_last) == scalar_nat as int);
        reveal(edwards_scalar_mul_signed);
    }
}

} // verus!
