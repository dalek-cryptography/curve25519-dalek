// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>
#![allow(non_snake_case)]

use core::cmp::Ordering;

use crate::backend::serial::curve_models::{ProjectiveNielsPoint, ProjectivePoint};
use crate::constants;
use crate::edwards::EdwardsPoint;
use crate::scalar::Scalar;
use crate::traits::Identity;
use crate::window::NafLookupTable5;

#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::curve_equation_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::straus_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::edwards_lemmas::vartime_double_base_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::scalar_specs::*;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::specs::window_specs::*;

use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Compute \\(aA + bB\\) in variable time, where \\(B\\) is the Ed25519 basepoint.
pub fn mul(a: &Scalar, A: &EdwardsPoint, b: &Scalar) -> (out: EdwardsPoint)
    requires
// Input point must be well-formed

        is_well_formed_edwards_point(*A),
        // Scalars must be canonical (< 2^255) for NAF computation
        scalar_as_nat(a) < pow2(255),
        scalar_as_nat(b) < pow2(255),
    ensures
// Result is a well-formed Edwards point

        is_well_formed_edwards_point(out),
        // Functional correctness: out = a*A + b*B where B is the Ed25519 basepoint
        edwards_point_as_affine(out) == {
            let aA = edwards_scalar_mul(edwards_point_as_affine(*A), scalar_as_nat(a));
            let bB = edwards_scalar_mul(spec_ed25519_basepoint(), scalar_as_nat(b));
            edwards_add(aA.0, aA.1, bB.0, bB.1)
        },
{
    let a_naf = a.non_adjacent_form(5);

    #[cfg(feature = "precomputed-tables")]
    let b_naf = b.non_adjacent_form(8);
    #[cfg(not(feature = "precomputed-tables"))]
    let b_naf = b.non_adjacent_form(5);

    let ghost A_affine = edwards_point_as_affine(*A);
    let bp_for_proof = constants::ED25519_BASEPOINT_POINT;
    let ghost B_affine = spec_ed25519_basepoint();
    let ghost pts_affine = seq![A_affine, B_affine];
    let ghost nafs = seq![a_naf@, b_naf@];

    // Find starting index
    let mut i: usize = 255;
    /* <ORIGINAL CODE>
    for j in (0..256).rev() {
        i = j;
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break;
        }
    }
    </ORIGINAL CODE> */
    // VERIFICATION NOTE: Verus doesn't support for-loops over Rev<Range<_>>
    // This loop checks indices 255, 254, ..., 1, 0 (inclusive) to match original behavior.
    loop
        invariant
            i <= 255,
            a_naf@.len() == 256,
            b_naf@.len() == 256,
            forall|j: int| 0 <= j < 256 ==> (j <= i as int || (a_naf@[j] == 0 && b_naf@[j] == 0)),
        decreases i + 1,  // +1 accounts for the final iteration at i == 0

    {
        if a_naf[i] != 0 || b_naf[i] != 0 {
            break ;
        }
        proof {
            assert(a_naf@[i as int] == 0);
            assert(b_naf@[i as int] == 0);
        }
        if i == 0 {
            break ;  // Checked index 0, now exit
        }
        let old_i = i;
        i -= 1;
        proof {
            assert(i as int + 1 == old_i as int);
            assert forall|j: int| 0 <= j < 256 implies (j <= (i as int) || (a_naf@[j] == 0
                && b_naf@[j] == 0)) by {
                if j <= (i as int) {
                } else if j == old_i as int {
                    assert(a_naf@[j] == 0);
                    assert(b_naf@[j] == 0);
                } else {
                    assert((old_i as int) < j);
                    assert(j < 256);
                }
            }
        }
    }

    let table_A = NafLookupTable5::<ProjectiveNielsPoint>::from(A);
    #[cfg(feature = "precomputed-tables")]
    let table_B = &constants::AFFINE_ODD_MULTIPLES_OF_BASEPOINT;
    #[cfg(not(feature = "precomputed-tables"))]
    let table_B = &NafLookupTable5::<ProjectiveNielsPoint>::from(
        &constants::ED25519_BASEPOINT_POINT,
    );

    let mut r = ProjectivePoint::identity();
    proof {
        lemma_identity_projective_point_properties();
        lemma_edwards_point_as_affine_canonical(*A);
        lemma_edwards_point_as_affine_canonical(bp_for_proof);
        assert(A_affine == edwards_point_as_affine(*A));
        assert(B_affine == edwards_point_as_affine(bp_for_proof));
        assert(pts_affine.len() == 2);
        assert(pts_affine[0] == A_affine);
        assert(pts_affine[1] == B_affine);
        assert(edwards_point_as_affine(bp_for_proof) == B_affine);
        #[cfg(feature = "precomputed-tables")]
        {
            axiom_affine_odd_multiples_of_basepoint_valid();
        }
        assert(nafs.len() == 2);
        assert(nafs[0] == a_naf@);
        assert(nafs[1] == b_naf@);
        assert(vartime_double_base_shared_input_valid(
            A_affine,
            B_affine,
            pts_affine,
            a_naf@,
            b_naf@,
            nafs,
            table_A.0,
            *A,
            bp_for_proof,
        ));
        assert forall|k: int, j: int|
            0 <= k < nafs.len() && (i as int) < j && j < 256 implies #[trigger] nafs[k][j] == 0 by {
            assert(0 <= j < 256);
            assert(j <= i as int || (a_naf@[j] == 0 && b_naf@[j] == 0));
            assert(!(j <= i as int));
            assert(a_naf@[j] == 0 && b_naf@[j] == 0);
            if k == 0 {
                assert(nafs[k] == a_naf@);
            } else {
                assert(k == 1);
                assert(nafs[k] == b_naf@);
            }
        }
        lemma_straus_vt_zero_suffix(pts_affine, nafs, i as int);
        assert(projective_point_as_affine_edwards(r) == edwards_identity());
        assert(projective_point_as_affine_edwards(r) == straus_vt_partial(
            pts_affine,
            nafs,
            i as int + 1,
        ));
    }

    loop
        invariant_except_break
            i <= 255,
            is_valid_projective_point(r),
            fe51_limbs_bounded(&r.X, 52),
            fe51_limbs_bounded(&r.Y, 52),
            fe51_limbs_bounded(&r.Z, 52),
            sum_of_limbs_bounded(&r.X, &r.Y, u64::MAX),
            vartime_double_base_shared_input_valid(
                A_affine,
                B_affine,
                pts_affine,
                a_naf@,
                b_naf@,
                nafs,
                table_A.0,
                *A,
                bp_for_proof,
            ),
            #[cfg(feature = "precomputed-tables")]
            naf_lookup_table8_affine_limbs_bounded(table_B.0),
            #[cfg(feature = "precomputed-tables")]
            is_valid_naf_lookup_table8_affine_coords(table_B.0, B_affine),
            #[cfg(feature = "precomputed-tables")]
            forall|j: int|
                0 <= j < 64 ==> is_valid_affine_niels_point(#[trigger] table_B.0[j]),
            #[cfg(not(feature = "precomputed-tables"))]
            naf_lookup_table5_projective_limbs_bounded(table_B.0),
            #[cfg(not(feature = "precomputed-tables"))]
            is_valid_naf_lookup_table5_projective(table_B.0, bp_for_proof),
            #[cfg(not(feature = "precomputed-tables"))]
            forall|j: int|
                0 <= j < 8 ==> is_valid_projective_niels_point(#[trigger] table_B.0[j]),
            projective_point_as_affine_edwards(r) == straus_vt_partial(
                pts_affine,
                nafs,
                i as int + 1,
            ),
        ensures
            is_valid_projective_point(r),
            fe51_limbs_bounded(&r.X, 52),
            fe51_limbs_bounded(&r.Y, 52),
            fe51_limbs_bounded(&r.Z, 52),
            sum_of_limbs_bounded(&r.X, &r.Y, u64::MAX),
            projective_point_as_affine_edwards(r) == straus_vt_partial(pts_affine, nafs, 0),
        decreases i,
    {
        let ghost old_i = i as int;
        let ghost prev_partial = straus_vt_partial(pts_affine, nafs, old_i + 1);
        let mut t = r.double();
        let ghost doubled_affine = completed_point_as_affine_edwards(t);
        let ghost col_a = straus_column_sum(pts_affine, nafs, old_i, 1);

        proof {
            p_gt_2();
            lemma_edwards_add_identity_right_canonical(doubled_affine);
            assert(doubled_affine == edwards_double(prev_partial.0, prev_partial.1));
        }

        match a_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = a_naf@[old_i];
                    assert(1 <= digit && digit <= 15 && (digit as int) % 2 != 0) by {
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions(digit);
                }
                /* ORIGINAL CODE:
                t = &t.as_extended() + &table_A.select(a_naf[i] as usize)
                */
                let selected_A = table_A.select(a_naf[i] as usize);
                let t_ext = t.as_extended();
                t = &t_ext + &selected_A;
                proof {
                    let digit = a_naf@[old_i];
                    let term_a = edwards_scalar_mul_signed(A_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_A) == term_a) by {
                        assert(A_affine == edwards_point_as_affine(*A));
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_A.0,
                            digit,
                            selected_A,
                            edwards_point_as_affine(*A),
                            true,
                        );
                    }
                    assert(pts_affine.len() >= 1);
                    assert(nafs.len() >= 1);
                    lemma_vartime_double_base_col_a(pts_affine, nafs, A_affine, a_naf@, old_i);
                    assert(col_a == term_a);
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_a.0,
                        col_a.1,
                    ));
                }
            },
            Ordering::Less => {
                proof {
                    let digit = a_naf@[old_i];
                    assert(-15 <= digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions(digit);
                }
                /* ORIGINAL CODE:
                t = &t.as_extended() - &table_A.select((-a_naf[i]) as usize)
                */
                let selected_A = table_A.select((-a_naf[i]) as usize);
                let t_ext = t.as_extended();
                t = &t_ext - &selected_A;
                proof {
                    let digit = a_naf@[old_i];
                    let abs_digit = (-digit) as i8;
                    let term_a = edwards_scalar_mul_signed(A_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_A)
                        == edwards_scalar_mul_signed(A_affine, abs_digit as int)) by {
                        assert(A_affine == edwards_point_as_affine(*A));
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_A.0,
                            abs_digit,
                            selected_A,
                            edwards_point_as_affine(*A),
                            true,
                        );
                    }
                    assert(term_a == edwards_neg(
                        projective_niels_point_as_affine_edwards(selected_A),
                    )) by {
                        lemma_neg_of_signed_scalar_mul(A_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    assert(pts_affine.len() >= 1);
                    assert(nafs.len() >= 1);
                    lemma_vartime_double_base_col_a(pts_affine, nafs, A_affine, a_naf@, old_i);
                    assert(col_a == term_a);
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_a.0,
                        col_a.1,
                    ));
                }
            },
            Ordering::Equal => {
                proof {
                    lemma_column_sum_canonical(pts_affine, nafs, old_i, 0);
                    lemma_column_sum_step_zero_digit(pts_affine, nafs, old_i, 0);
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_a.0,
                        col_a.1,
                    )) by {
                        lemma_edwards_add_identity_right_canonical(doubled_affine);
                    }
                }
            },
        }

        proof {
            assert(vartime_double_base_shared_input_valid(
                A_affine,
                B_affine,
                pts_affine,
                a_naf@,
                b_naf@,
                nafs,
                table_A.0,
                *A,
                bp_for_proof,
            ));
        }

        let ghost col_ab = straus_column_sum(pts_affine, nafs, old_i, 2);

        // VERIFICATION NOTE: the control flow below is duplicated across cfg branches.
        // The executable step matches the original code:
        //
        //     match b_naf[i].cmp(&0) {
        //         Ordering::Greater => t = &t.as_extended() + &table_B.select(b_naf[i] as usize),
        //         Ordering::Less => t = &t.as_extended() - &table_B.select((-b_naf[i]) as usize),
        //         Ordering::Equal => {}
        //     }
        //
        // We verify separate copies because the proof obligations differ substantially
        // between the `precomputed-tables` and non-precomputed cases, even though the
        // runtime behavior is intended to be the same.
        #[cfg(feature = "precomputed-tables")]
        match b_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = b_naf@[old_i];
                    assert(1 <= digit && digit < 128 && (digit as int) % 2 != 0) by {
                        assert(pow2(7) == 128) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions_width8(digit);
                }
                /* ORIGINAL CODE:
                t = &t.as_extended() + &table_B.select(b_naf[i] as usize)
                */
                let selected_B = table_B.select(b_naf[i] as usize);
                let t_ext = t.as_extended();
                proof {
                    lemma_unfold_edwards(t_ext);
                    assert(sum_of_limbs_bounded(&t_ext.Z, &t_ext.Z, u64::MAX)) by {
                        crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded(
                        &t_ext.Z, &t_ext.Z, 52);
                    }
                    assert(edwards_z_sum_bounded(t_ext));
                    assert(is_valid_affine_niels_point(selected_B));
                }
                t = &t_ext + &selected_B;
                proof {
                    let digit = b_naf@[old_i];
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(affine_niels_point_as_affine_edwards(selected_B) == term_b) by {
                        lemma_naf_select_is_signed_scalar_mul_affine8(
                            table_B.0,
                            digit,
                            selected_B,
                            B_affine,
                        );
                    }
                    lemma_vartime_double_base_col_ab(pts_affine, nafs, B_affine, b_naf@, old_i);
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1));
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Less => {
                proof {
                    let digit = b_naf@[old_i];
                    assert(-128 < digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(pow2(7) == 128) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions_width8(digit);
                }
                /* ORIGINAL CODE:
                t = &t.as_extended() - &table_B.select((-b_naf[i]) as usize)
                */
                let selected_B = table_B.select((-b_naf[i]) as usize);
                let t_ext = t.as_extended();
                proof {
                    lemma_unfold_edwards(t_ext);
                    assert(sum_of_limbs_bounded(&t_ext.Z, &t_ext.Z, u64::MAX)) by {
                        crate::lemmas::field_lemmas::add_lemmas::lemma_sum_of_limbs_bounded_from_fe51_bounded(
                        &t_ext.Z, &t_ext.Z, 52);
                    }
                    assert(edwards_z_sum_bounded(t_ext));
                    assert(is_valid_affine_niels_point(selected_B));
                }
                t = &t_ext - &selected_B;
                proof {
                    let digit = b_naf@[old_i];
                    let abs_digit = (-digit) as i8;
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(affine_niels_point_as_affine_edwards(selected_B)
                        == edwards_scalar_mul_signed(B_affine, abs_digit as int)) by {
                        lemma_naf_select_is_signed_scalar_mul_affine8(
                            table_B.0,
                            abs_digit,
                            selected_B,
                            B_affine,
                        );
                    }
                    assert(term_b == edwards_neg(affine_niels_point_as_affine_edwards(selected_B)))
                        by {
                        lemma_neg_of_signed_scalar_mul(B_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    lemma_vartime_double_base_col_ab(pts_affine, nafs, B_affine, b_naf@, old_i);
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1));
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Equal => {
                proof {
                    lemma_column_sum_canonical(pts_affine, nafs, old_i, 1);
                    lemma_column_sum_step_zero_digit(pts_affine, nafs, old_i, 1);
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        assert(col_ab == col_a);
                    }
                }
            },
        }

        #[cfg(not(feature = "precomputed-tables"))]
        match b_naf[i].cmp(&0) {
            Ordering::Greater => {
                proof {
                    let digit = b_naf@[old_i];
                    assert(1 <= digit && digit <= 15 && (digit as int) % 2 != 0) by {
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_positive_select_preconditions(digit);
                }
                /* ORIGINAL CODE: t = &t.as_extended() + &table_B.select(b_naf[i] as usize) */
                let selected_B = table_B.select(b_naf[i] as usize);
                let t_ext = t.as_extended();
                proof {
                    assert(is_well_formed_edwards_point(t_ext));
                    assert(is_valid_projective_niels_point(selected_B));
                }
                t = &t_ext + &selected_B;
                proof {
                    let digit = b_naf@[old_i];
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_B) == term_b) by {
                        assert(edwards_point_as_affine(bp_for_proof) == B_affine);
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_B.0,
                            digit,
                            selected_B,
                            edwards_point_as_affine(bp_for_proof),
                            true,
                        );
                    }
                    assert(pts_affine.len() >= 2);
                    assert(nafs.len() >= 2);
                    lemma_vartime_double_base_col_ab(pts_affine, nafs, B_affine, b_naf@, old_i);
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1));
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Less => {
                proof {
                    let digit = b_naf@[old_i];
                    assert(-15 <= digit && digit <= -1 && (digit as int) % 2 != 0) by {
                        assert(pow2(4) == 16) by {
                            lemma2_to64();
                        }
                    }
                    lemma_naf_digit_negative_select_preconditions(digit);
                }
                /* ORIGINAL CODE: t = &t.as_extended() - &table_B.select((-b_naf[i]) as usize) */
                let selected_B = table_B.select((-b_naf[i]) as usize);
                let t_ext = t.as_extended();
                proof {
                    assert(is_well_formed_edwards_point(t_ext));
                    assert(is_valid_projective_niels_point(selected_B));
                }
                t = &t_ext - &selected_B;
                proof {
                    let digit = b_naf@[old_i];
                    let abs_digit = (-digit) as i8;
                    let term_b = edwards_scalar_mul_signed(B_affine, digit as int);
                    assert(projective_niels_point_as_affine_edwards(selected_B)
                        == edwards_scalar_mul_signed(B_affine, abs_digit as int)) by {
                        assert(edwards_point_as_affine(bp_for_proof) == B_affine);
                        lemma_naf_select_is_signed_scalar_mul_projective(
                            table_B.0,
                            abs_digit,
                            selected_B,
                            edwards_point_as_affine(bp_for_proof),
                            true,
                        );
                    }
                    assert(term_b == edwards_neg(
                        projective_niels_point_as_affine_edwards(selected_B),
                    )) by {
                        lemma_neg_of_signed_scalar_mul(B_affine, abs_digit as int);
                        assert(digit as int == -(abs_digit as int));
                    }
                    assert(pts_affine.len() >= 2);
                    assert(nafs.len() >= 2);
                    lemma_vartime_double_base_col_ab(pts_affine, nafs, B_affine, b_naf@, old_i);
                    assert(col_ab == edwards_add(col_a.0, col_a.1, term_b.0, term_b.1));
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        axiom_edwards_add_associative(
                            doubled_affine.0,
                            doubled_affine.1,
                            col_a.0,
                            col_a.1,
                            term_b.0,
                            term_b.1,
                        );
                    }
                }
            },
            Ordering::Equal => {
                proof {
                    lemma_column_sum_canonical(pts_affine, nafs, old_i, 1);
                    lemma_column_sum_step_zero_digit(pts_affine, nafs, old_i, 1);
                    assert(completed_point_as_affine_edwards(t) == edwards_add(
                        doubled_affine.0,
                        doubled_affine.1,
                        col_ab.0,
                        col_ab.1,
                    )) by {
                        assert(col_ab == col_a);
                    }
                }
            },
        }
        r = t.as_projective();
        proof {
            lemma_straus_vt_step(pts_affine, nafs, old_i);
            assert(projective_point_as_affine_edwards(r) == completed_point_as_affine_edwards(t));
            assert(projective_point_as_affine_edwards(r) == straus_vt_partial(
                pts_affine,
                nafs,
                old_i,
            ));
        }

        if i == 0 {
            proof {
                assert(projective_point_as_affine_edwards(r) == straus_vt_partial(
                    pts_affine,
                    nafs,
                    0,
                ));
            }
            break ;
        }
        i -= 1;
        proof {
            assert(i as int + 1 == old_i);
        }
    }

    proof {
        lemma_fe51_limbs_bounded_weaken(&r.X, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&r.Y, 52, 54);
        lemma_fe51_limbs_bounded_weaken(&r.Z, 52, 54);
    }
    let result = r.as_extended();
    proof {
        assert(reconstruct(a_naf@) == scalar_as_nat(a) as int);
        assert(reconstruct(b_naf@) == scalar_as_nat(b) as int);
        lemma_straus_vt_partial_peel_last(pts_affine, nafs, 0);
        assert(pts_affine.drop_last() == seq![A_affine]);
        assert(nafs.drop_last() == seq![a_naf@]);
        assert(pts_affine.last() == B_affine);
        assert(nafs.last() == b_naf@);
        lemma_straus_vt_single(A_affine, a_naf@, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(a_naf@);
        lemma_straus_vt_single(B_affine, b_naf@, 0);
        lemma_reconstruct_naf_from_equals_reconstruct(b_naf@);
        assert(edwards_scalar_mul_signed(A_affine, scalar_as_nat(a) as int) == edwards_scalar_mul(
            A_affine,
            scalar_as_nat(a),
        )) by {
            reveal(edwards_scalar_mul_signed);
        }
        assert(edwards_scalar_mul_signed(B_affine, scalar_as_nat(b) as int) == edwards_scalar_mul(
            B_affine,
            scalar_as_nat(b),
        )) by {
            reveal(edwards_scalar_mul_signed);
        }
        assert(edwards_point_as_affine(result) == projective_point_as_affine_edwards(r));
        assert(projective_point_as_affine_edwards(r) == straus_vt_partial(pts_affine, nafs, 0));
        assert(straus_vt_partial(seq![A_affine], seq![a_naf@], 0) == edwards_scalar_mul_signed(
            A_affine,
            scalar_as_nat(a) as int,
        ));
        assert(straus_vt_partial(seq![B_affine], seq![b_naf@], 0) == edwards_scalar_mul_signed(
            B_affine,
            scalar_as_nat(b) as int,
        ));
        assert(straus_vt_partial(pts_affine, nafs, 0) == edwards_add(
            edwards_scalar_mul(A_affine, scalar_as_nat(a)).0,
            edwards_scalar_mul(A_affine, scalar_as_nat(a)).1,
            edwards_scalar_mul(B_affine, scalar_as_nat(b)).0,
            edwards_scalar_mul(B_affine, scalar_as_nat(b)).1,
        ));
        assert(edwards_point_as_affine(result) == edwards_add(
            edwards_scalar_mul(A_affine, scalar_as_nat(a)).0,
            edwards_scalar_mul(A_affine, scalar_as_nat(a)).1,
            edwards_scalar_mul(B_affine, scalar_as_nat(b)).0,
            edwards_scalar_mul(B_affine, scalar_as_nat(b)).1,
        ));
        assert(is_well_formed_edwards_point(result));
    }
    result
}

} // verus!
