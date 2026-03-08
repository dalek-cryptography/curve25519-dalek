//! Defines additional methods on `RistrettoPoint` for Lizard.
//!
//! For the reference mathematical intent of the encoding/decoding scheme, see
//! `crate::specs::lizard_specs`.
#![allow(non_snake_case)]

use digest::generic_array::typenum::U32;
use digest::Digest;

use crate::constants;
use crate::field::FieldElement;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

#[allow(unused_imports)]
use crate::backend::serial::u64::subtle_assumes::{
    choice_and, choice_or, conditional_assign_generic, ct_eq_bytes32, negate_field_element,
    select_u8,
};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::core_assumes::axiom_sha256_output_length;
use crate::core_assumes::{bytes32_8_to_24, sha256_hash_bytes, write_bytes32_8_to_24};

use crate::edwards::EdwardsPoint;

use super::jacobi_quartic::JacobiPoint;
use super::lizard_constants;

use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use core::prelude::*;

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::specs::edwards_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs::*;
#[allow(unused_imports)]
use crate::specs::field_specs_u64::*;
#[allow(unused_imports)]
use crate::specs::lizard_specs::*;
#[allow(unused_imports)]
use crate::specs::ristretto_specs::*;

#[allow(unused_imports)]
use crate::lemmas::field_lemmas::add_lemmas::*;

#[allow(unused_imports)]
use crate::lemmas::field_lemmas::from_bytes_lemmas::*;

verus! {

impl RistrettoPoint {
    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    pub fn from_uniform_bytes_single_elligator(bytes: &[u8; 32]) -> (result: RistrettoPoint)
        ensures
    // Well-formedness: result is a valid Edwards point in the even subgroup

            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            // Correctness: affine coordinates match spec-level Elligator on the input bytes
            edwards_point_as_affine(result.0) == spec_elligator_ristretto_flavor(
                fe51_as_canonical_nat(&spec_fe51_from_bytes(bytes)),
            ),
    {
        /* ORIGINAL CODE: RistrettoPoint::elligator_ristretto_flavor(&FieldElement::from_bytes(bytes)) */
        let fe = FieldElement::from_bytes(bytes);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let result = RistrettoPoint::elligator_ristretto_flavor(&fe);
        proof {
            let fe_spec = spec_fe51_from_bytes(bytes);
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(&fe_spec)) by {
                lemma_from_u8_32_as_nat(bytes);
                lemma_as_nat_32_mod_255(bytes);
            }
            assert(spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe))
                == spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe_spec)));
        }
        result
    }

    /// Encode 16 bytes of data to a RistrettoPoint, using the Lizard method
    ///
    /// VERIFICATION NOTE: the implementation uses Digest, unsupported by Verus.
    /// We verify below a refactored implementation that uses SHA256 provided via
    /// an external_body specification.
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    pub fn lizard_encode<D: Digest>(data: &[u8; 16]) -> RistrettoPoint where
        D: Digest<OutputSize = U32>,
     {
        let mut fe_bytes: [u8; 32] = Default::default();

        let digest = D::digest(data);
        fe_bytes[0..32].copy_from_slice(digest.as_slice());
        fe_bytes[8..24].copy_from_slice(data);
        fe_bytes[0] &= 254;  // make positive since Elligator on r and -r is the same
        fe_bytes[31] &= 63;
        let fe = FieldElement::from_bytes(&fe_bytes);
        RistrettoPoint::elligator_ristretto_flavor(&fe)
    }

    /// Verus-friendly variant of `lizard_encode::<Sha256>`.
    ///
    pub fn lizard_encode_verus(data: &[u8; 16]) -> (result: RistrettoPoint)
        ensures
            is_well_formed_edwards_point(result.0),
            is_in_even_subgroup(result.0),
            edwards_point_as_affine(result.0) == spec_lizard_encode(data@),
    {
        /* ORIGINAL CODE: let mut fe_bytes: [u8; 32] = Default::default(); */
        let mut fe_bytes: [u8; 32] = [0u8;32];
        /* ORIGINAL CODE: let digest = D::digest(data); */
        let digest: [u8; 32] = sha256_hash_bytes(data);
        /* ORIGINAL CODE: fe_bytes[0..32].copy_from_slice(digest.as_slice()); */
        fe_bytes = digest;
        /* ORIGINAL CODE: fe_bytes[8..24].copy_from_slice(data); */
        write_bytes32_8_to_24(&mut fe_bytes, data);

        fe_bytes[0] &= 254;  // make positive since Elligator on r and -r is the same
        fe_bytes[31] &= 63;

        let fe = FieldElement::from_bytes(&fe_bytes);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let result = RistrettoPoint::elligator_ristretto_flavor(&fe);
        proof {
            // elligator postcondition gives:
            //   edwards_point_as_affine(result.0)
            //     == spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe))
            // We need: fe51_as_canonical_nat(&fe) == lizard_r(&lizard_fe_bytes(data@))
            // Step 1: Connect exec from_bytes to spec from_bytes on fe_bytes
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(
                &spec_fe51_from_bytes(&fe_bytes),
            )) by {
                lemma_from_u8_32_as_nat(&fe_bytes);
                lemma_as_nat_32_mod_255(&fe_bytes);
            };

            // Step 2: Show fe_bytes matches lizard_fe_bytes(data@) pointwise
            axiom_sha256_output_length(data@);
            let spec_bytes = lizard_fe_bytes(data@);
            assert(fe_bytes@ =~= spec_bytes@);
        }
        result
    }

    /// Decode 16 bytes of data from a RistrettoPoint, using the Lizard method
    ///
    /// VERIFICATION NOTE: the implementation uses Digest, unsupported by Verus.
    /// We verify below a refactored implementation that uses SHA256 provided via
    /// an external_body specification.
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    pub fn lizard_decode<D: Digest>(&self) -> Option<[u8; 16]> where D: Digest<OutputSize = U32> {
        let mut result: [u8; 16] = Default::default();
        let mut h: [u8; 32] = Default::default();
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();
        let mut n_found = 0;
        /* ORIGINAL CODE: for (j, fe_j) in fes.iter().enumerate() {
           Verus cannot compile .enumerate() even with verifier::external. */
        for j in 0..8 {
            let fe_j = &fes[j];
            let mut ok = Choice::from((mask >> j) & 1);
            let buf2 = fe_j.as_bytes();  // array
            h.copy_from_slice(&D::digest(&buf2[8..24]));  // array
            h[8..24].copy_from_slice(&buf2[8..24]);
            h[0] &= 254;
            h[31] &= 63;
            ok &= h.ct_eq(&buf2);
            for i in 0..16 {
                result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok);
            }
            n_found += ok.unwrap_u8();
        }
        if n_found == 1 {
            Some(result)
        } else {
            None
        }
    }

    /// Verus-friendly variant of `lizard_decode::<Sha256>`.
    ///
    pub fn lizard_decode_verus(&self) -> (result: Option<[u8; 16]>)
        requires
            is_well_formed_edwards_point(self.0),
        ensures
            match result {
                Some(bytes) => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    // Correctness: exec result matches Ristretto-level spec decode
                    spec_lizard_decode_ristretto(x, y) == Some(
                        bytes@,
                    )
                    // Soundness: encode(bytes) lands in the coset of self
                     && is_lizard_preimage_coset(bytes@, ristretto_coset_affine(x, y))
                }),
                None => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    spec_lizard_decode_ristretto(x, y).is_None()
                }),
            },
    {
        /* ORIGINAL CODE: let mut result: [u8; 16] = Default::default(); */
        let mut result: [u8; 16] = [0u8;16];
        /* ORIGINAL CODE: let mut h: [u8; 32] = Default::default(); */
        let mut h: [u8; 32] = [0u8;32];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        let mut n_found: u32 = 0;
        /* ORIGINAL CODE: for (j, fe_j) in fes.iter().enumerate() { */
        for j in 0..8
            invariant
                n_found <= j as u32,
        {
            let mut ok = Choice::from((mask >> j) & 1);
            /* ORIGINAL CODE:
            let buf2 = fe_j.as_bytes(); */
            let buf2 = fes[j].as_bytes();  // array
            /* ORIGINAL CODE:
            h.copy_from_slice(&D::digest(&buf2[8..24])); */
            let msg: [u8; 16] = bytes32_8_to_24(&buf2);
            h = sha256_hash_bytes(&msg);  // array
            /* ORIGINAL CODE:
            h[8..24].copy_from_slice(&buf2[8..24]); */
            write_bytes32_8_to_24(&mut h, &msg);  // array
            h[0] &= 254;
            h[31] &= 63;
            /* ORIGINAL CODE: ok &= h.ct_eq(&buf2); */
            ok = choice_and(ok, ct_eq_bytes32(&h, &buf2));
            /* ORIGINAL CODE: result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok); */
            for i in 0..16 {
                result[i] = select_u8(&result[i], &buf2[8 + i], ok);
            }
            /* ORIGINAL CODE: n_found += ok.unwrap_u8() as u32; */
            let add: u32 = ok.unwrap_u8() as u32;
            n_found = n_found + add;
        }

        let result = if n_found == 1 {
            Some(result)
        } else {
            None
        };
        proof {
            // PROOF BYPASS: Full decode correctness requires:
            // 1. Exhaustiveness: elligator_ristretto_flavor_inverse returns ALL
            //    field elements mapping to the coset (depends on to_jacobi_quartic_ristretto)
            // 2. Uniqueness: the SHA-256 consistency check matches exactly one
            //    candidate when spec_lizard_decode_ristretto returns Some (depends on
            //    spec_sha256 being collision-resistant for the Lizard byte layout)
            // 3. Soundness: successful decode implies re-encoding maps to a coset
            //    member (follows from the above once Elligator roundtrip is proved)
            assert(match result {
                Some(bytes) => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    spec_lizard_decode_ristretto(x, y) == Some(bytes@) && is_lizard_preimage_coset(
                        bytes@,
                        ristretto_coset_affine(x, y),
                    )
                }),
                None => ({
                    let (x, y) = edwards_point_as_affine(self.0);
                    spec_lizard_decode_ristretto(x, y).is_None()
                }),
            }) by {
                admit();
            };
        }
        result
    }

    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    pub fn encode_253_bits(data: &[u8; 32]) -> (result: Option<RistrettoPoint>)
        ensures
            match result {
                Some(
                    p,
                ) =>
                // Well-formedness: result is a valid Edwards point in the even subgroup
                is_well_formed_edwards_point(p.0) && is_in_even_subgroup(
                    p.0,
                )
                // Correctness: affine coordinates match spec-level Elligator on the input bytes
                 && edwards_point_as_affine(p.0) == spec_elligator_ristretto_flavor(
                    fe51_as_canonical_nat(&spec_fe51_from_bytes(data)),
                ),
                // Always succeeds for valid 32-byte input
                None => false,
            },
    {
        if data.len() != 32 {
            return None;
        }
        let fe = FieldElement::from_bytes(data);
        proof {
            lemma_fe51_limbs_bounded_weaken(&fe, 51, 54);
        }
        let p = RistrettoPoint::elligator_ristretto_flavor(&fe);
        let result = Some(p);
        proof {
            let fe_spec = spec_fe51_from_bytes(data);
            assert(fe51_as_canonical_nat(&fe) == fe51_as_canonical_nat(&fe_spec)) by {
                lemma_from_u8_32_as_nat(data);
                lemma_as_nat_32_mod_255(data);
            }
            assert(spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe))
                == spec_elligator_ristretto_flavor(fe51_as_canonical_nat(&fe_spec)));
        }
        result
    }

    /// Directly decode a RistrettoPoint as 253 bits, using Elligator
    ///
    /// Elligator inversion: compute up to 8 field-element preimages of a Ristretto point.
    /// Returns `(mask, candidates)` where bit `j` of `mask` is set iff
    /// `Elligator(candidates[j])` equals `self`.  Used by `lizard_decode_verus`
    /// to find which candidate (if any) has the Lizard `b(m)` structure.
    pub fn decode_253_bits(&self) -> (result: (u8, [[u8; 32]; 8]))
        requires
            is_well_formed_edwards_point(self.0),
        ensures
    // Elligator inversion: each valid candidate maps forward to a coset member of self

            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|j: int|
                    #![trigger result.1[j]]
                    0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(
                            fe51_as_canonical_nat(&spec_fe51_from_bytes(&result.1[j])),
                        );
                        ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
                    })
            }),
    {
        let mut ret = [[0u8;32];8];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        for j in 0..8 {
            ret[j] = fes[j].as_bytes();
        }
        proof {
            // PROOF BYPASS: connecting as_bytes + spec_fe51_from_bytes roundtrip
            // to the Elligator inversion property from
            // elligator_ristretto_flavor_inverse. Requires proving that
            // as_bytes/from_bytes is a roundtrip for canonical field elements.
            admit();
        }
        (mask, ret)
    }

    /// Return the coset self + E[4], for debugging.
    pub fn xcoset4(&self) -> (result: [EdwardsPoint; 4])
        requires
            is_well_formed_edwards_point(self.0),
        ensures
    // Well-formedness: all four coset elements are valid Edwards points

            is_well_formed_edwards_point(result[0]),
            is_well_formed_edwards_point(result[1]),
            is_well_formed_edwards_point(result[2]),
            is_well_formed_edwards_point(result[3]),
            // Identity: first element is self
            result[0] == self.0,
            // Correctness: remaining elements are self + T_{2,4,6} (order-4 torsion points)
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                edwards_point_as_affine(result[1]) == coset[1] && edwards_point_as_affine(result[2])
                    == coset[2] && edwards_point_as_affine(result[3]) == coset[3]
            }),
    {
        /* ORIGINAL CODE: [self.0, self.0 + constants::EIGHT_TORSION[2], self.0 + constants::EIGHT_TORSION[4], self.0 + constants::EIGHT_TORSION[6]] */
        let t2 = constants::EIGHT_TORSION[2];
        let t4 = constants::EIGHT_TORSION[4];
        let t6 = constants::EIGHT_TORSION[6];
        proof {
            use_type_invariant(t2);
            use_type_invariant(t4);
            use_type_invariant(t6);
            assert(is_well_formed_edwards_point(t2)) by {
                lemma_unfold_edwards(t2);
            }
            assert(is_well_formed_edwards_point(t4)) by {
                lemma_unfold_edwards(t4);
            }
            assert(is_well_formed_edwards_point(t6)) by {
                lemma_unfold_edwards(t6);
            }
        }
        let result = [self.0, &self.0 + &t2, &self.0 + &t4, &self.0 + &t6];
        result
    }

    /// Computes the at most 8 positive FieldElements f such that
    /// self == elligator_ristretto_flavor(f).
    /// Assumes self is even.
    ///
    /// Returns a bitmask of which elements in fes are set.
    pub fn elligator_ristretto_flavor_inverse(&self) -> (result: (u8, [FieldElement; 8]))
        requires
            is_well_formed_edwards_point(self.0),
        ensures
    // Representation: all 8 field elements have bounded limbs

            forall|j: int| 0 <= j < 8 ==> #[trigger] fe51_limbs_bounded(&result.1[j], 54),
            // Elligator inversion: each valid candidate maps forward to a coset
            // member of self (not necessarily self.0 itself, since candidates come
            // from all 4 coset representatives via to_jacobi_quartic_ristretto)
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|j: int|
                    #![trigger result.1[j]]
                    0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(
                            fe51_as_canonical_nat(&result.1[j]),
                        );
                        ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
                    })
            }),
    {
        // Elligator2 computes a Point from a FieldElement in two steps: first
        // it computes a (s,t) on the Jacobi quartic and then computes the
        // corresponding even point on the Edwards curve.
        //
        // We invert in three steps.  Any Ristretto point has four representatives
        // as even Edwards points.  For each of those even Edwards points,
        // there are two points on the Jacobi quartic that map to it.
        // Each of those eight points on the Jacobi quartic might have an
        // Elligator2 preimage.
        //
        // Essentially we first loop over the four representatives of our point,
        // then for each of them consider both points on the Jacobi quartic and
        // check whether they have an inverse under Elligator2.  We take the
        // following shortcut though.
        //
        // We can compute two Jacobi quartic points for (x,y) and (-x,-y)
        // at the same time.  The four Jacobi quartic points are two of
        // such pairs.
        let mut mask: u8 = 0;
        let jcs = self.to_jacobi_quartic_ristretto();
        let mut ret = [FieldElement::ONE;8];

        for i in 0..4 {
            // Limb bounds from to_jacobi_quartic_ristretto (admitted there)
            assert(fe51_limbs_bounded(&jcs[i as int].S, 54)) by { admit() }
            assert(fe51_limbs_bounded(&jcs[i as int].T, 54)) by { admit() }
            let (ok, fe) = jcs[i].elligator_inv();
            let mut tmp: u8 = 0;
            ret[2 * i] = fe;
            /* ORIGINAL CODE: tmp.conditional_assign(&1, ok); */
            conditional_assign_generic(&mut tmp, &1u8, ok);
            mask |= tmp << (2 * i);

            let jc = jcs[i].dual();
            proof {
                lemma_fe51_limbs_bounded_weaken(&jc.S, 52, 54);
                lemma_fe51_limbs_bounded_weaken(&jc.T, 52, 54);
            }
            let (ok, fe) = jc.elligator_inv();
            let mut tmp: u8 = 0;
            ret[2 * i + 1] = fe;
            /* ORIGINAL CODE: tmp.conditional_assign(&1, ok); */
            conditional_assign_generic(&mut tmp, &1u8, ok);
            mask |= tmp << (2 * i + 1);
        }

        let result = (mask, ret);
        proof {
            // PROOF BYPASS: limb bounds for all 8 elements (follows from
            // elligator_inv postcondition once the loop admits above are resolved)
            assert(forall|j: int| 0 <= j < 8 ==> #[trigger] fe51_limbs_bounded(&result.1[j], 54))
                by { admit() };

            // PROOF BYPASS: Elligator inversion correctness (requires proving
            // that to_jacobi_quartic_ristretto produces correct Jacobi points AND
            // that elligator_inv roundtrips through jacobi_to_edwards_affine)
            assert({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                forall|j: int|
                    #![trigger result.1[j]]
                    0 <= j < 8 && (result.0 & (1u8 << j as u8)) != 0 ==> ({
                        let ej = spec_elligator_ristretto_flavor(
                            fe51_as_canonical_nat(&result.1[j]),
                        );
                        ej == coset[0] || ej == coset[1] || ej == coset[2] || ej == coset[3]
                    })
            }) by { admit() };
        }
        result
    }

    /// Find a point on the Jacobi quartic associated to each of the four
    /// points Ristretto equivalent to self.
    ///
    /// There is one exception: for (0,-1) there is no point on the quartic and
    /// so we repeat one on the quartic equivalent to (0,1).
    fn to_jacobi_quartic_ristretto(self) -> (result: [JacobiPoint; 4])
        requires
            is_well_formed_edwards_point(self.0),
        ensures
    // Representation: all 4 Jacobi quartic points have 54-bounded limbs

            forall|i: int|
                0 <= i < 4 ==> #[trigger] fe51_limbs_bounded(&result[i].S, 54)
                    && fe51_limbs_bounded(&result[i].T, 54),
            // Generic case (x ≠ 0 ∧ y ≠ 0): exact coset member correspondence.
            // Jacobi quartic point i maps back to Edwards coset member i.
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                x != 0 && y != 0 ==> forall|i: int|
                    #![trigger coset[i]]
                    0 <= i < 4 ==> jacobi_to_edwards_affine(
                        fe51_as_canonical_nat(&result[i].S),
                        fe51_as_canonical_nat(&result[i].T),
                    ) == coset[i]
            }),
            // Edge case (x = 0 ∨ y = 0): each Jacobi point still maps to
            // *some* coset member (possibly repeated). For (0, −1) there is
            // no quartic point, so the impl substitutes one equivalent to (0, 1).
            ({
                let (x, y) = edwards_point_as_affine(self.0);
                let coset = ristretto_coset_affine(x, y);
                (x == 0 || y == 0) ==> forall|i: int|
                    #![trigger coset[i]]
                    0 <= i < 4 ==> ({
                        let ji = jacobi_to_edwards_affine(
                            fe51_as_canonical_nat(&result[i].S),
                            fe51_as_canonical_nat(&result[i].T),
                        );
                        ji == coset[0] || ji == coset[1] || ji == coset[2] || ji == coset[3]
                    })
            }),
    {
        proof {
            // PROOF BYPASS: requires proving (1) limb bounds through ~30 field
            // operations and (2) algebraic correctness that the computed (S,T)
            // values satisfy jacobi_to_edwards_affine(S,T) == coset[i].
            // The algebraic part involves projective-to-affine Jacobi quartic
            // correspondence and is a deep multi-week proof effort.
            admit();
        }
        let x2 = self.0.X.square();  // X^2
        let y2 = self.0.Y.square();  // Y^2
        let y4 = y2.square();  // Y^4
        let z2 = self.0.Z.square();  // Z^2
        let z_min_y = &self.0.Z - &self.0.Y;  // Z - Y
        let z_pl_y = &self.0.Z + &self.0.Y;  // Z + Y
        let z2_min_y2 = &z2 - &y2;  // Z^2 - Y^2

        // gamma := 1/sqrt( Y^4 X^2 (Z^2 - Y^2) )
        let (_, gamma) = (&(&y4 * &x2) * &z2_min_y2).invsqrt();

        let den = &gamma * &y2;

        let s_over_x = &den * &z_min_y;
        let sp_over_xp = &den * &z_pl_y;

        let s0 = &s_over_x * &self.0.X;
        /* ORIGINAL CODE: let s1 = &(-(&sp_over_xp)) * &self.0.X; */
        let neg_sp_over_xp = negate_field_element(&sp_over_xp);
        let s1 = &neg_sp_over_xp * &self.0.X;

        // t_0 := -2/sqrt(-d-1) * Z * sOverX
        // t_1 := -2/sqrt(-d-1) * Z * spOverXp
        let tmp = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &self.0.Z;
        let mut t0 = &tmp * &s_over_x;
        let mut t1 = &tmp * &sp_over_xp;

        // den := -1/sqrt(1+d) (Y^2 - Z^2) gamma
        /* ORIGINAL CODE: let den = &(&(-(&z2_min_y2)) * &lizard_constants::MINVSQRT_ONE_PLUS_D) * &gamma; */
        let neg_z2_min_y2 = negate_field_element(&z2_min_y2);
        let den = &(&neg_z2_min_y2 * &lizard_constants::MINVSQRT_ONE_PLUS_D) * &gamma;

        // Same as before but with the substitution (X, Y, Z) = (Y, X, i*Z)
        let iz = &constants::SQRT_M1 * &self.0.Z;  // iZ
        let iz_min_x = &iz - &self.0.X;  // iZ - X
        let iz_pl_x = &iz + &self.0.X;  // iZ + X

        let s_over_y = &den * &iz_min_x;
        let sp_over_yp = &den * &iz_pl_x;

        let mut s2 = &s_over_y * &self.0.Y;
        /* ORIGINAL CODE: let mut s3 = &(-(&sp_over_yp)) * &self.0.Y; */
        let neg_sp_over_yp = negate_field_element(&sp_over_yp);
        let mut s3 = &neg_sp_over_yp * &self.0.Y;

        // t_2 := -2/sqrt(-d-1) * i*Z * sOverY
        // t_3 := -2/sqrt(-d-1) * i*Z * spOverYp
        let tmp = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &iz;
        let mut t2 = &tmp * &s_over_y;
        let mut t3 = &tmp * &sp_over_yp;

        // Special case: X=0 or Y=0.  Then return
        //
        //  (0,1)   (1,-2i/sqrt(-d-1)   (-1,-2i/sqrt(-d-1))
        //
        // Note that if X=0 or Y=0, then s_i = t_i = 0.
        /* ORIGINAL CODE: let x_or_y_is_zero = self.0.X.is_zero() | self.0.Y.is_zero(); */
        let x_or_y_is_zero = choice_or(self.0.X.is_zero(), self.0.Y.is_zero());
        t0.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        t1.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        t2.conditional_assign(&lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D, x_or_y_is_zero);
        t3.conditional_assign(&lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D, x_or_y_is_zero);
        s2.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        /* ORIGINAL CODE: s3.conditional_assign(&(-(&FieldElement::ONE)), x_or_y_is_zero); */
        let minus_one = negate_field_element(&FieldElement::ONE);
        s3.conditional_assign(&minus_one, x_or_y_is_zero);

        [
            JacobiPoint { S: s0, T: t0 },
            JacobiPoint { S: s1, T: t1 },
            JacobiPoint { S: s2, T: t2 },
            JacobiPoint { S: s3, T: t3 },
        ]
    }
}

} // verus!
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test {

    use sha2;

    use self::sha2::Sha256;
    use super::*;
    use crate::ristretto::CompressedRistretto;
    use rand_core::RngCore;
    #[cfg(feature = "rand")]
    use rand_os::OsRng;
    use subtle::ConditionallySelectable;
    use subtle::ConstantTimeEq;

    fn test_lizard_encode_helper(data: &[u8; 16], result: &[u8; 32]) {
        let p = RistrettoPoint::lizard_encode::<Sha256>(data);
        let p_bytes = p.compress().to_bytes();
        assert!(&p_bytes == result);
        let p = CompressedRistretto::from_slice(&p_bytes)
            .unwrap()
            .decompress()
            .unwrap();
        let data_out = p.lizard_decode::<Sha256>().unwrap();
        assert!(&data_out == data);
    }

    #[test]
    fn test_lizard_encode() {
        test_lizard_encode_helper(
            &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            &[
                0xf0, 0xb7, 0xe3, 0x44, 0x84, 0xf7, 0x4c, 0xf0, 0xf, 0x15, 0x2, 0x4b, 0x73, 0x85,
                0x39, 0x73, 0x86, 0x46, 0xbb, 0xbe, 0x1e, 0x9b, 0xc7, 0x50, 0x9a, 0x67, 0x68, 0x15,
                0x22, 0x7e, 0x77, 0x4f,
            ],
        );

        test_lizard_encode_helper(
            &[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            &[
                0xcc, 0x92, 0xe8, 0x1f, 0x58, 0x5a, 0xfc, 0x5c, 0xaa, 0xc8, 0x86, 0x60, 0xd8, 0xd1,
                0x7e, 0x90, 0x25, 0xa4, 0x44, 0x89, 0xa3, 0x63, 0x4, 0x21, 0x23, 0xf6, 0xaf, 0x7,
                0x2, 0x15, 0x6e, 0x65,
            ],
        );

        test_lizard_encode_helper(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            &[
                0xc8, 0x30, 0x57, 0x3f, 0x8a, 0x8e, 0x77, 0x78, 0x67, 0x1f, 0x76, 0xcd, 0xc7, 0x96,
                0xdc, 0xa, 0x23, 0x5c, 0xf1, 0x77, 0xf1, 0x97, 0xd9, 0xfc, 0xba, 0x6, 0xe8, 0x4e,
                0x96, 0x24, 0x74, 0x44,
            ],
        );
    }

    #[test]
    fn test_elligator_inv() {
        let mut rng = rand::thread_rng();

        for i in 0..100 {
            let mut fe_bytes = [0u8; 32];

            if i == 0 {
                // Test for first corner-case: fe = 0
                fe_bytes = [0u8; 32];
            } else if i == 1 {
                // Test for second corner-case: fe = +sqrt(i*d)
                fe_bytes = [
                    168, 27, 92, 74, 203, 42, 48, 117, 170, 109, 234, 14, 45, 169, 188, 205, 21,
                    110, 235, 115, 153, 84, 52, 117, 151, 235, 123, 244, 88, 85, 179, 5,
                ];
            } else {
                // For the rest, just generate a random field element to test.
                rng.fill_bytes(&mut fe_bytes);
            }
            fe_bytes[0] &= 254; // positive
            fe_bytes[31] &= 127; // < 2^255-19
            let fe = FieldElement::from_bytes(&fe_bytes);

            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            for pt2 in &pt.xcoset4() {
                let (mask, fes) = RistrettoPoint(*pt2).elligator_ristretto_flavor_inverse();

                let mut found = false;
                for (j, fe_j) in fes.iter().enumerate() {
                    if mask & (1 << j) != 0 {
                        assert_eq!(RistrettoPoint::elligator_ristretto_flavor(fe_j), pt);
                        if *fe_j == fe {
                            found = true;
                        }
                    }
                }
                assert!(found);
            }
        }
    }
}
