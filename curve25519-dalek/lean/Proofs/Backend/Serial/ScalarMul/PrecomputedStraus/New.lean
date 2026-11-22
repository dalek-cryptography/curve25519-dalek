/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Helpers.Collect
import Proofs.Window.NafLookupTable8From
public section

/-! # `VartimePrecomputedStraus::new`

The tables of odd multiples (`NafLookupTable8` of affine Niels points) of the static points, in
order (the patched collecting loop). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

open window.«NafLookupTable8AffineNielsPoint64bit-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«64bit-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«64bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«64bit-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«64bit-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec
      P (hps P hP).1 (hps P hP).2) (alloc.vec.Vec.new _) (by simpa using hys))
  rintro v ⟨zs, hv, hzs⟩
  rw [WP.spec_ok]
  replace hv : v.val = zs := by rw [hv]; rfl
  refine ⟨?_, fun t ht => ?_⟩
  · change List.Forall₂ window.NafLookupTable8.Represents v.val (ps.map (·.toPoint))
    rw [hv, List.forall₂_map_right_iff]
    exact (hzs.flip).imp fun t P h => h.1
  · rw [hv] at ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ((List.forall₂_iff_get.mp hzs).2 i (hzs.length_eq ▸ hi) hi).2

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end VartimePrecomputedStraus.«64bit-tables».Insts

namespace VartimePrecomputedStraus.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

open window.«NafLookupTable8AffineNielsPoint32bit-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«32bit-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«32bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«32bit-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«32bit-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec
      P (hps P hP).1 (hps P hP).2) (alloc.vec.Vec.new _) (by simpa using hys))
  rintro v ⟨zs, hv, hzs⟩
  rw [WP.spec_ok]
  replace hv : v.val = zs := by rw [hv]; rfl
  refine ⟨?_, fun t ht => ?_⟩
  · change List.Forall₂ window.NafLookupTable8.Represents v.val (ps.map (·.toPoint))
    rw [hv, List.forall₂_map_right_iff]
    exact (hzs.flip).imp fun t P h => h.1
  · rw [hv] at ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ((List.forall₂_iff_get.mp hzs).2 i (hzs.length_eq ▸ hi) hi).2

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end VartimePrecomputedStraus.«32bit-tables».Insts

namespace VartimePrecomputedStraus.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

open window.«NafLookupTable8AffineNielsPoint64bit-notables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«64bit-notables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«64bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«64bit-notables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«64bit-notables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPoint64bit-notables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPoint64bit-notables».from_spec
      P (hps P hP).1 (hps P hP).2) (alloc.vec.Vec.new _) (by simpa using hys))
  rintro v ⟨zs, hv, hzs⟩
  rw [WP.spec_ok]
  replace hv : v.val = zs := by rw [hv]; rfl
  refine ⟨?_, fun t ht => ?_⟩
  · change List.Forall₂ window.NafLookupTable8.Represents v.val (ps.map (·.toPoint))
    rw [hv, List.forall₂_map_right_iff]
    exact (hzs.flip).imp fun t P h => h.1
  · rw [hv] at ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ((List.forall₂_iff_get.mp hzs).2 i (hzs.length_eq ▸ hi) hi).2

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end VartimePrecomputedStraus.«64bit-notables».Insts

namespace VartimePrecomputedStraus.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

open window.«NafLookupTable8AffineNielsPoint32bit-notables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«32bit-notables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«32bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«32bit-notables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«32bit-notables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPoint32bit-notables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPoint32bit-notables».from_spec
      P (hps P hP).1 (hps P hP).2) (alloc.vec.Vec.new _) (by simpa using hys))
  rintro v ⟨zs, hv, hzs⟩
  rw [WP.spec_ok]
  replace hv : v.val = zs := by rw [hv]; rfl
  refine ⟨?_, fun t ht => ?_⟩
  · change List.Forall₂ window.NafLookupTable8.Represents v.val (ps.map (·.toPoint))
    rw [hv, List.forall₂_map_right_iff]
    exact (hzs.flip).imp fun t P h => h.1
  · rw [hv] at ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact ((List.forall₂_iff_get.mp hzs).2 i (hzs.length_eq ▸ hi) hi).2

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end VartimePrecomputedStraus.«32bit-notables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
