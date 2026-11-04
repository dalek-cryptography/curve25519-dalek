/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.ScalarMul
import Proofs.Helpers.Collect
import Proofs.Window.NafLookupTable8From
public section

/-! # `VartimePrecomputedStraus::new`

The tables of odd multiples (`NafLookupTable8` of affine Niels points) of the static points, in
order (the patched collecting loop). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

open window.«NafLookupTable8AffineNielsPointx86_64-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«x86_64-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec
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

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end VartimePrecomputedStraus.«x86_64-tables».Insts

namespace VartimePrecomputedStraus.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

open window.«NafLookupTable8AffineNielsPointi686-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«i686-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«i686-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«i686-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec
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

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end VartimePrecomputedStraus.«i686-tables».Insts

namespace VartimePrecomputedStraus.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

open window.«NafLookupTable8AffineNielsPointx86_64-no-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«x86_64-no-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«x86_64-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«x86_64-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«x86_64-no-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointx86_64-no-tables».from_spec
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

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end VartimePrecomputedStraus.«x86_64-no-tables».Insts

namespace VartimePrecomputedStraus.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

open window.«NafLookupTable8AffineNielsPointi686-no-tables».Insts in
/-- `VartimePrecomputedStraus::new`: a precomputation of the points the input yields (through
`borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«i686-no-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«i686-no-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«i686-no-tables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points ⦃ (r : VartimePrecomputedStraus.«i686-no-tables») =>
      r.Represents (ps.map (·.toPoint)) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  unfold new_loop
  apply spec_bind (collect.collectMapLoop_spec _ borrowInst.borrow
    «CoreConvertFromSharedAEdwardsPointi686-no-tables».«from»
    (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) it ys hit ps hborrow
    (fun P hP =>
        «CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
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

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end VartimePrecomputedStraus.«i686-no-tables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
