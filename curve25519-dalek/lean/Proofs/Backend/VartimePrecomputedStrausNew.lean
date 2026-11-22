/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.GetSelectedBackend
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.New
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStraus64bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-tables».Insts in
/-- `VartimePrecomputedStraus::new` (backend): the serial precomputation. -/
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
      r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  step
  step with
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables».new_spec
    _ _ _ ys ps hstatic_points hborrow hps hys as ⟨v, hv, hvb⟩
  obtain ⟨h1, h2⟩ := (v.represents_iff _).mp hv
  exact ⟨h1, h2, hvb⟩

end «VartimePrecomputedStraus64bit-tables»

namespace «VartimePrecomputedStraus32bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-tables».Insts in
/-- `VartimePrecomputedStraus::new` (backend): the serial precomputation. -/
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
      r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  step
  step with
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables».new_spec
    _ _ _ ys ps hstatic_points hborrow hps hys as ⟨v, hv, hvb⟩
  obtain ⟨h1, h2⟩ := (v.represents_iff _).mp hv
  exact ⟨h1, h2, hvb⟩

end «VartimePrecomputedStraus32bit-tables»

namespace «VartimePrecomputedStraus64bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-notables».Insts in
/-- `VartimePrecomputedStraus::new` (backend): the serial precomputation. -/
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
      r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  step
  step with
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables».new_spec
    _ _ _ ys ps hstatic_points hborrow hps hys as ⟨v, hv, hvb⟩
  obtain ⟨h1, h2⟩ := (v.represents_iff _).mp hv
  exact ⟨h1, h2, hvb⟩

end «VartimePrecomputedStraus64bit-notables»

namespace «VartimePrecomputedStraus32bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-notables».Insts in
/-- `VartimePrecomputedStraus::new` (backend): the serial precomputation. -/
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
      r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  step
  step with
      «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables».new_spec
    _ _ _ ys ps hstatic_points hborrow hps hys as ⟨v, hv, hvb⟩
  obtain ⟨h1, h2⟩ := (v.represents_iff _).mp hv
  exact ⟨h1, h2, hvb⟩

end «VartimePrecomputedStraus32bit-notables»

end Curve25519Dalek.backend
