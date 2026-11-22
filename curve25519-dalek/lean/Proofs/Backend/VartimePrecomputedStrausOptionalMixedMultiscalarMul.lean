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
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

namespace «VartimePrecomputedStraus64bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-tables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables» renaming
  optional_mixed_multiscalar_mul_spec → serial_spec in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«64bit-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«64bit-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«64bit-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact serial_spec
    _ _ _ _ _ inner _ _ _ _ xs ss ys ds qops ((inner.represents_iff _).mpr ⟨hself, rfl⟩) hself_b
        hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStraus64bit-tables»

namespace «VartimePrecomputedStraus32bit-tables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-tables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables» renaming
  optional_mixed_multiscalar_mul_spec → serial_spec in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«32bit-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«32bit-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«32bit-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact serial_spec
    _ _ _ _ _ inner _ _ _ _ xs ss ys ds qops ((inner.represents_iff _).mpr ⟨hself, rfl⟩) hself_b
        hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStraus32bit-tables»

namespace «VartimePrecomputedStraus64bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«64bit-notables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables» renaming
  optional_mixed_multiscalar_mul_spec → serial_spec in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«64bit-notables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«64bit-notables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«64bit-notables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-notables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact serial_spec
    _ _ _ _ _ inner _ _ _ _ xs ss ys ds qops ((inner.represents_iff _).mpr ⟨hself, rfl⟩) hself_b
        hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStraus64bit-notables»

namespace «VartimePrecomputedStraus32bit-notables»

open serial.scalar_mul.precomputed_straus.VartimePrecomputedStraus.«32bit-notables».Insts in
open «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables» renaming
  optional_mixed_multiscalar_mul_spec → serial_spec in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (backend): the serial one. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«32bit-notables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«32bit-notables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«32bit-notables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26 ∧ Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-notables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rcases self with ⟨inner⟩
  unfold optional_mixed_multiscalar_mul
  exact serial_spec
    _ _ _ _ _ inner _ _ _ _ xs ss ys ds qops ((inner.represents_iff _).mpr ⟨hself, rfl⟩) hself_b
        hstatic_scalars hdynamic_scalars
    hdynamic_points hborrow_static hborrow_dynamic hss hds hqs hxs hys hqops hstatic hdynamic

end «VartimePrecomputedStraus32bit-notables»

end Curve25519Dalek.backend
