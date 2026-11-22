/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Edwards.Add
import Proofs.Edwards.AddAssign
import Proofs.Edwards.AsProjectiveNiels
import Proofs.Edwards.Identity
import Proofs.Edwards.MulByPow2
public import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.AsInt
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix2w
import Proofs.Scalar.ToRadix2wSizeHint
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.Pippenger.OptionalMultiscalarMulGeneric
public section

/-! # `Pippenger::optional_multiscalar_mul`

Pippenger's bucket method with radix-`2^w` digits (`w ∈ {6, 7, 8}` by the input size): for each
digit position `e` from the top, the points are added into the buckets `1, …, 2^(w-1)` by the
absolute value of their digit (subtracted for a negative digit), the buckets are combined into
`∑_b b • bucket_b = ∑_i d_i[e] • P_i` by two running sums, and the column is added to `2^w •` the
total. Only the first `min(|scalars|, |points|)` pairs are used (the patched zip); a `None`
among them gives `None`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.pippenger

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

private theorem optional_multiscalar_mul_loop0_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-tables») :
    optional_multiscalar_mul_loop0 it buckets =
      EdwardsOps.Bits64Tables.pippengerLoop0 it.end buckets it.start := by
  cases it
  rfl

private theorem reset_loop_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-tables») :
    optional_multiscalar_mul_loop1_loop0 it buckets =
      EdwardsOps.Bits64Tables.pippengerLoop10 it.end buckets it.start := by
  cases it
  rfl

private theorem accumulation_loop_eq
    (it : core.slice.iter.Iter ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-tables») (e : Usize) :
    optional_multiscalar_mul_loop1_loop1 it buckets e =
      loop (fun (it1, b) => EdwardsOps.Bits64Tables.pippengerLoop11Body e it1 b) (it, buckets) := by
  unfold optional_multiscalar_mul_loop1_loop1
  congr 1
  funext ⟨it1, b⟩
  unfold optional_multiscalar_mul_loop1_loop1.body EdwardsOps.pippengerLoop11Body
  simp only [uncurry]
  apply congrArg (Std.bind (core.slice.iter.IteratorSliceIter.next it1))
  funext ⟨o, it2⟩
  rcases o with _ | ⟨digits, pt⟩
  · rfl
  · apply congrArg (Std.bind (Array.index_usize digits e))
    funext i
    apply congrArg (Std.bind (lift (IScalar.cast .I16 i)))
    funext d
    apply congrArg (Std.bind (lift (core.cmp.impls.OrdI16.cmp d 0#i16)))
    funext ordering
    cases ordering with
    | lt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl
    | eq =>
      change ok (ControlFlow.cont (it2, b)) =
        Std.bind (ok b) (fun b1 => ok (ControlFlow.cont (it2, b1)))
      rw [Std.bind_ok]
    | gt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl

private theorem running_sum_loop_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-tables»)
    (inter sum : edwards.EdwardsPoint.«64bit-tables») :
    optional_multiscalar_mul_loop1_loop2 it buckets inter sum =
      loop (fun (it1, i, s) => EdwardsOps.Bits64Tables.pippengerLoop12Body buckets it1 i s)
        (it, inter, sum) := by
  unfold optional_multiscalar_mul_loop1_loop2
  congr 1

private theorem optional_multiscalar_mul_loop1_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-tables»)
    (total : Option edwards.EdwardsPoint.«64bit-tables») :
    optional_multiscalar_mul_loop1 it w bc sp buckets total =
      loop (fun (it1, b, t) => EdwardsOps.Bits64Tables.pippengerLoop1Body w bc sp it1 b t)
        (it, buckets, total) := by
  unfold optional_multiscalar_mul_loop1
  congr 1
  funext ⟨it1, b, t⟩
  unfold optional_multiscalar_mul_loop1.body EdwardsOps.pippengerLoop1Body
  simp only [reset_loop_eq, accumulation_loop_eq, running_sum_loop_eq,
    core.slice.Slice.iter, bind_ok, EdwardsOps.pippengerLoop11, EdwardsOps.pippengerLoop12,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  congr 1
  funext ⟨o, it2⟩
  cases o with
  | none => rfl
  | some e =>
    congr 1; funext b1
    funext b2
    congr 1; funext i
    congr 1; funext inter
    congr 1; funext sm
    congr 1; funext sm1
    cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPoint64bit-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«64bit-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.Bits64Tables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPoint64bit-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

open «VartimeMultiscalarMulPippengerEdwardsPoint64bit-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«64bit-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.Bits64Tables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq, EdwardsOps.pippengerScalarsPoints,
    EdwardsOps.pippengerLoop1, core.iter.traits.iterator.Iterator.rev.trait_default,
    bind_ok, core.iter.traits.iterator.Iterator.rev.default]
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«64bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«64bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.Bits64Tables.pippengerMain_spec
    EdwardsOps.Bits64Tables.identity_spec EdwardsOps.Bits64Tables.add_spec
    EdwardsOps.Bits64Tables.addAssign_spec EdwardsOps.Bits64Tables.mulByPow2_spec
    EdwardsOps.Bits64Tables.addN_spec EdwardsOps.Bits64Tables.subN_spec
    EdwardsOps.Bits64Tables.asExtended_spec EdwardsOps.Bits64Tables.asProjectiveNiels_spec
      scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

private theorem optional_multiscalar_mul_loop0_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-tables») :
    optional_multiscalar_mul_loop0 it buckets =
      EdwardsOps.Bits32Tables.pippengerLoop0 it.end buckets it.start := by
  cases it
  rfl

private theorem reset_loop_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-tables») :
    optional_multiscalar_mul_loop1_loop0 it buckets =
      EdwardsOps.Bits32Tables.pippengerLoop10 it.end buckets it.start := by
  cases it
  rfl

private theorem accumulation_loop_eq
    (it : core.slice.iter.Iter ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-tables») (e : Usize) :
    optional_multiscalar_mul_loop1_loop1 it buckets e =
      loop (fun (it1, b) => EdwardsOps.Bits32Tables.pippengerLoop11Body e it1 b) (it, buckets) := by
  unfold optional_multiscalar_mul_loop1_loop1
  congr 1
  funext ⟨it1, b⟩
  unfold optional_multiscalar_mul_loop1_loop1.body EdwardsOps.pippengerLoop11Body
  simp only [uncurry]
  apply congrArg (Std.bind (core.slice.iter.IteratorSliceIter.next it1))
  funext ⟨o, it2⟩
  rcases o with _ | ⟨digits, pt⟩
  · rfl
  · apply congrArg (Std.bind (Array.index_usize digits e))
    funext i
    apply congrArg (Std.bind (lift (IScalar.cast .I16 i)))
    funext d
    apply congrArg (Std.bind (lift (core.cmp.impls.OrdI16.cmp d 0#i16)))
    funext ordering
    cases ordering with
    | lt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl
    | eq =>
      change ok (ControlFlow.cont (it2, b)) =
        Std.bind (ok b) (fun b1 => ok (ControlFlow.cont (it2, b1)))
      rw [Std.bind_ok]
    | gt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl

private theorem running_sum_loop_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-tables»)
    (inter sum : edwards.EdwardsPoint.«32bit-tables») :
    optional_multiscalar_mul_loop1_loop2 it buckets inter sum =
      loop (fun (it1, i, s) => EdwardsOps.Bits32Tables.pippengerLoop12Body buckets it1 i s)
        (it, inter, sum) := by
  unfold optional_multiscalar_mul_loop1_loop2
  congr 1

private theorem optional_multiscalar_mul_loop1_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-tables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-tables»)
    (total : Option edwards.EdwardsPoint.«32bit-tables») :
    optional_multiscalar_mul_loop1 it w bc sp buckets total =
      loop (fun (it1, b, t) => EdwardsOps.Bits32Tables.pippengerLoop1Body w bc sp it1 b t)
        (it, buckets, total) := by
  unfold optional_multiscalar_mul_loop1
  congr 1
  funext ⟨it1, b, t⟩
  unfold optional_multiscalar_mul_loop1.body EdwardsOps.pippengerLoop1Body
  simp only [reset_loop_eq, accumulation_loop_eq, running_sum_loop_eq,
    core.slice.Slice.iter, bind_ok, EdwardsOps.pippengerLoop11, EdwardsOps.pippengerLoop12,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  congr 1
  funext ⟨o, it2⟩
  cases o with
  | none => rfl
  | some e =>
    congr 1; funext b1
    funext b2
    congr 1; funext i
    congr 1; funext inter
    congr 1; funext sm
    congr 1; funext sm1
    cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

namespace «VartimeMultiscalarMulPippengerEdwardsPoint32bit-tables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«32bit-tables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-tables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.Bits32Tables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPoint32bit-tables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

open «VartimeMultiscalarMulPippengerEdwardsPoint32bit-tables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«32bit-tables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.Bits32Tables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq, EdwardsOps.pippengerScalarsPoints,
    EdwardsOps.pippengerLoop1, core.iter.traits.iterator.Iterator.rev.trait_default,
    bind_ok, core.iter.traits.iterator.Iterator.rev.default]
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«32bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«32bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-tables») => (r = none ↔ none ∈ ops.take ss.length)
          ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.Bits32Tables.pippengerMain_spec
    EdwardsOps.Bits32Tables.identity_spec EdwardsOps.Bits32Tables.add_spec
    EdwardsOps.Bits32Tables.addAssign_spec EdwardsOps.Bits32Tables.mulByPow2_spec
    EdwardsOps.Bits32Tables.addN_spec EdwardsOps.Bits32Tables.subN_spec
    EdwardsOps.Bits32Tables.asExtended_spec EdwardsOps.Bits32Tables.asProjectiveNiels_spec
      scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

private theorem optional_multiscalar_mul_loop0_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-notables») :
    optional_multiscalar_mul_loop0 it buckets =
      EdwardsOps.Bits64NoTables.pippengerLoop0 it.end buckets it.start := by
  cases it
  rfl

private theorem reset_loop_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-notables») :
    optional_multiscalar_mul_loop1_loop0 it buckets =
      EdwardsOps.Bits64NoTables.pippengerLoop10 it.end buckets it.start := by
  cases it
  rfl

private theorem accumulation_loop_eq
    (it : core.slice.iter.Iter ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-notables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-notables») (e : Usize) :
    optional_multiscalar_mul_loop1_loop1 it buckets e =
      loop (fun (it1, b) => EdwardsOps.Bits64NoTables.pippengerLoop11Body e it1 b) (it, buckets) :=
        by
  unfold optional_multiscalar_mul_loop1_loop1
  congr 1
  funext ⟨it1, b⟩
  unfold optional_multiscalar_mul_loop1_loop1.body EdwardsOps.pippengerLoop11Body
  simp only [uncurry]
  apply congrArg (Std.bind (core.slice.iter.IteratorSliceIter.next it1))
  funext ⟨o, it2⟩
  rcases o with _ | ⟨digits, pt⟩
  · rfl
  · apply congrArg (Std.bind (Array.index_usize digits e))
    funext i
    apply congrArg (Std.bind (lift (IScalar.cast .I16 i)))
    funext d
    apply congrArg (Std.bind (lift (core.cmp.impls.OrdI16.cmp d 0#i16)))
    funext ordering
    cases ordering with
    | lt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl
    | eq =>
      change ok (ControlFlow.cont (it2, b)) =
        Std.bind (ok b) (fun b1 => ok (ControlFlow.cont (it2, b1)))
      rw [Std.bind_ok]
    | gt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl

private theorem running_sum_loop_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-notables»)
    (inter sum : edwards.EdwardsPoint.«64bit-notables») :
    optional_multiscalar_mul_loop1_loop2 it buckets inter sum =
      loop (fun (it1, i, s) => EdwardsOps.Bits64NoTables.pippengerLoop12Body buckets it1 i s)
        (it, inter, sum) := by
  unfold optional_multiscalar_mul_loop1_loop2
  congr 1

private theorem optional_multiscalar_mul_loop1_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-notables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«64bit-notables»)
    (total : Option edwards.EdwardsPoint.«64bit-notables») :
    optional_multiscalar_mul_loop1 it w bc sp buckets total =
      loop (fun (it1, b, t) => EdwardsOps.Bits64NoTables.pippengerLoop1Body w bc sp it1 b t)
        (it, buckets, total) := by
  unfold optional_multiscalar_mul_loop1
  congr 1
  funext ⟨it1, b, t⟩
  unfold optional_multiscalar_mul_loop1.body EdwardsOps.pippengerLoop1Body
  simp only [reset_loop_eq, accumulation_loop_eq, running_sum_loop_eq,
    core.slice.Slice.iter, bind_ok, EdwardsOps.pippengerLoop11, EdwardsOps.pippengerLoop12,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  congr 1
  funext ⟨o, it2⟩
  cases o with
  | none => rfl
  | some e =>
    congr 1; funext b1
    funext b2
    congr 1; funext i
    congr 1; funext inter
    congr 1; funext sm
    congr 1; funext sm1
    cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

namespace «VartimeMultiscalarMulPippengerEdwardsPoint64bit-notables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«64bit-notables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«64bit-notables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.Bits64NoTables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPoint64bit-notables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

open «VartimeMultiscalarMulPippengerEdwardsPoint64bit-notables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«64bit-notables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.Bits64NoTables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq, EdwardsOps.pippengerScalarsPoints,
    EdwardsOps.pippengerLoop1, core.iter.traits.iterator.Iterator.rev.trait_default,
    bind_ok, core.iter.traits.iterator.Iterator.rev.default]
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«64bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«64bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-notables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.Bits64NoTables.pippengerMain_spec
    EdwardsOps.Bits64NoTables.identity_spec EdwardsOps.Bits64NoTables.add_spec
    EdwardsOps.Bits64NoTables.addAssign_spec EdwardsOps.Bits64NoTables.mulByPow2_spec
    EdwardsOps.Bits64NoTables.addN_spec EdwardsOps.Bits64NoTables.subN_spec
    EdwardsOps.Bits64NoTables.asExtended_spec EdwardsOps.Bits64NoTables.asProjectiveNiels_spec
      scalarsInst
    borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints hborrow_scalars hss hps
    hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

private theorem optional_multiscalar_mul_loop0_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-notables») :
    optional_multiscalar_mul_loop0 it buckets =
      EdwardsOps.Bits32NoTables.pippengerLoop0 it.end buckets it.start := by
  cases it
  rfl

private theorem reset_loop_eq (it : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-notables») :
    optional_multiscalar_mul_loop1_loop0 it buckets =
      EdwardsOps.Bits32NoTables.pippengerLoop10 it.end buckets it.start := by
  cases it
  rfl

private theorem accumulation_loop_eq
    (it : core.slice.iter.Iter ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-notables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-notables») (e : Usize) :
    optional_multiscalar_mul_loop1_loop1 it buckets e =
      loop (fun (it1, b) => EdwardsOps.Bits32NoTables.pippengerLoop11Body e it1 b) (it, buckets) :=
        by
  unfold optional_multiscalar_mul_loop1_loop1
  congr 1
  funext ⟨it1, b⟩
  unfold optional_multiscalar_mul_loop1_loop1.body EdwardsOps.pippengerLoop11Body
  simp only [uncurry]
  apply congrArg (Std.bind (core.slice.iter.IteratorSliceIter.next it1))
  funext ⟨o, it2⟩
  rcases o with _ | ⟨digits, pt⟩
  · rfl
  · apply congrArg (Std.bind (Array.index_usize digits e))
    funext i
    apply congrArg (Std.bind (lift (IScalar.cast .I16 i)))
    funext d
    apply congrArg (Std.bind (lift (core.cmp.impls.OrdI16.cmp d 0#i16)))
    funext ordering
    cases ordering with
    | lt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl
    | eq =>
      change ok (ControlFlow.cont (it2, b)) =
        Std.bind (ok b) (fun b1 => ok (ControlFlow.cont (it2, b1)))
      rw [Std.bind_ok]
    | gt =>
      simp only [uncurry, Std.bind_assoc, bind_ok]
      rfl

private theorem running_sum_loop_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-notables»)
    (inter sum : edwards.EdwardsPoint.«32bit-notables») :
    optional_multiscalar_mul_loop1_loop2 it buckets inter sum =
      loop (fun (it1, i, s) => EdwardsOps.Bits32NoTables.pippengerLoop12Body buckets it1 i s)
        (it, inter, sum) := by
  unfold optional_multiscalar_mul_loop1_loop2
  congr 1

private theorem optional_multiscalar_mul_loop1_eq
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-notables»))
    (buckets : alloc.vec.Vec edwards.EdwardsPoint.«32bit-notables»)
    (total : Option edwards.EdwardsPoint.«32bit-notables») :
    optional_multiscalar_mul_loop1 it w bc sp buckets total =
      loop (fun (it1, b, t) => EdwardsOps.Bits32NoTables.pippengerLoop1Body w bc sp it1 b t)
        (it, buckets, total) := by
  unfold optional_multiscalar_mul_loop1
  congr 1
  funext ⟨it1, b, t⟩
  unfold optional_multiscalar_mul_loop1.body EdwardsOps.pippengerLoop1Body
  simp only [reset_loop_eq, accumulation_loop_eq, running_sum_loop_eq,
    core.slice.Slice.iter, bind_ok, EdwardsOps.pippengerLoop11, EdwardsOps.pippengerLoop12,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default]
  congr 1
  funext ⟨o, it2⟩
  cases o with
  | none => rfl
  | some e =>
    congr 1; funext b1
    funext b2
    congr 1; funext i
    congr 1; funext inter
    congr 1; funext sm
    congr 1; funext sm1
    cases t <;> rfl

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

namespace «VartimeMultiscalarMulPippengerEdwardsPoint32bit-notables».optional_multiscalar_mul

private theorem scalars_points_loop_eq {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It
      (Option edwards.EdwardsPoint.«32bit-notables»))
    (scalars : Slice S) (points : It) (w : Usize)
    (out : alloc.vec.Vec ((Array I8 64#usize) × ProjectiveNielsPoint.«32bit-notables»))
    (k : Usize) :
    scalars_points_loop borrowInst iterInst scalars points w out k =
      EdwardsOps.Bits32NoTables.pippengerScalarsPoints borrowInst iterInst scalars points w out
        k := by
  unfold scalars_points_loop EdwardsOps.pippengerScalarsPoints
  congr 1
  funext ⟨p, o, k⟩
  unfold scalars_points_loop.body EdwardsOps.pippengerScalarsPointsBody
  dsimp only
  -- the bodies match on the iterator's result with their own matchers
  split
  · congr 1; funext t; congr 1; funext s; congr 1; funext s1; congr 1; funext ⟨o, p1⟩
    rcases o with _ | _ | P <;> rfl
  · rfl

end «VartimeMultiscalarMulPippengerEdwardsPoint32bit-notables».optional_multiscalar_mul

namespace Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

open «VartimeMultiscalarMulPippengerEdwardsPoint32bit-notables».optional_multiscalar_mul in
private theorem optional_multiscalar_mul_eq {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option edwards.EdwardsPoint.«32bit-notables») IntoIter2) (scalars : I) (points : J) :
    optional_multiscalar_mul scalarsInst borrowInst pointsInst scalars points =
      EdwardsOps.Bits32NoTables.pippengerMain scalarsInst borrowInst pointsInst scalars points := by
  unfold optional_multiscalar_mul EdwardsOps.pippengerMain
  simp only [scalars_points, scalars_points_loop_eq, optional_multiscalar_mul_loop0_eq,
    optional_multiscalar_mul_loop1_eq, EdwardsOps.pippengerScalarsPoints,
    EdwardsOps.pippengerLoop1, core.iter.traits.iterator.Iterator.rev.trait_default,
    bind_ok, core.iter.traits.iterator.Iterator.rev.default]
  congr 1; funext t
  congr 1; funext scalars1
  congr 1; funext w; congr 1; funext md; congr 1; funext dc; congr 1; funext bc
  congr 1; funext t1; congr 1; funext o
  rcases o with _ | sp <;> rfl

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option edwards.EdwardsPoint.«32bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option edwards.EdwardsPoint.«32bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26 ∧ P.OnCurve)
    (hxs : xs.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-notables») =>
          (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  rw [optional_multiscalar_mul_eq]
  exact EdwardsOps.Bits32NoTables.pippengerMain_spec
    EdwardsOps.Bits32NoTables.identity_spec EdwardsOps.Bits32NoTables.add_spec
    EdwardsOps.Bits32NoTables.addAssign_spec EdwardsOps.Bits32NoTables.mulByPow2_spec
    EdwardsOps.Bits32NoTables.addN_spec EdwardsOps.Bits32NoTables.subN_spec
    EdwardsOps.Bits32NoTables.asExtended_spec EdwardsOps.Bits32NoTables.asProjectiveNiels_spec
    scalarsInst borrowScalarInst pointsInst scalars points xs ops ss hscalars hpoints
    hborrow_scalars hss hps hxs

end Pippenger.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

end Curve25519Dalek.backend.serial.scalar_mul.pippenger
