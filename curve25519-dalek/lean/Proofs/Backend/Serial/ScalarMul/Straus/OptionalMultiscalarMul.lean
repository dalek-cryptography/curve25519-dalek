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
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Helpers.Cmp
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
public import Proofs.Helpers.EdwardsOps.Instances
public import Proofs.Backend.Serial.ScalarMul.Straus.OptionalMultiscalarMulGeneric
public section

/-! # `Straus::optional_multiscalar_mul`

Variable-time Straus: the width-`5` non-adjacent forms of the scalars, the tables of odd
multiples of the points (`None` as soon as a point is `None`, as the patched helper), and
Horner's rule in base `2` over the `256` digit positions, adding `d • P_i` for each nonzero digit
(up to the shorter of the two inputs). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.straus

section
open «Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
    (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-tablesCompletedPoint64bit-tables»
    (sub_spec)

namespace «VartimeMultiscalarMulStrausEdwardsPoint64bit-tables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 256#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        (fun s => scalar.Scalar.non_adjacent_form s 5#usize) it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPoint64bit-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

private theorem optional_multiscalar_mul_loop1_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»))
    (i : Usize) (t : CompletedPoint.«64bit-tables»)
    (it : core.ops.range.Range Usize) :
    optional_multiscalar_mul_loop1_loop0_loop0 it nafs lookup_tables i t =
      EdwardsOps.Bits64Tables.strausLoop00 it nafs lookup_tables i t := by
  unfold optional_multiscalar_mul_loop1_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop1_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»))
    (r : ProjectivePoint.«64bit-tables») :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r =
      EdwardsOps.Bits64Tables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop1_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»))
    (r : ProjectivePoint.«64bit-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«64bit-tables») => res.OnCurve ∧ res.LimbsLt 52 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop1_loop0_eq]
  exact EdwardsOps.Bits64Tables.strausLoop0_spec
    EdwardsOps.Bits64Tables.addN_spec EdwardsOps.Bits64Tables.subN_spec
    EdwardsOps.Bits64Tables.asExtended_spec EdwardsOps.Bits64Tables.pDouble_spec
    EdwardsOps.Bits64Tables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

set_option linter.style.longLine false in
open «VartimeMultiscalarMulStrausEdwardsPoint64bit-tables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none`;
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul_loop0
  apply spec_bind (optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs)
  intro nafs hnafs
  step with hpoints' as ⟨it1, hit1⟩
  let post := fun (r : Option edwards.EdwardsPoint.«64bit-tables») =>
    (r = none ↔ none ∈ ops) ∧ ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
      (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧ R.LimbsLt 52
  suffices h : ∀ it rest, pointsInst.iteratorInst.Yields it rest →
      ∀ (seen : List edwards.EdwardsPoint.«64bit-tables»)
        (tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-tables»)),
      ops = seen.map some ++ rest →
      List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) seen tables.val →
      optional_multiscalar_mul_loop1 scalarsInst borrowScalarInst pointsInst it nafs tables
        ⦃ post ⦄ by
    exact h it1 ops hit1 [] (alloc.vec.Vec.new _) rfl .nil
  intro it rest hit
  induction hit with
  | nil hnext =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    have hnn : none ∉ ops := by simp [hseen]
    have ht : List.Forall₂
        (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) (ops.filterMap id) tables.val := by
      simpa [hseen] using htables
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! ht
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop1_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePoint64bit-tables».as_extended_spec as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]
  | @cons it it' x rest hnext _ ih =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp [uncurry, core.option.Option.map, post, hseen]
    · simp only [uncurry, core.option.Option.map, Std.bind_assoc]
      unfold optional_multiscalar_mul.closure.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPoint64bit-tablesNafLookupTable5ProjectiveNielsPoint64bit-tables».call_once
      simp only [Std.bind_tc_eq, Std.bind_assoc, bind_ok]
      obtain ⟨hPb, hPon⟩ := hps P (by simp [hseen])
      apply spec_bind
        (window.«NafLookupTable5ProjectiveNielsPoint64bit-tables».Insts.«CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec
          P hPb hPon)
      rintro z ⟨hz, hzb⟩
      step with alloc.vec.Vec.push_spec tables z (by
        have hp := congrArg List.length hseen
        have ht := htables.length_eq
        simp only [List.length_append, List.length_map, List.length_cons] at hp
        change tables.val.length < Usize.max
        omega) as ⟨out, hout⟩
      have ih' := ih (seen ++ [P]) out
        (by simpa [List.map_append, List.append_assoc] using hseen)
        (by rw [hout]; exact List.rel_append htables (List.Forall₂.cons ⟨hz, hzb⟩ .nil))
      unfold optional_multiscalar_mul_loop1 at ih'
      exact ih'

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables»

end

section
open «Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
    (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-tablesCompletedPoint32bit-tables»
    (sub_spec)

namespace «VartimeMultiscalarMulStrausEdwardsPoint32bit-tables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 256#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        (fun s => scalar.Scalar.non_adjacent_form s 5#usize) it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPoint32bit-tables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

private theorem optional_multiscalar_mul_loop1_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»))
    (i : Usize) (t : CompletedPoint.«32bit-tables»)
    (it : core.ops.range.Range Usize) :
    optional_multiscalar_mul_loop1_loop0_loop0 it nafs lookup_tables i t =
      EdwardsOps.Bits32Tables.strausLoop00 it nafs lookup_tables i t := by
  unfold optional_multiscalar_mul_loop1_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop1_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»))
    (r : ProjectivePoint.«32bit-tables») :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r =
      EdwardsOps.Bits32Tables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop1_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»))
    (r : ProjectivePoint.«32bit-tables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 27)
    (hD : ∀ m < n, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«32bit-tables») => res.OnCurve ∧ res.LimbsLt 26 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop1_loop0_eq]
  exact EdwardsOps.Bits32Tables.strausLoop0_spec
    EdwardsOps.Bits32Tables.addN_spec EdwardsOps.Bits32Tables.subN_spec
    EdwardsOps.Bits32Tables.asExtended_spec EdwardsOps.Bits32Tables.pDouble_spec
    EdwardsOps.Bits32Tables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend hr
    hrb hrp

set_option linter.style.longLine false in
open «VartimeMultiscalarMulStrausEdwardsPoint32bit-tables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none`;
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-tables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul_loop0
  apply spec_bind (optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs)
  intro nafs hnafs
  step with hpoints' as ⟨it1, hit1⟩
  let post := fun (r : Option edwards.EdwardsPoint.«32bit-tables») =>
    (r = none ↔ none ∈ ops) ∧ ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
      (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧ R.LimbsLt 26
  suffices h : ∀ it rest, pointsInst.iteratorInst.Yields it rest →
      ∀ (seen : List edwards.EdwardsPoint.«32bit-tables»)
        (tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-tables»)),
      ops = seen.map some ++ rest →
      List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) seen tables.val →
      optional_multiscalar_mul_loop1 scalarsInst borrowScalarInst pointsInst it nafs tables
        ⦃ post ⦄ by
    exact h it1 ops hit1 [] (alloc.vec.Vec.new _) rfl .nil
  intro it rest hit
  induction hit with
  | nil hnext =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    have hnn : none ∉ ops := by simp [hseen]
    have ht : List.Forall₂
        (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) (ops.filterMap id) tables.val := by
      simpa [hseen] using htables
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! ht
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop1_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePoint32bit-tables».as_extended_spec as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]
  | @cons it it' x rest hnext _ ih =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp [uncurry, core.option.Option.map, post, hseen]
    · simp only [uncurry, core.option.Option.map, Std.bind_assoc]
      unfold optional_multiscalar_mul.closure.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPoint32bit-tablesNafLookupTable5ProjectiveNielsPoint32bit-tables».call_once
      simp only [Std.bind_tc_eq, Std.bind_assoc, bind_ok]
      obtain ⟨hPb, hPon⟩ := hps P (by simp [hseen])
      apply spec_bind
        (window.«NafLookupTable5ProjectiveNielsPoint32bit-tables».Insts.«CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec
          P hPb hPon)
      rintro z ⟨hz, hzb⟩
      step with alloc.vec.Vec.push_spec tables z (by
        have hp := congrArg List.length hseen
        have ht := htables.length_eq
        simp only [List.length_append, List.length_map, List.length_cons] at hp
        change tables.val.length < Usize.max
        omega) as ⟨out, hout⟩
      have ih' := ih (seen ++ [P]) out
        (by simpa [List.map_append, List.append_assoc] using hseen)
        (by rw [hout]; exact List.rel_append htables (List.Forall₂.cons ⟨hz, hzb⟩ .nil))
      unfold optional_multiscalar_mul_loop1 at ih'
      exact ih'

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables»

end

section
open «Shared0EdwardsPoint64bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
    (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint64bit-notablesCompletedPoint64bit-notables»
    (sub_spec)

namespace «VartimeMultiscalarMulStrausEdwardsPoint64bit-notables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 256#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        (fun s => scalar.Scalar.non_adjacent_form s 5#usize) it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPoint64bit-notables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

private theorem optional_multiscalar_mul_loop1_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»))
    (i : Usize) (t : CompletedPoint.«64bit-notables»)
    (it : core.ops.range.Range Usize) :
    optional_multiscalar_mul_loop1_loop0_loop0 it nafs lookup_tables i t =
      EdwardsOps.Bits64NoTables.strausLoop00 it nafs lookup_tables i t := by
  unfold optional_multiscalar_mul_loop1_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop1_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»))
    (r : ProjectivePoint.«64bit-notables») :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r =
      EdwardsOps.Bits64NoTables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop1_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»))
    (r : ProjectivePoint.«64bit-notables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 54)
    (hD : ∀ m < n, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 52)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«64bit-notables») => res.OnCurve ∧ res.LimbsLt 52 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop1_loop0_eq]
  exact EdwardsOps.Bits64NoTables.strausLoop0_spec
    EdwardsOps.Bits64NoTables.addN_spec EdwardsOps.Bits64NoTables.subN_spec
    EdwardsOps.Bits64NoTables.asExtended_spec EdwardsOps.Bits64NoTables.pDouble_spec
    EdwardsOps.Bits64NoTables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend
      hr
    hrb hrp

set_option linter.style.longLine false in
open «VartimeMultiscalarMulStrausEdwardsPoint64bit-notables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none`;
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^52`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«64bit-notables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 52 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul_loop0
  apply spec_bind (optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs)
  intro nafs hnafs
  step with hpoints' as ⟨it1, hit1⟩
  let post := fun (r : Option edwards.EdwardsPoint.«64bit-notables») =>
    (r = none ↔ none ∈ ops) ∧ ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
      (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧ R.LimbsLt 52
  suffices h : ∀ it rest, pointsInst.iteratorInst.Yields it rest →
      ∀ (seen : List edwards.EdwardsPoint.«64bit-notables»)
        (tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«64bit-notables»)),
      ops = seen.map some ++ rest →
      List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) seen tables.val →
      optional_multiscalar_mul_loop1 scalarsInst borrowScalarInst pointsInst it nafs tables
        ⦃ post ⦄ by
    exact h it1 ops hit1 [] (alloc.vec.Vec.new _) rfl .nil
  intro it rest hit
  induction hit with
  | nil hnext =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    have hnn : none ∉ ops := by simp [hseen]
    have ht : List.Forall₂
        (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 54) (ops.filterMap id) tables.val := by
      simpa [hseen] using htables
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! ht
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop1_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePoint64bit-notables».as_extended_spec as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]
  | @cons it it' x rest hnext _ ih =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp [uncurry, core.option.Option.map, post, hseen]
    · simp only [uncurry, core.option.Option.map, Std.bind_assoc]
      unfold optional_multiscalar_mul.closure.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPoint64bit-notablesNafLookupTable5ProjectiveNielsPoint64bit-notables».call_once
      simp only [Std.bind_tc_eq, Std.bind_assoc, bind_ok]
      obtain ⟨hPb, hPon⟩ := hps P (by simp [hseen])
      apply spec_bind
        (window.«NafLookupTable5ProjectiveNielsPoint64bit-notables».Insts.«CoreConvertFromSharedAEdwardsPoint64bit-notables».from_spec
          P hPb hPon)
      rintro z ⟨hz, hzb⟩
      step with alloc.vec.Vec.push_spec tables z (by
        have hp := congrArg List.length hseen
        have ht := htables.length_eq
        simp only [List.length_append, List.length_map, List.length_cons] at hp
        change tables.val.length < Usize.max
        omega) as ⟨out, hout⟩
      have ih' := ih (seen ++ [P]) out
        (by simpa [List.map_append, List.append_assoc] using hseen)
        (by rw [hout]; exact List.rel_append htables (List.Forall₂.cons ⟨hz, hzb⟩ .nil))
      unfold optional_multiscalar_mul_loop1 at ih'
      exact ih'

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables»

end

section
open «Shared0EdwardsPoint32bit-notables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
    (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPoint32bit-notablesCompletedPoint32bit-notables»
    (sub_spec)

namespace «VartimeMultiscalarMulStrausEdwardsPoint32bit-notables».optional_multiscalar_mul

/-- The scalars' width-`5` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 256#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        (fun s => scalar.Scalar.non_adjacent_form s 5#usize) it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s 5#usize)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s 5#usize (by decide) (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) _ (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end «VartimeMultiscalarMulStrausEdwardsPoint32bit-notables».optional_multiscalar_mul

namespace Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

private theorem optional_multiscalar_mul_loop1_loop0_loop0_eq
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»))
    (i : Usize) (t : CompletedPoint.«32bit-notables»)
    (it : core.ops.range.Range Usize) :
    optional_multiscalar_mul_loop1_loop0_loop0 it nafs lookup_tables i t =
      EdwardsOps.Bits32NoTables.strausLoop00 it nafs lookup_tables i t := by
  unfold optional_multiscalar_mul_loop1_loop0_loop0 EdwardsOps.strausLoop00
  congr 1

private theorem optional_multiscalar_mul_loop1_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»))
    (r : ProjectivePoint.«32bit-notables») :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r =
      EdwardsOps.Bits32NoTables.strausLoop0 iter nafs lookup_tables r := by
  unfold optional_multiscalar_mul_loop1_loop0 EdwardsOps.strausLoop0
  congr 1

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
@[local step]
private theorem optional_multiscalar_mul_loop1_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»))
    (r : ProjectivePoint.«32bit-notables») (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧ lookup_tables.val[m]!.LimbsLt 27)
    (hD : ∀ m < n, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : r.OnCurve) (hrb : r.LimbsLt 26)
    (hrp : r.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    optional_multiscalar_mul_loop1_loop0 iter nafs lookup_tables r
      ⦃ (res : ProjectivePoint.«32bit-notables») => res.OnCurve ∧ res.LimbsLt 26 ∧
        res.toPoint = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_multiscalar_mul_loop1_loop0_eq]
  exact EdwardsOps.Bits32NoTables.strausLoop0_spec
    EdwardsOps.Bits32NoTables.addN_spec EdwardsOps.Bits32NoTables.subN_spec
    EdwardsOps.Bits32NoTables.asExtended_spec EdwardsOps.Bits32NoTables.pDouble_spec
    EdwardsOps.Bits32NoTables.cAsProjective_spec iter nafs lookup_tables r P n hn hT hD hstart hend
      hr
    hrb hrp

set_option linter.style.longLine false in
open «VartimeMultiscalarMulStrausEdwardsPoint32bit-notables» in
/-- `Straus::optional_multiscalar_mul`: `none` iff some point is `none`;
otherwise `∑ s_i • P_i` over the scalars and points, up to the shorter input (unreduced
scalars `< 2^255`); limbs `< 2^26`. -/
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
    (hxs : xs.length ≤ Usize.max) (hops : ops.length ≤ Usize.max) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option edwards.EdwardsPoint.«32bit-notables») => (r = none ↔ none ∈ ops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_multiscalar_mul
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  unfold optional_multiscalar_mul_loop0
  apply spec_bind (optional_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_scalars hss hxs)
  intro nafs hnafs
  step with hpoints' as ⟨it1, hit1⟩
  let post := fun (r : Option edwards.EdwardsPoint.«32bit-notables») =>
    (r = none ↔ none ∈ ops) ∧ ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
      (List.zipWith (fun s P => s.asNat • P.toPoint) ss (ops.filterMap id)).sum ∧ R.LimbsLt 26
  suffices h : ∀ it rest, pointsInst.iteratorInst.Yields it rest →
      ∀ (seen : List edwards.EdwardsPoint.«32bit-notables»)
        (tables : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«32bit-notables»)),
      ops = seen.map some ++ rest →
      List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) seen tables.val →
      optional_multiscalar_mul_loop1 scalarsInst borrowScalarInst pointsInst it nafs tables
        ⦃ post ⦄ by
    exact h it1 ops hit1 [] (alloc.vec.Vec.new _) rfl .nil
  intro it rest hit
  induction hit with
  | nil hnext =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    have hnn : none ∉ ops := by simp [hseen]
    have ht : List.Forall₂
        (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) (ops.filterMap id) tables.val := by
      simpa [hseen] using htables
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! ht
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hnafs
    have hn : min ss.length (ops.filterMap id).length = min nafs.length tables.length := by
      rw [hTlen, hDlen]
    step with
        ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
      as ⟨r, hron, hr, hrb⟩
    step as ⟨iter, hiter⟩
    step with optional_multiscalar_mul_loop1_loop0_spec iter nafs tables r
      (fun k => (ops.filterMap id)[k]!.toPoint) (min ss.length (ops.filterMap id).length) hn
      (fun k hk => hT k (by have := min_le_right ss.length (ops.filterMap id).length; omega))
      (fun k hk => (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hron hrb
      (by
        rw [hr, hiter]
        exact (Finset.sum_eq_zero fun k _ => by
          rw [show ({ start := 0#usize, «end» := 256#usize } : core.ops.range.Range Usize).end.val
            = 256 from rfl, nafTail_eq_zero _ _ fun j hj hj' => by omega, zero_smul]).symm)
      as ⟨q, hqon, hqb, hq⟩
    step with «ProjectivePoint32bit-notables».as_extended_spec as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hq, sum_zipWith_eq]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [nafTail_zero, (hD k (by have := min_le_left ss.length (ops.filterMap id).length; omega)).1,
      natCast_zsmul]
  | @cons it it' x rest hnext _ ih =>
    intro seen tables hseen htables
    unfold optional_multiscalar_mul_loop1 loop optional_multiscalar_mul_loop1.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp [uncurry, core.option.Option.map, post, hseen]
    · simp only [uncurry, core.option.Option.map, Std.bind_assoc]
      unfold optional_multiscalar_mul.closure.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPoint32bit-notablesNafLookupTable5ProjectiveNielsPoint32bit-notables».call_once
      simp only [Std.bind_tc_eq, Std.bind_assoc, bind_ok]
      obtain ⟨hPb, hPon⟩ := hps P (by simp [hseen])
      apply spec_bind
        (window.«NafLookupTable5ProjectiveNielsPoint32bit-notables».Insts.«CoreConvertFromSharedAEdwardsPoint32bit-notables».from_spec
          P hPb hPon)
      rintro z ⟨hz, hzb⟩
      step with alloc.vec.Vec.push_spec tables z (by
        have hp := congrArg List.length hseen
        have ht := htables.length_eq
        simp only [List.length_append, List.length_map, List.length_cons] at hp
        change tables.val.length < Usize.max
        omega) as ⟨out, hout⟩
      have ih' := ih (seen ++ [P]) out
        (by simpa [List.map_append, List.append_assoc] using hseen)
        (by rw [hout]; exact List.rel_append htables (List.Forall₂.cons ⟨hz, hzb⟩ .nil))
      unfold optional_multiscalar_mul_loop1 at ih'
      exact ih'

end Straus.Insts.«Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables»

end

end Curve25519Dalek.backend.serial.scalar_mul.straus
