/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.AddProjectiveNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Backend.Serial.CurveModels.CompletedAsProjective
import Proofs.Backend.Serial.CurveModels.ProjectiveAsExtended
import Proofs.Backend.Serial.CurveModels.ProjectiveDouble
import Proofs.Backend.Serial.CurveModels.ProjectiveIdentity
import Proofs.Backend.Serial.CurveModels.SubAffineNiels
import Proofs.Backend.Serial.CurveModels.SubProjectiveNiels
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5From
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Lemmas
import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Generic
import Proofs.Helpers.EdwardsOps.Instances
public section

/-! # `VartimePrecomputedStraus::optional_mixed_multiscalar_mul` (`i686-no-tables`)

Variable-time Straus with precomputed tables for the static points: width-`8` non-adjacent forms
of the static scalars against the precomputed `NafLookupTable8`s, width-`5` ones of the dynamic
scalars against tables of the dynamic points built on the fly (`None` at the first `None` point),
Horner's rule in base `2` over the `256` digit positions. Missing static scalars count as `0`;
the patched code asserts `|static scalars| ≤ |static points|` and, after the `None` check,
`|dynamic scalars| = |dynamic points|`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

/-- For `ps[m]!` on the static points. -/
private noncomputable instance instInhabitedPoint : Inhabited curve25519.edwards.Point := ⟨0⟩

section
open «Shared0EdwardsPointi686-no-tables».Insts
open «CoreOpsArithAddSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (add_spec)
open «CoreOpsArithSubSharedAProjectiveNielsPointi686-no-tablesCompletedPointi686-no-tables»
    (sub_spec)

set_option linter.style.longLine false
namespace «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausi686-no-tablesEdwardsPointi686-no-tables»
set_option linter.style.longLine true
namespace optional_mixed_multiscalar_mul

/-- The scalars' width-`w` non-adjacent forms. -/
@[local step]
private theorem nafs_spec {It Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator It Clause0_Item)
    (borrowInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (scalars : It) (xs : List Clause0_Item) (hit : iterInst.Yields scalars xs)
    (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hlen : xs.length ≤ Usize.max) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) :
    loop (fun ((it, out) : It × alloc.vec.Vec (Array I8 256#usize)) =>
      collect.collectMapBody iterInst borrowInst.borrow
        (fun s => scalar.Scalar.non_adjacent_form s w) it out)
      (scalars, alloc.vec.Vec.new _)
      ⦃ (r : alloc.vec.Vec (Array I8 256#usize)) =>
        List.Forall₂ (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
          d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val) ss r.val ⦄ := by
  apply spec_mono (collect.collectMapLoop_spec iterInst borrowInst.borrow
    (fun s => scalar.Scalar.non_adjacent_form s w)
    (fun s d => d.asInt 1 = s.asNat ∧ ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 →
      d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ w.val)
    scalars xs hit ss hborrow (fun s hs =>
      spec_mono (scalar.Scalar.non_adjacent_form_spec s w hw (hss s hs))
        fun d ⟨hval, hdig, _⟩ => ⟨hval, hdig⟩) (alloc.vec.Vec.new _) (by simpa using hlen))
  rintro r ⟨zs, hr, hzs⟩
  simpa [hr] using hzs

end optional_mixed_multiscalar_mul
set_option linter.style.longLine false
end «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausi686-no-tablesEdwardsPointi686-no-tables»
set_option linter.style.longLine true

namespace VartimePrecomputedStraus.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimePrecomputedStrausi686-no-tablesEdwardsPointi686-no-tables»
set_option linter.style.longLine true

private theorem optional_mixed_multiscalar_mul_loop2_loop0_eq
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec
      (window.NafLookupTable8 AffineNielsPoint.«i686-no-tables»))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
      (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (dp : Usize) (S : ProjectivePoint.«i686-no-tables») :
    optional_mixed_multiscalar_mul_loop2_loop0 iter v static_nafs dynamic_nafs
        dynamic_lookup_tables dp S =
      EdwardsOps.I686NoTables.pstLoop0 iter v static_nafs dynamic_nafs dynamic_lookup_tables dp
        S := by
  unfold optional_mixed_multiscalar_mul_loop2_loop0
    EdwardsOps.pstLoop0
  congr 1

/-- The outer loop over the digit positions, from the top. -/
@[local step]
private theorem optional_mixed_multiscalar_mul_loop2_loop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 AffineNielsPoint.«i686-no-tables»))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec
        (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»))
    (dp : Usize) (S : ProjectivePoint.«i686-no-tables») (P Q : ℕ → curve25519.edwards.Point)
    (hdp : dp.val ≤ dynamic_nafs.length ∧ dp.val ≤ dynamic_lookup_tables.length)
    (hsl : static_nafs.length ≤ v.length)
    (hT : ∀ m < dp.val, dynamic_lookup_tables.val[m]!.Represents (Q m) ∧
      dynamic_lookup_tables.val[m]!.LimbsLt 27)
    (hD : ∀ m < dp.val, ∀ e : ℕ, e < 256 → (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hV : ∀ m < static_nafs.length, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt 27)
    (hE : ∀ m < static_nafs.length, ∀ e : ℕ, e < 256 → (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hS : S.OnCurve) (hSb : S.LimbsLt 26)
    (hSp : S.toPoint =
      (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! iter.iter.end.val • Q m) +
        ∑ m ∈ Finset.range static_nafs.length,
          nafTail static_nafs.val[m]! iter.iter.end.val • P m) :
    optional_mixed_multiscalar_mul_loop2_loop0 iter v static_nafs dynamic_nafs
      dynamic_lookup_tables dp S
      ⦃ (r : ProjectivePoint.«i686-no-tables») => r.OnCurve ∧ r.LimbsLt 26 ∧ r.toPoint =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! 0 • Q m) +
          ∑ m ∈ Finset.range static_nafs.length, nafTail static_nafs.val[m]! 0 • P m ⦄ := by
  rw [optional_mixed_multiscalar_mul_loop2_loop0_eq]
  exact EdwardsOps.I686NoTables.pstLoop0_spec
    EdwardsOps.I686NoTables.addN_spec EdwardsOps.I686NoTables.subN_spec
    EdwardsOps.I686NoTables.addA_spec EdwardsOps.I686NoTables.subA_spec
    EdwardsOps.I686NoTables.asExtended_spec EdwardsOps.I686NoTables.pDouble_spec
    EdwardsOps.I686NoTables.cAsProjective_spec iter v static_nafs dynamic_nafs dynamic_lookup_tables
    dp S P Q hdp hsl hT hD hV hE hstart hend hS hSb hSp

set_option linter.style.longLine false in
/-- `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`: for a precomputation of the
static points `ps`, `none` iff some dynamic point is `none`; otherwise
`∑ s_i • ps_i + ∑ d_i • Q_i` over the static scalars (at most `|ps|`, the missing ones count as
`0`) and the dynamic scalars and points (as many scalars as points); unreduced scalars
`< 2^255`; limbs `< 2^26`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option edwards.EdwardsPoint.«i686-no-tables») Clause4_IntoIter)
    (self : VartimePrecomputedStraus.«i686-no-tables») (static_scalars : I) (dynamic_scalars : J)
    (dynamic_points : K) (ps : List curve25519.edwards.Point) (xs : List Clause0_Item)
    (ss : List scalar.Scalar) (ys : List Clause2_Item) (ds : List scalar.Scalar)
    (qops : List (Option edwards.EdwardsPoint.«i686-no-tables»))
    (hself : self.Represents ps) (hself_b : self.LimbsLt 27)
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
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ ps.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option edwards.EdwardsPoint.«i686-no-tables») => (r = none ↔ none ∈ qops) ∧
        ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
          R.LimbsLt 26 ⦄ := by
  unfold optional_mixed_multiscalar_mul
  have h1 : staticScalarsInst.into_iter static_scalars
      ⦃ (it : Clause0_IntoIter) => staticScalarsInst.iteratorInst.Yields it xs ⦄ :=
    hstatic_scalars
  have h2 : dynamicScalarsInst.into_iter dynamic_scalars
      ⦃ (it : Clause2_IntoIter) => dynamicScalarsInst.iteratorInst.Yields it ys ⦄ :=
    hdynamic_scalars
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h1 as ⟨it, hit⟩
  unfold optional_mixed_multiscalar_mul_loop0
  apply spec_bind (optional_mixed_multiscalar_mul.nafs_spec
    _ _ it xs hit ss hborrow_static hss hxs 8#usize (by decide))
  intro sn hsn
  step with h2 as ⟨it1, hit1⟩
  unfold optional_mixed_multiscalar_mul_loop1
  apply spec_bind (optional_mixed_multiscalar_mul.nafs_spec
    _ _ it1 ys hit1 ds hborrow_dynamic hds hys 5#usize (by decide))
  intro dn hdn
  step with h3 as ⟨it2, hit2⟩
  let post := fun (r : Option edwards.EdwardsPoint.«i686-no-tables») =>
    (r = none ↔ none ∈ qops) ∧ ∀ R, r = some R → R.OnCurve ∧ R.toPoint =
      (List.zipWith (fun s P => s.asNat • P) ss ps).sum +
        (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds (qops.filterMap id)).sum ∧
      R.LimbsLt 26
  suffices h : ∀ it ops, dynamicPointsInst.iteratorInst.Yields it ops →
      ∀ (seen : List edwards.EdwardsPoint.«i686-no-tables»)
        (dtabs : alloc.vec.Vec (window.NafLookupTable5 ProjectiveNielsPoint.«i686-no-tables»)),
      qops = seen.map some ++ ops →
      List.Forall₂ (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) seen dtabs.val →
      optional_mixed_multiscalar_mul_loop2 staticScalarsInst borrowStaticInst dynamicScalarsInst
        borrowDynamicInst dynamicPointsInst it self sn dn dtabs ⦃ post ⦄ by
    exact h it2 qops hit2 [] (alloc.vec.Vec.new _) rfl .nil
  intro it ops hit
  induction hit with
  | nil hnext =>
    intro seen dtabs hseen htabs
    unfold optional_mixed_multiscalar_mul_loop2 loop optional_mixed_multiscalar_mul_loop2.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    have hnn : none ∉ qops := by simp [hseen]
    have hdtabs : List.Forall₂
        (fun P t => t.Represents P.toPoint ∧ t.LimbsLt 27) (qops.filterMap id) dtabs.val := by
      simpa [hseen] using htabs
    obtain ⟨hTlen, hT⟩ := forall₂_getElem! hdtabs
    obtain ⟨hDlen, hD⟩ := forall₂_getElem! hdn
    obtain ⟨hSlen, hS⟩ := forall₂_getElem! hsn
    obtain ⟨hVlen, hV⟩ := forall₂_getElem! hself
    have hfl := length_filterMap_id qops hnn
    have hdq := hdynamic hnn
    have hstatic := hstatic hnn
    step
    step
    step with
        ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
      as ⟨S0, hS0on, hS0, hS0b⟩
    step as ⟨iter, hiter⟩
    step with optional_mixed_multiscalar_mul_loop2_loop0_spec iter self.static_lookup_tables sn dn dtabs
      (alloc.vec.Vec.len dtabs) S0 (fun m => ps[m]!) (fun m => ((qops.filterMap id)[m]!).toPoint)
      ⟨by scalar_tac, by scalar_tac⟩ (by scalar_tac)
      (fun m hm => hT m (by scalar_tac))
      (fun m hm => (hD m (by scalar_tac)).2)
      (fun m hm => ⟨hV m (by scalar_tac),
        hself_b _ (by rw [getElem!_pos _ m (by scalar_tac)]; exact List.getElem_mem _)⟩)
      (fun m hm => (hS m (by scalar_tac)).2)
      (by rw [hiter]; rfl) (by rw [hiter]; decide) hS0on hS0b
      (by
        have he : iter.iter.end.val = 256 := by rw [hiter]; rfl
        rw [hS0, he]
        simp only [nafTail_eq_zero _ 256 fun j hj hj' => absurd hj' (Nat.not_lt.mpr hj),
          zero_smul, Finset.sum_const_zero, add_zero])
      as ⟨S1, hS1on, hS1b, hS1⟩
    step with «ProjectivePointi686-no-tables».as_extended_spec as ⟨R, hRon, hR, hRb⟩
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : R = R' := Option.some.inj hR'
    refine ⟨hRon, ?_, hRb⟩
    rw [hR, hS1, add_comm, sum_zipWith_eq, sum_zipWith_eq,
      show min ss.length ps.length = sn.val.length by
        rw [← hSlen]; exact Nat.min_eq_left hstatic,
      show min ds.length (qops.filterMap id).length = (alloc.vec.Vec.len dtabs).val by
        rw [alloc.vec.Vec.len_val, show dtabs.length = dtabs.val.length from rfl, ← hTlen, hfl,
          hdq, Nat.min_self]]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hS k (by rw [hSlen]; exact hk')).1, natCast_zsmul]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [nafTail_zero, (hD k (by scalar_tac)).1, natCast_zsmul]
  | @cons it it' x ops hnext _ ih =>
    intro seen dtabs hseen htabs
    unfold optional_mixed_multiscalar_mul_loop2 loop optional_mixed_multiscalar_mul_loop2.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | P
    · simp [uncurry, core.option.Option.map, post, hseen]
    · simp only [uncurry, core.option.Option.map, Std.bind_assoc]
      unfold optional_mixed_multiscalar_mul.closure.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPointi686-no-tablesNafLookupTable5ProjectiveNielsPointi686-no-tables».call_once
      simp only [Std.bind_tc_eq, Std.bind_assoc, bind_ok]
      obtain ⟨hPb, hPon⟩ := hqs P (by simp [hseen])
      apply spec_bind (window.«NafLookupTable5ProjectiveNielsPointi686-no-tables».Insts.«CoreConvertFromSharedAEdwardsPointi686-no-tables».from_spec
        P hPb hPon)
      rintro z ⟨hz, hzb⟩
      step with alloc.vec.Vec.push_spec dtabs z (by
        have hp := congrArg List.length hseen
        have ht := htabs.length_eq
        simp only [List.length_append, List.length_map, List.length_cons] at hp
        change dtabs.val.length < Usize.max
        omega) as ⟨out, hout⟩
      have ih' := ih (seen ++ [P]) out
        (by simpa [List.map_append, List.append_assoc] using hseen)
        (by rw [hout]; exact List.rel_append htabs (List.Forall₂.cons ⟨hz, hzb⟩ .nil))
      unfold optional_mixed_multiscalar_mul_loop2 at ih'
      exact ih'

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end VartimePrecomputedStraus.«i686-no-tables».Insts

end

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
