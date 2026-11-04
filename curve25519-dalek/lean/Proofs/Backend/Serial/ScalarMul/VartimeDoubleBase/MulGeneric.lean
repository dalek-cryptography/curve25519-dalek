/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
import Proofs.Helpers.Iterator
public import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
public import Proofs.Helpers.EdwardsOps
public section

/-! # `vartime_double_base::mul`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`Mul.lean`).

`a • A + b • B` for the basepoint `B`, in variable time: the non-adjacent forms of `a` (width
`5`) and `b` (width `8` with the precomputed table `AFFINE_ODD_MULTIPLES_OF_BASEPOINT` in the
`x86_64-tables` configuration, width `5` with a table built from `ED25519_BASEPOINT_POINT`
otherwise), Horner's rule from the highest nonzero digit down, adding `d • A` and `d • B` for
each nonzero digit from the tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

/-- One step of Horner's rule on two points. -/
private theorem horner_step (x y d e : ℤ) (A B : curve25519.edwards.Point) :
    2 • (x • A + y • B) + d • A + e • B = (d + 2 * x) • A + (e + 2 * y) • B := by
  rw [smul_add, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, add_smul, add_smul]
  push_cast
  abel


end Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.vartime_double_base

open ControlFlow

/-- `mul_loop0.body`, the same in every configuration. -/
@[expose] def vdbLoop0Body (a_naf b_naf : Array I8 256#usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (i : Usize) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × Usize)
      Usize) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done i)
  | some j =>
    let i1 ← Array.index_usize a_naf j
    if i1 != 0#i8
    then ok (done j)
    else
      let i2 ← Array.index_usize b_naf j
      if i2 != 0#i8
      then ok (done j)
      else ok (cont (iter1, j))

/-- `mul_loop0`, the same in every configuration. -/
@[expose] def vdbLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) : Result Usize := do
  loop (fun (iter1, i1) => vdbLoop0Body a_naf b_naf iter1 i1) (iter, i)

open scoped Helpers.IndexStep in
/-- The first loop of `mul`: the highest index at which a digit of `a` or `b` is nonzero (`0` if
there is none). -/
theorem vdbLoop0_spec (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (a_naf b_naf : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 256) (hi : i.val < 256)
    (hz : ∀ k, iter.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0) :
    vdbLoop0 iter a_naf b_naf i ⦃ (r : Usize) =>
      r.val < 256 ∧ ∀ k, r.val < k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0 ⦄ := by
  unfold vdbLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, j) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ j.val < 256 ∧
      ∀ k, it.iter.end.val ≤ k → k < 256 → a_naf[k]!.val = 0 ∧ b_naf[k]!.val = 0)
  · rintro ⟨it, j⟩ ⟨hst, hen, hj, hzk⟩
    unfold vdbLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, e, ho, he, hstart1, hend1⟩
      subst ho
      step as ⟨x, hx⟩
      by_cases hx0 : x.val = 0
      · have hx' : (x != 0#i8) = false := by
          rw [bne_eq_false_iff_eq]; scalar_tac
        simp only [hx', Bool.false_eq_true, ↓reduceIte]
        step as ⟨y, hy⟩
        by_cases hy0 : y.val = 0
        · have hy' : (y != 0#i8) = false := by
            rw [bne_eq_false_iff_eq]; scalar_tac
          simp only [hy', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          refine ⟨by rw [hstart1, hst], by scalar_tac, by scalar_tac, fun k hk hk' => ?_,
            by scalar_tac⟩
          rcases Nat.eq_or_lt_of_le (hend1 ▸ hk) with h | h
          · subst h; exact ⟨hx ▸ hx0, hy ▸ hy0⟩
          · exact hzk k (by omega) hk'
        · have hy' : (y != 0#i8) = true := by
            rw [bne_iff_ne]; intro h; apply hy0; rw [h]; rfl
          simp only [hy', ↓reduceIte, WP.spec_ok]
          exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
      · have hx' : (x != 0#i8) = true := by
          rw [bne_iff_ne]; intro h; apply hx0; rw [h]; rfl
        simp only [hx', ↓reduceIte, WP.spec_ok]
        exact ⟨by scalar_tac, fun k hk hk' => hzk k (by omega) hk'⟩
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      exact ⟨hj, fun k _ hk' => hzk k (by omega) hk'⟩
  · exact ⟨hstart, hend, hi, hz⟩

variable (O : EdwardsOps)

/-- `mul_loop1.body` over the point operations (vdbLoop1T). -/
@[expose] def vdbLoop1TBody (a_naf b_naf : Array I8 256#usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An) (i : Usize)
    (r : O.Pr) :
    Result (ControlFlow (Usize × O.Pr) O.E) := do
  let t ← O.pDouble r
  let digit ← Array.index_usize a_naf i
  let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
  let t1 ←
    match o with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A i2
      O.subN ep pnp
    | Ordering.eq => ok t
    | Ordering.gt =>
      do
      let ep ← O.asExtended t
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN table_A i1
      O.addN ep pnp
  let digit1 ← Array.index_usize b_naf i
  let o1 ← lift (core.cmp.impls.OrdI8.cmp digit1 0#i8)
  let t2 ←
    match o1 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t1
      let i1 ← -. digit1
      let i2 ← lift (IScalar.hcast .Usize i1)
      let anp ← window.NafLookupTable8.select O.copyA table_B i2
      O.subA ep anp
    | Ordering.eq => ok t1
    | Ordering.gt =>
      do
      let ep ← O.asExtended t1
      let i1 ← lift (IScalar.hcast .Usize digit1)
      let anp ← window.NafLookupTable8.select O.copyA table_B i1
      O.addA ep anp
  let r1 ← O.cAsProjective t2
  if i = 0#usize
  then
    let ep ← O.pAsExtended r1
    ok (done ep)
  else let i1 ← i - 1#usize
       ok (cont (i1, r1))

/-- `mul_loop1` over the point operations (vdbLoop1T). -/
@[expose] def vdbLoop1T (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An) (r : O.Pr) :
    Result O.E := do
  loop (fun (i1, r1) => O.vdbLoop1TBody a_naf b_naf table_A table_B i1 r1) (i, r)

/-- `mul_loop1.body` over the point operations (vdbLoop1N). -/
@[expose] def vdbLoop1NBody (a_naf b_naf : Array I8 256#usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N) (i : Usize)
    (r : O.Pr) :
    Result (ControlFlow (Usize × O.Pr) O.E) := do
  let t ← O.pDouble r
  let digit ← Array.index_usize a_naf i
  let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
  let t1 ←
    match o with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A i2
      O.subN ep pnp
    | Ordering.eq => ok t
    | Ordering.gt =>
      do
      let ep ← O.asExtended t
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN table_A i1
      O.addN ep pnp
  let digit1 ← Array.index_usize b_naf i
  let o1 ← lift (core.cmp.impls.OrdI8.cmp digit1 0#i8)
  let t2 ←
    match o1 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t1
      let i1 ← -. digit1
      let i2 ← lift (IScalar.hcast .Usize i1)
      let anp ← window.NafLookupTable5.select O.copyN table_B i2
      O.subN ep anp
    | Ordering.eq => ok t1
    | Ordering.gt =>
      do
      let ep ← O.asExtended t1
      let i1 ← lift (IScalar.hcast .Usize digit1)
      let anp ← window.NafLookupTable5.select O.copyN table_B i1
      O.addN ep anp
  let r1 ← O.cAsProjective t2
  if i = 0#usize
  then
    let ep ← O.pAsExtended r1
    ok (done ep)
  else let i1 ← i - 1#usize
       ok (cont (i1, r1))

/-- `mul_loop1` over the point operations (vdbLoop1N). -/
@[expose] def vdbLoop1N (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N) (r : O.Pr) :
    Result O.E := do
  loop (fun (i1, r1) => O.vdbLoop1NBody a_naf b_naf table_A table_B i1 r1) (i, r)

open scoped Helpers.IndexStep in
/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
theorem vdbLoop1T_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (haddA : O.AddASpec)
    (hsubA : O.SubASpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec) (hpasE : O.PAsExtendedSpec)
    (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An)
    (r : O.Pr) (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt O.nB)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt O.aB)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 8)
    (hi : i.val < 256) (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    O.vdbLoop1T a_naf b_naf i table_A table_B r ⦃ (res : O.E) => O.OnCurve res ∧
        O.toPoint res = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ O.Bnd res ⦄ := by
  unfold vdbLoop1T
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ O.pOnCurve q ∧ O.pBnd q ∧
      O.pToPoint q = nafTail a_naf (j.val + 1) • A + nafTail b_naf (j.val + 1) • B)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold vdbLoop1TBody
    step with hdbl q hqb hq as ⟨t, hton, htp, htb⟩
    step as ⟨d, hd⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t1 => O.cOnCurve t1 ∧ O.cToPoint t1 = O.cToPoint t + d.val • A ∧
      O.cBnd t1)
    · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE t htb hton as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i2 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with hsubN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨hton, rfl, htb⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE t htb hton as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i1 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with haddN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t1 ⟨ht1on, ht1p, ht1b⟩
    step as ⟨e, he⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp e 0#i8) = ok (compare e.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t2 => O.cOnCurve t2 ∧ O.cToPoint t2 = O.cToPoint t1 + e.val • B ∧
      O.cBnd t2)
    · rcases lt_trichotomy e.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE t1 ht1b ht1on as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 8) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable8.select_spec (P := B) _ table_B i2 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with hsubA ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show O.aToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨ht1on, rfl, ht1b⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE t1 ht1b ht1on as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 8) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable8.select_spec (P := B) _ table_B i1 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with haddA ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show O.aToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t2 ⟨ht2on, ht2p, ht2b⟩
    step with hasP t2 ht2b ht2on as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : O.pToPoint r1 = nafTail a_naf j.val • A + nafTail b_naf j.val • B := by
      rw [hr1p, ht2p, ht1p, htp, hqp, horner_step, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd, ← he]
    split
    · step with hpasE r1 hr1b hr1on as ⟨res, hreson, hresp, hresb⟩
      have hj0 : j.val = 0 := by scalar_tac
      refine ⟨hreson, ?_, hresb⟩
      rw [hresp, hval, hj0]
    · step as ⟨j1, hj1⟩
      have hj1' : j1.val + 1 = j.val := by scalar_tac
      refine ⟨by scalar_tac, hr1on, hr1b, ?_, by scalar_tac⟩
      rw [hval, hj1']
  · exact ⟨hi, hr, hrb, hrp⟩

open scoped Helpers.IndexStep in
/-- The second loop of `mul`: after the digits `i, …, 255`, the accumulator represents
`nafTail a i • A + nafTail b i • B`. -/
theorem vdbLoop1N_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec) (hpasE : O.PAsExtendedSpec)
    (a_naf b_naf : Array I8 256#usize) (i : Usize)
    (table_A : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N)
    (r : O.Pr) (A B : curve25519.edwards.Point)
    (hA : table_A.Represents A) (hAb : table_A.LimbsLt O.nB)
    (hB : table_B.Represents B) (hBb : table_B.LimbsLt O.nB)
    (ha : ∀ k : ℕ, k < 256 → a_naf[k]!.val ≠ 0 → a_naf[k]!.val % 2 = 1 ∧
      2 * |a_naf[k]!.val| < 2 ^ 5)
    (hb : ∀ k : ℕ, k < 256 → b_naf[k]!.val ≠ 0 → b_naf[k]!.val % 2 = 1 ∧
      2 * |b_naf[k]!.val| < 2 ^ 5)
    (hi : i.val < 256) (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = nafTail a_naf (i.val + 1) • A + nafTail b_naf (i.val + 1) • B) :
    O.vdbLoop1N a_naf b_naf i table_A table_B r ⦃ (res : O.E) => O.OnCurve res ∧
        O.toPoint res = nafTail a_naf 0 • A + nafTail b_naf 0 • B ∧ O.Bnd res ⦄ := by
  unfold vdbLoop1N
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ O.pOnCurve q ∧ O.pBnd q ∧
      O.pToPoint q = nafTail a_naf (j.val + 1) • A + nafTail b_naf (j.val + 1) • B)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold vdbLoop1NBody
    step with hdbl q hqb hq as ⟨t, hton, htp, htb⟩
    step as ⟨d, hd⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t1 => O.cOnCurve t1 ∧ O.cToPoint t1 = O.cToPoint t + d.val • A ∧
      O.cBnd t1)
    · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE t htb hton as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i2 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with hsubN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨hton, rfl, htb⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE t htb hton as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (ha j.val hj (by rw [← hd]; omega))
        rw [← hd, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := A) _ table_A i1 hAb hA
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with haddN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine ⟨ht1on, ?_, ht1b⟩
        rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t1 ⟨ht1on, ht1p, ht1b⟩
    step as ⟨e, he⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp e 0#i8) = ok (compare e.val 0) from rfl, bind_ok]
    apply spec_bind (Pₘ := fun t2 => O.cOnCurve t2 ∧ O.cToPoint t2 = O.cToPoint t1 + e.val • B ∧
      O.cBnd t2)
    · rcases lt_trichotomy e.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE t1 ht1b ht1on as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_neg hneg] at hk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := B) _ table_B i2 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with hsubN ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        rw [hzero, zero_smul, add_zero]
        exact ⟨ht1on, rfl, ht1b⟩
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE t1 ht1b ht1on as ⟨ep, hepon, hep, hepb⟩
        have hk := naf_digit_abs (w := 5) (by norm_num) (hb j.val hj (by rw [← he]; omega))
        rw [← he, abs_of_pos hpos] at hk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := B) _ table_B i1 hBb hB
            ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
        step with haddN ep pnp hepb hpb hepon hpon as ⟨t2, ht2on, ht2p, ht2b⟩
        refine ⟨ht2on, ?_, ht2b⟩
        rw [ht2p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
        exact add_nsmul_eq _ _ _ _ (by omega)
    rintro t2 ⟨ht2on, ht2p, ht2b⟩
    step with hasP t2 ht2b ht2on as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : O.pToPoint r1 = nafTail a_naf j.val • A + nafTail b_naf j.val • B := by
      rw [hr1p, ht2p, ht1p, htp, hqp, horner_step, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd, ← he]
    split
    · step with hpasE r1 hr1b hr1on as ⟨res, hreson, hresp, hresb⟩
      have hj0 : j.val = 0 := by scalar_tac
      refine ⟨hreson, ?_, hresb⟩
      rw [hresp, hval, hj0]
    · step as ⟨j1, hj1⟩
      have hj1' : j1.val + 1 = j.val := by scalar_tac
      refine ⟨by scalar_tac, hr1on, hr1b, ?_, by scalar_tac⟩
      rw [hval, hj1']
  · exact ⟨hi, hr, hrb, hrp⟩

end Curve25519Dalek.EdwardsOps
