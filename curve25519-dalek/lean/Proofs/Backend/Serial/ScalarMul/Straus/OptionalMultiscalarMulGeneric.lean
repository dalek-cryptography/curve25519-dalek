/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Helpers.Cmp
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
public import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.NonAdjacentForm
import Proofs.Window.NafLookupTable5Select
public import Proofs.Helpers.EdwardsOps
public section

/-! # `Straus::optional_multiscalar_mul`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`OptionalMultiscalarMul.lean`).

Variable-time Straus: the width-`5` non-adjacent forms of the scalars, the tables of odd
multiples of the points (`None` as soon as a point is `None`, as the patched helper), and
Horner's rule in base `2` over the `256` digit positions, adding `d • P_i` for each nonzero digit
(up to the shorter of the two inputs). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.straus

/-- `Forall₂` as a statement about the entries `getElem!`. -/
theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _


end Curve25519Dalek.backend.serial.scalar_mul.straus

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.straus

variable (O : EdwardsOps)

open ControlFlow

/-- `optional_multiscalar_mul_loop0_loop0.body` over the point operations. -/
@[expose] def strausLoop00Body (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (i : Usize)
    (iter : core.ops.range.Range Usize) (t : O.C) :
    Result (ControlFlow ((core.ops.range.Range Usize) × O.C) O.C) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done t)
  | some k =>
    let a ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array I8 256#usize)) nafs k
    let nlt ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.NafLookupTable5 O.N))
        lookup_tables k
    let digit ← Array.index_usize a i
    let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
    match o with
    | Ordering.lt =>
      let ep ← O.asExtended t
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN nlt i2
      let t1 ← O.subN ep pnp
      ok (cont (iter1, t1))
    | Ordering.eq => ok (cont (iter1, t))
    | Ordering.gt =>
      let ep ← O.asExtended t
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN nlt i1
      let t1 ← O.addN ep pnp
      ok (cont (iter1, t1))

/-- `optional_multiscalar_mul_loop0_loop0` over the point operations. -/
@[expose] def strausLoop00 (iter : core.ops.range.Range Usize)
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (i : Usize) (t : O.C) :
    Result O.C := do
  loop (fun (iter1, t1) => O.strausLoop00Body nafs lookup_tables i iter1 t1) (iter, t)

/-- `optional_multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def strausLoop0Body (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (r : O.Pr) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.Pr)
      O.Pr) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done r)
  | some i =>
    let t ← O.pDouble r
    let i1 := alloc.vec.Vec.len nafs
    let i2 := alloc.vec.Vec.len lookup_tables
    let n ← lift (core.cmp.impls.OrdUsize.min i1 i2)
    let t1 ← O.strausLoop00 { start := 0#usize, «end» := n } nafs lookup_tables i t
    let r1 ← O.cAsProjective t1
    ok (cont (iter1, r1))

/-- `optional_multiscalar_mul_loop0` over the point operations. -/
@[expose] def strausLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (r : O.Pr) : Result O.Pr := do
  loop (fun (iter1, r1) => O.strausLoop0Body nafs lookup_tables iter1 r1) (iter, r)

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[i] • P_k` for `k = k₀, …, n - 1`. -/
private theorem strausLoop00_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec) (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (i : Usize) (t : O.C) (n k : Usize) (P : ℕ → curve25519.edwards.Point)
    (hi : i.val < 256) (hn : n.val ≤ nafs.length ∧ n.val ≤ lookup_tables.length)
    (hT : ∀ m < n.val, lookup_tables.val[m]!.Represents (P m) ∧
      lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < n.val, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hk : k.val ≤ n.val) (ht : O.cOnCurve t) (htb : O.cBnd t) :
    O.strausLoop00 { start := k, «end» := n } nafs lookup_tables i t
      ⦃ (r : O.C) => O.cOnCurve r ∧ O.cBnd r ∧
        O.cToPoint r = O.cToPoint t + ∑ m ∈ Finset.Ico k.val n.val,
          (nafs.val[m]!)[i.val]!.val • P m ⦄ := by
  unfold strausLoop00
  apply loop.spec_decr_nat (measure := fun (it, _) => n.val - it.start.val)
    (inv := fun (it, t') => it.end = n ∧ k.val ≤ it.start.val ∧
      it.start.val ≤ n.val ∧ O.cOnCurve t' ∧ O.cBnd t' ∧
      O.cToPoint t' = O.cToPoint t + ∑ m ∈ Finset.Ico k.val it.start.val,
        (nafs.val[m]!)[i.val]!.val • P m)
  · rintro ⟨⟨k', e⟩, t'⟩ ⟨he, hkk, hkn, ht'on, ht'b, ht'p⟩
    dsimp only at he
    subst e
    unfold strausLoop00Body
    by_cases hlt : k' < n
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hk1, he1⟩
      subst ho
      have hm : k'.val < n.val := hlt
      obtain ⟨hrep, hb⟩ := hT k'.val hm
      step as ⟨a, ha⟩
      rw [← getElem!_pos] at ha
      step as ⟨tab, htab⟩
      rw [← getElem!_pos] at htab
      step as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI8.cmp d 0#i8) = ok (compare d.val 0) from rfl, bind_ok]
      have hfinish (t1 : O.C) (ht1on : O.cOnCurve t1)
          (ht1p : O.cToPoint t1 = O.cToPoint t' + d.val • P k'.val) (ht1b : O.cBnd t1) :
          it1.end = n ∧ k.val ≤ it1.start.val ∧ it1.start.val ≤ n.val ∧
          O.cOnCurve t1 ∧ O.cBnd t1 ∧
          O.cToPoint t1 = O.cToPoint t + ∑ m ∈ Finset.Ico k.val it1.start.val,
            (nafs.val[m]!)[i.val]!.val • P m ∧ n.val - it1.start.val < n.val - k'.val := by
        refine ⟨he1, by scalar_tac, by scalar_tac, ht1on, ht1b, ?_, by scalar_tac⟩
        rw [ht1p, ht'p, show it1.start.val = k'.val + 1 by scalar_tac,
          Finset.sum_Ico_succ_top hkk, add_assoc, hd, ha]
      rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
      · rw [(compare_lt_iff_lt).mpr hneg]
        simp only
        step with hasE t' ht'b ht'on as ⟨ep, hepon, hep, hepb⟩
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_neg hneg] at hdk
        step as ⟨i1, hi1⟩
        step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
        step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i2
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with hsubN ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine hfinish t1 ht1on ?_ ht1b
        rw [ht1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
        exact sub_nsmul_eq _ _ _ _ (by omega)
      · rw [(compare_eq_iff_eq).mpr hzero]
        simp only [WP.spec_ok]
        exact hfinish t' ht'on (by rw [hzero, zero_smul, add_zero]) ht'b
      · rw [(compare_gt_iff_gt).mpr hpos]
        simp only
        step with hasE t' ht'b ht'on as ⟨ep, hepon, hep, hepb⟩
        have hdk := naf_digit_abs (w := 5) (by norm_num)
          (hD k'.val hm i.val hi (by rw [← ha, ← hd]; omega))
        rw [← ha, ← hd, abs_of_pos hpos] at hdk
        step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
        step with window.NafLookupTable5.select_spec (P := P k'.val) _ tab i1
          (htab ▸ hb) (htab ▸ hrep) ⟨by omega, by omega⟩ as ⟨q, hqon, hq, hqb⟩
        step with haddN ep q hepb hqb hepon hqon as ⟨t1, ht1on, ht1p, ht1b⟩
        refine hfinish t1 ht1on ?_ ht1b
        rw [ht1p, hep, show O.nToPoint q = PointRepr.toPoint q from rfl, hq]
        exact add_nsmul_eq _ _ _ _ (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : k'.val = n.val := by scalar_tac
      exact ⟨ht'on, ht'b, this ▸ ht'p⟩
  · exact ⟨rfl, le_refl _, hk, ht, htb,
      by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 255`, the accumulator represents
`∑_{m < n} nafTail d_m e • P_m`. -/
theorem strausLoop0_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (nafs : alloc.vec.Vec (Array I8 256#usize))
    (lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (r : O.Pr) (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min nafs.length lookup_tables.length)
    (hT : ∀ m < n, lookup_tables.val[m]!.Represents (P m) ∧
      lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < n, ∀ e : ℕ, e < 256 → (nafs.val[m]!)[e]!.val ≠ 0 →
      (nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! iter.iter.end.val • P m) :
    O.strausLoop0 iter nafs lookup_tables r ⦃ (res : O.Pr) => O.pOnCurve res ∧ O.pBnd res ∧
        O.pToPoint res = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! 0 • P m ⦄ := by
  unfold strausLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ O.pOnCurve q ∧
      O.pBnd q ∧
        O.pToPoint q = ∑ m ∈ Finset.range n, nafTail nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold strausLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      step with hdbl q hqb hqon as ⟨t, hton, htp, htb⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with O.strausLoop00_spec haddN hsubN hasE nafs lookup_tables i t m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hton htb
        as ⟨t1, ht1on, ht1b, ht1⟩
      step with hasP t1 ht1b ht1on as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      rw [hq1, ht1, htp, hqp, hmn, ← Finset.range_eq_Ico, hend1, ← hi,
        horner2 n i.val (fun k => nafs.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hr, hrb, hrp⟩

end Curve25519Dalek.EdwardsOps
