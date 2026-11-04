/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
public import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.AsInt
public import Proofs.Helpers.Naf
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.Vec
import Proofs.Scalar.AsRadix2w
import Proofs.Scalar.ToRadix2wSizeHint
public import Proofs.Helpers.EdwardsOps
public section

/-! # `Pippenger::optional_multiscalar_mul`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`OptionalMultiscalarMul.lean`).

Pippenger's bucket method with radix-`2^w` digits (`w ∈ {6, 7, 8}` by the input size): for each
digit position `e` from the top, the points are added into the buckets `1, …, 2^(w-1)` by the
absolute value of their digit (subtracted for a negative digit), the buckets are combined into
`∑_b b • bucket_b = ∑_i d_i[e] • P_i` by two running sums, and the column is added to `2^w •` the
total. Only the first `min(|scalars|, |points|)` pairs are used (the patched zip); a `None`
among them gives `None`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.pippenger

/-- `Forall₂` as a statement about the entries `getElem!`. -/
private theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ k < l₁.length, R l₁[k]! l₂[k]! := by
  refine ⟨h.length_eq, fun k hk => ?_⟩
  rw [getElem!_pos l₁ k hk, getElem!_pos l₂ k (h.length_eq ▸ hk)]
  exact (List.forall₂_iff_get.mp h).2 k hk _

/-- The pairs actually used: with no `none` among the first `|ss|` points, the sum over the
`zipWith` with the `some` points is the sum over the first `min |ss| |ops|` indices. -/
private theorem sum_zipWith_filterMap {α β G : Type} [Inhabited α] [Inhabited β]
    [AddCommMonoid G] (f : α → β → G) (ss : List α) (ops : List (Option β))
    (h : none ∉ ops.take ss.length) :
    (List.zipWith f ss (ops.filterMap id)).sum =
      ∑ k ∈ Finset.range (min ss.length ops.length), f ss[k]! (ops[k]!.getD default) := by
  induction ss generalizing ops with
  | nil => simp
  | cons s ss ih =>
    cases ops with
    | nil => simp
    | cons o ops =>
      rcases o with _ | b
      · simp at h
      · rw [List.filterMap_cons_some (by rfl), List.zipWith_cons_cons, List.sum_cons,
          ih ops (by simpa using h), List.length_cons, List.length_cons, Nat.add_min_add_right,
          Finset.sum_range_succ']
        simp [add_comm]

/-- The digits of position `< dc` give the value, if the others vanish. -/
private theorem sum_digits (d : Array I8 64#usize) (w dc : ℕ) (hdc : dc ≤ 64)
    (hz : ∀ j : ℕ, j < 64 → dc ≤ j → d[j]!.val = 0) :
    ∑ j ∈ Finset.range dc, 2 ^ (w * j) * d[j]!.val = d.asInt w := by
  rw [Array.asInt_eq_sum, show (64#usize).val = 64 from rfl,
    ← Finset.sum_range_add_sum_Ico _ hdc]
  have h0 : ∑ j ∈ Finset.Ico dc 64, (2 : ℤ) ^ (w * j) * d[j]!.val = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have := Finset.mem_Ico.mp hj
      rw [hz j this.2 this.1, mul_zero]
  rw [h0, add_zero]

/-- Exchanging the sums over the digit positions and the points. -/
private theorem sum_columns (m dc w : ℕ) (d : ℕ → Array I8 64#usize)
    (P : ℕ → curve25519.edwards.Point) :
    ∑ j ∈ Finset.range dc, 2 ^ (w * j) • ∑ k ∈ Finset.range m, ((d k)[j]!.val : ℤ) • P k =
      ∑ k ∈ Finset.range m, (∑ j ∈ Finset.range dc, 2 ^ (w * j) * (d k)[j]!.val) • P k := by
  simp_rw [Finset.smul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, smul_smul]
  push_cast
  rfl

/-- The weighted sum `∑_{b < n} (b + 1) • f l[b]` of the buckets `l`. -/
private noncomputable def wsum {α : Type} [Inhabited α] (f : α → curve25519.edwards.Point)
    (l : List α)
    (n : ℕ) : curve25519.edwards.Point :=
  ∑ b ∈ Finset.range n, (b + 1) • f l[b]!

private theorem getElem!_set_ne' {α : Type} [Inhabited α] (l : List α) (b j : ℕ) (x : α)
    (h : j ≠ b) : (l.set b x)[j]! = l[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm h)]

private theorem getElem!_set_eq' {α : Type} [Inhabited α] (l : List α) (b : ℕ) (x : α)
    (h : b < l.length) : (l.set b x)[b]! = x := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

/-- Changing bucket `b` changes the weighted sum by `(b + 1) •` the change. -/
private theorem wsum_set {α : Type} [Inhabited α] (f : α → curve25519.edwards.Point)
    (l : List α) (n b : ℕ) (hb : b < n) (hl : l.length = n) (x : α) :
    wsum f (l.set b x) n = wsum f l n + (b + 1) • (f x - f l[b]!) := by
  unfold wsum
  have hmem : b ∈ Finset.range n := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
    getElem!_set_eq' l b x (hl ▸ hb)]
  have hrest : ∑ j ∈ (Finset.range n).erase b, (j + 1) • f (l.set b x)[j]! =
      ∑ j ∈ (Finset.range n).erase b, (j + 1) • f l[j]! :=
    Finset.sum_congr rfl fun j hj => by
      rw [getElem!_set_ne' l b j x (Finset.ne_of_mem_erase hj)]
  rw [hrest, smul_sub]
  abel

/-- The running sums of `optional_multiscalar_mul`: `∑_{b ∈ [i, n)} (b - i + 1) • B b`. -/
private theorem running_sum_step (B : ℕ → curve25519.edwards.Point) (i n : ℕ) (hi : i < n) :
    (∑ b ∈ Finset.Ico (i + 1) n, (b - (i + 1) + 1) • B b) + ∑ b ∈ Finset.Ico i n, B b =
      ∑ b ∈ Finset.Ico i n, (b - i + 1) • B b := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hi, Finset.sum_eq_sum_Ico_succ_bot hi,
    show i - i + 1 = 1 by omega, one_smul]
  have h : ∀ b ∈ Finset.Ico (i + 1) n, (b - i + 1) • B b = (b - (i + 1) + 1) • B b + B b :=
    fun b hb => by
      have := (Finset.mem_Ico.mp hb).1
      rw [show b - i + 1 = (b - (i + 1) + 1) + 1 by omega, succ_nsmul]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  abel


end Curve25519Dalek.backend.serial.scalar_mul.pippenger

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.pippenger

variable (O : EdwardsOps)

open ControlFlow

/-- The buckets of `optional_multiscalar_mul`: `n` points on the curve within the limb bounds. -/
def BucketsOK (v : alloc.vec.Vec O.E) (n : ℕ) : Prop :=
  v.length = n ∧ ∀ j < n, O.OnCurve v.val[j]! ∧ O.Bnd v.val[j]!

/-- The column of digit position `e`: `∑_k d_k[e] • P_k`. -/
noncomputable def column (sp : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (P : ℕ → curve25519.edwards.Point) (e : ℕ) : curve25519.edwards.Point :=
  ∑ k ∈ Finset.range sp.length, ((sp.val[k]!).1[e]!.val : ℤ) • P k

/-- `optional_multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def pippengerLoop0Body (iter : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec O.E) :
    Result (ControlFlow ((core.ops.range.Range Usize) × (alloc.vec.Vec O.E))
      (alloc.vec.Vec O.E)) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buckets)
  | some _ =>
    let ep ← O.identity
    let buckets1 ← alloc.vec.Vec.push buckets ep
    ok (cont (iter1, buckets1))

/-- `optional_multiscalar_mul_loop0` over the point operations. -/
@[expose] def pippengerLoop0 (buckets_count : Usize) (buckets : alloc.vec.Vec O.E) (b : Usize) :
    Result (alloc.vec.Vec O.E) := do
  loop (fun (iter1, buckets1) => O.pippengerLoop0Body iter1 buckets1)
    ({ start := b, «end» := buckets_count }, buckets)

/-- `optional_multiscalar_mul_loop1_loop0.body` over the point operations. -/
@[expose] def pippengerLoop10Body (iter : core.ops.range.Range Usize)
    (buckets : alloc.vec.Vec O.E) :
    Result (ControlFlow ((core.ops.range.Range Usize) × (alloc.vec.Vec O.E))
      (alloc.vec.Vec O.E)) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done buckets)
  | some b =>
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice O.E) buckets b
    let ep ← O.identity
    let buckets1 := index_mut_back ep
    ok (cont (iter1, buckets1))

/-- `optional_multiscalar_mul_loop1_loop0` over the point operations. -/
@[expose] def pippengerLoop10 (buckets_count : Usize) (buckets : alloc.vec.Vec O.E) (b : Usize) :
    Result (alloc.vec.Vec O.E) := do
  loop (fun (iter1, buckets1) => O.pippengerLoop10Body iter1 buckets1)
    ({ start := b, «end» := buckets_count }, buckets)

/-- `optional_multiscalar_mul_loop1_loop1.body` over the point operations. -/
@[expose] def pippengerLoop11Body (digit_index : Usize)
    (iter : core.slice.iter.Iter ((Array I8 64#usize) × O.N))
    (buckets : alloc.vec.Vec O.E) :
    Result (ControlFlow ((core.slice.iter.Iter ((Array I8 64#usize) × O.N)) ×
      (alloc.vec.Vec O.E)) (alloc.vec.Vec O.E)) := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done buckets)
  | some p =>
    let (digits, pt) := p
    let i1 ← Array.index_usize digits digit_index
    let digit ← lift (IScalar.cast .I16 i1)
    let o ← lift (core.cmp.impls.OrdI16.cmp digit 0#i16)
    let buckets1 ←
      match o with
      | Ordering.lt =>
        do
        let i2 ← -. digit
        let i3 ← i2 - 1#i16
        let b ← lift (IScalar.hcast .Usize i3)
        let ep ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice O.E) buckets b
        let cp ← O.subN ep pt
        let ep1 ← O.asExtended cp
        let (_, index_mut_back) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice O.E) buckets b
        ok (index_mut_back ep1)
      | Ordering.eq => ok buckets
      | Ordering.gt =>
        do
        let i2 ← digit - 1#i16
        let b ← lift (IScalar.hcast .Usize i2)
        let ep ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice O.E) buckets b
        let cp ← O.addN ep pt
        let ep1 ← O.asExtended cp
        let (_, index_mut_back) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice O.E) buckets b
        ok (index_mut_back ep1)
    ok (cont (iter1, buckets1))

/-- `optional_multiscalar_mul_loop1_loop1` over the point operations. -/
@[expose] def pippengerLoop11 (scalars_points : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (buckets : alloc.vec.Vec O.E) (digit_index : Usize) (si : Usize) :
    Result (alloc.vec.Vec O.E) := do
  loop (fun (iter1, buckets1) => O.pippengerLoop11Body digit_index iter1 buckets1)
    ({ slice := alloc.vec.Vec.deref scalars_points, i := si.val }, buckets)

/-- `optional_multiscalar_mul_loop1_loop2.body` over the point operations. -/
@[expose] def pippengerLoop12Body (buckets : alloc.vec.Vec O.E)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets_intermediate_sum : O.E) (buckets_sum : O.E) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.E × O.E)
      O.E) := do
  let (o, iter1) ← core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done buckets_sum)
  | some i1 =>
    let ep ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice O.E) buckets i1
    let buckets_intermediate_sum1 ← O.addAssign buckets_intermediate_sum ep
    let buckets_sum1 ← O.addAssign buckets_sum buckets_intermediate_sum1
    ok (cont (iter1, buckets_intermediate_sum1, buckets_sum1))

/-- `optional_multiscalar_mul_loop1_loop2` over the point operations. -/
@[expose] def pippengerLoop12 (buckets : alloc.vec.Vec O.E) (buckets_intermediate_sum : O.E)
    (buckets_sum : O.E) (i : Usize) : Result O.E := do
  loop
    (fun (iter1, buckets_intermediate_sum1, buckets_sum1) =>
      O.pippengerLoop12Body buckets iter1 buckets_intermediate_sum1 buckets_sum1)
    ({ iter := { start := 0#usize, «end» := i } }, buckets_intermediate_sum, buckets_sum)

/-- `optional_multiscalar_mul_loop1.body` over the point operations. -/
@[expose] def pippengerLoop1Body (w : Usize) (buckets_count : Usize)
    (scalars_points : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (buckets : alloc.vec.Vec O.E) (total : Option O.E) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) ×
      (alloc.vec.Vec O.E) × (Option O.E)) (Option O.E)) := do
  let (o, iter1) ← core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done total)
  | some digit_index1 =>
    let buckets1 ← O.pippengerLoop10 buckets_count buckets 0#usize
    let buckets2 ← O.pippengerLoop11 scalars_points buckets1 digit_index1 0#usize
    let i ← buckets_count - 1#usize
    let buckets_intermediate_sum ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice O.E) buckets2 i
    let buckets_sum ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice O.E) buckets2 i
    let buckets_sum1 ← O.pippengerLoop12 buckets2 buckets_intermediate_sum buckets_sum i
    match total with
    | none => ok (cont (iter1, buckets2, some buckets_sum1))
    | some total1 =>
      let i1 ← lift (UScalar.cast .U32 w)
      let ep ← O.mulByPow2 total1 i1
      let buckets_sum2 ← O.add ep buckets_sum1
      ok (cont (iter1, buckets2, some buckets_sum2))

/-- `optional_multiscalar_mul_loop1` over the point operations. -/
@[expose] def pippengerLoop1 (w : Usize) (buckets_count : Usize)
    (scalars_points : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (buckets : alloc.vec.Vec O.E) (total : Option O.E) (digit_index : Usize) :
    Result (Option O.E) := do
  loop
    (fun (iter1, buckets1, total1) =>
      O.pippengerLoop1Body w buckets_count scalars_points iter1 buckets1 total1)
    ({ iter := { start := 0#usize, «end» := digit_index } }, buckets, total)

/-- The first loop: `buckets_count` identities. -/
private theorem pippengerLoop0_spec (hid : O.IdentitySpec) (bc : Usize)
    (buckets : alloc.vec.Vec O.E) (b : Usize) (hbc : bc.val ≤ 128) (hb : b.val ≤ bc.val)
    (hlen : buckets.length = b.val)
    (hbk : ∀ j < b.val, O.OnCurve buckets.val[j]! ∧ O.Bnd buckets.val[j]! ∧
      O.toPoint buckets.val[j]! = 0) :
    O.pippengerLoop0 bc buckets b ⦃ (r : alloc.vec.Vec O.E) => O.BucketsOK r bc.val ⦄ := by
  unfold pippengerLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => bc.val - it.start.val)
    (inv := fun (it, v) => it.end = bc ∧ it.start.val ≤ bc.val ∧ v.length = it.start.val ∧
      ∀ j < it.start.val, O.OnCurve v.val[j]! ∧ O.Bnd v.val[j]! ∧ O.toPoint v.val[j]! = 0)
  · rintro ⟨⟨b', e⟩, v⟩ ⟨he, hb', hl, hv⟩
    dsimp only at he
    subst e
    unfold pippengerLoop0Body
    by_cases hlt : b' < bc
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hb1, he1⟩
      subst ho
      apply spec_bind hid
      rintro e ⟨heon, he, heb⟩
      step as ⟨v1, hv1⟩
      refine ⟨he1, by scalar_tac, by rw [alloc.vec.Vec.length_of_val_eq_append hv1, hl, hb1], ?_,
        by scalar_tac⟩
      rw [hb1, ← hl]
      exact alloc.vec.Vec.forall_lt_of_val_eq_append
        (P := fun _ x => O.OnCurve x ∧ O.Bnd x ∧ O.toPoint x = 0) hv1 (hl ▸ hv) ⟨heon, heb, he⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨this ▸ hl, fun j hj => ⟨(hv j (this ▸ hj)).1, (hv j (this ▸ hj)).2.1⟩⟩
  · exact ⟨rfl, hb, hlen, hbk⟩

/-- The reset loop: every bucket becomes the identity. -/
private theorem pippengerLoop10_spec (hid : O.IdentitySpec) (bc : Usize)
    (buckets : alloc.vec.Vec O.E) (b : Usize) (hok : O.BucketsOK buckets bc.val)
    (hb : b.val ≤ bc.val)
    (hz : ∀ j < b.val, O.toPoint buckets.val[j]! = 0) :
    O.pippengerLoop10 bc buckets b ⦃ (r : alloc.vec.Vec O.E) =>
        O.BucketsOK r bc.val ∧ ∀ j < bc.val, O.toPoint r.val[j]! = 0 ⦄ := by
  unfold pippengerLoop10
  apply loop.spec_decr_nat (measure := fun (it, _) => bc.val - it.start.val)
    (inv := fun (it, v) => it.end = bc ∧ it.start.val ≤ bc.val ∧ O.BucketsOK v bc.val ∧
      ∀ j < it.start.val, O.toPoint v.val[j]! = 0)
  · rintro ⟨⟨b', e⟩, v⟩ ⟨he, hb', ⟨hl, hv⟩, hvz⟩
    dsimp only at he
    subst e
    unfold pippengerLoop10Body
    by_cases hlt : b' < bc
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hb1, he1⟩
      subst ho
      step as ⟨x, back, hx, hback⟩
      apply spec_bind hid
      rintro e ⟨heon, he, heb⟩
      have hbl : b'.val < v.val.length := by
        rw [show v.val.length = v.length from rfl, hl]; scalar_tac
      rw [WP.spec_ok]
      refine ⟨he1, by scalar_tac, ⟨?_, fun j hj => ?_⟩, fun j hj => ?_, by scalar_tac⟩
      · rw [hback, alloc.vec.Vec.set_length, hl]
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact ⟨heon, heb⟩
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
      · rw [hback, alloc.vec.Vec.set_val_eq]
        rcases eq_or_ne j b'.val with rfl | hne
        · rw [getElem!_set_eq' _ _ _ hbl]; exact he
        · rw [getElem!_set_ne' _ _ _ _ hne]; exact hvz j (by scalar_tac)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : b'.val = bc.val := by scalar_tac
      exact ⟨⟨hl, hv⟩, fun j hj => hvz j (this ▸ hj)⟩
  · exact ⟨rfl, hb, hok, hz⟩

/-- The running sums: `buckets_sum` ends as `∑_b (b + 1) • bucket_b`. -/
private theorem pippengerLoop12_spec (hadda : O.AddAssignSpec) (buckets : alloc.vec.Vec O.E)
    (bc : ℕ)
    (hok : O.BucketsOK buckets bc) (inter sum : O.E) (i : Usize)
    (hi : i.val < bc) (hinter : O.OnCurve inter ∧ O.Bnd inter ∧
      O.toPoint inter = ∑ b ∈ Finset.Ico i.val bc, O.toPoint buckets.val[b]!)
    (hsum : O.OnCurve sum ∧ O.Bnd sum ∧
      O.toPoint sum = ∑ b ∈ Finset.Ico i.val bc, (b - i.val + 1) • O.toPoint buckets.val[b]!) :
    O.pippengerLoop12 buckets inter sum i ⦃ (r : O.E) => O.OnCurve r ∧ O.Bnd r ∧
        O.toPoint r = wsum O.toPoint buckets.val bc ⦄ := by
  unfold pippengerLoop12
  apply loop.spec_decr_nat (measure := fun (ri, _, _) => ri.iter.end.val)
    (inv := fun (ri, it, sm) => ri.iter.start = 0#usize ∧ ri.iter.end.val < bc ∧
      O.OnCurve it ∧ O.Bnd it ∧
        O.toPoint it = ∑ b ∈ Finset.Ico ri.iter.end.val bc, O.toPoint buckets.val[b]! ∧
      O.OnCurve sm ∧ O.Bnd sm ∧
        O.toPoint sm = ∑ b ∈ Finset.Ico ri.iter.end.val bc,
          (b - ri.iter.end.val + 1) • O.toPoint buckets.val[b]!)
  · rintro ⟨⟨⟨start, i'⟩⟩, it, sm⟩ ⟨hst, hi', hiton, hitb, hitp, hsmon, hsmb, hsmp⟩
    dsimp only at hst
    subst start
    unfold pippengerLoop12Body
    by_cases hpos : i' > 0#usize
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, ri1, i1, ho, hii, hstart, hend⟩
      subst ho
      have hi1b : i1.val < bc := by scalar_tac
      step as ⟨ep, hep⟩
      rw [← getElem!_pos] at hep
      obtain ⟨hepon, hepb⟩ := hok.2 i1.val hi1b
      rw [← hep] at hepon hepb
      step with hadda it ep hitb hepb hiton hepon as ⟨it1, hit1on, hit1, hit1b⟩
      step with hadda sm it1 hsmb hit1b hsmon hit1on as ⟨sm1, hsm1on, hsm1, hsm1b⟩
      have hii' : i'.val = i1.val + 1 := hii.symm
      have hsum1 : ∑ b ∈ Finset.Ico i1.val bc, O.toPoint buckets.val[b]! =
          ∑ b ∈ Finset.Ico i'.val bc, O.toPoint buckets.val[b]! + O.toPoint ep := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hi1b, hii', hep, add_comm]
      simp only [hend]
      refine ⟨hstart, hi1b, hit1on, hit1b, by rw [hit1, hitp, hsum1], hsm1on, hsm1b, ?_,
        by rw [hii']; exact Nat.lt_succ_self _⟩
      rw [hsm1, hit1, hsmp, hitp, ← hsum1, hii']
      exact running_sum_step (fun b => O.toPoint buckets.val[b]!) i1.val bc hi1b
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, ri1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have h0 : i'.val = 0 := by scalar_tac
      refine ⟨hsmon, hsmb, ?_⟩
      rw [hsmp, h0, wsum, Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.sub_zero]
  · exact ⟨rfl, hi, hinter.1, hinter.2.1, hinter.2.2, hsum.1, hsum.2.1, hsum.2.2⟩

open scoped Helpers.IndexStep in
/-- The accumulation loop: point `k` (from `si` on) is added to bucket `d_k[e] - 1`, or subtracted
from bucket `-d_k[e] - 1`; the weighted sum of the buckets grows by `d_k[e] • P_k`. -/
private theorem pippengerLoop11_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (buckets : alloc.vec.Vec O.E) (e si : Usize) (bc : ℕ)
    (P : ℕ → curve25519.edwards.Point) (he : e.val < 64) (hbc : bc ≤ 128)
    (hsp : ∀ k < sp.length, O.nOnCurve (sp.val[k]!).2 ∧ O.nBnd (sp.val[k]!).2 ∧
      O.nToPoint (sp.val[k]!).2 = P k)
    (hdig : ∀ k < sp.length, -(bc : ℤ) ≤ (sp.val[k]!).1[e.val]!.val ∧
      (sp.val[k]!).1[e.val]!.val ≤ bc)
    (hok : O.BucketsOK buckets bc) (hsi : si.val ≤ sp.length) :
    O.pippengerLoop11 sp buckets e si ⦃ (r : alloc.vec.Vec O.E) => O.BucketsOK r bc ∧
        wsum O.toPoint r.val bc = wsum O.toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val sp.length, (sp.val[k]!).1[e.val]!.val • P k ⦄ := by
  have hsplen : (alloc.vec.Vec.deref sp).val = sp.val := Slice.from_val _ _
  unfold pippengerLoop11
  apply loop.spec_decr_nat (measure := fun (it, _) => sp.length - it.i)
    (inv := fun (it, v) => it.slice = alloc.vec.Vec.deref sp ∧ si.val ≤ it.i ∧ it.i ≤ sp.length ∧
      O.BucketsOK v bc ∧
      wsum O.toPoint v.val bc = wsum O.toPoint buckets.val bc +
          ∑ k ∈ Finset.Ico si.val it.i, (sp.val[k]!).1[e.val]!.val • P k)
  · rintro ⟨⟨slice, si'⟩, v⟩ ⟨hslice, hss, hsl, ⟨hvl, hv⟩, hw⟩
    dsimp only at hslice
    subst slice
    dsimp only at hss hsl hw
    unfold pippengerLoop11Body
    by_cases hlt : si' < sp.length
    · step with sliceNextSome (alloc.vec.Vec.deref sp) si' (by simpa only [hsplen] using hlt)
        as ⟨o, it1, ho, hi1⟩
      subst ho hi1
      rw [← getElem!_pos (alloc.vec.Vec.deref sp).val si'
        (by simpa only [hsplen] using hlt), hsplen]
      generalize hdp : sp.val[si']! = pair
      obtain ⟨digits, pt⟩ := pair
      replace hdp : (digits, pt) = sp.val[si']! := hdp.symm
      obtain ⟨hpton, hptb, hptp⟩ := hsp si' hlt
      obtain ⟨hdl, hdu⟩ := hdig si' hlt
      rw [← hdp] at hpton hptb hptp hdl hdu
      simp only at hpton hptb hptp hdl hdu
      step as ⟨d8, hd8⟩
      step with IScalar.cast_inBounds_spec as ⟨d, hd⟩
      rw [show lift (core.cmp.impls.OrdI16.cmp d 0#i16) = ok (compare d.val 0) from rfl, bind_ok]
      apply spec_bind (Pₘ := fun v1 => O.BucketsOK v1 bc ∧
        wsum O.toPoint v1.val bc = wsum O.toPoint v.val bc + d.val • P si')
      · rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
        · rw [(compare_lt_iff_lt).mpr hneg]
          simp only
          step as ⟨i2, hi2⟩
          step as ⟨i3, hi3⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = (-d.val).toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with hsubN ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with hasE c hcb hcon as ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [sub_sub_cancel_left, smul_neg, ← natCast_zsmul, ← neg_zsmul]
            congr 1
            push_cast
            omega
        · rw [(compare_eq_iff_eq).mpr hzero]
          simp only [WP.spec_ok]
          rw [hzero, zero_smul, add_zero]
          exact ⟨⟨hvl, hv⟩, rfl⟩
        · rw [(compare_gt_iff_gt).mpr hpos]
          simp only
          step as ⟨i2, hi2⟩
          step with IScalar.hcast_inBounds_spec as ⟨b, hb⟩
          have hbv : b.val + 1 = d.val.toNat := by scalar_tac
          have hbl : b.val < bc := by scalar_tac
          step as ⟨ep, hep⟩
          rw [← getElem!_pos] at hep
          obtain ⟨hepon, hepb⟩ := hv b.val hbl
          rw [← hep] at hepon hepb
          step with haddN ep pt hepb hptb hepon hpton as ⟨c, hcon, hc, hcb⟩
          step with hasE c hcb hcon as ⟨ep1, hep1on, hep1, hep1b⟩
          step as ⟨y, back, hy, hback⟩
          have hbl' : b.val < v.val.length := by
            rw [show v.val.length = v.length from rfl, hvl]; exact hbl
          refine ⟨⟨by rw [hback, alloc.vec.Vec.set_length, hvl], fun j hj => ?_⟩, ?_⟩
          · rw [hback, alloc.vec.Vec.set_val_eq]
            rcases eq_or_ne j b.val with rfl | hne
            · rw [getElem!_set_eq' _ _ _ hbl']; exact ⟨hep1on, hep1b⟩
            · rw [getElem!_set_ne' _ _ _ _ hne]; exact hv j hj
          · rw [hback, alloc.vec.Vec.set_val_eq, wsum_set _ _ _ _ hbl hvl, hep1, hc, ← hep, hptp]
            congr 1
            rw [add_sub_cancel_left, ← natCast_zsmul]
            congr 1
            push_cast
            omega
      · rintro v1 ⟨hok1, hw1⟩
        rw [WP.spec_ok]
        dsimp only
        refine ⟨rfl, by omega, by omega, hok1, ?_, by omega⟩
        rw [hw1, hw, Finset.sum_Ico_succ_top hss,
          add_assoc, hd, hd8, ← hdp]
    · step with sliceNextNone (alloc.vec.Vec.deref sp) si'
        (by simpa only [hsplen] using Nat.le_of_not_lt hlt) as ⟨o, it1, ho, hi1⟩
      subst ho hi1
      simp only [WP.spec_ok]
      have : si' = sp.length := by scalar_tac
      exact ⟨⟨hvl, hv⟩, this ▸ hw⟩
  · exact ⟨rfl, le_refl _, hsi, hok, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

open scoped Helpers.IndexStep in
/-- The outer loop over the digit positions, from the top: the total is
`∑_{j} 2^(w j) • column (di + j)` over the positions processed. -/
private theorem pippengerLoop1_spec (hid : O.IdentitySpec) (hadd : O.AddSpec)
    (hadda : O.AddAssignSpec)
    (hmul : O.MulByPow2Spec) (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec) (w bc : Usize)
    (sp : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (buckets : alloc.vec.Vec O.E) (total : Option O.E) (di : Usize)
    (P : ℕ → curve25519.edwards.Point) (dc : ℕ) (hw : 0 < w.val ∧ w.val ≤ 8)
    (hbc1 : 1 ≤ bc.val) (hbc : bc.val ≤ 128) (hdc : dc ≤ 64)
    (hsp : ∀ k < sp.length, O.nOnCurve (sp.val[k]!).2 ∧ O.nBnd (sp.val[k]!).2 ∧
      O.nToPoint (sp.val[k]!).2 = P k)
    (hdig : ∀ k < sp.length, ∀ e : ℕ, e < 64 → -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
      (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ))
    (hok : O.BucketsOK buckets bc.val) (hdi : di.val ≤ dc)
    (hnone : total = none ↔ di.val = dc)
    (hsome : ∀ T, total = some T → O.OnCurve T ∧ O.Bnd T ∧
      O.toPoint T =
        ∑ j ∈ Finset.range (dc - di.val), 2 ^ (w.val * j) • O.column sp P (di.val + j)) :
    O.pippengerLoop1 w bc sp buckets total di ⦃ (r : Option O.E) => (r = none ↔ dc = 0) ∧
        ∀ T, r = some T → O.OnCurve T ∧ O.Bnd T ∧
          O.toPoint T = ∑ j ∈ Finset.range dc, 2 ^ (w.val * j) • O.column sp P j ⦄ := by
  unfold pippengerLoop1
  apply loop.spec_decr_nat (measure := fun (ri, _, _) => ri.iter.end.val)
    (inv := fun (ri, v, t) => ri.iter.start = 0#usize ∧
      O.BucketsOK v bc.val ∧ ri.iter.end.val ≤ dc ∧ (t = none ↔ ri.iter.end.val = dc) ∧
      ∀ T, t = some T → O.OnCurve T ∧ O.Bnd T ∧
        O.toPoint T = ∑ j ∈ Finset.range (dc - ri.iter.end.val),
          2 ^ (w.val * j) • O.column sp P (ri.iter.end.val + j))
  · rintro ⟨⟨⟨start, d⟩⟩, v, t⟩ ⟨hst, hv, hd, htn, hts⟩
    dsimp only at hst
    subst start
    unfold pippengerLoop1Body
    by_cases hpos : d > 0#usize
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, ri1, d1, ho, hdd, hstart, hend⟩
      subst ho
      have hd1 : d1.val = d.val - 1 := by omega
      have hdpos : 0 < d.val := hpos
      have hdd' : d.val = d1.val + 1 := hdd.symm
      have hd1lt : d1.val < dc := by
        rw [hd1]; exact lt_of_lt_of_le (Nat.sub_lt hdpos Nat.one_pos) hd
      have hd164 : d1.val < 64 := lt_of_lt_of_le hd1lt hdc
      step with O.pippengerLoop10_spec hid bc v 0#usize hv (Nat.zero_le _)
        (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨v1, hv1, hv1z⟩
      step with O.pippengerLoop11_spec haddN hsubN hasE sp v1 d1 0#usize bc.val P
        hd164 hbc hsp (fun k hk => hdig k hk d1.val hd164) hv1
        (Nat.zero_le _) as ⟨v2, hv2, hw2⟩
      step as ⟨i, hi⟩
      have hib : i.val < bc.val := by
        rw [hi]; exact Nat.sub_lt (lt_of_lt_of_le Nat.one_pos hbc1) Nat.one_pos
      have hil : i.val < v2.val.length := by
        rw [show v2.val.length = v2.length from rfl, hv2.1]; exact hib
      step as ⟨inter, hinter⟩
      rw [← getElem!_pos] at hinter
      step as ⟨sm, hsm⟩
      rw [← getElem!_pos] at hsm
      have hIco : Finset.Ico i.val bc.val = {i.val} := by
        rw [show bc.val = i.val + 1 by rw [hi]; exact (Nat.sub_add_cancel hbc1).symm,
          Nat.Ico_succ_singleton]
      obtain ⟨hion, hib'⟩ := hv2.2 i.val hib
      step with O.pippengerLoop12_spec hadda v2 bc.val hv2 inter sm i hib
        ⟨hinter ▸ hion, hinter ▸ hib', by rw [hIco, Finset.sum_singleton, hinter]⟩
        ⟨hsm ▸ hion, hsm ▸ hib', by
          rw [hIco, Finset.sum_singleton, hsm, Nat.sub_self, zero_add, one_smul]⟩
        as ⟨c, hcon, hcb, hc⟩
      have hzero : wsum O.toPoint v1.val bc.val = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [hv1z b (Finset.mem_range.mp hb), smul_zero]
      have hcol : O.toPoint c = O.column sp P d1.val := by
        rw [hc, hw2, hzero, zero_add, ← Finset.range_eq_Ico]
        rfl
      rcases t with _ | T
      · have hdc' : d.val = dc := htn.mp rfl
        dsimp only
        rw [WP.spec_ok]
        simp only [hend]
        refine ⟨hstart, hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd']; exact Nat.lt_succ_self _⟩
        obtain rfl : c = T' := Option.some.inj hT'
        refine ⟨hcon, hcb, ?_⟩
        rw [hcol, show dc - d1.val = 1 by rw [← hdc', hdd', Nat.add_sub_cancel_left],
          Finset.sum_range_one, mul_zero, pow_zero, one_smul, add_zero]
      · obtain ⟨hTon, hTb, hT⟩ := hts T rfl
        have hdc' : d.val ≠ dc := fun h => by cases htn.mpr h
        dsimp only
        step as ⟨k, hk⟩
        have hkw : k.val = w.val := by
          rw [hk, UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt (lt_of_le_of_lt hw.2 (by decide))
        step with hmul T k hTb hTon (by rw [hkw]; exact hw.1) as ⟨T2, hT2on, hT2, hT2b⟩
        step with hadd T2 c hT2b hcb hT2on hcon as ⟨T3, hT3on, hT3, hT3b⟩
        simp only [hend]
        refine ⟨hstart, hv2, Nat.le_of_lt hd1lt,
          ⟨fun h => (by cases h), fun h => absurd h (Nat.ne_of_lt hd1lt)⟩,
          fun T' hT' => ?_, by rw [hdd']; exact Nat.lt_succ_self _⟩
        obtain rfl : T3 = T' := Option.some.inj hT'
        refine ⟨hT3on, hT3b, ?_⟩
        have hdcd : dc - d1.val = (dc - d.val) + 1 := by
          rw [hdd', Nat.sub_add_eq]
          exact (Nat.sub_add_cancel (Nat.sub_pos_of_lt hd1lt)).symm
        rw [hT3, hT2, hT, hcol, hkw, hdcd, Finset.sum_range_succ', Finset.smul_sum]
        rw [mul_zero, pow_zero, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, ← pow_add, hdd', show w.val + w.val * j = w.val * (j + 1) by ring,
          show d1.val + 1 + j = d1.val + (j + 1) by ring]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, ri1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have h0 : d.val = 0 := by scalar_tac
      refine ⟨by rw [htn, h0]; exact eq_comm, fun T hT => ?_⟩
      obtain ⟨hTon, hTb, hT'⟩ := hts T hT
      refine ⟨hTon, hTb, ?_⟩
      rw [hT', h0, Nat.sub_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [zero_add]
  · exact ⟨rfl, hok, hdi, hnone, hsome⟩

/-- The pairs collected by `scalars_points`, up to `m`: digits of `ss[j]` and the projective Niels
form of the point `ops[j] = some P`. -/
def PairsOK (w : ℕ) (ss : List scalar.Scalar) (ops : List (Option O.E))
    (v : alloc.vec.Vec ((Array I8 64#usize) × O.N)) (m : ℕ) : Prop :=
  v.length = m ∧ ∀ j < m, ∃ P, ops[j]! = some P ∧
    O.nOnCurve (v.val[j]!).2 ∧ O.nBnd (v.val[j]!).2 ∧ O.nToPoint (v.val[j]!).2 = O.toPoint P ∧
    (v.val[j]!).1.asInt w = ss[j]!.asNat ∧
    (∀ i : ℕ, i < 64 → -2 ^ w ≤ 2 * (v.val[j]!).1[i]!.val ∧ 2 * (v.val[j]!).1[i]!.val ≤ 2 ^ w) ∧
    ∀ i : ℕ, i < 64 → 256 < i * w → (v.val[j]!).1[i]!.val = 0

/-- `optional_multiscalar_mul.scalars_points_loop.body` over the point operations. -/
@[expose] def pippengerScalarsPointsBody {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It (Option O.E)) (scalars : Slice S) (w : Usize)
    (points : It) (out : alloc.vec.Vec ((Array I8 64#usize) × O.N)) (k : Usize) :
    Result (ControlFlow (It × (alloc.vec.Vec ((Array I8 64#usize) × O.N)) × Usize)
      (Option (alloc.vec.Vec ((Array I8 64#usize) × O.N)))) := do
  let i := Slice.len scalars
  if k < i
  then
    let t ← Slice.index_usize scalars k
    let s ← borrowInst.borrow t
    let s1 ← scalar.Scalar.as_radix_2w s w
    let (o, points1) ← iterInst.next points
    match o with
    | none => ok (done (some out))
    | some o1 =>
      match o1 with
      | none => ok (done none)
      | some P =>
        let pnp ← O.asProjectiveNiels P
        let out1 ← alloc.vec.Vec.push out (s1, pnp)
        let k1 ← k + 1#usize
        ok (cont (points1, out1, k1))
  else ok (done (some out))

/-- `optional_multiscalar_mul.scalars_points_loop` over the point operations. -/
@[expose] def pippengerScalarsPoints {S It : Type} (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It (Option O.E)) (scalars : Slice S)
    (points : It) (w : Usize) (out : alloc.vec.Vec ((Array I8 64#usize) × O.N)) (k : Usize) :
    Result (Option (alloc.vec.Vec ((Array I8 64#usize) × O.N))) := do
  loop
    (fun (points1, out1, k1) =>
      O.pippengerScalarsPointsBody borrowInst iterInst scalars w points1 out1 k1)
    (points, out, k)

/-- `Pippenger::optional_multiscalar_mul` over the point operations. -/
@[expose] def pippengerMain {I J Item IntoIter IntoIter2 : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item IntoIter)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J (Option O.E) IntoIter2)
    (scalars : I) (points : J) : Result (Option O.E) := do
  let t ← scalarsInst.into_iter scalars
  let scalars1 ← alloc.vec.FromIteratorVec.from_iter
    (core.iter.traits.collect.IntoIterator.Blanket scalarsInst.iteratorInst) t
  let size := alloc.vec.Vec.len scalars1
  let w ←
    if size < 500#usize
    then ok 6#usize
    else if size < 800#usize
         then ok 7#usize
         else ok 8#usize
  let max_digit ← 1#usize <<< w
  let digits_count ← scalar.Scalar.to_radix_2w_size_hint w
  let buckets_count ← max_digit / 2#usize
  let s := alloc.vec.Vec.deref scalars1
  let t1 ← pointsInst.into_iter points
  let o ← O.pippengerScalarsPoints borrowInst pointsInst.iteratorInst s t1 w
    (alloc.vec.Vec.new ((Array I8 64#usize) × O.N)) 0#usize
  match o with
  | none => ok none
  | some scalars_points =>
    let buckets ← O.pippengerLoop0 buckets_count (alloc.vec.Vec.new O.E) 0#usize
    let total ← O.pippengerLoop1 w buckets_count scalars_points buckets none digits_count
    let ep ← core.option.Option.expect total (toStr "should have more than zero digits")
    ok (some ep)

/-- The loop of `scalars_points`: the digits of each scalar with the next point, until the
scalars or the points run out; `none` at the first `none` point. -/
private theorem pippengerScalarsPoints_spec (hapn : O.AsProjectiveNielsSpec) {S It : Type}
    (borrowInst : core.borrow.Borrow S scalar.Scalar)
    (iterInst : core.iter.traits.iterator.Iterator It (Option O.E))
    (scalars : Slice S) (ss : List scalar.Scalar)
    (hborrow : List.Forall₂
      (fun x s => borrowInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) scalars.val ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (w : Usize) (hw : 4 ≤ w.val ∧ w.val ≤ 8)
    (ops : List (Option O.E))
    (hps : ∀ P, some P ∈ ops → O.Bnd P ∧ O.OnCurve P) (points : It) (k : Usize)
    (hit : iterInst.Yields points (ops.drop k.val)) (hk : k.val ≤ ss.length)
    (hkops : k.val ≤ ops.length)
    (out : alloc.vec.Vec ((Array I8 64#usize) × O.N))
    (hout : O.PairsOK w.val ss ops out k.val) :
    O.pippengerScalarsPoints borrowInst iterInst scalars points w out k
      ⦃ (r : Option (alloc.vec.Vec ((Array I8 64#usize) × O.N))) =>
        (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ v, r = some v → O.PairsOK w.val ss ops v (min ss.length ops.length) ⦄ := by
  have hslen : scalars.val.length = ss.length := hborrow.length_eq
  have hsb : ∀ k (hk : k < scalars.val.length),
      borrowInst.borrow scalars.val[k] ⦃ (s' : scalar.Scalar) => s' = ss[k]! ⦄ := fun k hk => by
    rw [getElem!_pos ss k (hslen ▸ hk)]
    exact (List.forall₂_iff_get.mp hborrow).2 k hk _
  unfold pippengerScalarsPoints
  apply loop.spec_decr_nat (measure := fun (_, _, k') => ss.length - k'.val)
    (inv := fun (it, o, k') => iterInst.Yields it (ops.drop k'.val) ∧ k'.val ≤ ss.length ∧
      k'.val ≤ ops.length ∧ O.PairsOK w.val ss ops o k'.val)
  · rintro ⟨it, o, k'⟩ ⟨hit', hk', hko, hpo⟩
    unfold pippengerScalarsPointsBody
    by_cases hlt : k'.val < ss.length
    · have hlt' : k' < Slice.len scalars := by scalar_tac
      simp only [hlt', ite_true]
      step as ⟨t, ht⟩
      subst ht
      step with hsb k'.val (by scalar_tac) as ⟨s, hs⟩
      have hs' : s.asNat < 2 ^ 255 := hs ▸ hss _
          (by rw [getElem!_pos ss _ hlt]; exact List.getElem_mem _)
      step with scalar.Scalar.as_radix_2w_spec s w hw hs' as ⟨d, hdv, hdlow, hdall, hdz⟩
      generalize hrest : ops.drop k'.val = rest at hit'
      cases hit' with
      | nil hnext =>
        step with hnext as ⟨o', it1, hq⟩
        subst hq
        dsimp only
        rw [WP.spec_ok]
        have hko' : k'.val = ops.length := by
          have := congrArg List.length hrest
          simp at this; scalar_tac
        refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
        · rw [List.take_of_length_le (by scalar_tac)] at h
          obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
          obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
          rw [getElem!_pos ops j hj, hjn] at hP
          cases hP
        · obtain rfl := Option.some.inj hv
          rwa [show min ss.length ops.length = k'.val by scalar_tac]
      | @cons it it' x xs' hnext hrest' =>
        step with hnext as ⟨o', it1, ho, hit1⟩
        subst ho hit1
        have hk'o : k'.val < ops.length := by
          by_contra hcon
          rw [List.drop_eq_nil_of_le (by scalar_tac)] at hrest
          cases hrest
        have hx : ops[k'.val]! = x := by
          rw [getElem!_pos ops k'.val hk'o]
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).1.symm
        have hxs : xs' = ops.drop (k'.val + 1) := by
          have := List.drop_eq_getElem_cons hk'o
          rw [hrest] at this
          exact (List.cons.inj this).2
        rcases x with _ | P
        · dsimp only
          rw [WP.spec_ok]
          refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => by cases hv⟩
          rw [← hx]
          exact List.mem_take_iff_getElem.mpr ⟨k'.val, by simp only [lt_min_iff]; scalar_tac, by
            rw [getElem!_pos ops k'.val hk'o]⟩
        · have hPmem : some P ∈ ops := by
            rw [← hx, getElem!_pos ops k'.val hk'o]; exact List.getElem_mem _
          obtain ⟨hPb, hPon⟩ := hps P hPmem
          step with hapn P hPb hPon as ⟨pnp, hpon, hpp, hpb⟩
          step with alloc.vec.Vec.push_spec o (d, pnp) (by
            have := hpo.1; have := alloc.vec.Vec.len_ineq o; scalar_tac) as ⟨o1, ho1⟩
          step as ⟨k1, hk1⟩
          have hk1v : k1.val = k'.val + 1 := by scalar_tac
          refine ⟨by rw [hk1v, ← hxs]; exact hrest', by scalar_tac, by scalar_tac,
            ⟨by rw [alloc.vec.Vec.length_of_val_eq_append ho1, hpo.1, hk1v], fun j hj => ?_⟩,
            by scalar_tac⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (hk1v ▸ hj) with hj' | rfl
          · have hjo : j < o.length := hpo.1 ▸ hj'
            rw [show o1.val[j]! = o1[j]! from rfl,
              alloc.vec.Vec.getElem!_of_val_eq_append_of_lt ho1 hjo]
            exact hpo.2 j hj'
          · have := alloc.vec.Vec.getElem!_of_val_eq_append_length ho1
            rw [hpo.1] at this
            rw [show o1.val[k'.val]! = o1[k'.val]! from rfl, this]
            exact ⟨P, hx, hpon, hpb, hpp, by rw [hdv, hs], hdall, hdz⟩
    · have hge : ¬ k' < Slice.len scalars := by scalar_tac
      simp only [hge, ite_false, WP.spec_ok]
      have hks : k'.val = ss.length := by scalar_tac
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun v hv => ?_⟩
      · obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem h
        simp only [List.length_take] at hj
        obtain ⟨P, hP, -⟩ := hpo.2 j (by scalar_tac)
        rw [getElem!_pos ops j (by scalar_tac), ← List.getElem_take (j := ss.length)] at hP
        · rw [hjn] at hP; cases hP
        · rw [List.length_take]; exact hj
      · obtain rfl := Option.some.inj hv
        rwa [show min ss.length ops.length = k'.val by scalar_tac]
  · exact ⟨hit, hk, hkops, hout⟩

/-- `Pippenger::optional_multiscalar_mul`: `none` iff a `none` point is paired with a scalar;
otherwise `∑ s_i • P_i` over the pairs (up to the shorter input; unreduced scalars `< 2^255`);
limbs `< 2^52`. -/
theorem pippengerMain_spec (hid : O.IdentitySpec) (hadd : O.AddSpec)
    (hadda : O.AddAssignSpec) (hmul : O.MulByPow2Spec) (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec)
    (hapn : O.AsProjectiveNielsSpec) {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option O.E)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option O.E)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255)
    (hps : ∀ P, some P ∈ ops → O.Bnd P ∧ O.OnCurve P)
    (hxs : xs.length ≤ Usize.max) :
    O.pippengerMain scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option O.E) => (r = none ↔ none ∈ ops.take ss.length) ∧
        ∀ R, r = some R → O.OnCurve R ∧ O.toPoint R =
          (List.zipWith (fun s P => s.asNat • O.toPoint P) ss (ops.filterMap id)).sum ∧
          O.Bnd R ⦄ := by
  unfold pippengerMain
  have hscalars' : scalarsInst.into_iter scalars
      ⦃ (it : Clause0_IntoIter) => scalarsInst.iteratorInst.Yields it xs ⦄ := hscalars
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hscalars' as ⟨it, hit⟩
  step with collect.fromIter_spec _ it xs hit hxs as ⟨vs, hvs⟩
  apply spec_bind (Pₘ := fun (w : Usize) => 6 ≤ w.val ∧ w.val ≤ 8)
  · split_ifs <;> rw [WP.spec_ok] <;> decide
  intro w hw
  have hw256 : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw.2
  step with Usize.ShiftLeft_spec 1#usize w (by
      rcases System.Platform.numBits_eq with h | h <;> simp only [h] <;> scalar_tac)
    as ⟨md, hmd, hmdbv⟩
  have hmd' : md.val = 2 ^ w.val := by
    rw [hmd, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  step with scalar.Scalar.to_radix_2w_size_hint_spec w ⟨by scalar_tac, hw.2⟩ as
      ⟨dc, hdc4, hdc5, hdc6, hdc7, hdc8⟩
  step as ⟨bc, hbc⟩
  have hbc' : 2 * bc.val = 2 ^ w.val := by
    rw [hbc, hmd']
    exact Nat.mul_div_cancel' (dvd_pow_self 2 (by scalar_tac))
  have hbc8 : bc.val ≤ 128 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw.2; scalar_tac
  have hbc1 : 1 ≤ bc.val := by
    have := Nat.one_le_two_pow (n := w.val); scalar_tac
  have hdcw : dc.val ≤ 64 ∧ ∀ i, dc.val ≤ i → 256 < i * w.val := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc7 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
    · rw [hdc8 h]; exact ⟨by decide, fun i hi => by rw [h]; scalar_tac⟩
  have hdc0 : dc.val ≠ 0 := by
    rcases (show w.val = 6 ∨ w.val = 7 ∨ w.val = 8 by scalar_tac) with h | h | h
    · rw [hdc6 h]; decide
    · rw [hdc7 h]; decide
    · rw [hdc8 h]; decide
  step with hpoints' as ⟨it1, hit1⟩
  step with O.pippengerScalarsPoints_spec hapn
    _ _ _ ss (by rw [show (alloc.vec.Vec.deref vs).val = vs.val from Slice.from_val _ _, hvs]; exact
        hborrow_scalars) hss w
    ⟨by scalar_tac, hw.2⟩ ops hps it1 0#usize (by simpa using hit1) (Nat.zero_le _) (Nat.zero_le _)
    (alloc.vec.Vec.new _) ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    as ⟨o, hnone, hsome⟩
  rcases o with _ | sp
  · dsimp only
    rw [WP.spec_ok]
    exact ⟨by simpa using hnone, fun R hR => by cases hR⟩
  · have hnn : none ∉ ops.take ss.length := fun h => by cases hnone.mpr h
    obtain ⟨hsplen, hsp⟩ := hsome sp rfl
    let P : ℕ → curve25519.edwards.Point := fun k => O.toPoint ((ops[k]!).getD default)
    have hsp' : ∀ k < sp.length, O.nOnCurve (sp.val[k]!).2 ∧ O.nBnd (sp.val[k]!).2 ∧
        O.nToPoint (sp.val[k]!).2 = P k := fun k hk => by
      obtain ⟨Q, hQ, hon, hb, hp, -⟩ := hsp k (hsplen ▸ hk)
      exact ⟨hon, hb, by
        rw [hp]; change O.toPoint Q = O.toPoint ((ops[k]!).getD default); rw [hQ]; rfl⟩
    have hdig : ∀ k < sp.length, ∀ e : ℕ, e < 64 → -(bc.val : ℤ) ≤ (sp.val[k]!).1[e]!.val ∧
        (sp.val[k]!).1[e]!.val ≤ (bc.val : ℤ) := fun k hk e he => by
      obtain ⟨Q, -, -, -, -, -, hb, -⟩ := hsp k (hsplen ▸ hk)
      have := hb e he
      have hbz : (2 : ℤ) ^ w.val = 2 * bc.val := by exact_mod_cast hbc'.symm
      rw [hbz] at this
      constructor <;> linarith [this.1, this.2]
    step with O.pippengerLoop0_spec hid bc (alloc.vec.Vec.new _) 0#usize hbc8
      (Nat.zero_le _) rfl (fun j hj => absurd hj (Nat.not_lt_zero j)) as ⟨b, hb⟩
    step with O.pippengerLoop1_spec hid hadd hadda hmul haddN hsubN hasE w bc sp b none dc P dc.val
      ⟨by scalar_tac, hw.2⟩ hbc1 hbc8 hdcw.1 hsp' hdig hb (le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩
      (fun T hT => by cases hT) as ⟨t, htn, hts⟩
    rcases t with _ | T
    · exact absurd (htn.mp rfl) hdc0
    obtain ⟨hTon, hTb, hT⟩ := hts T rfl
    step with core.option.Option.expect.spec as ⟨R, hR⟩
    obtain rfl : T = R := Option.some.inj hR
    refine ⟨by simpa using hnn, fun R' hR' => ?_⟩
    obtain rfl : T = R' := Option.some.inj hR'
    refine ⟨hTon, ?_, hTb⟩
    unfold EdwardsOps.column at hT
    rw [hT, sum_zipWith_filterMap _ _ _ hnn, ← hsplen, sum_columns]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    obtain ⟨Q, hQ, -, -, -, hval, -, hz⟩ := hsp k (hsplen ▸ hk')
    rw [sum_digits _ _ _ hdcw.1 fun j hj hj' => hz j hj (hdcw.2 j hj'), hval, natCast_zsmul]

end Curve25519Dalek.EdwardsOps
