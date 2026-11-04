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
import Proofs.Scalar.AsRadix16
import Zeroize
public import Proofs.Helpers.EdwardsOps
public section

/-! # `Straus::multiscalar_mul`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`MultiscalarMul.lean`).

Constant-time Straus: the lookup tables of `P, 2 P, …, 8 P` of the points, the radix-`16` digits
of the scalars, and Horner's rule over the `64` digit positions, adding `d_i[j] • P_i` for every
point (up to the shorter of the two inputs, as the patched index loop) after `16 •` the
accumulator. The inputs are `IntoIterator`s (`IntoIterator.Yields`) whose items are borrowed as
scalars and points. -/

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

/-- One digit position: `16 •` the sum, plus the digits, is the sum of the next tails. -/
private theorem horner16 (n j : ℕ) (d : ℕ → Array I8 64#usize) (P : ℕ → curve25519.edwards.Point)
    (hj : j < 64) :
    2 ^ 4 • (∑ k ∈ Finset.range n, radix16Tail (d k) (j + 1) • P k) +
      ∑ k ∈ Finset.range n, (d k)[j]!.val • P k =
      ∑ k ∈ Finset.range n, radix16Tail (d k) j • P k := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [radix16Tail_eq _ _ hj, ← natCast_zsmul, smul_smul, ← add_smul, add_comm]
  push_cast
  ring_nf


end Curve25519Dalek.backend.serial.scalar_mul.straus

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.straus

variable (O : EdwardsOps)

open ControlFlow

/-- `multiscalar_mul_loop0_loop0.body` over the point operations. -/
@[expose] def strausMsLoop00Body (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (j : Usize)
    (iter : core.ops.range.Range Usize) (Q : O.E) :
    Result (ControlFlow ((core.ops.range.Range Usize) × O.E) O.E) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done Q)
  | some i =>
    let a ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array I8 64#usize)) scalar_digits
        i
    let lt ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (window.LookupTable O.N))
        lookup_tables i
    let i1 ← Array.index_usize a j
    let R_i ← O.ltSelect lt i1
    let cp ← O.addN Q R_i
    let Q1 ← O.asExtended cp
    ok (cont (iter1, Q1))

/-- The inner range loop over the point operations. -/
@[expose] def strausMsLoop00 (iter : core.ops.range.Range Usize)
    (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : O.E) (j : Usize) : Result O.E := do
  loop (fun (iter1, Q1) => O.strausMsLoop00Body lookup_tables scalar_digits j iter1 Q1) (iter, Q)

/-- `multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def strausMsLoop0Body (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize))
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (Q : O.E) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.E)
      O.E) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done Q)
  | some j =>
    let Q1 ← O.mulByPow2 Q 4#u32
    let i := alloc.vec.Vec.len scalar_digits
    let i1 := alloc.vec.Vec.len lookup_tables
    let n ← lift (core.cmp.impls.OrdUsize.min i i1)
    let Q2 ← O.strausMsLoop00 { start := 0#usize, «end» := n } lookup_tables scalar_digits Q1 j
    ok (cont (iter1, Q2))

/-- `multiscalar_mul_loop0` over the point operations. -/
@[expose] def strausMsLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : O.E) : Result O.E := do
  loop (fun (iter1, Q1) => O.strausMsLoop0Body lookup_tables scalar_digits iter1 Q1) (iter, Q)

open scoped Helpers.IndexStep in
/-- The inner loop: adds `d_k[j] • P_k` for `k = i, …, n - 1`. -/
private theorem strausMsLoop00_spec (haddN : O.AddNSpec) (hasE : O.AsExtendedSpec)
    (hsel : O.LtSelectSpec) (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : O.E)
    (j n i : Usize) (P : ℕ → curve25519.edwards.Point) (hj : j.val < 64)
    (hn : n.val ≤ lookup_tables.length ∧ n.val ≤ scalar_digits.length)
    (hT : ∀ k < n.val, lookup_tables.val[k]!.Represents (P k) ∧
      lookup_tables.val[k]!.LimbsLt O.nB)
    (hD : ∀ k < n.val, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hi : i.val ≤ n.val) (hQ : O.Bnd Q) (hon : O.OnCurve Q) :
    O.strausMsLoop00 { start := i, «end» := n } lookup_tables scalar_digits Q j
      ⦃ (r : O.E) => O.OnCurve r ∧ O.Bnd r ∧
        O.toPoint r = O.toPoint Q + ∑ k ∈ Finset.Ico i.val n.val,
          (scalar_digits.val[k]!)[j.val]!.val • P k ⦄ := by
  unfold strausMsLoop00
  apply loop.spec_decr_nat (measure := fun (it, _) => n.val - it.start.val)
    (inv := fun (it, Q') => it.end = n ∧ i.val ≤ it.start.val ∧
      it.start.val ≤ n.val ∧ O.OnCurve Q' ∧ O.Bnd Q' ∧
      O.toPoint Q' = O.toPoint Q + ∑ k ∈ Finset.Ico i.val it.start.val,
        (scalar_digits.val[k]!)[j.val]!.val • P k)
  · rintro ⟨⟨i', e⟩, Q'⟩ ⟨he, hii, hin, hQ'on, hQ'b, hQ'p⟩
    dsimp only at he
    subst e
    unfold strausMsLoop00Body
    by_cases hlt : i' < n
    · step with core.iter.range.IteratorRange.next_Usize_some_spec
        as ⟨o, it1, ho, hi1, he1⟩
      subst ho
      have hk : i'.val < n.val := hlt
      step as ⟨d, hd⟩
      step as ⟨lt, hlt'⟩
      rw [← getElem!_pos] at hlt' hd
      step as ⟨x, hx⟩
      obtain ⟨hrep, hb⟩ := hT i'.val hk
      step with hsel lt x (P i'.val) (hlt' ▸ hb) (hlt' ▸ hrep)
        (by rw [hx, hd]; exact hD i'.val hk j.val hj) as ⟨q, hqon, hq, hqb⟩
      step with haddN Q' q hQ'b hqb hQ'on hqon as ⟨c, hcon, hc, hcb⟩
      step with hasE c hcb hcon as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      refine ⟨he1, by scalar_tac, by scalar_tac, hQ1on, hQ1b, ?_, by scalar_tac⟩
      rw [hQ1, hc, hQ'p, hq, hx, hd, show it1.start.val = i'.val + 1 by scalar_tac,
        Finset.sum_Ico_succ_top hii, add_assoc]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have : i'.val = n.val := by scalar_tac
      exact ⟨hQ'on, hQ'b, this ▸ hQ'p⟩
  · exact ⟨rfl, le_refl _, hi, hon, hQ, by rw [Finset.Ico_self, Finset.sum_empty, add_zero]⟩

/-- The outer loop: after the digit positions `e, …, 63`, the accumulator represents
`∑_{k < n} radix16Tail d_k e • P_k`. -/
theorem strausMsLoop0_spec (haddN : O.AddNSpec) (hasE : O.AsExtendedSpec)
    (hsel : O.LtSelectSpec) (hmul : O.MulByPow2Spec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (lookup_tables : alloc.vec.Vec (window.LookupTable O.N))
    (scalar_digits : alloc.vec.Vec (Array I8 64#usize)) (Q : O.E)
    (P : ℕ → curve25519.edwards.Point) (n : ℕ)
    (hn : n = min scalar_digits.length lookup_tables.length)
    (hT : ∀ k < n, lookup_tables.val[k]!.Represents (P k) ∧ lookup_tables.val[k]!.LimbsLt O.nB)
    (hD : ∀ k < n, ∀ e : ℕ, e < 64 → -8 ≤ (scalar_digits.val[k]!)[e]!.val ∧
      (scalar_digits.val[k]!)[e]!.val ≤ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 64)
    (hQ : O.Bnd Q) (hon : O.OnCurve Q)
    (hQp : O.toPoint Q = ∑ k ∈ Finset.range n,
      radix16Tail scalar_digits.val[k]! iter.iter.end.val • P k) :
    O.strausMsLoop0 iter lookup_tables scalar_digits Q ⦃ (r : O.E) => O.OnCurve r ∧ O.Bnd r ∧
        O.toPoint r = ∑ k ∈ Finset.range n, radix16Tail scalar_digits.val[k]! 0 • P k ⦄ := by
  unfold strausMsLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, Q') => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 64 ∧ O.OnCurve Q' ∧
      O.Bnd Q' ∧ O.toPoint Q' = ∑ k ∈ Finset.range n,
        radix16Tail scalar_digits.val[k]! it.iter.end.val • P k)
  · rintro ⟨it, Q'⟩ ⟨hst, hen, hQ'on, hQ'b, hQ'p⟩
    unfold strausMsLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      step with hmul Q' 4#u32 hQ'b hQ'on (by decide) as ⟨Q1, hQ1on, hQ1, hQ1b⟩
      step as ⟨m, hm⟩
      have hmn : m.val = n := by rw [hn]; scalar_tac
      step with O.strausMsLoop00_spec haddN hasE hsel lookup_tables scalar_digits Q1 j m 0#usize P
        (by scalar_tac) (by scalar_tac) (hmn ▸ hT) (hmn ▸ hD) (by scalar_tac) hQ1b hQ1on
        as ⟨Q2, hQ2on, hQ2b, hQ2⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hQ2on, hQ2b, ?_, by scalar_tac⟩
      rw [hQ2, hQ1, hQ'p, hmn, ← Finset.range_eq_Ico,
        hend1, ← hj, horner16 n j.val (fun k => scalar_digits.val[k]!) P (by scalar_tac)]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hQ'p
      exact ⟨hQ'on, hQ'b, hQ'p⟩
  · exact ⟨hstart, hend, hon, hQ, hQp⟩

end Curve25519Dalek.EdwardsOps
