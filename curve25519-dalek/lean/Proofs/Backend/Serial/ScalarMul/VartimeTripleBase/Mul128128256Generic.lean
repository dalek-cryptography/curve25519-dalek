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
import Proofs.Scalar.HalfWidthNonAdjacentForm
import Proofs.Scalar.SplitAt128
import Proofs.Window.NafLookupTable5Select
import Proofs.Window.NafLookupTable8Select
public import Proofs.Helpers.EdwardsOps
public section

/-! # `vartime_triple_base::mul_128_128_256`: the generic part

The proofs over `EdwardsOps`, apart from the instances (`Mul128128256.lean`).

`a₁ • A₁ + a₂ • A₂ + b • B` for the basepoint `B`, in variable time, for `a₁, a₂ < 2^128`: `b` is
split as `b_lo + 2^128 b_hi`, the four `128`-bit scalars are recoded as width-`5` non-adjacent
forms, whose digits above index `128` vanish (`naf5_digits_eq_zero_of_lt`), and Horner's rule runs
from the highest nonzero digit (at most `HEEA_MAX_INDEX = 129`) down, adding `d • A₁`, `d • A₂`,
`d • B` and `d • 2^128 B` for each nonzero digit `d` from tables of odd multiples. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.backend.serial.scalar_mul.vartime_triple_base

/-- The digits of the four recodings at index `k` vanish. -/
@[nolint defsWithUnderscore]
abbrev DigitsZero (a₁ a₂ c₁ c₂ : Array I8 256#usize) (k : ℕ) : Prop :=
  a₁[k]!.val = 0 ∧ a₂[k]!.val = 0 ∧ c₁[k]!.val = 0 ∧ c₂[k]!.val = 0

/-- One step of Horner's rule on four points. -/
private theorem horner_step (x₁ x₂ x₃ x₄ d₁ d₂ d₃ d₄ : ℤ) (P₁ P₂ P₃ P₄ : curve25519.edwards.Point) :
    2 • (x₁ • P₁ + x₂ • P₂ + x₃ • P₃ + x₄ • P₄) + d₁ • P₁ + d₂ • P₂ + d₃ • P₃ + d₄ • P₄ =
      (d₁ + 2 * x₁) • P₁ + (d₂ + 2 * x₂) • P₂ + (d₃ + 2 * x₃) • P₃ + (d₄ + 2 * x₄) • P₄ := by
  simp only [smul_add, ← natCast_zsmul, smul_smul, add_smul]
  push_cast
  abel

/-- `b = b_lo + 2^128 b_hi` on the points: `b_lo • B + b_hi • 2^128 B = b • B`. -/
theorem split_smul (lo hi b : ℕ) (h : lo + 2 ^ 128 * hi = b)
    (B : curve25519.edwards.Point) :
    lo • B + hi • 2 ^ 128 • B = b • B := by
  rw [smul_smul, ← add_smul, ← h, mul_comm]

/-- The recoding of a value below `2^128` has no digit above index `128`. -/
theorem naf_high_zero {d : Array I8 256#usize} {x : ℕ} (hx : x < 2 ^ 128)
    (hval : d.asInt 1 = x)
    (hdig : ∀ i : ℕ, i < 256 → d[i]!.val ≠ 0 → d[i]!.val % 2 = 1 ∧ 2 * |d[i]!.val| < 2 ^ 5)
    (hnaf : ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + 5 → d[i]!.val ≠ 0 →
      d[j]!.val = 0) :
    ∀ k : ℕ, 129 < k → k < 256 → d[k]!.val = 0 :=
  fun k hk hk' => naf5_digits_eq_zero_of_lt d hval hx hdig hnaf k (by omega) hk'


end Curve25519Dalek.backend.serial.scalar_mul.vartime_triple_base

/-! ## The loops over a configuration's point operations -/

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.vartime_triple_base

open ControlFlow

/-- `mul_128_128_256_loop0.body`, the same in every configuration. -/
@[expose] def vtbLoop0Body (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize)) (i : Usize) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize)) ×
      Usize) Usize) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done i)
  | some j =>
    let i1 ← Array.index_usize a1_naf j
    if i1 != 0#i8
    then ok (done j)
    else
      let i2 ← Array.index_usize a2_naf j
      if i2 != 0#i8
      then ok (done j)
      else
        let i3 ← Array.index_usize b_lo_naf j
        if i3 != 0#i8
        then ok (done j)
        else
          let i4 ← Array.index_usize b_hi_naf j
          if i4 != 0#i8
          then ok (done j)
          else ok (cont (iter1, j))

/-- `mul_128_128_256_loop0`, the same in every configuration. -/
@[expose] def vtbLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize) (i : Usize) : Result Usize := do
  loop (fun (iter1, i1) => vtbLoop0Body a1_naf a2_naf b_lo_naf b_hi_naf iter1 i1) (iter, i)

open scoped Helpers.IndexStep in
/-- The first loop of `mul_128_128_256`, over `HEEA_MAX_INDEX, …, 0`: the highest index `≤ 129` at
which a digit of one of the four recodings is nonzero (`0` if there is none), given that all
digits above the iterator's range vanish. -/
theorem vtbLoop0_spec
    (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Usize))
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize) (hstart : iter.iter.start.val = 0)
    (hend : iter.iter.end.val ≤ 129) (hex : iter.iter.exhausted = false) (hi : i.val ≤ 129)
    (hz : ∀ k, iter.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k) :
    vtbLoop0 iter a₁ a₂ c₁ c₂ i ⦃ (r : Usize) =>
      r.val ≤ 129 ∧ ∀ k, r.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k ⦄ := by
  unfold vtbLoop0
  apply loop.spec_decr_nat
    (measure := fun (it, _) => if it.iter.exhausted then 0 else it.iter.end.val + 2)
    (inv := fun (it, j) => it.iter.start.val = 0 ∧ j.val ≤ 129 ∧ it.iter.end.val ≤ 129 ∧
      ∀ k, (if it.iter.exhausted then 0 else it.iter.end.val + 1) ≤ k → k < 256 →
        DigitsZero a₁ a₂ c₁ c₂ k)
  · rintro ⟨it, j⟩ ⟨hst, hj, hen, hzk⟩
    unfold vtbLoop0Body
    cases hexh : it.iter.exhausted
    · rw [hexh] at hzk
      simp only [Bool.false_eq_true, ↓reduceIte] at hzk
      step with core.iter.adapters.rev.Rev.next_RangeInclusive_Usize_some_spec
          (core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
            core.iter.range.StepUsize) rfl it hexh (by omega)
        as ⟨o, it1, ho, hst1, hlt1, heq1⟩
      subst ho
      simp only
      -- the digits at the yielded index `it.iter.end`
      have hdone : ∀ k, it.iter.end.val < k → k < 256 → DigitsZero a₁ a₂ c₁ c₂ k :=
        fun k hk hk' => hzk k (by omega) hk'
      step as ⟨x₁, hx₁⟩
      by_cases h₁ : x₁.val = 0
      · have h₁' : (x₁ != 0#i8) = false := by rw [bne_eq_false_iff_eq]; scalar_tac
        simp only [h₁', Bool.false_eq_true, ↓reduceIte]
        step as ⟨x₂, hx₂⟩
        by_cases h₂ : x₂.val = 0
        · have h₂' : (x₂ != 0#i8) = false := by rw [bne_eq_false_iff_eq]; scalar_tac
          simp only [h₂', Bool.false_eq_true, ↓reduceIte]
          step as ⟨x₃, hx₃⟩
          by_cases h₃ : x₃.val = 0
          · have h₃' : (x₃ != 0#i8) = false := by rw [bne_eq_false_iff_eq]; scalar_tac
            simp only [h₃', Bool.false_eq_true, ↓reduceIte]
            step as ⟨x₄, hx₄⟩
            by_cases h₄ : x₄.val = 0
            · have h₄' : (x₄ != 0#i8) = false := by rw [bne_eq_false_iff_eq]; scalar_tac
              simp only [h₄', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
              have hz0 : DigitsZero a₁ a₂ c₁ c₂ it.iter.end.val :=
                ⟨hx₁ ▸ h₁, hx₂ ▸ h₂, hx₃ ▸ h₃, hx₄ ▸ h₄⟩
              rcases Nat.lt_or_ge it.iter.start.val it.iter.end.val with hlt | hge
              · obtain ⟨hend1, hex1⟩ := hlt1 hlt
                simp only [hex1, Bool.false_eq_true, ↓reduceIte]
                refine ⟨by rw [hst1, hst], by omega, by omega, fun k hk hk' => ?_, ?_⟩
                rotate_left
                · simp only [hexh, Bool.false_eq_true, ↓reduceIte]; omega
                rcases Nat.eq_or_lt_of_le (show it.iter.end.val ≤ k by omega) with h | h
                · subst h; exact hz0
                · exact hdone k h hk'
              · obtain ⟨hend1, hex1⟩ := heq1 (by omega)
                simp only [hex1, ↓reduceIte]
                refine ⟨by rw [hst1, hst], by omega, by rw [hend1]; omega, fun k _ hk' => ?_, ?_⟩
                rotate_left
                · simp only [hexh, Bool.false_eq_true, ↓reduceIte]; omega
                rcases Nat.eq_or_lt_of_le (Nat.zero_le k) with h | h
                · rw [← h, show 0 = it.iter.end.val by omega]; exact hz0
                · exact hdone k (by omega) hk'
            · have h₄' : (x₄ != 0#i8) = true := by
                rw [bne_iff_ne]; intro h; apply h₄; rw [h]; rfl
              simp only [h₄', ↓reduceIte, WP.spec_ok]
              exact ⟨hen, hdone⟩
          · have h₃' : (x₃ != 0#i8) = true := by
              rw [bne_iff_ne]; intro h; apply h₃; rw [h]; rfl
            simp only [h₃', ↓reduceIte, WP.spec_ok]
            exact ⟨hen, hdone⟩
        · have h₂' : (x₂ != 0#i8) = true := by
            rw [bne_iff_ne]; intro h; apply h₂; rw [h]; rfl
          simp only [h₂', ↓reduceIte, WP.spec_ok]
          exact ⟨hen, hdone⟩
      · have h₁' : (x₁ != 0#i8) = true := by
          rw [bne_iff_ne]; intro h; apply h₁; rw [h]; rfl
        simp only [h₁', ↓reduceIte, WP.spec_ok]
        exact ⟨hen, hdone⟩
    · rw [hexh] at hzk
      simp only [↓reduceIte] at hzk
      step with core.iter.adapters.rev.Rev.next_RangeInclusive_Usize_none_spec
          (core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
            core.iter.range.StepUsize) rfl it hexh
        as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      exact ⟨hj, fun k _ hk' => hzk k (Nat.zero_le k) hk'⟩
  · refine ⟨hstart, hi, hend, ?_⟩
    simp only [hex, Bool.false_eq_true, ↓reduceIte]
    exact fun k hk hk' => hz k (by omega) hk'

/-- The digit facts of `non_adjacent_form` at width `5`. -/
@[nolint defsWithUnderscore]
abbrev Naf5Digits (d : Array I8 256#usize) : Prop :=
  ∀ k : ℕ, k < 256 → d[k]!.val ≠ 0 → d[k]!.val % 2 = 1 ∧ 2 * |d[k]!.val| < 2 ^ 5

variable (O : EdwardsOps)

/-- `mul_128_128_256_loop1.body` over the point operations (vtbLoop1T). -/
@[expose] def vtbLoop1TBody (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An)
    (table_B_128 : window.NafLookupTable5 O.N) (i : Usize) (r : O.Pr) :
    Result (ControlFlow (Usize × O.Pr) O.E) := do
  let t ← O.pDouble r
  let digit ← Array.index_usize a1_naf i
  let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
  let t1 ←
    match o with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A1 i2
      O.subN ep pnp
    | Ordering.eq => ok t
    | Ordering.gt =>
      do
      let ep ← O.asExtended t
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN table_A1 i1
      O.addN ep pnp
  let digit1 ← Array.index_usize a2_naf i
  let o1 ← lift (core.cmp.impls.OrdI8.cmp digit1 0#i8)
  let t2 ←
    match o1 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t1
      let i1 ← -. digit1
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A2 i2
      O.subN ep pnp
    | Ordering.eq => ok t1
    | Ordering.gt =>
      do
      let ep ← O.asExtended t1
      let i1 ← lift (IScalar.hcast .Usize digit1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A2 i1
      O.addN ep pnp
  let digit2 ← Array.index_usize b_lo_naf i
  let o2 ← lift (core.cmp.impls.OrdI8.cmp digit2 0#i8)
  let t3 ←
    match o2 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t2
      let i1 ← -. digit2
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable8.select O.copyA table_B i2
      O.subA ep pnp
    | Ordering.eq => ok t2
    | Ordering.gt =>
      do
      let ep ← O.asExtended t2
      let i1 ← lift (IScalar.hcast .Usize digit2)
      let pnp ← window.NafLookupTable8.select O.copyA table_B i1
      O.addA ep pnp
  let digit3 ← Array.index_usize b_hi_naf i
  let o3 ← lift (core.cmp.impls.OrdI8.cmp digit3 0#i8)
  let t4 ←
    match o3 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t3
      let i1 ← -. digit3
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_B_128 i2
      O.subN ep pnp
    | Ordering.eq => ok t3
    | Ordering.gt =>
      do
      let ep ← O.asExtended t3
      let i1 ← lift (IScalar.hcast .Usize digit3)
      let pnp ← window.NafLookupTable5.select O.copyN table_B_128 i1
      O.addN ep pnp
  let r1 ← O.cAsProjective t4
  if i = 0#usize
  then
    let ep ← O.pAsExtended r1
    ok (done ep)
  else let i1 ← i - 1#usize
       ok (cont (i1, r1))

/-- `mul_128_128_256_loop1` over the point operations (vtbLoop1T). -/
@[expose] def vtbLoop1T (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An)
    (table_B_128 : window.NafLookupTable5 O.N) (r : O.Pr) : Result O.E := do
  loop (fun (i1, r1) =>
    O.vtbLoop1TBody a1_naf a2_naf b_lo_naf b_hi_naf table_A1 table_A2 table_B table_B_128 i1 r1)
    (i, r)

/-- `mul_128_128_256_loop1.body` over the point operations (vtbLoop1N). -/
@[expose] def vtbLoop1NBody (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N)
    (table_B_128 : window.NafLookupTable5 O.N) (i : Usize) (r : O.Pr) :
    Result (ControlFlow (Usize × O.Pr) O.E) := do
  let t ← O.pDouble r
  let digit ← Array.index_usize a1_naf i
  let o ← lift (core.cmp.impls.OrdI8.cmp digit 0#i8)
  let t1 ←
    match o with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t
      let i1 ← -. digit
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A1 i2
      O.subN ep pnp
    | Ordering.eq => ok t
    | Ordering.gt =>
      do
      let ep ← O.asExtended t
      let i1 ← lift (IScalar.hcast .Usize digit)
      let pnp ← window.NafLookupTable5.select O.copyN table_A1 i1
      O.addN ep pnp
  let digit1 ← Array.index_usize a2_naf i
  let o1 ← lift (core.cmp.impls.OrdI8.cmp digit1 0#i8)
  let t2 ←
    match o1 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t1
      let i1 ← -. digit1
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A2 i2
      O.subN ep pnp
    | Ordering.eq => ok t1
    | Ordering.gt =>
      do
      let ep ← O.asExtended t1
      let i1 ← lift (IScalar.hcast .Usize digit1)
      let pnp ← window.NafLookupTable5.select O.copyN table_A2 i1
      O.addN ep pnp
  let digit2 ← Array.index_usize b_lo_naf i
  let o2 ← lift (core.cmp.impls.OrdI8.cmp digit2 0#i8)
  let t3 ←
    match o2 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t2
      let i1 ← -. digit2
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_B i2
      O.subN ep pnp
    | Ordering.eq => ok t2
    | Ordering.gt =>
      do
      let ep ← O.asExtended t2
      let i1 ← lift (IScalar.hcast .Usize digit2)
      let pnp ← window.NafLookupTable5.select O.copyN table_B i1
      O.addN ep pnp
  let digit3 ← Array.index_usize b_hi_naf i
  let o3 ← lift (core.cmp.impls.OrdI8.cmp digit3 0#i8)
  let t4 ←
    match o3 with
    | Ordering.lt =>
      do
      let ep ← O.asExtended t3
      let i1 ← -. digit3
      let i2 ← lift (IScalar.hcast .Usize i1)
      let pnp ← window.NafLookupTable5.select O.copyN table_B_128 i2
      O.subN ep pnp
    | Ordering.eq => ok t3
    | Ordering.gt =>
      do
      let ep ← O.asExtended t3
      let i1 ← lift (IScalar.hcast .Usize digit3)
      let pnp ← window.NafLookupTable5.select O.copyN table_B_128 i1
      O.addN ep pnp
  let r1 ← O.cAsProjective t4
  if i = 0#usize
  then
    let ep ← O.pAsExtended r1
    ok (done ep)
  else let i1 ← i - 1#usize
       ok (cont (i1, r1))

/-- `mul_128_128_256_loop1` over the point operations (vtbLoop1N). -/
@[expose] def vtbLoop1N (a1_naf a2_naf b_lo_naf b_hi_naf : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N)
    (table_B_128 : window.NafLookupTable5 O.N) (r : O.Pr) : Result O.E := do
  loop (fun (i1, r1) =>
    O.vtbLoop1NBody a1_naf a2_naf b_lo_naf b_hi_naf table_A1 table_A2 table_B table_B_128 i1 r1)
    (i, r)

/-- Adding the contribution `d • P` of one NAF digit `d` (width `5`) from a table of odd multiples
of `P`, as in the loop body: subtract the entry `-d` if `d < 0`, add the entry `d` if `d > 0`. -/
private theorem vtbAddDigitN_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec)
    (hasE : O.AsExtendedSpec) (t : O.C) (d : I8) (table : window.NafLookupTable5 O.N)
    (P : curve25519.edwards.Point)
    (ht : O.cOnCurve t) (htb : O.cBnd t) (hT : table.Represents P) (hTb : table.LimbsLt O.nB)
    (hd : d.val ≠ 0 → d.val % 2 = 1 ∧ 2 * |d.val| < 2 ^ 5) :
    (match compare d.val 0 with
      | Ordering.lt => do
        let ep ← O.asExtended t
        let i1 ← -. d
        let i2 ← lift (IScalar.hcast .Usize i1)
        let pnp ← window.NafLookupTable5.select O.copyN table i2
        O.subN ep pnp
      | Ordering.eq => ok t
      | Ordering.gt => do
        let ep ← O.asExtended t
        let i1 ← lift (IScalar.hcast .Usize d)
        let pnp ← window.NafLookupTable5.select O.copyN table i1
        O.addN ep pnp) ⦃ (t1 : O.C) =>
      O.cOnCurve t1 ∧ O.cToPoint t1 = O.cToPoint t + d.val • P ∧ O.cBnd t1 ⦄ := by
  rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
  · rw [(compare_lt_iff_lt).mpr hneg]
    simp only
    step with hasE t htb ht as ⟨ep, hepon, hep, hepb⟩
    have hk := naf_digit_abs (w := 5) (by norm_num) (hd (by omega))
    rw [abs_of_neg hneg] at hk
    step as ⟨i1, hi1⟩
    step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
    step with window.NafLookupTable5.select_spec (P := P) _ table i2 hTb hT
        ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
    step with hsubN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
    refine ⟨ht1on, ?_, ht1b⟩
    rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
    exact sub_nsmul_eq _ _ _ _ (by omega)
  · rw [(compare_eq_iff_eq).mpr hzero]
    simp only [WP.spec_ok]
    rw [hzero, zero_smul, add_zero]
    exact ⟨ht, rfl, htb⟩
  · rw [(compare_gt_iff_gt).mpr hpos]
    simp only
    step with hasE t htb ht as ⟨ep, hepon, hep, hepb⟩
    have hk := naf_digit_abs (w := 5) (by norm_num) (hd (by omega))
    rw [abs_of_pos hpos] at hk
    step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
    step with window.NafLookupTable5.select_spec (P := P) _ table i1 hTb hT
        ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
    step with haddN ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
    refine ⟨ht1on, ?_, ht1b⟩
    rw [ht1p, hep, show O.nToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
    exact add_nsmul_eq _ _ _ _ (by omega)

/-- Adding the contribution `d • P` of one NAF digit `d` (width `5`) from a table of odd multiples
of `P`, as in the loop body: subtract the entry `-d` if `d < 0`, add the entry `d` if `d > 0`. -/
private theorem vtbAddDigitA_spec (haddA : O.AddASpec) (hsubA : O.SubASpec)
    (hasE : O.AsExtendedSpec) (t : O.C) (d : I8) (table : window.NafLookupTable8 O.An)
    (P : curve25519.edwards.Point)
    (ht : O.cOnCurve t) (htb : O.cBnd t) (hT : table.Represents P) (hTb : table.LimbsLt O.aB)
    (hd : d.val ≠ 0 → d.val % 2 = 1 ∧ 2 * |d.val| < 2 ^ 5) :
    (match compare d.val 0 with
      | Ordering.lt => do
        let ep ← O.asExtended t
        let i1 ← -. d
        let i2 ← lift (IScalar.hcast .Usize i1)
        let pnp ← window.NafLookupTable8.select O.copyA table i2
        O.subA ep pnp
      | Ordering.eq => ok t
      | Ordering.gt => do
        let ep ← O.asExtended t
        let i1 ← lift (IScalar.hcast .Usize d)
        let pnp ← window.NafLookupTable8.select O.copyA table i1
        O.addA ep pnp) ⦃ (t1 : O.C) =>
      O.cOnCurve t1 ∧ O.cToPoint t1 = O.cToPoint t + d.val • P ∧ O.cBnd t1 ⦄ := by
  rcases lt_trichotomy d.val 0 with hneg | hzero | hpos
  · rw [(compare_lt_iff_lt).mpr hneg]
    simp only
    step with hasE t htb ht as ⟨ep, hepon, hep, hepb⟩
    have hk := naf_digit_abs (w := 5) (by norm_num) (hd (by omega))
    rw [abs_of_neg hneg] at hk
    step as ⟨i1, hi1⟩
    step with IScalar.hcast_inBounds_spec as ⟨i2, hi2⟩
    step with window.NafLookupTable8.select_spec (P := P) _ table i2 hTb hT
        ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
    step with hsubA ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
    refine ⟨ht1on, ?_, ht1b⟩
    rw [ht1p, hep, show O.aToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
    exact sub_nsmul_eq _ _ _ _ (by omega)
  · rw [(compare_eq_iff_eq).mpr hzero]
    simp only [WP.spec_ok]
    rw [hzero, zero_smul, add_zero]
    exact ⟨ht, rfl, htb⟩
  · rw [(compare_gt_iff_gt).mpr hpos]
    simp only
    step with hasE t htb ht as ⟨ep, hepon, hep, hepb⟩
    have hk := naf_digit_abs (w := 5) (by norm_num) (hd (by omega))
    rw [abs_of_pos hpos] at hk
    step with IScalar.hcast_inBounds_spec as ⟨i1, hi1⟩
    step with window.NafLookupTable8.select_spec (P := P) _ table i1 hTb hT
        ⟨by omega, by omega⟩ as ⟨pnp, hpon, hpp, hpb⟩
    step with haddA ep pnp hepb hpb hepon hpon as ⟨t1, ht1on, ht1p, ht1b⟩
    refine ⟨ht1on, ?_, ht1b⟩
    rw [ht1p, hep, show O.aToPoint pnp = PointRepr.toPoint pnp from rfl, hpp]
    exact add_nsmul_eq _ _ _ _ (by omega)

open scoped Helpers.IndexStep in
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
theorem vtbLoop1T_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (haddA : O.AddASpec)
    (hsubA : O.SubASpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec) (hpasE : O.PAsExtendedSpec)
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable8 O.An)
    (table_B_128 : window.NafLookupTable5 O.N)
    (r : O.Pr) (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt O.nB)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt O.nB)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt O.aB)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt O.nB)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    O.vtbLoop1T a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r ⦃ (res : O.E) =>
        O.OnCurve res ∧ O.toPoint res =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        O.Bnd res ⦄ := by
  unfold vtbLoop1T
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ O.pOnCurve q ∧ O.pBnd q ∧
      O.pToPoint q = nafTail a₁ (j.val + 1) • P₁ + nafTail a₂ (j.val + 1) • P₂ +
        nafTail c₁ (j.val + 1) • P₃ + nafTail c₂ (j.val + 1) • P₄)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold vtbLoop1TBody
    step with hdbl q hqb hq as ⟨t, hton, htp, htb⟩
    step as ⟨d₁, hd₁⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₁ 0#i8) = ok (compare d₁.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t d₁ table_A1 P₁ hton htb h₁ h₁b
      (hd₁ ▸ ha₁ j.val hj))
    rintro t₁ ⟨ht₁on, ht₁p, ht₁b⟩
    step as ⟨d₂, hd₂⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₂ 0#i8) = ok (compare d₂.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t₁ d₂ table_A2 P₂ ht₁on ht₁b h₂ h₂b
      (hd₂ ▸ ha₂ j.val hj))
    rintro t₂ ⟨ht₂on, ht₂p, ht₂b⟩
    step as ⟨d₃, hd₃⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₃ 0#i8) = ok (compare d₃.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitA_spec haddA hsubA hasE t₂ d₃ table_B P₃ ht₂on ht₂b h₃ h₃b
      (hd₃ ▸ hc₁ j.val hj))
    rintro t₃ ⟨ht₃on, ht₃p, ht₃b⟩
    step as ⟨d₄, hd₄⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₄ 0#i8) = ok (compare d₄.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t₃ d₄ table_B_128 P₄ ht₃on ht₃b h₄ h₄b
      (hd₄ ▸ hc₂ j.val hj))
    rintro t₄ ⟨ht₄on, ht₄p, ht₄b⟩
    step with hasP t₄ ht₄b ht₄on as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : O.pToPoint r1 = nafTail a₁ j.val • P₁ + nafTail a₂ j.val • P₂ +
        nafTail c₁ j.val • P₃ + nafTail c₂ j.val • P₄ := by
      rw [hr1p, ht₄p, ht₃p, ht₂p, ht₁p, htp, hqp, horner_step, nafTail_eq _ _ hj,
        nafTail_eq _ _ hj, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd₁, ← hd₂, ← hd₃, ← hd₄]
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
/-- The second loop of `mul_128_128_256`: after the digits `i, …, 255`, the accumulator represents
`∑ nafTail dₖ i • Pₖ` over the four recodings and points. -/
theorem vtbLoop1N_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (hasE : O.AsExtendedSpec)
    (hdbl : O.PDoubleSpec) (hasP : O.CAsProjectiveSpec) (hpasE : O.PAsExtendedSpec)
    (a₁ a₂ c₁ c₂ : Array I8 256#usize) (i : Usize)
    (table_A1 table_A2 : window.NafLookupTable5 O.N) (table_B : window.NafLookupTable5 O.N)
    (table_B_128 : window.NafLookupTable5 O.N)
    (r : O.Pr) (P₁ P₂ P₃ P₄ : curve25519.edwards.Point)
    (h₁ : table_A1.Represents P₁) (h₁b : table_A1.LimbsLt O.nB)
    (h₂ : table_A2.Represents P₂) (h₂b : table_A2.LimbsLt O.nB)
    (h₃ : table_B.Represents P₃) (h₃b : table_B.LimbsLt O.nB)
    (h₄ : table_B_128.Represents P₄) (h₄b : table_B_128.LimbsLt O.nB)
    (ha₁ : Naf5Digits a₁) (ha₂ : Naf5Digits a₂) (hc₁ : Naf5Digits c₁) (hc₂ : Naf5Digits c₂)
    (hi : i.val < 256) (hr : O.pOnCurve r) (hrb : O.pBnd r)
    (hrp : O.pToPoint r = nafTail a₁ (i.val + 1) • P₁ + nafTail a₂ (i.val + 1) • P₂ +
      nafTail c₁ (i.val + 1) • P₃ + nafTail c₂ (i.val + 1) • P₄) :
    O.vtbLoop1N a₁ a₂ c₁ c₂ i table_A1 table_A2 table_B table_B_128 r ⦃ (res : O.E) =>
        O.OnCurve res ∧ O.toPoint res =
          nafTail a₁ 0 • P₁ + nafTail a₂ 0 • P₂ + nafTail c₁ 0 • P₃ + nafTail c₂ 0 • P₄ ∧
        O.Bnd res ⦄ := by
  unfold vtbLoop1N
  apply loop.spec_decr_nat (measure := fun (j, _) => j.val)
    (inv := fun (j, q) => j.val < 256 ∧ O.pOnCurve q ∧ O.pBnd q ∧
      O.pToPoint q = nafTail a₁ (j.val + 1) • P₁ + nafTail a₂ (j.val + 1) • P₂ +
        nafTail c₁ (j.val + 1) • P₃ + nafTail c₂ (j.val + 1) • P₄)
  · rintro ⟨j, q⟩ ⟨hj, hq, hqb, hqp⟩
    unfold vtbLoop1NBody
    step with hdbl q hqb hq as ⟨t, hton, htp, htb⟩
    step as ⟨d₁, hd₁⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₁ 0#i8) = ok (compare d₁.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t d₁ table_A1 P₁ hton htb h₁ h₁b
      (hd₁ ▸ ha₁ j.val hj))
    rintro t₁ ⟨ht₁on, ht₁p, ht₁b⟩
    step as ⟨d₂, hd₂⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₂ 0#i8) = ok (compare d₂.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t₁ d₂ table_A2 P₂ ht₁on ht₁b h₂ h₂b
      (hd₂ ▸ ha₂ j.val hj))
    rintro t₂ ⟨ht₂on, ht₂p, ht₂b⟩
    step as ⟨d₃, hd₃⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₃ 0#i8) = ok (compare d₃.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t₂ d₃ table_B P₃ ht₂on ht₂b h₃ h₃b
      (hd₃ ▸ hc₁ j.val hj))
    rintro t₃ ⟨ht₃on, ht₃p, ht₃b⟩
    step as ⟨d₄, hd₄⟩
    rw [show lift (core.cmp.impls.OrdI8.cmp d₄ 0#i8) = ok (compare d₄.val 0) from rfl, bind_ok]
    apply spec_bind (O.vtbAddDigitN_spec haddN hsubN hasE t₃ d₄ table_B_128 P₄ ht₃on ht₃b h₄ h₄b
      (hd₄ ▸ hc₂ j.val hj))
    rintro t₄ ⟨ht₄on, ht₄p, ht₄b⟩
    step with hasP t₄ ht₄b ht₄on as ⟨r1, hr1on, hr1p, hr1b⟩
    have hval : O.pToPoint r1 = nafTail a₁ j.val • P₁ + nafTail a₂ j.val • P₂ +
        nafTail c₁ j.val • P₃ + nafTail c₂ j.val • P₄ := by
      rw [hr1p, ht₄p, ht₃p, ht₂p, ht₁p, htp, hqp, horner_step, nafTail_eq _ _ hj,
        nafTail_eq _ _ hj, nafTail_eq _ _ hj, nafTail_eq _ _ hj, ← hd₁, ← hd₂, ← hd₃, ← hd₄]
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
