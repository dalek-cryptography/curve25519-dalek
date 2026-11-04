/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Proofs.Helpers.EdwardsOps
public import Defs.Scalar
public import Proofs.Helpers.Naf
public import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Lemmas
public import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Loop00
public import Proofs.Backend.Serial.ScalarMul.PrecomputedStraus.OptionalMixedMultiscalarMul.Loop01
import Proofs.Helpers.Iterator
import Proofs.Helpers.StepSpecs
public section

/-! # `optional_mixed_multiscalar_mul`'s loops, over a configuration's point operations

The three loops of `VartimePrecomputedStraus::optional_mixed_multiscalar_mul`, over the
`EdwardsOps` of a configuration: the four configurations' loops are `rfl`-equal to these, and their
specs follow (`OptionalMixedMultiscalarMul/X86Tables.lean`, …). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.EdwardsOps

open Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

variable (O : EdwardsOps)

open ControlFlow

/-- `optional_mixed_multiscalar_mul_loop0.body` over the point operations. -/
@[expose] def pstLoop0Body (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (dp : Usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (S : O.Pr) :
    Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) × O.Pr)
      O.Pr) := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter
  match o with
  | none => ok (done S)
  | some j =>
    let R ← O.pDouble S
    let R1 ← O.pstLoop00 { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R
    let i := alloc.vec.Vec.len static_nafs
    let R2 ← O.pstLoop01 { start := 0#usize, «end» := i } v static_nafs j R1
    let S1 ← O.cAsProjective R2
    ok (cont (iter1, S1))

/-- `optional_mixed_multiscalar_mul_loop0` over the point operations. -/
@[expose] def pstLoop0 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N)) (dp : Usize)
    (S : O.Pr) : Result O.Pr := do
  loop (fun (iter1, S1) =>
    O.pstLoop0Body v static_nafs dynamic_nafs dynamic_lookup_tables dp iter1 S1) (iter, S)

/-- The outer loop over the digit positions, from the top. -/
theorem pstLoop0_spec (haddN : O.AddNSpec) (hsubN : O.SubNSpec) (haddA : O.AddASpec)
    (hsubA : O.SubASpec) (hasE : O.AsExtendedSpec) (hdbl : O.PDoubleSpec)
    (hasP : O.CAsProjectiveSpec)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (v : alloc.vec.Vec (window.NafLookupTable8 O.An))
    (static_nafs dynamic_nafs : alloc.vec.Vec (Array I8 256#usize))
    (dynamic_lookup_tables : alloc.vec.Vec (window.NafLookupTable5 O.N))
    (dp : Usize) (S : O.Pr) (P Q : ℕ → curve25519.edwards.Point)
    (hdp : dp.val ≤ dynamic_nafs.length ∧ dp.val ≤ dynamic_lookup_tables.length)
    (hsl : static_nafs.length ≤ v.length)
    (hT : ∀ m < dp.val, dynamic_lookup_tables.val[m]!.Represents (Q m) ∧
      dynamic_lookup_tables.val[m]!.LimbsLt O.nB)
    (hD : ∀ m < dp.val, ∀ e : ℕ, e < 256 → (dynamic_nafs.val[m]!)[e]!.val ≠ 0 →
      (dynamic_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(dynamic_nafs.val[m]!)[e]!.val| < 2 ^ 5)
    (hV : ∀ m < static_nafs.length, v.val[m]!.Represents (P m) ∧ v.val[m]!.LimbsLt O.aB)
    (hE : ∀ m < static_nafs.length, ∀ e : ℕ, e < 256 → (static_nafs.val[m]!)[e]!.val ≠ 0 →
      (static_nafs.val[m]!)[e]!.val % 2 = 1 ∧ 2 * |(static_nafs.val[m]!)[e]!.val| < 2 ^ 8)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val ≤ 256)
    (hS : O.pOnCurve S) (hSb : O.pBnd S)
    (hSp : O.pToPoint S =
      (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! iter.iter.end.val • Q m) +
        ∑ m ∈ Finset.range static_nafs.length,
          nafTail static_nafs.val[m]! iter.iter.end.val • P m) :
    O.pstLoop0 iter v static_nafs dynamic_nafs dynamic_lookup_tables dp S
      ⦃ (r : O.Pr) => O.pOnCurve r ∧ O.pBnd r ∧ O.pToPoint r =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! 0 • Q m) +
          ∑ m ∈ Finset.range static_nafs.length, nafTail static_nafs.val[m]! 0 • P m ⦄ := by
  unfold pstLoop0
  apply loop.spec_decr_nat (measure := fun (it, _) => it.iter.end.val)
    (inv := fun (it, q) => it.iter.start.val = 0 ∧ it.iter.end.val ≤ 256 ∧ O.pOnCurve q ∧
      O.pBnd q ∧ O.pToPoint q =
        (∑ m ∈ Finset.range dp.val, nafTail dynamic_nafs.val[m]! it.iter.end.val • Q m) +
          ∑ m ∈ Finset.range static_nafs.length,
            nafTail static_nafs.val[m]! it.iter.end.val • P m)
  · rintro ⟨it, q⟩ ⟨hst, hen, hqon, hqb, hqp⟩
    unfold pstLoop0Body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, j, ho, hj, hstart1, hend1⟩
      subst ho
      have hj256 : j.val < 256 := by scalar_tac
      step with hdbl q hqb hqon as ⟨R, hRon, hRp, hRb⟩
      step with O.pstLoop00_spec haddN hsubN hasE
        { start := 0#usize, «end» := dp } dynamic_nafs dynamic_lookup_tables j R Q hj256 hdp hT hD
        (Nat.zero_le _) hRon hRb as ⟨R1, hR1on, hR1b, hR1⟩
      step with O.pstLoop01_spec haddA hsubA hasE
        { start := 0#usize, «end» := alloc.vec.Vec.len static_nafs } static_nafs v j R1 P hj256
        ⟨by simp, by simpa using hsl⟩ (by simpa using hV) (by simpa using hE) (Nat.zero_le _)
        hR1on hR1b as ⟨R2, hR2on, hR2b, hR2⟩
      step with hasP R2 hR2b hR2on as ⟨q1, hq1on, hq1, hq1b⟩
      refine ⟨by rw [hstart1, hst], by scalar_tac, hq1on, hq1b, ?_, by scalar_tac⟩
      simp only [alloc.vec.Vec.len_val] at hR1 hR2
      rw [hq1, hR2, hR1, hRp, hqp, ← Finset.range_eq_Ico, ← Finset.range_eq_Ico, hend1, ← hj,
        add_assoc, ← add_assoc (2 • _),
        horner2_two dp.val static_nafs.length j.val (fun k => dynamic_nafs.val[k]!)
          (fun k => static_nafs.val[k]!) Q P hj256]
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      rw [show it.iter.end.val = 0 by omega] at hqp
      exact ⟨hqon, hqb, hqp⟩
  · exact ⟨hstart, hend, hS, hSb, hSp⟩


end Curve25519Dalek.EdwardsOps
