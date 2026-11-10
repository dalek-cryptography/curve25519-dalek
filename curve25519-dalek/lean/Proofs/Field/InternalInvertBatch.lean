/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Curve25519.Prime
import Mathlib.Algebra.Field.ZMod
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Field.Invert
import Proofs.Field.IsZero
import Proofs.Helpers.Field
import Proofs.Helpers.Iterator
import Proofs.Helpers.Array
import Proofs.Helpers.ZMod
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.One
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

/-! ## Prefix products of the nonzero inputs, in `ZMod p` -/

/-- The factor of input `k` in the running product: the input, or `1` if it is zero. -/
private def fac (inputs : Slice FieldElement51) (k : ℕ) : ZMod p :=
  if (inputs[k]!.asNat : ZMod p) = 0 then 1 else (inputs[k]!.asNat : ZMod p)

/-- The product of the nonzero inputs before index `i`. -/
private def pre (inputs : Slice FieldElement51) (i : ℕ) : ZMod p :=
  ∏ k ∈ Finset.range i, fac inputs k

private theorem fac_ne_zero (inputs : Slice FieldElement51) (k : ℕ) : fac inputs k ≠ 0 := by
  unfold fac
  split_ifs with h
  · exact one_ne_zero
  · exact h

private theorem pre_ne_zero (inputs : Slice FieldElement51) (i : ℕ) : pre inputs i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => fac_ne_zero inputs k

private theorem pre_succ (inputs : Slice FieldElement51) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * fac inputs i :=
  Finset.prod_range_succ _ i

private theorem not_one : (1#u8 &&& ~~~(1#u8 : subtle.Choice)) = 0#u8 := by decide

private theorem not_zero : (1#u8 &&& ~~~(0#u8 : subtle.Choice)) = 1#u8 := by decide

/-- `fe` is the product of the nonzero inputs before index `i`, with limbs `< 2^54`. -/
private def IsPre (inputs : Slice FieldElement51) (fe : FieldElement51) (i : ℕ) : Prop :=
  (fe.asNat : ZMod p) = pre inputs i ∧ fe.LimbsLt 54

/-! ## First loop: prefix products into `scratch` -/

/-- Writing the prefix product at index `i` extends the prefix products of `s` to `i + 1`. -/
private theorem isPre_set {inputs s : Slice FieldElement51} {a : FieldElement51} {i : Usize}
    (hs : ∀ k < i.val, IsPre inputs s[k]! k) (ha : IsPre inputs a i.val) (hi : i.val < s.length) :
    ∀ k < i.val + 1, IsPre inputs (s.set i a)[k]! k :=
  Slice.forall_lt_succ_set (P := fun k x => IsPre inputs x k) hs ha hi

/-- One step of the first loop: store `acc` at `i`, multiply it by input `i` unless zero. -/
private theorem internal_invert_batch_loop0_body_spec (inputs scratch : Slice FieldElement51)
    (acc : FieldElement51)
    (it : core.ops.range.Range Usize) (hn : it.end.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hlt : it.start.val < it.end.val)
    (hinputs : ∀ k < inputs.length, (inputs[k]!).LimbsLt 54)
    (hacc : IsPre inputs acc it.start.val) :
    internal_invert_batch_loop0.body inputs it scratch acc ⦃ r =>
      ∃ acc1 it1, r = .cont (it1, scratch.set it.start acc, acc1) ∧
        it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
        IsPre inputs acc1 (it.start.val + 1) ⦄ := by
  unfold internal_invert_batch_loop0.body
  have hlt' : it.start.val < inputs.length := hn ▸ hlt
  have hab := hacc.2
  step with core.iter.range.IteratorRange.next_Usize_some_spec
    as ⟨o, it1, ho, hstart1, hend1⟩
  subst ho
  step as ⟨fe, hfe⟩
  step as ⟨s1, hs1⟩
  have hfe' : fe = inputs[it.start.val]! := by
    rw [hfe, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : fe.LimbsLt 54 := hfe' ▸ hinputs it.start.val hlt'
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨c1, _, hc1'⟩
  step as ⟨acc1, ha0, ha1⟩
  refine ⟨acc1, it1, by rw [hs1], hstart1, hend1, ?_⟩
  rw [IsPre, pre_succ, ← hacc.1, fac, ← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hc1'
    rw [ha0 hc1', ite_eq_left hz, mul_one]
    exact ⟨rfl, hab⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hc1'
    rw [ha1 hc1', ite_eq_right hz, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact ⟨hfe1, fun j hj => lt_trans (hfe1b j hj) (by norm_num)⟩

@[local step]
private theorem internal_invert_batch_loop0_spec (inputs scratch : Slice FieldElement51)
    (acc : FieldElement51)
    (it : core.ops.range.Range Usize) (hn : it.end.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hi : it.start.val ≤ it.end.val)
    (hinputs : ∀ k < inputs.length, (inputs[k]!).LimbsLt 54)
    (hacc : IsPre inputs acc it.start.val)
    (hscratch : ∀ k < it.start.val, IsPre inputs scratch[k]! k) :
    internal_invert_batch_loop0 it inputs scratch acc ⦃ (s : Slice FieldElement51)
      (a : FieldElement51) =>
      s.length = inputs.length ∧ IsPre inputs a inputs.length ∧
      ∀ k < inputs.length, IsPre inputs s[k]! k ⦄ := by
  unfold internal_invert_batch_loop0
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.end.val - it.start.val)
    (inv := fun (it, s, a) => it.end.val = inputs.length ∧ it.start.val ≤ it.end.val ∧
      s.length = inputs.length ∧ IsPre inputs a it.start.val ∧
      ∀ k < it.start.val, IsPre inputs s[k]! k)
  · rintro ⟨it', s, a⟩ ⟨hend, hi', hsl, ha, hs⟩
    dsimp only
    by_cases hlt : it'.start.val < it'.end.val
    · apply spec_mono
        (internal_invert_batch_loop0_body_spec inputs s a it' hend hsl hlt hinputs ha)
      rintro r ⟨acc1, it1, rfl, hi1, hend1, hacc1⟩
      have hsl' : it'.start.val < s.length := by omega
      refine ⟨⟨by simpa only [hend1] using hend, by scalar_tac,
        by rw [Slice.set_length, hsl], hi1 ▸ hacc1, hi1 ▸ isPre_set hs ha hsl'⟩, ?_⟩
      dsimp only
      rw [hi1, hend1]
      omega
    · unfold internal_invert_batch_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it'.start.val = inputs.length := by omega
      rw [hin] at ha hs
      exact ⟨hsl, ha, hs⟩
  · exact ⟨hn, hi, hlen, hacc, hscratch⟩

/-! ## Second loop: the inverses, from the back -/

/-- What the batch inversion leaves in place of the input `x`. -/
private def Done (x r : FieldElement51) : Prop :=
  ((x.asNat : ZMod p) = 0 → r = x) ∧
  ((x.asNat : ZMod p) ≠ 0 → (r.asNat : ZMod p) * x.asNat = 1 ∧ r.LimbsLt 52)

/-- One step of the second loop replaces the last unchecked input by its inverse, unless zero,
and updates `acc` to the inverse of the preceding prefix product. -/
private theorem internal_invert_batch_loop1_body_spec
    (inputs0 inputs scratch : Slice FieldElement51) (acc : FieldElement51)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hlt : it.iter.start.val < it.iter.end.val) (hend : it.iter.end.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, (inputs0[k]!).LimbsLt 54)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1)
    (haccb : acc.LimbsLt 54)
    (hlow : ∀ j < it.iter.end.val, inputs[j]! = inputs0[j]!) :
    internal_invert_batch_loop1.body it inputs scratch acc ⦃ r =>
      ∃ fe acc1 k1 it1, r = .cont (it1, inputs.set k1 fe, scratch, acc1) ∧
        k1.val + 1 = it.iter.end.val ∧
        it1.iter.start = it.iter.start ∧ it1.iter.end = k1 ∧
        (acc1.asNat : ZMod p) * pre inputs0 k1.val = 1 ∧ (acc1.LimbsLt 54) ∧
        Done inputs0[k1.val]! fe ⦄ := by
  unfold internal_invert_batch_loop1.body
  step with core.iter.adapters.rev.Rev.next_Usize_some_spec
    as ⟨o, it1, k1, ho, hkk, hstart1, hend1⟩
  subst ho
  have hk1' : k1.val < inputs0.length := by scalar_tac
  have hk1k : k1.val < it.iter.end.val := by omega
  step as ⟨fe, back, hfe, hback⟩
  step as ⟨fe1, scratch_back, hfe1, hscratch_back⟩
  have hfe' : fe = inputs0[k1.val]! := by
    rw [hfe, ← hlow k1.val hk1k, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : fe.LimbsLt 54 := hfe' ▸ hinputs k1.val hk1'
  step as ⟨tmp, htmp, htmpb⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨nz, _, hnz⟩
  have hfe1' : fe1 = scratch[k1.val]! := by
    rw [hfe1, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfe1b : fe1.LimbsLt 54 := hfe1' ▸ (hscratch k1.val hk1').2
  step as ⟨prod, hprod, hprodb⟩
  step as ⟨fe3, hfe30, hfe31⟩
  step as ⟨acc1, ha0, ha1⟩
  have hscratch_keep : scratch_back fe1 = scratch := by
    rw [hscratch_back, hfe1]
    exact Slice.update_index_eq _ _ _ (by scalar_tac)
  refine ⟨fe3, acc1, k1, it1, by rw [hback, hscratch_keep], hkk, hstart1, hend1, ?_⟩
  rw [← hkk, pre_succ, fac, ← hfe'] at hacc
  unfold Done
  rw [← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hnz
    rw [ha0 hnz, hfe30 hnz]
    rw [ite_eq_left hz, mul_one] at hacc
    exact ⟨hacc, haccb, fun _ => rfl, fun h => absurd hz h⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hnz
    rw [ha1 hnz, hfe31 hnz]
    rw [ite_eq_right hz] at hacc
    have htmp' : (tmp.asNat : ZMod p) = acc.asNat * fe.asNat := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact htmp
    have hprod' : (prod.asNat : ZMod p) = acc.asNat * pre inputs0 k1.val := by
      rw [← (hscratch k1.val hk1').1, ← hfe1', ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact hprod
    refine ⟨by rw [htmp', ← hacc]; ring, fun j hj => lt_trans (htmpb j hj) (by norm_num),
      fun h => absurd h hz, fun _ => ⟨by rw [hprod', ← hacc]; ring, hprodb⟩⟩

/-- Writing the result for index `k1` keeps the inputs below `k1` and extends the results to
`k1`. -/
private theorem done_set {inputs0 s : Slice FieldElement51} {fe : FieldElement51} {k1 : Usize}
    {k : ℕ} (hkk : k1.val + 1 = k) (hk1 : k1.val < s.length)
    (hl : ∀ j < k, s[j]! = inputs0[j]!)
    (hh : ∀ j < inputs0.length, k ≤ j → Done inputs0[j]! s[j]!)
    (hfe : Done inputs0[k1.val]! fe) :
    (∀ j < k1.val, (s.set k1 fe)[j]! = inputs0[j]!) ∧
    ∀ j < inputs0.length, k1.val ≤ j → Done inputs0[j]! (s.set k1 fe)[j]! := by
  obtain ⟨hkeep, hdone⟩ :=
    Slice.forall_ge_pred_set (P := fun j x => Done inputs0[j]! x) hkk hk1 hh hfe
  exact ⟨fun j hj => (hkeep j hj).trans (hl j (hkk ▸ Nat.lt_succ_of_lt hj)), hdone⟩

@[local step]
private theorem internal_invert_batch_loop1_spec (inputs0 inputs scratch : Slice FieldElement51)
    (acc : FieldElement51)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hstart : it.iter.start.val = 0) (hk : it.iter.end.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, (inputs0[k]!).LimbsLt 54)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1)
    (haccb : acc.LimbsLt 54)
    (hlow : ∀ j < it.iter.end.val, inputs[j]! = inputs0[j]!)
    (hhigh : ∀ j < inputs0.length,
      it.iter.end.val ≤ j → Done inputs0[j]! inputs[j]!) :
    internal_invert_batch_loop1 it inputs scratch acc ⦃ (r _scratch : Slice FieldElement51) =>
      r.length = inputs0.length ∧ ∀ j < inputs0.length, Done inputs0[j]! r[j]! ⦄ := by
  unfold internal_invert_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _, _, _) => it.iter.end.val)
    (inv := fun (it, s, sc, a) => it.iter.start.val = 0 ∧
      it.iter.end.val ≤ inputs0.length ∧ s.length = inputs0.length ∧ sc = scratch ∧
      (a.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1 ∧ a.LimbsLt 54 ∧
      (∀ j < it.iter.end.val, s[j]! = inputs0[j]!) ∧
      ∀ j < inputs0.length, it.iter.end.val ≤ j → Done inputs0[j]! s[j]!)
  · rintro ⟨it', s, sc, a⟩ ⟨hst, hk', hsl, hsc, ha, hab, hl, hh⟩
    subst sc
    dsimp only
    by_cases hlt : it'.iter.start.val < it'.iter.end.val
    · apply spec_mono (internal_invert_batch_loop1_body_spec inputs0 s scratch a it' hlt hk'
        hsl hinputs hscratch hslen ha hab hl)
      rintro r ⟨fe, acc1, k1, it1, rfl, hkk, hstart1, hend1, hacc1, hacc1b, hfe⟩
      have hk1 : k1.val < s.length := by omega
      obtain ⟨hl1, hh1⟩ := done_set hkk hk1 hl hh hfe
      refine ⟨⟨by simpa only [hstart1] using hst, by scalar_tac,
        by rw [Slice.set_length, hsl], rfl, ?_, hacc1b, ?_, ?_⟩, ?_⟩
      · simpa only [hend1] using hacc1
      · simpa only [hend1] using hl1
      · simpa only [hend1] using hh1
      · dsimp only
        rw [hend1]
        omega
    · unfold internal_invert_batch_loop1.body
      step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have hk0 : it'.iter.end.val = 0 := by omega
      rw [hk0] at hh
      exact ⟨hsl, fun j hj => hh j hj (Nat.zero_le j)⟩
  · exact ⟨hstart, hk, hlen, rfl, hacc, haccb, hlow, hhigh⟩

@[step]
theorem internal_invert_batch_spec (inputs scratch : Slice FieldElement51)
    (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, (inputs[i]!).LimbsLt 54) :
    internal_invert_batch inputs scratch ⦃ (r _scratch : Slice FieldElement51) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 52) ⦄ := by
  unfold internal_invert_batch
  step as ⟨hlen'⟩
  step as ⟨one, hone, honeb⟩
  have hone' : IsPre inputs one (0#usize).val := by
    refine ⟨?_, fun j hj => lt_trans (honeb j hj) (by norm_num)⟩
    rw [hone]
    simp [pre]
  step with internal_invert_batch_loop0_spec inputs scratch one
    { start := 0#usize, «end» := inputs.len } (by simp) hlen
    (by simp) hinputs hone' (fun k hk => absurd hk (by simp))
    as ⟨scratch1, acc1, hs1len, hacc1', hs1⟩
  obtain ⟨hacc1, hacc1b⟩ := hacc1'
  step as ⟨c, _, hc1, hc0⟩
  rw [hc0 (fun h => pre_ne_zero inputs inputs.length
    (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h))]
  step as ⟨c1, _, hc1'⟩
  rw [not_zero] at hc1'
  subst hc1'
  step as ⟨b, hb⟩
  have hbt : b = true := by
    rw [hb]
    decide
  step as ⟨hbt'⟩
  step as ⟨acc2, hinv1, hinv0, hacc2b⟩
  have hn : inputs.len.val = inputs.length := by simp
  have hacc2 : (acc2.asNat : ZMod p) * pre inputs inputs.len.val = 1 := by
    have hne : acc1.asNat % p ≠ 0 := fun h =>
      pre_ne_zero inputs inputs.length (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
    have h := ZMod.natCast_eq_natCast_of_mod_eq (hinv1 hne)
    push_cast at h
    rw [hn, ← hacc1, h]
  step as ⟨rev, hrev⟩
  step with internal_invert_batch_loop1_spec inputs inputs scratch1 acc2 rev
    (by simp [hrev]) (by simp [hrev]) rfl
    hinputs hs1 hs1len (by simpa [hrev] using hacc2)
    (fun j hj => lt_trans (hacc2b j hj) (by norm_num))
    (fun j _ => rfl) (fun j hj hkj => absurd hj (by simpa [hrev] using Nat.not_lt.mpr hkj))
    as ⟨r, scratch2, hrlen, hr⟩
  refine ⟨hrlen, fun i hi => ⟨fun h => (hr i hi).1 (ZMod.natCast_eq_zero_iff_mod.mpr h),
    fun h => ?_⟩⟩
  obtain ⟨h1, h2⟩ := (hr i hi).2 (fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h'))
  refine ⟨?_, h2⟩
  rw [← one_mod_p, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  exact h1

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

/-! ## Prefix products of the nonzero inputs, in `ZMod p` -/

/-- The factor of input `k` in the running product: the input, or `1` if it is zero. -/
private def fac (inputs : Slice FieldElement2625) (k : ℕ) : ZMod p :=
  if (inputs[k]!.asNat : ZMod p) = 0 then 1 else (inputs[k]!.asNat : ZMod p)

/-- The product of the nonzero inputs before index `i`. -/
private def pre (inputs : Slice FieldElement2625) (i : ℕ) : ZMod p :=
  ∏ k ∈ Finset.range i, fac inputs k

private theorem fac_ne_zero (inputs : Slice FieldElement2625) (k : ℕ) : fac inputs k ≠ 0 := by
  unfold fac
  split_ifs with h
  · exact one_ne_zero
  · exact h

private theorem pre_ne_zero (inputs : Slice FieldElement2625) (i : ℕ) : pre inputs i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => fac_ne_zero inputs k

private theorem pre_succ (inputs : Slice FieldElement2625) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * fac inputs i :=
  Finset.prod_range_succ _ i

private theorem not_one : (1#u8 &&& ~~~(1#u8 : subtle.Choice)) = 0#u8 := by decide

private theorem not_zero : (1#u8 &&& ~~~(0#u8 : subtle.Choice)) = 1#u8 := by decide

/-- `fe` is the product of the nonzero inputs before index `i`, with limbs `< 2^27`. -/
private def IsPre (inputs : Slice FieldElement2625) (fe : FieldElement2625) (i : ℕ) : Prop :=
  (fe.asNat : ZMod p) = pre inputs i ∧ fe.LimbsLt 27

/-! ## First loop: prefix products into `scratch` -/

/-- Writing the prefix product at index `i` extends the prefix products of `s` to `i + 1`. -/
private theorem isPre_set {inputs s : Slice FieldElement2625} {a : FieldElement2625} {i : Usize}
    (hs : ∀ k < i.val, IsPre inputs s[k]! k) (ha : IsPre inputs a i.val) (hi : i.val < s.length) :
    ∀ k < i.val + 1, IsPre inputs (s.set i a)[k]! k :=
  Slice.forall_lt_succ_set (P := fun k x => IsPre inputs x k) hs ha hi

/-- One step of the first loop: store `acc` at `i`, multiply it by input `i` unless zero. -/
private theorem internal_invert_batch_loop0_body_spec (inputs scratch : Slice FieldElement2625)
    (acc : FieldElement2625)
    (it : core.ops.range.Range Usize) (hn : it.end.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hlt : it.start.val < it.end.val)
    (hinputs : ∀ k < inputs.length, (inputs[k]!).LimbsLt 27)
    (hacc : IsPre inputs acc it.start.val) :
    internal_invert_batch_loop0.body inputs it scratch acc ⦃ r =>
      ∃ acc1 it1, r = .cont (it1, scratch.set it.start acc, acc1) ∧
        it1.start.val = it.start.val + 1 ∧ it1.end = it.end ∧
        IsPre inputs acc1 (it.start.val + 1) ⦄ := by
  unfold internal_invert_batch_loop0.body
  have hlt' : it.start.val < inputs.length := hn ▸ hlt
  have hab := hacc.2
  step with core.iter.range.IteratorRange.next_Usize_some_spec
    as ⟨o, it1, ho, hstart1, hend1⟩
  subst ho
  step as ⟨fe, hfe⟩
  step as ⟨s1, hs1⟩
  have hfe' : fe = inputs[it.start.val]! := by
    rw [hfe, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : fe.LimbsLt 27 := hfe' ▸ hinputs it.start.val hlt'
  step as ⟨fe1, hfe1, hfe1b⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨c1, _, hc1'⟩
  step as ⟨acc1, ha0, ha1⟩
  refine ⟨acc1, it1, by rw [hs1], hstart1, hend1, ?_⟩
  rw [IsPre, pre_succ, ← hacc.1, fac, ← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hc1'
    rw [ha0 hc1', ite_eq_left hz, mul_one]
    exact ⟨rfl, hab⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hc1'
    rw [ha1 hc1', ite_eq_right hz, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
    exact ⟨hfe1, fun j hj => lt_trans (hfe1b j hj) (by norm_num)⟩

@[local step]
private theorem internal_invert_batch_loop0_spec (inputs scratch : Slice FieldElement2625)
    (acc : FieldElement2625)
    (it : core.ops.range.Range Usize) (hn : it.end.val = inputs.length)
    (hlen : scratch.length = inputs.length) (hi : it.start.val ≤ it.end.val)
    (hinputs : ∀ k < inputs.length, (inputs[k]!).LimbsLt 27)
    (hacc : IsPre inputs acc it.start.val)
    (hscratch : ∀ k < it.start.val, IsPre inputs scratch[k]! k) :
    internal_invert_batch_loop0 it inputs scratch acc ⦃ (s : Slice FieldElement2625)
      (a : FieldElement2625) =>
      s.length = inputs.length ∧ IsPre inputs a inputs.length ∧
      ∀ k < inputs.length, IsPre inputs s[k]! k ⦄ := by
  unfold internal_invert_batch_loop0
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.end.val - it.start.val)
    (inv := fun (it, s, a) => it.end.val = inputs.length ∧ it.start.val ≤ it.end.val ∧
      s.length = inputs.length ∧ IsPre inputs a it.start.val ∧
      ∀ k < it.start.val, IsPre inputs s[k]! k)
  · rintro ⟨it', s, a⟩ ⟨hend, hi', hsl, ha, hs⟩
    dsimp only
    by_cases hlt : it'.start.val < it'.end.val
    · apply spec_mono
        (internal_invert_batch_loop0_body_spec inputs s a it' hend hsl hlt hinputs ha)
      rintro r ⟨acc1, it1, rfl, hi1, hend1, hacc1⟩
      have hsl' : it'.start.val < s.length := by omega
      refine ⟨⟨by simpa only [hend1] using hend, by scalar_tac,
        by rw [Slice.set_length, hsl], hi1 ▸ hacc1, hi1 ▸ isPre_set hs ha hsl'⟩, ?_⟩
      dsimp only
      rw [hi1, hend1]
      omega
    · unfold internal_invert_batch_loop0.body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : it'.start.val = inputs.length := by omega
      rw [hin] at ha hs
      exact ⟨hsl, ha, hs⟩
  · exact ⟨hn, hi, hlen, hacc, hscratch⟩

/-! ## Second loop: the inverses, from the back -/

/-- What the batch inversion leaves in place of the input `x`. -/
private def Done (x r : FieldElement2625) : Prop :=
  ((x.asNat : ZMod p) = 0 → r = x) ∧
  ((x.asNat : ZMod p) ≠ 0 → (r.asNat : ZMod p) * x.asNat = 1 ∧ r.LimbsLt 26)

/-- One step of the second loop replaces the last unchecked input by its inverse, unless zero,
and updates `acc` to the inverse of the preceding prefix product. -/
private theorem internal_invert_batch_loop1_body_spec
    (inputs0 inputs scratch : Slice FieldElement2625) (acc : FieldElement2625)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hlt : it.iter.start.val < it.iter.end.val) (hend : it.iter.end.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, (inputs0[k]!).LimbsLt 27)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1)
    (haccb : acc.LimbsLt 27)
    (hlow : ∀ j < it.iter.end.val, inputs[j]! = inputs0[j]!) :
    internal_invert_batch_loop1.body it inputs scratch acc ⦃ r =>
      ∃ fe acc1 k1 it1, r = .cont (it1, inputs.set k1 fe, scratch, acc1) ∧
        k1.val + 1 = it.iter.end.val ∧
        it1.iter.start = it.iter.start ∧ it1.iter.end = k1 ∧
        (acc1.asNat : ZMod p) * pre inputs0 k1.val = 1 ∧ (acc1.LimbsLt 27) ∧
        Done inputs0[k1.val]! fe ⦄ := by
  unfold internal_invert_batch_loop1.body
  step with core.iter.adapters.rev.Rev.next_Usize_some_spec
    as ⟨o, it1, k1, ho, hkk, hstart1, hend1⟩
  subst ho
  have hk1' : k1.val < inputs0.length := by scalar_tac
  have hk1k : k1.val < it.iter.end.val := by omega
  step as ⟨fe, back, hfe, hback⟩
  step as ⟨fe1, scratch_back, hfe1, hscratch_back⟩
  have hfe' : fe = inputs0[k1.val]! := by
    rw [hfe, ← hlow k1.val hk1k, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfeb : fe.LimbsLt 27 := hfe' ▸ hinputs k1.val hk1'
  step as ⟨tmp, htmp, htmpb⟩
  step as ⟨c, _, hc1, hc0⟩
  step as ⟨nz, _, hnz⟩
  have hfe1' : fe1 = scratch[k1.val]! := by
    rw [hfe1, Slice.getElem!_Nat_eq, getElem!_pos]
  have hfe1b : fe1.LimbsLt 27 := hfe1' ▸ (hscratch k1.val hk1').2
  step as ⟨prod, hprod, hprodb⟩
  step as ⟨fe3, hfe30, hfe31⟩
  step as ⟨acc1, ha0, ha1⟩
  have hscratch_keep : scratch_back fe1 = scratch := by
    rw [hscratch_back, hfe1]
    exact Slice.update_index_eq _ _ _ (by scalar_tac)
  refine ⟨fe3, acc1, k1, it1, by rw [hback, hscratch_keep], hkk, hstart1, hend1, ?_⟩
  rw [← hkk, pre_succ, fac, ← hfe'] at hacc
  unfold Done
  rw [← hfe']
  by_cases hz : (fe.asNat : ZMod p) = 0
  · rw [hc1 (ZMod.natCast_eq_zero_iff_mod.mp hz), not_one] at hnz
    rw [ha0 hnz, hfe30 hnz]
    rw [ite_eq_left hz, mul_one] at hacc
    exact ⟨hacc, haccb, fun _ => rfl, fun h => absurd hz h⟩
  · rw [hc0 (fun h => hz (ZMod.natCast_eq_zero_iff_mod.mpr h)), not_zero] at hnz
    rw [ha1 hnz, hfe31 hnz]
    rw [ite_eq_right hz] at hacc
    have htmp' : (tmp.asNat : ZMod p) = acc.asNat * fe.asNat := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact htmp
    have hprod' : (prod.asNat : ZMod p) = acc.asNat * pre inputs0 k1.val := by
      rw [← (hscratch k1.val hk1').1, ← hfe1', ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
      exact hprod
    refine ⟨by rw [htmp', ← hacc]; ring, fun j hj => lt_trans (htmpb j hj) (by norm_num),
      fun h => absurd h hz, fun _ => ⟨by rw [hprod', ← hacc]; ring, hprodb⟩⟩

/-- Writing the result for index `k1` keeps the inputs below `k1` and extends the results to
`k1`. -/
private theorem done_set {inputs0 s : Slice FieldElement2625} {fe : FieldElement2625} {k1 : Usize}
    {k : ℕ} (hkk : k1.val + 1 = k) (hk1 : k1.val < s.length)
    (hl : ∀ j < k, s[j]! = inputs0[j]!)
    (hh : ∀ j < inputs0.length, k ≤ j → Done inputs0[j]! s[j]!)
    (hfe : Done inputs0[k1.val]! fe) :
    (∀ j < k1.val, (s.set k1 fe)[j]! = inputs0[j]!) ∧
    ∀ j < inputs0.length, k1.val ≤ j → Done inputs0[j]! (s.set k1 fe)[j]! := by
  obtain ⟨hkeep, hdone⟩ :=
    Slice.forall_ge_pred_set (P := fun j x => Done inputs0[j]! x) hkk hk1 hh hfe
  exact ⟨fun j hj => (hkeep j hj).trans (hl j (hkk ▸ Nat.lt_succ_of_lt hj)), hdone⟩

@[local step]
private theorem internal_invert_batch_loop1_spec (inputs0 inputs scratch : Slice FieldElement2625)
    (acc : FieldElement2625)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hstart : it.iter.start.val = 0) (hk : it.iter.end.val ≤ inputs0.length)
    (hlen : inputs.length = inputs0.length)
    (hinputs : ∀ k < inputs0.length, (inputs0[k]!).LimbsLt 27)
    (hscratch : ∀ k < inputs0.length, IsPre inputs0 scratch[k]! k)
    (hslen : scratch.length = inputs0.length)
    (hacc : (acc.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1)
    (haccb : acc.LimbsLt 27)
    (hlow : ∀ j < it.iter.end.val, inputs[j]! = inputs0[j]!)
    (hhigh : ∀ j < inputs0.length,
      it.iter.end.val ≤ j → Done inputs0[j]! inputs[j]!) :
    internal_invert_batch_loop1 it inputs scratch acc ⦃ (r _scratch : Slice FieldElement2625) =>
      r.length = inputs0.length ∧ ∀ j < inputs0.length, Done inputs0[j]! r[j]! ⦄ := by
  unfold internal_invert_batch_loop1
  apply loop.spec_decr_nat (measure := fun (it, _, _, _) => it.iter.end.val)
    (inv := fun (it, s, sc, a) => it.iter.start.val = 0 ∧
      it.iter.end.val ≤ inputs0.length ∧ s.length = inputs0.length ∧ sc = scratch ∧
      (a.asNat : ZMod p) * pre inputs0 it.iter.end.val = 1 ∧ a.LimbsLt 27 ∧
      (∀ j < it.iter.end.val, s[j]! = inputs0[j]!) ∧
      ∀ j < inputs0.length, it.iter.end.val ≤ j → Done inputs0[j]! s[j]!)
  · rintro ⟨it', s, sc, a⟩ ⟨hst, hk', hsl, hsc, ha, hab, hl, hh⟩
    subst sc
    dsimp only
    by_cases hlt : it'.iter.start.val < it'.iter.end.val
    · apply spec_mono (internal_invert_batch_loop1_body_spec inputs0 s scratch a it' hlt hk'
        hsl hinputs hscratch hslen ha hab hl)
      rintro r ⟨fe, acc1, k1, it1, rfl, hkk, hstart1, hend1, hacc1, hacc1b, hfe⟩
      have hk1 : k1.val < s.length := by omega
      obtain ⟨hl1, hh1⟩ := done_set hkk hk1 hl hh hfe
      refine ⟨⟨by simpa only [hstart1] using hst, by scalar_tac,
        by rw [Slice.set_length, hsl], rfl, ?_, hacc1b, ?_, ?_⟩, ?_⟩
      · simpa only [hend1] using hacc1
      · simpa only [hend1] using hl1
      · simpa only [hend1] using hh1
      · dsimp only
        rw [hend1]
        omega
    · unfold internal_invert_batch_loop1.body
      step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have hk0 : it'.iter.end.val = 0 := by omega
      rw [hk0] at hh
      exact ⟨hsl, fun j hj => hh j hj (Nat.zero_le j)⟩
  · exact ⟨hstart, hk, hlen, rfl, hacc, haccb, hlow, hhigh⟩

@[step]
theorem internal_invert_batch_spec (inputs scratch : Slice FieldElement2625)
    (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, (inputs[i]!).LimbsLt 27) :
    internal_invert_batch inputs scratch ⦃ (r _scratch : Slice FieldElement2625) =>
      r.length = inputs.length ∧
      ∀ i < inputs.length,
        (inputs[i]!.asNat % p = 0 → r[i]! = inputs[i]!) ∧
        (inputs[i]!.asNat % p ≠ 0 → r[i]!.asNat * inputs[i]!.asNat % p = 1 ∧
          (r[i]!).LimbsLt 26) ⦄ := by
  unfold internal_invert_batch
  step as ⟨hlen'⟩
  step as ⟨one, hone, honeb⟩
  have hone' : IsPre inputs one (0#usize).val := by
    refine ⟨?_, fun j hj => lt_trans (honeb j hj) (by norm_num)⟩
    rw [hone]
    simp [pre]
  step with internal_invert_batch_loop0_spec inputs scratch one
    { start := 0#usize, «end» := inputs.len } (by simp) hlen
    (by simp) hinputs hone' (fun k hk => absurd hk (by simp))
    as ⟨scratch1, acc1, hs1len, hacc1', hs1⟩
  obtain ⟨hacc1, hacc1b⟩ := hacc1'
  step as ⟨c, _, hc1, hc0⟩
  rw [hc0 (fun h => pre_ne_zero inputs inputs.length
    (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h))]
  step as ⟨c1, _, hc1'⟩
  rw [not_zero] at hc1'
  subst hc1'
  step as ⟨b, hb⟩
  have hbt : b = true := by
    rw [hb]
    decide
  step as ⟨hbt'⟩
  step as ⟨acc2, hinv1, hinv0, hacc2b⟩
  have hn : inputs.len.val = inputs.length := by simp
  have hacc2 : (acc2.asNat : ZMod p) * pre inputs inputs.len.val = 1 := by
    have hne : acc1.asNat % p ≠ 0 := fun h =>
      pre_ne_zero inputs inputs.length (hacc1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
    have h := ZMod.natCast_eq_natCast_of_mod_eq (hinv1 hne)
    push_cast at h
    rw [hn, ← hacc1, h]
  step as ⟨rev, hrev⟩
  step with internal_invert_batch_loop1_spec inputs inputs scratch1 acc2 rev
    (by simp [hrev]) (by simp [hrev]) rfl
    hinputs hs1 hs1len (by simpa [hrev] using hacc2)
    (fun j hj => lt_trans (hacc2b j hj) (by norm_num))
    (fun j _ => rfl) (fun j hj hkj => absurd hj (by simpa [hrev] using Nat.not_lt.mpr hkj))
    as ⟨r, scratch2, hrlen, hr⟩
  refine ⟨hrlen, fun i hi => ⟨fun h => (hr i hi).1 (ZMod.natCast_eq_zero_iff_mod.mpr h),
    fun h => ?_⟩⟩
  obtain ⟨h1, h2⟩ := (hr i hi).2 (fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h'))
  refine ⟨?_, h2⟩
  rw [← one_mod_p, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  exact h1

end Curve25519Dalek.field.FieldElement2625
