/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Curve25519.Prime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Scalar.AsMontgomery
import Proofs.Backend.Serial.U64.Scalar.FromMontgomery
import Proofs.Backend.Serial.U64.Scalar.MontgomeryMul
import Proofs.Helpers.Array
import Proofs.Helpers.Montgomery
import Proofs.Helpers.Scalar
import Proofs.Helpers.Scalar52
import Proofs.Helpers.ZMod
import Proofs.Scalar.Eq
import Proofs.Scalar.One
import Proofs.Scalar.Scalar52MontgomeryInvert
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Scalar.Zero
import Proofs.Backend.Serial.U32.Scalar.AsMontgomery
import Proofs.Backend.Serial.U32.Scalar.FromMontgomery
import Proofs.Backend.Serial.U32.Scalar.MontgomeryMul
import Proofs.Helpers.Scalar29
import Proofs.Scalar.Scalar29MontgomeryInvert
import Proofs.Scalar.Scalar29Pack
import Zeroize.Instances
import Zeroize.Lemmas
import Proofs.Helpers.Iterator
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

open backend.serial.u64.scalar (Scalar52)

/-! ## Prefix products of the inputs, in `ZMod L` -/

/-- The product of the inputs before index `i`. -/
private def pre (inputs : Slice Scalar) (i : ℕ) : ZMod L :=
  ∏ k ∈ Finset.range i, (inputs[k]!.asNat : ZMod L)

private theorem pre_succ (inputs : Slice Scalar) (i : ℕ) :
    pre inputs (i + 1) = pre inputs i * inputs[i]!.asNat :=
  Finset.prod_range_succ _ i

private theorem pre_ne_zero (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    pre inputs inputs.length ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k hk h0 =>
    hinputs k (Finset.mem_range.mp hk) (ZMod.natCast_eq_zero_iff_mod.mp h0)

/-- `v` is the Montgomery form `x * R` of `x`, reduced and with 52-bit limbs. -/
private def MontVal (v : Scalar52) (x : ZMod L) : Prop :=
  (v.asNat : ZMod L) = x * montgomeryRadix ∧ v.asNat < L ∧ v.LimbsLt 52

/-- The Montgomery product of two Montgomery forms. -/
private theorem montVal_mul {a b r : Scalar52} {x y : ZMod L} (ha : MontVal a x)
    (hb : (b.asNat : ZMod L) = y * montgomeryRadix)
    (hr : r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = x * y * montgomeryRadix := by
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ montgomeryRadix_natCast_ne_zero
  rw [hr', ha.1, hb]
  ring

/-- The Montgomery product of a plain value and a Montgomery form. -/
private theorem plain_mul {a b r : Scalar52} {y : ZMod L}
    (hb : (b.asNat : ZMod L) = y * montgomeryRadix)
    (hr : r.asNat * montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = a.asNat * y := by
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ montgomeryRadix_natCast_ne_zero
  rw [hr', hb]
  ring

private theorem mod_L_eq_one {a : ℕ} (h : (a : ZMod L) = 1) : a % L = 1 := by
  rw [← Nat.mod_eq_of_lt ((Nat.one_lt_two_pow (by decide)).trans two_pow_252_lt_L)]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by exact_mod_cast h)

/-! ## First loop: Montgomery forms of the inputs and of their prefix products -/

/-- One step of the first loop: store `acc` at `i`, replace input `i` by its Montgomery form `y`
and multiply `acc` by it. -/
private theorem loop0_body_spec (inputs ins : Slice Scalar) (sc : Slice Scalar52) (a : Scalar52)
    (n i : Usize) (hlt : i < n) (hn : n.val = inputs.length) (hinl : ins.length = inputs.length)
    (hscl : sc.length = inputs.length) (ha : MontVal a (pre inputs i.val))
    (hx : ins[i.val]! = inputs[i.val]!) :
    invert_batch_internal.«x86_64-tables_loop0».body { start := i, «end» := n } ins sc a
      ⦃ r =>
      ∃ y a1 i1, r = .cont ({ start := i1, «end» := n }, ins.set i y, sc.set i a, a1) ∧
        i1.val = i.val + 1 ∧
        (y.asNat : ZMod L) = inputs[i.val]!.asNat * montgomeryRadix ∧
        MontVal a1 (pre inputs (i.val + 1)) ⦄ := by
  unfold invert_batch_internal.«x86_64-tables_loop0».body
  have hil : i.val < ins.length := hinl ▸ hn ▸ hlt
  have hab := ha.2.2
  step with core.iter.range.IteratorRange.next_Usize_some_spec
    as ⟨o, it1, ho, hi1, he1⟩
  subst ho
  step as ⟨x, back, hx', hback⟩
  step as ⟨sc1, hsc1⟩
  have hx'' : x = inputs[i.val]! := by
    rw [hx', ← hx, Slice.getElem!_Nat_eq, getElem!_pos]
  step as ⟨u, hu, hub⟩
  step as ⟨t, ht, htb⟩
  have htL : t.asNat < L := ht ▸ Nat.mod_lt _ L_pos
  step with Scalar52.pack_spec t htb (lt_two_pow_256_of_lt_L htL) as ⟨y, hy⟩
  step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a t hab htb
    (Nat.mul_lt_mul'' (ha.2.1.trans backend.serial.u64.scalar.L_lt_montgomeryRadix) htL) as
    ⟨a1, ha1, ha1L, ha1b⟩
  have hit1 : it1 = { start := it1.start, «end» := n } := by
    cases it1
    simp_all
  have ht' : (t.asNat : ZMod L) = inputs[i.val]!.asNat * montgomeryRadix := by
    rw [← hx'', ← hu]
    exact_mod_cast (ZMod.natCast_eq_natCast_of_mod_eq ht.symm).symm
  refine ⟨y, a1, it1.start, by rw [hback, hsc1, hit1], hi1,
    by rw [← ht']; exact congrArg Nat.cast hy,
    ⟨?_, ha1L, ha1b⟩⟩
  rw [pre_succ]
  exact montVal_mul ha ht' ha1

@[local step]
private theorem loop0_spec (inputs : Slice Scalar) (scratch : Slice Scalar52) (acc : Scalar52)
    (n : Usize) (hn : n.val = inputs.length) (hlen : scratch.length = inputs.length)
    (hacc : MontVal acc 1) :
    invert_batch_internal.«x86_64-tables_loop0» { start := 0#usize, «end» := n } inputs scratch acc
      ⦃ (inputs1 : Slice Scalar) (scratch1 : Slice Scalar52) (acc1 : Scalar52) =>
      inputs1.length = inputs.length ∧ scratch1.length = inputs.length ∧
      MontVal acc1 (pre inputs inputs.length) ∧
      (∀ k < inputs.length, MontVal scratch1[k]! (pre inputs k)) ∧
      ∀ k < inputs.length,
        (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix ⦄ := by
  unfold invert_batch_internal.«x86_64-tables_loop0»
  apply loop.spec_decr_nat (measure := fun x => n.val - x.1.start.val)
    (inv := fun x => x.1.end = n ∧ x.1.start.val ≤ n.val ∧
      x.2.1.length = inputs.length ∧ x.2.2.1.length = inputs.length ∧
      MontVal x.2.2.2 (pre inputs x.1.start.val) ∧
      (∀ k < x.1.start.val, MontVal x.2.2.1[k]! (pre inputs k)) ∧
      (∀ k < x.1.start.val,
        (x.2.1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix) ∧
      ∀ k < inputs.length, x.1.start.val ≤ k → x.2.1[k]! = inputs[k]!)
  · rintro ⟨⟨i, e⟩, ins, sc, a⟩ ⟨he, hi, hinl, hscl, ha, hsc, hlow, hhigh⟩
    dsimp only at he
    subst e
    by_cases hlt : i < n
    · have hil : i.val < inputs.length := hn ▸ hlt
      apply spec_mono (loop0_body_spec inputs ins sc a n i hlt hn hinl hscl ha
        (hhigh i.val hil le_rfl))
      rintro r ⟨y, a1, i1, rfl, hi1, hy, ha1⟩
      refine ⟨⟨rfl, hi1 ▸ hlt, by rw [Slice.set_length, hinl], by rw [Slice.set_length, hscl],
        hi1 ▸ ha1,
        hi1 ▸ Slice.forall_lt_succ_set (P := fun k x => MontVal x (pre inputs k)) hsc ha
          (hscl ▸ hil),
        hi1 ▸ Slice.forall_lt_succ_set
          (P := fun k x => (x.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix) hlow hy
          (hinl ▸ hil), fun k hk hik => ?_⟩, ?_⟩
      · rw [hi1] at hik
        rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_lt hik)]
        exact hhigh k hk (Nat.le_of_succ_le hik)
      · dsimp only
        rw [hi1]
        exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · unfold invert_batch_internal.«x86_64-tables_loop0».body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : i.val = inputs.length := hn ▸ Nat.le_antisymm hi (Nat.le_of_not_lt hlt)
      rw [hin] at ha hsc hlow
      exact ⟨hinl, hscl, ha, hsc, hlow⟩
  · refine ⟨rfl, by simp, rfl, hlen, by simpa [pre] using hacc, fun k hk => absurd hk (by simp),
      fun k hk => absurd hk (by simp), fun k _ _ => rfl⟩

/-! ## Second loop: the inverses, from the back -/

/-- One step of the second loop: input `k - 1` is replaced by its inverse and `acc` becomes the
inverse of the product before `k - 1`. -/
private theorem loop1_body_spec (inputs inputs1 ins : Slice Scalar) (scratch : Slice Scalar52)
    (a : Scalar52) (k : Usize) (hpos : k > 0#usize) (hk : k.val ≤ inputs.length)
    (hscratch : ∀ k < inputs.length, MontVal scratch[k]! (pre inputs k))
    (hinputs1 : ∀ k < inputs.length,
      (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix)
    (hinl : ins.length = inputs.length) (hslen : scratch.length = inputs.length)
    (ha : (a.asNat : ZMod L) * pre inputs k.val = 1) (haL : a.asNat < L)
    (hab : a.LimbsLt 52) (hlow : ∀ j < k.val, ins[j]! = inputs1[j]!) :
    invert_batch_internal.«x86_64-tables_loop1».body scratch
      { iter := { start := 0#usize, «end» := k } } ins a ⦃ r =>
      ∃ y t k1, r = .cont ({ iter := { start := 0#usize, «end» := k1 } }, ins.set k1 y, t) ∧
        k1.val + 1 = k.val ∧
        (t.asNat : ZMod L) * pre inputs k1.val = 1 ∧ t.asNat < L ∧
        t.LimbsLt 52 ∧
        (y.asNat : ZMod L) * inputs[k1.val]!.asNat = 1 ∧ y.asNat < L ⦄ := by
  unfold invert_batch_internal.«x86_64-tables_loop1».body
  step with core.iter.adapters.rev.Rev.next_Usize_some_spec
    as ⟨o, it1, k1, ho, hk1, hstart, hend⟩
  subst ho
  have hkk : k1.val + 1 = k.val := by scalar_tac
  have hk1' : k1.val < inputs.length := lt_of_lt_of_le (hkk ▸ Nat.lt_succ_self k1.val) hk
  have hk1i : k1.val < ins.length := hinl ▸ hk1'
  have hk1s : k1.val < scratch.length := hslen ▸ hk1'
  step as ⟨x, back, hx, hback⟩
  step as ⟨z, hz⟩
  have hx' : x = inputs1[k1.val]! := by
    rw [hx, ← hlow k1.val (hkk ▸ Nat.lt_succ_self _), Slice.getElem!_Nat_eq, getElem!_pos]
  step as ⟨u, hu, hub⟩
  step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a u hab hub
    (by
      rw [Nat.mul_comm]
      exact Nat.mul_lt_mul'' (backend.serial.u64.scalar.Scalar52.asNat_lt u hub) haL) as
    ⟨t, ht, htL, htb⟩
  have hz' : z = scratch[k1.val]! := by
    rw [hz, Slice.getElem!_Nat_eq, getElem!_pos]
  have hzm : MontVal z (pre inputs k1.val) := hz' ▸ hscratch k1.val hk1'
  step with backend.serial.u64.scalar.Scalar52.montgomery_mul_spec a z hab hzm.2.2
    (Nat.mul_lt_mul'' (haL.trans backend.serial.u64.scalar.L_lt_montgomeryRadix)
      hzm.2.1) as ⟨w, hw, hwL, hwb⟩
  step with Scalar52.pack_spec w hwb (lt_two_pow_256_of_lt_L hwL) as ⟨y, hy⟩
  have hit1 : it1 = { iter := { start := 0#usize, «end» := k1 } } := by
    rcases it1 with ⟨⟨s, e⟩⟩
    simp_all
  rw [← hkk, pre_succ] at ha
  have hu' : (u.asNat : ZMod L) = inputs[k1.val]!.asNat * montgomeryRadix := by
    rw [hu, hx']
    exact hinputs1 k1.val hk1'
  refine ⟨y, t, k1, by rw [hback, hit1], hkk, by rw [plain_mul hu' ht, ← ha]; ring, htL, htb,
    by rw [hy, plain_mul hzm.1 hw, ← ha]; ring, hy ▸ hwL⟩

@[local step]
private theorem loop1_spec (inputs inputs1 : Slice Scalar) (scratch : Slice Scalar52)
    (acc : Scalar52) (n : Usize) (hn : n.val = inputs.length)
    (hlen : inputs1.length = inputs.length) (hslen : scratch.length = inputs.length)
    (hscratch : ∀ k < inputs.length, MontVal scratch[k]! (pre inputs k))
    (hinputs1 : ∀ k < inputs.length,
      (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * montgomeryRadix)
    (hacc : (acc.asNat : ZMod L) * pre inputs inputs.length = 1) (haccL : acc.asNat < L)
    (haccb : acc.LimbsLt 52) :
    invert_batch_internal.«x86_64-tables_loop1» { iter := { start := 0#usize, «end» := n } }
      inputs1 scratch acc
      ⦃ (r : Slice Scalar) =>
      r.length = inputs.length ∧
      ∀ j < inputs.length, (r[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ r[j]!.asNat < L ⦄ := by
  unfold invert_batch_internal.«x86_64-tables_loop1»
  apply loop.spec_decr_nat (measure := fun x => x.1.iter.end.val)
    (inv := fun x => x.1.iter.start = 0#usize ∧ x.1.iter.end.val ≤ inputs.length ∧
      x.2.1.length = inputs.length ∧
      (x.2.2.asNat : ZMod L) * pre inputs x.1.iter.end.val = 1 ∧ x.2.2.asNat < L ∧
      x.2.2.LimbsLt 52 ∧ (∀ j < x.1.iter.end.val, x.2.1[j]! = inputs1[j]!) ∧
      ∀ j < inputs.length, x.1.iter.end.val ≤ j →
        (x.2.1[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ x.2.1[j]!.asNat < L)
  · rintro ⟨⟨⟨start, k⟩⟩, ins, a⟩ ⟨hstart, hk, hinl, ha, haL, hab, hlow, hhigh⟩
    dsimp only at hstart
    subst start
    by_cases hpos : k > 0#usize
    · apply spec_mono (loop1_body_spec inputs inputs1 ins scratch a k hpos hk hscratch hinputs1
        hinl hslen ha haL hab hlow)
      rintro r ⟨y, t, k1, rfl, hkk, ht, htL, htb, hy, hyL⟩
      have hk1k : k1.val < k.val := hkk ▸ Nat.lt_succ_self _
      obtain ⟨hl1, hh1⟩ := Slice.forall_ge_pred_set
        (P := fun j x => (x.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ x.asNat < L) hkk
        (hinl ▸ lt_of_lt_of_le hk1k hk) hhigh ⟨hy, hyL⟩
      exact ⟨⟨rfl, Nat.le_of_lt (Nat.lt_of_lt_of_le hk1k hk),
        by rw [Slice.set_length, hinl], ht, htL,
        htb, fun j hj => (hl1 j hj).trans (hlow j (Nat.lt_trans hj hk1k)), hh1⟩, hk1k⟩
    · unfold invert_batch_internal.«x86_64-tables_loop1».body
      step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have hk0 : k.val = 0 := by scalar_tac
      rw [hk0] at hhigh
      exact ⟨hinl, fun j hj => hhigh j hj (Nat.zero_le j)⟩
  · exact ⟨rfl, by scalar_tac, hlen, hn ▸ hacc, haccL, haccb, fun j _ => rfl,
      fun j hj hkj => absurd hj (by scalar_tac)⟩

/-! ## The same, for the 29-bit limbs of the i686 targets -/

open backend.serial.u32.scalar (Scalar29)

/-- `v` is the Montgomery form `x * R` of `x`, reduced and with 29-bit limbs. -/
private def MontVal29 (v : Scalar29) (x : ZMod L) : Prop :=
  (v.asNat : ZMod L) = x * backend.serial.u32.scalar.montgomeryRadix ∧ v.asNat < L ∧ v.LimbsLt 29

/-- The Montgomery product of two Montgomery forms. -/
private theorem montVal29_mul {a b r : Scalar29} {x y : ZMod L} (ha : MontVal29 a x)
    (hb : (b.asNat : ZMod L) = y * backend.serial.u32.scalar.montgomeryRadix)
    (hr : r.asNat * backend.serial.u32.scalar.montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = x * y * backend.serial.u32.scalar.montgomeryRadix := by
  have hr' : (r.asNat : ZMod L) * backend.serial.u32.scalar.montgomeryRadix =
      a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  rw [hr', ha.1, hb]
  ring

/-- The Montgomery product of a plain value and a Montgomery form. -/
private theorem plain29_mul {a b r : Scalar29} {y : ZMod L}
    (hb : (b.asNat : ZMod L) = y * backend.serial.u32.scalar.montgomeryRadix)
    (hr : r.asNat * backend.serial.u32.scalar.montgomeryRadix % L = a.asNat * b.asNat % L) :
    (r.asNat : ZMod L) = a.asNat * y := by
  have hr' : (r.asNat : ZMod L) * backend.serial.u32.scalar.montgomeryRadix =
      a.asNat * b.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  apply mul_right_cancel₀ backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  rw [hr', hb]
  ring

/-! ## First loop: Montgomery forms of the inputs and of their prefix products -/

/-- One step of the first loop: store `acc` at `i`, replace input `i` by its Montgomery form `y`
and multiply `acc` by it. -/
private theorem loop0_body29_spec (inputs ins : Slice Scalar) (sc : Slice Scalar29) (a : Scalar29)
    (n i : Usize) (hlt : i < n) (hn : n.val = inputs.length) (hinl : ins.length = inputs.length)
    (hscl : sc.length = inputs.length) (ha : MontVal29 a (pre inputs i.val))
    (hx : ins[i.val]! = inputs[i.val]!) :
    invert_batch_internal.«i686-tables_loop0».body { start := i, «end» := n } ins sc a
      ⦃ r =>
      ∃ y a1 i1, r = .cont ({ start := i1, «end» := n }, ins.set i y, sc.set i a, a1) ∧
        i1.val = i.val + 1 ∧
        (y.asNat : ZMod L) = inputs[i.val]!.asNat * backend.serial.u32.scalar.montgomeryRadix ∧
        MontVal29 a1 (pre inputs (i.val + 1)) ⦄ := by
  unfold invert_batch_internal.«i686-tables_loop0».body
  have hil : i.val < ins.length := hinl ▸ hn ▸ hlt
  have hab := ha.2.2
  step with core.iter.range.IteratorRange.next_Usize_some_spec
    as ⟨o, it1, ho, hi1, he1⟩
  subst ho
  step as ⟨x, back, hx', hback⟩
  step as ⟨sc1, hsc1⟩
  have hx'' : x = inputs[i.val]! := by
    rw [hx', ← hx, Slice.getElem!_Nat_eq, getElem!_pos]
  step as ⟨u, hu, hub⟩
  step as ⟨t, ht, htb⟩
  have htL : t.asNat < L := ht ▸ Nat.mod_lt _ L_pos
  step with Scalar29.pack_spec t htb (lt_two_pow_256_of_lt_L htL) as ⟨y, hy⟩
  step with backend.serial.u32.scalar.Scalar29.montgomery_mul_spec a t hab htb
    (Nat.mul_lt_mul'' (ha.2.1.trans backend.serial.u32.scalar.L_lt_montgomeryRadix) htL) as
    ⟨a1, ha1, ha1L, ha1b⟩
  have hit1 : it1 = { start := it1.start, «end» := n } := by
    cases it1
    simp_all
  have ht' : (t.asNat : ZMod L) =
      inputs[i.val]!.asNat * backend.serial.u32.scalar.montgomeryRadix := by
    rw [← hx'', ← hu]
    exact_mod_cast (ZMod.natCast_eq_natCast_of_mod_eq ht.symm).symm
  refine ⟨y, a1, it1.start, by rw [hback, hsc1, hit1], hi1,
    by rw [← ht']; exact congrArg Nat.cast hy,
    ⟨?_, ha1L, ha1b⟩⟩
  rw [pre_succ]
  exact montVal29_mul ha ht' ha1

@[local step]
private theorem loop029_spec (inputs : Slice Scalar) (scratch : Slice Scalar29) (acc : Scalar29)
    (n : Usize) (hn : n.val = inputs.length) (hlen : scratch.length = inputs.length)
    (hacc : MontVal29 acc 1) :
    invert_batch_internal.«i686-tables_loop0» { start := 0#usize, «end» := n } inputs scratch acc
      ⦃ (inputs1 : Slice Scalar) (scratch1 : Slice Scalar29) (acc1 : Scalar29) =>
      inputs1.length = inputs.length ∧ scratch1.length = inputs.length ∧
      MontVal29 acc1 (pre inputs inputs.length) ∧
      (∀ k < inputs.length, MontVal29 scratch1[k]! (pre inputs k)) ∧
      ∀ k < inputs.length,
        (inputs1[k]!.asNat : ZMod L) =
            inputs[k]!.asNat * backend.serial.u32.scalar.montgomeryRadix ⦄ := by
  unfold invert_batch_internal.«i686-tables_loop0»
  apply loop.spec_decr_nat (measure := fun x => n.val - x.1.start.val)
    (inv := fun x => x.1.end = n ∧ x.1.start.val ≤ n.val ∧
      x.2.1.length = inputs.length ∧ x.2.2.1.length = inputs.length ∧
      MontVal29 x.2.2.2 (pre inputs x.1.start.val) ∧
      (∀ k < x.1.start.val, MontVal29 x.2.2.1[k]! (pre inputs k)) ∧
      (∀ k < x.1.start.val,
        (x.2.1[k]!.asNat : ZMod L) = inputs[k]!.asNat * backend.serial.u32.scalar.montgomeryRadix) ∧
      ∀ k < inputs.length, x.1.start.val ≤ k → x.2.1[k]! = inputs[k]!)
  · rintro ⟨⟨i, e⟩, ins, sc, a⟩ ⟨he, hi, hinl, hscl, ha, hsc, hlow, hhigh⟩
    dsimp only at he
    subst e
    by_cases hlt : i < n
    · have hil : i.val < inputs.length := hn ▸ hlt
      apply spec_mono (loop0_body29_spec inputs ins sc a n i hlt hn hinl hscl ha
        (hhigh i.val hil le_rfl))
      rintro r ⟨y, a1, i1, rfl, hi1, hy, ha1⟩
      refine ⟨⟨rfl, hi1 ▸ hlt, by rw [Slice.set_length, hinl], by rw [Slice.set_length, hscl],
        hi1 ▸ ha1,
        hi1 ▸ Slice.forall_lt_succ_set (P := fun k x => MontVal29 x (pre inputs k)) hsc ha
          (hscl ▸ hil),
        hi1 ▸ Slice.forall_lt_succ_set
          (P := fun k x => (x.asNat : ZMod L) =
              inputs[k]!.asNat * backend.serial.u32.scalar.montgomeryRadix) hlow hy
          (hinl ▸ hil), fun k hk hik => ?_⟩, ?_⟩
      · rw [hi1] at hik
        rw [Slice.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_lt hik)]
        exact hhigh k hk (Nat.le_of_succ_le hik)
      · dsimp only
        rw [hi1]
        exact Nat.sub_lt_sub_left hlt (Nat.lt_succ_self _)
    · unfold invert_batch_internal.«i686-tables_loop0».body
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit1⟩
      subst ho
      simp only [WP.spec_ok]
      have hin : i.val = inputs.length := hn ▸ Nat.le_antisymm hi (Nat.le_of_not_lt hlt)
      rw [hin] at ha hsc hlow
      exact ⟨hinl, hscl, ha, hsc, hlow⟩
  · refine ⟨rfl, by simp, rfl, hlen, by simpa [pre] using hacc, fun k hk => absurd hk (by simp),
      fun k hk => absurd hk (by simp), fun k _ _ => rfl⟩

/-! ## Second loop: the inverses, from the back -/

/-- One step of the second loop: input `k - 1` is replaced by its inverse and `acc` becomes the
inverse of the product before `k - 1`. -/
private theorem loop1_body29_spec (inputs inputs1 ins : Slice Scalar) (scratch : Slice Scalar29)
    (a : Scalar29) (k : Usize) (hpos : k > 0#usize) (hk : k.val ≤ inputs.length)
    (hscratch : ∀ k < inputs.length, MontVal29 scratch[k]! (pre inputs k))
    (hinputs1 : ∀ k < inputs.length,
      (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * backend.serial.u32.scalar.montgomeryRadix)
    (hinl : ins.length = inputs.length) (hslen : scratch.length = inputs.length)
    (ha : (a.asNat : ZMod L) * pre inputs k.val = 1) (haL : a.asNat < L)
    (hab : a.LimbsLt 29) (hlow : ∀ j < k.val, ins[j]! = inputs1[j]!) :
    invert_batch_internal.«i686-tables_loop1».body scratch
      { iter := { start := 0#usize, «end» := k } } ins a ⦃ r =>
      ∃ y t k1, r = .cont ({ iter := { start := 0#usize, «end» := k1 } }, ins.set k1 y, t) ∧
        k1.val + 1 = k.val ∧
        (t.asNat : ZMod L) * pre inputs k1.val = 1 ∧ t.asNat < L ∧
        t.LimbsLt 29 ∧
        (y.asNat : ZMod L) * inputs[k1.val]!.asNat = 1 ∧ y.asNat < L ⦄ := by
  unfold invert_batch_internal.«i686-tables_loop1».body
  step with core.iter.adapters.rev.Rev.next_Usize_some_spec
    as ⟨o, it1, k1, ho, hk1, hstart, hend⟩
  subst ho
  have hkk : k1.val + 1 = k.val := by scalar_tac
  have hk1' : k1.val < inputs.length := lt_of_lt_of_le (hkk ▸ Nat.lt_succ_self k1.val) hk
  have hk1i : k1.val < ins.length := hinl ▸ hk1'
  have hk1s : k1.val < scratch.length := hslen ▸ hk1'
  step as ⟨x, back, hx, hback⟩
  step as ⟨z, hz⟩
  have hx' : x = inputs1[k1.val]! := by
    rw [hx, ← hlow k1.val (hkk ▸ Nat.lt_succ_self _), Slice.getElem!_Nat_eq, getElem!_pos]
  step as ⟨u, hu, hub⟩
  step with backend.serial.u32.scalar.Scalar29.montgomery_mul_spec a u hab hub
    (by
      rw [Nat.mul_comm]
      exact Nat.mul_lt_mul'' (backend.serial.u32.scalar.Scalar29.asNat_lt u hub) haL) as
    ⟨t, ht, htL, htb⟩
  have hz' : z = scratch[k1.val]! := by
    rw [hz, Slice.getElem!_Nat_eq, getElem!_pos]
  have hzm : MontVal29 z (pre inputs k1.val) := hz' ▸ hscratch k1.val hk1'
  step with backend.serial.u32.scalar.Scalar29.montgomery_mul_spec a z hab hzm.2.2
    (Nat.mul_lt_mul'' (haL.trans backend.serial.u32.scalar.L_lt_montgomeryRadix)
      hzm.2.1) as ⟨w, hw, hwL, hwb⟩
  step with Scalar29.pack_spec w hwb (lt_two_pow_256_of_lt_L hwL) as ⟨y, hy⟩
  have hit1 : it1 = { iter := { start := 0#usize, «end» := k1 } } := by
    rcases it1 with ⟨⟨s, e⟩⟩
    simp_all
  rw [← hkk, pre_succ] at ha
  have hu' : (u.asNat : ZMod L) =
      inputs[k1.val]!.asNat * backend.serial.u32.scalar.montgomeryRadix := by
    rw [hu, hx']
    exact hinputs1 k1.val hk1'
  refine ⟨y, t, k1, by rw [hback, hit1], hkk, by rw [plain29_mul hu' ht, ← ha]; ring, htL, htb,
    by rw [hy, plain29_mul hzm.1 hw, ← ha]; ring, hy ▸ hwL⟩

@[local step]
private theorem loop129_spec (inputs inputs1 : Slice Scalar) (scratch : Slice Scalar29)
    (acc : Scalar29) (n : Usize) (hn : n.val = inputs.length)
    (hlen : inputs1.length = inputs.length) (hslen : scratch.length = inputs.length)
    (hscratch : ∀ k < inputs.length, MontVal29 scratch[k]! (pre inputs k))
    (hinputs1 : ∀ k < inputs.length,
      (inputs1[k]!.asNat : ZMod L) = inputs[k]!.asNat * backend.serial.u32.scalar.montgomeryRadix)
    (hacc : (acc.asNat : ZMod L) * pre inputs inputs.length = 1) (haccL : acc.asNat < L)
    (haccb : acc.LimbsLt 29) :
    invert_batch_internal.«i686-tables_loop1» { iter := { start := 0#usize, «end» := n } }
      inputs1 scratch acc
      ⦃ (r : Slice Scalar) =>
      r.length = inputs.length ∧
      ∀ j < inputs.length, (r[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ r[j]!.asNat < L ⦄ := by
  unfold invert_batch_internal.«i686-tables_loop1»
  apply loop.spec_decr_nat (measure := fun x => x.1.iter.end.val)
    (inv := fun x => x.1.iter.start = 0#usize ∧ x.1.iter.end.val ≤ inputs.length ∧
      x.2.1.length = inputs.length ∧
      (x.2.2.asNat : ZMod L) * pre inputs x.1.iter.end.val = 1 ∧ x.2.2.asNat < L ∧
      x.2.2.LimbsLt 29 ∧ (∀ j < x.1.iter.end.val, x.2.1[j]! = inputs1[j]!) ∧
      ∀ j < inputs.length, x.1.iter.end.val ≤ j →
        (x.2.1[j]!.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ x.2.1[j]!.asNat < L)
  · rintro ⟨⟨⟨start, k⟩⟩, ins, a⟩ ⟨hstart, hk, hinl, ha, haL, hab, hlow, hhigh⟩
    dsimp only at hstart
    subst start
    by_cases hpos : k > 0#usize
    · apply spec_mono (loop1_body29_spec inputs inputs1 ins scratch a k hpos hk hscratch hinputs1
        hinl hslen ha haL hab hlow)
      rintro r ⟨y, t, k1, rfl, hkk, ht, htL, htb, hy, hyL⟩
      have hk1k : k1.val < k.val := hkk ▸ Nat.lt_succ_self _
      obtain ⟨hl1, hh1⟩ := Slice.forall_ge_pred_set
        (P := fun j x => (x.asNat : ZMod L) * inputs[j]!.asNat = 1 ∧ x.asNat < L) hkk
        (hinl ▸ lt_of_lt_of_le hk1k hk) hhigh ⟨hy, hyL⟩
      exact ⟨⟨rfl, Nat.le_of_lt (Nat.lt_of_lt_of_le hk1k hk),
        by rw [Slice.set_length, hinl], ht, htL,
        htb, fun j hj => (hl1 j hj).trans (hlow j (Nat.lt_trans hj hk1k)), hh1⟩, hk1k⟩
    · unfold invert_batch_internal.«i686-tables_loop1».body
      step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      simp only [WP.spec_ok]
      have hk0 : k.val = 0 := by scalar_tac
      rw [hk0] at hhigh
      exact ⟨hinl, fun j hj => hhigh j hj (Nat.zero_le j)⟩
  · exact ⟨rfl, by scalar_tac, hlen, hn ▸ hacc, haccL, haccb, fun j _ => rfl,
      fun j hj hkj => absurd hj (by scalar_tac)⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«x86_64-tables_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_internal.«x86_64-tables»
  have hR := montgomeryRadix_natCast_ne_zero
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  have haccm : MontVal acc 1 := by
    refine ⟨?_, hacc ▸ Nat.mod_lt _ L_pos, haccb⟩
    rw [one_mul, hacc, hone, ONE_spec, one_mul]
    exact ZMod.natCast_mod _ _
  step with loop0_spec inputs scratch acc inputs.len (by simp) hlen haccm as
    ⟨inputs1, scratch1, acc1, hin1l, hsc1l, hacc1, hsc1, hin1⟩
  step with Scalar52.pack_spec acc1 hacc1.2.2 (lt_two_pow_256_of_lt_L hacc1.2.1) as ⟨s1, hs1⟩
  have hacc1ne : acc1.asNat % L ≠ 0 := fun h =>
    mul_ne_zero (pre_ne_zero inputs hinputs) hR
      (hacc1.1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
  step with core.cmp.PartialEq.ne.trait_default.spec Insts.CoreCmpPartialEqScalar s1 ZERO
    (Insts.CoreCmpPartialEqScalar.eq_spec s1 ZERO) as ⟨b, hb⟩
  have hbt : b = true := hb.mpr fun h => hacc1ne (by
    rw [Nat.mod_eq_of_lt hacc1.2.1, ← hs1, h]
    exact ZERO_spec)
  step
  step with Scalar52.montgomery_invert_spec acc1 hacc1.2.2 hacc1.2.1 as
    ⟨s2, hs2, hs20, hs2L, hs2b⟩
  step as ⟨acc2, hacc2, hacc2L, hacc2b⟩
  step with Scalar52.pack_spec acc2 hacc2b (lt_two_pow_256_of_lt_L hacc2L) as ⟨ret, hret⟩
  have hacc2' : (acc2.asNat : ZMod L) * pre inputs inputs.length = 1 := by
    have h2 : (s2.asNat : ZMod L) * acc1.asNat = montgomeryRadix ^ 2 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (hs2 hacc1ne)
    have h3 : (acc2.asNat : ZMod L) * montgomeryRadix = s2.asNat := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hacc2
    apply mul_right_cancel₀ (pow_ne_zero 2 hR)
    linear_combination (pre inputs inputs.length * montgomeryRadix) * h3 -
      (s2.asNat : ZMod L) * hacc1.1 + h2
  step as ⟨iter, hiter⟩
  have hiter' : iter = { iter := { start := 0#usize, «end» := inputs.len } } := by
    cases iter
    dsimp only at hiter
    congr 1
    rw [hiter]
    congr 1
    scalar_tac
  subst iter
  step with loop1_spec inputs inputs1 scratch1 acc2 inputs.len (by simp) hin1l hsc1l hsc1 hin1
    hacc2' hacc2L hacc2b as ⟨r, hrl, hr⟩
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_const_spec
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize (Array.repeat 5#usize 0#u64)
    backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize.zeroize_spec
  unfold pre at hacc2'
  refine ⟨hrl, fun i hi => ⟨mod_L_eq_one ?_, (hr i hi).2⟩, mod_L_eq_one ?_, hret ▸ hacc2L⟩
  · push_cast
    exact (hr i hi).1
  · rw [hret]
    push_cast
    exact hacc2'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«x86_64-no-tables_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u64.scalar.Scalar52) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«x86_64-no-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u64.scalar.Scalar52) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_internal.«x86_64-tables_spec» inputs scratch hlen hinputs

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«i686-tables_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u32.scalar.Scalar29) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«i686-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u32.scalar.Scalar29) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ := by
  unfold invert_batch_internal.«i686-tables»
  have hR := backend.serial.u32.scalar.montgomeryRadix_natCast_ne_zero
  step as ⟨one, hone, honeb⟩
  step as ⟨acc, hacc, haccb⟩
  have haccm : MontVal29 acc 1 := by
    refine ⟨?_, hacc ▸ Nat.mod_lt _ L_pos, haccb⟩
    rw [one_mul, hacc, hone, ONE_spec, one_mul]
    exact ZMod.natCast_mod _ _
  step with loop029_spec inputs scratch acc inputs.len (by simp) hlen haccm as
    ⟨inputs1, scratch1, acc1, hin1l, hsc1l, hacc1, hsc1, hin1⟩
  step with Scalar29.pack_spec acc1 hacc1.2.2 (lt_two_pow_256_of_lt_L hacc1.2.1) as ⟨s1, hs1⟩
  have hacc1ne : acc1.asNat % L ≠ 0 := fun h =>
    mul_ne_zero (pre_ne_zero inputs hinputs) hR
      (hacc1.1 ▸ ZMod.natCast_eq_zero_iff_mod.mpr h)
  step with core.cmp.PartialEq.ne.trait_default.spec Insts.CoreCmpPartialEqScalar s1 ZERO
    (Insts.CoreCmpPartialEqScalar.eq_spec s1 ZERO) as ⟨b, hb⟩
  have hbt : b = true := hb.mpr fun h => hacc1ne (by
    rw [Nat.mod_eq_of_lt hacc1.2.1, ← hs1, h]
    exact ZERO_spec)
  step
  step with Scalar29.montgomery_invert_spec acc1 hacc1.2.2 hacc1.2.1 as
    ⟨s2, hs2, hs20, hs2L, hs2b⟩
  step as ⟨acc2, hacc2, hacc2L, hacc2b⟩
  step with Scalar29.pack_spec acc2 hacc2b (lt_two_pow_256_of_lt_L hacc2L) as ⟨ret, hret⟩
  have hacc2' : (acc2.asNat : ZMod L) * pre inputs inputs.length = 1 := by
    have h2 : (s2.asNat : ZMod L) * acc1.asNat = backend.serial.u32.scalar.montgomeryRadix ^ 2 := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (hs2 hacc1ne)
    have h3 : (acc2.asNat : ZMod L) * backend.serial.u32.scalar.montgomeryRadix = s2.asNat := by
      exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hacc2
    apply mul_right_cancel₀ (pow_ne_zero 2 hR)
    linear_combination (pre inputs inputs.length * backend.serial.u32.scalar.montgomeryRadix) * h3 -
      (s2.asNat : ZMod L) * hacc1.1 + h2
  step as ⟨iter, hiter⟩
  have hiter' : iter = { iter := { start := 0#usize, «end» := inputs.len } } := by
    cases iter
    dsimp only at hiter
    congr 1
    rw [hiter]
    congr 1
    scalar_tac
  subst iter
  step with loop129_spec inputs inputs1 scratch1 acc2 inputs.len (by simp) hin1l hsc1l hsc1 hin1
    hacc2' hacc2L hacc2b as ⟨r, hrl, hr⟩
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with core.slice.iter.IterMut.Insts.ZeroizeZeroize.zeroize_const_spec
    backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize (Array.repeat 9#usize 0#u32)
    backend.serial.u32.scalar.Scalar29.Insts.ZeroizeZeroize.zeroize_spec
  unfold pre at hacc2'
  refine ⟨hrl, fun i hi => ⟨mod_L_eq_one ?_, (hr i hi).2⟩, mod_L_eq_one ?_, hret ▸ hacc2L⟩
  · push_cast
    exact (hr i hi).1
  · rw [hret]
    push_cast
    exact hacc2'

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_batch_internal.«i686-no-tables_spec» (inputs : Slice Scalar)
    (scratch : Slice backend.serial.u32.scalar.Scalar29) (hlen : scratch.length = inputs.length)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_internal.«i686-no-tables» inputs scratch
      ⦃ (ret : Scalar) (r : Slice Scalar)
      (_scratch : Slice backend.serial.u32.scalar.Scalar29) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄ :=
  invert_batch_internal.«i686-tables_spec» inputs scratch hlen hinputs

end Curve25519Dalek.scalar.Scalar
