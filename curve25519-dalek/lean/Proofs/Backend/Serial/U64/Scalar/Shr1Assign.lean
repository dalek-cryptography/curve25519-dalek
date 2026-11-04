/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Scalar.Index
import Proofs.Backend.Serial.U64.Scalar.IndexMut
import Proofs.Helpers.AsNat
import Proofs.Helpers.Iterator
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

/-- One limb of the shift: the halved limb with the incoming carry on top. -/
private theorem shr1_limb {x c : ℕ} (hx : x < 2 ^ 52) (hc : c < 2) :
    2 * (x >>> 1 ||| c <<< 51) + x % 2 = x + 2 ^ 52 * c ∧ (x >>> 1 ||| c <<< 51) < 2 ^ 52 := by
  have h1 : x >>> 1 < 2 ^ 51 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h1, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  constructor <;> omega

/-- The value invariant of the shift loop after one more limb. -/
private theorem shr1_sum_step {S S' P limb v c c' Self T : ℕ} (hset : S' + P * limb = S + P * v)
    (hIH : 2 * S + P * 2 ^ 52 * c = Self + (T + P * limb)) (hv : 2 * v + c' = limb + 2 ^ 52 * c) :
    2 * S' + P * c' = Self + T := by
  zify at *
  linear_combination 2 * hset + hIH + (P : ℤ) * hv

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

/-- The loop of `shr1_assign` shifts the limbs right by one bit, from the top limb down,
moving each limb's low bit into the next limb below. -/
@[local step]
private theorem shr1_assign_loop_spec (self : Scalar52)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (hiter : iter.iter = { start := 0#usize, «end» := 5#usize })
    (hself : self.LimbsLt 52) :
    shr1_assign_loop iter self 0#u64 ⦃ (c : U64) (r : Scalar52) =>
      2 * r.asNat + c.val = self.asNat ∧ c.val < 2 ∧ r.LimbsLt 52 ⦄ := by
  unfold shr1_assign_loop
  apply loop.spec_decr_nat (measure := fun (it, _, _) => it.iter.end.val)
    (inv := fun (it, s, carry) => it.iter.start = 0#usize ∧ it.iter.end.val ≤ 5 ∧
      carry.val < 2 ∧ s.LimbsLt 52 ∧
      (∀ i < it.iter.end.val, s[i]! = self[i]!) ∧
      2 * s.asNat + 2 ^ (52 * it.iter.end.val) * carry.val =
        self.asNat + ∑ j ∈ Finset.range it.iter.end.val, 2 ^ (52 * j) * self[j]!.val)
  · rintro ⟨it, s, carry⟩ ⟨hstart, hend, hcarry, hs, hlow, hsum⟩
    unfold shr1_assign_loop.body
    by_cases hlt : 0 < it.iter.end.val
    · step with core.iter.adapters.rev.Rev.next_Usize_some_spec
        as ⟨o, it1, i, ho, hi, hstart1, hend1⟩
      subst ho
      have hik : i.val < it.iter.end.val := by scalar_tac
      have hi5 : i.val < 5 := by scalar_tac
      have hend1' : it1.iter.end.val = i.val := by rw [hend1]
      step as ⟨limb, hlimb⟩
      step as ⟨c', hc'⟩
      step as ⟨hi_part, hhi_part, _⟩
      step as ⟨lo_part, hlo_part, _⟩
      step as ⟨_, back, _, hback⟩
      step as ⟨v, hv⟩
      have hlimb_lt : limb.val < 2 ^ 52 := hlimb ▸ hs _ (by scalar_tac)
      have hlo' : lo_part.val = carry.val <<< 51 := by
        rw [hlo_part, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; scalar_tac)]
      have hv' : v.val = limb.val >>> 1 ||| carry.val <<< 51 := by
        rw [hv, UScalar.val_or, hhi_part, hlo']
      have hc'' : c'.val = limb.val % 2 := by
        rw [hc', UScalar.val_and, show (1#u64).val = 1 from rfl, Nat.and_one_is_mod]
      obtain ⟨hstep, hv_lt⟩ := shr1_limb hlimb_lt hcarry
      rw [← hv', ← hc''] at hstep
      rw [← hv'] at hv_lt
      have hsi : s[i.val]! = self[i.val]! := hlow _ hik
      refine ⟨hstart1.trans hstart, hend1' ▸ hi5.le, hc'' ▸ Nat.mod_lt _ (by norm_num),
        fun j hj => ?_, fun j hj => ?_, ?_, hend1' ▸ hik⟩
      · rw [hback]
        by_cases hij : i.val = j
        · rw [Array.getElem!_Nat_set_eq _ _ _ _ ⟨hij, by simpa [← hij] using hi5⟩]
          exact hv_lt
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ hij]
          exact hs j hj
      · rw [hend1'] at hj
        rw [hback, Array.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_lt hj).symm]
        exact hlow j (hj.trans hik)
      · rw [hback, hend1']
        rw [← hi, Nat.mul_succ, pow_add, Finset.sum_range_succ, ← hsi, ← hlimb] at hsum
        have hset := Array.asNat_set_add 52 s i v hi5
        rw [← hlimb] at hset
        exact shr1_sum_step (by simpa only [scalar.Scalar52.asNat_def] using hset) hsum hstep
    · step with core.iter.adapters.rev.Rev.next_Usize_none_spec as ⟨o, it1, ho⟩
      subst ho
      have he : it.iter.end.val = 0 := Nat.eq_zero_of_not_pos hlt
      rw [he, Nat.mul_zero, pow_zero, Nat.one_mul, Finset.sum_range_zero, Nat.add_zero] at hsum
      dsimp only
      simp only [WP.spec_ok]
      exact ⟨hsum, hcarry, hs⟩
  · dsimp only
    rw [hiter]
    refine ⟨rfl, by simp, by simp, hself, fun _ _ => rfl, ?_⟩
    rw [show (0#u64).val = 0 from rfl, Nat.mul_zero, Nat.add_zero, two_mul]
    simp only [Scalar52.asNat_def, Array.asNat_eq_sum]

@[step]
theorem shr1_assign_spec (self : Scalar52) (hself : self.LimbsLt 52) :
    shr1_assign self ⦃ (c : U64) (r : Scalar52) =>
      2 * r.asNat + c.val = self.asNat ∧ c.val < 2 ∧ r.LimbsLt 52 ⦄ := by
  unfold shr1_assign
  step*

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
