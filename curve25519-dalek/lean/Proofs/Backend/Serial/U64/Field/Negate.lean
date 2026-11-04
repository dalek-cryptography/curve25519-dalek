/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alok Singh
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Backend.Serial.U64.Field.Reduce
import Proofs.Backend.Serial.U64.Field.SixteenP
import Proofs.Helpers.AsNat
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- The closure of `negate`: limb `i` of `16 p - self`. -/
@[local step]
private theorem negate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut_spec
    (c : negate.closure) (i : Usize) (hi : i.val < 5) (hc : c[i.val]!.val < 2 ^ 54) :
    negate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut c i
      ⦃ (r : U64) (c' : negate.closure) =>
        r.val + c[i.val]!.val = SIXTEEN_P[i.val]!.val ∧ c' = c ⦄ := by
  have h16 := SIXTEEN_P_spec.2.1 i.val hi
  simp (disch := scalar_tac) only [Array.getElem!_Nat_eq, getElem!_pos] at hc h16 ⊢
  unfold negate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step*

@[step]
theorem negate_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    negate self ⦃ (r : FieldElement51) =>
      (r.asNat + self.asNat) % p = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold negate
  apply spec_bind (core.array.from_fn_spec 5#usize _ self (fun _ c => c = self)
    (fun i x => x.val + self[i]!.val = SIXTEEN_P[i]!.val) rfl fun i c hi hc => ?_)
  · rintro a ha
    have hlimbs : ∀ i : ℕ, i < 5 → a[i]!.val + self[i]!.val = SIXTEEN_P[i]!.val := fun i hi => by
      rw [Array.getElem!_Nat_eq, getElem!_pos a.val i (by simpa using hi)]
      exact ha i (by simpa using hi)
    step as ⟨r, hr, hr_lt, hr_2p⟩
    refine ⟨?_, hr_lt⟩
    have hsum : FieldElement51.asNat a + self.asNat = FieldElement51.asNat SIXTEEN_P :=
      by simpa only [field.FieldElement51.asNat_def] using
        Array.asNat_add_eq 51 a self SIXTEEN_P hlimbs
    rw [Nat.add_mod, hr, ← Nat.add_mod, hsum, SIXTEEN_P_spec.1, Nat.mul_mod_left]
  · subst hc
    exact negate.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut_spec c i hi
      (hself i.val hi)

end Curve25519Dalek.backend.serial.u64.field.FieldElement51
