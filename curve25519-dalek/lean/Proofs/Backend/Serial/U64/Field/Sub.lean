/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
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

namespace Curve25519Dalek.backend.serial.u64.field
namespace SubShared0FieldElement51SharedAFieldElement51FieldElement51

/-- The closure of `sub`: limb `i` of `self + 16 p - rhs`. -/
@[local step]
private theorem sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut_spec
    (self rhs : FieldElement51) (i : Usize) (hi : i.val < 5)
    (hself : self[i.val]!.val < 2 ^ 54) (hrhs : rhs[i.val]!.val < 2 ^ 54) :
    sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut (self, rhs) i
      ⦃ (r : U64) (c' : sub.closure) =>
        r.val + rhs[i.val]!.val = self[i.val]!.val + SIXTEEN_P[i.val]!.val ∧
          c' = (self, rhs) ⦄ := by
  have h16 := SIXTEEN_P_spec.2.1 i.val hi
  have h16' := SIXTEEN_P_spec.2.2 i.val hi
  simp (disch := scalar_tac) only [Array.getElem!_Nat_eq, getElem!_pos] at hself hrhs h16 h16' ⊢
  unfold sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step*

end SubShared0FieldElement51SharedAFieldElement51FieldElement51
end Curve25519Dalek.backend.serial.u64.field

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithSubSharedAFieldElement51FieldElement51

open backend.serial.u64.field (SIXTEEN_P SIXTEEN_P_spec)
open backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51

@[step]
theorem sub_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    sub self rhs ⦃ (r : FieldElement51) =>
      (r.asNat + rhs.asNat) % p = self.asNat % p ∧ r.LimbsLt 52 ⦄ := by
  unfold sub
  apply spec_bind (core.array.from_fn_spec 5#usize _ (self, rhs) (fun _ c => c = (self, rhs))
    (fun i x => x.val + rhs[i]!.val = self[i]!.val + SIXTEEN_P[i]!.val) rfl
    fun i c hi hc => ?_)
  · rintro a ha
    have hlimbs : ∀ i : ℕ, i < 5 → a[i]!.val + rhs[i]!.val = self[i]!.val + SIXTEEN_P[i]!.val :=
      fun i hi => by
        rw [Array.getElem!_Nat_eq, getElem!_pos a.val i (by simpa using hi)]
        exact ha i (by simpa using hi)
    step as ⟨r, hr, hr_lt, hr_2p⟩
    refine ⟨?_, hr_lt⟩
    have hsum : FieldElement51.asNat a + rhs.asNat = self.asNat + FieldElement51.asNat SIXTEEN_P :=
      by simpa only [backend.serial.u64.field.FieldElement51.asNat_def] using
        Array.asNat_add_eq_add 51 a rhs self SIXTEEN_P hlimbs
    rw [Nat.add_mod, hr, ← Nat.add_mod, hsum, SIXTEEN_P_spec.1, Nat.add_mul_mod_self_right]
  · subst hc
    exact sub.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut_spec
      self rhs i hi (hself i.val hi) (hrhs i.val hi)

end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51
