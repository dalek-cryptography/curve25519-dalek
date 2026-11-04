/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
public import Proofs.Field.Pow22501
public import Curve25519.Basic
public section

/-! # `FieldElement::pow_p58`

`x ^ ((p - 5) / 8)` from `pow22501`, proved once over a `Backend` in `ZMod p`; the specs of
both backends follow. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `FieldElement::pow_p58` over a backend. -/
@[expose] def powP58Body (x : B.F) : Result B.F := do
  let (t19, _) ← B.pow22501 x
  let t20 ← B.pow2k t19 2#u32
  B.mul x t20

private theorem two_pow_sub_one_mul_four_add_one (a c : ℕ) (hc : a + 2 = c) :
    (2 ^ a - 1) * 2 ^ 2 + 1 = 2 ^ c - 3 := by
  subst hc
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hc : 3 ≤ 2 ^ (a + 2) := by rw [pow_add]; omega
  zify [ha, hc]
  ring

/-- `powP58Body` computes `x ^ (2^252 - 3)`. -/
theorem powP58Body_spec (h22501 : B.Pow22501Spec) (hmul : B.MulSpec) (hp2k : B.Pow2kSpec)
    (x : B.F) (hx : B.SqIn x) :
    B.powP58Body x ⦃ r => B.toField r = B.toField x ^ (2 ^ 252 - 3) ∧ B.Red r ⦄ := by
  unfold powP58Body
  step with h22501 x hx as ⟨t19, t3, h19, _, h19', _⟩
  generalize hn : 2 ^ 250 - 1 = n at h19
  step with hp2k t19 2#u32 (by decide) (B.red_sqIn h19') as ⟨t20, h20, h20'⟩
  step with hmul x t20 (B.sqIn_mulIn hx) (B.red_mulIn h20') as ⟨r, hr, hr'⟩
  refine ⟨?_, hr'⟩
  subst hn
  rw [hr, h20, h19, ← pow_mul, ← pow_succ', two_pow_sub_one_mul_four_add_one 250 252 rfl]

end Curve25519Dalek.Backend

namespace Curve25519Dalek.field.FieldElement51

theorem pow_p58_eq : pow_p58 = Backend.powP58Body Backend.U64 := rfl

@[step]
theorem pow_p58_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    pow_p58 self ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat ^ (2 ^ 252 - 3) % p ∧ r.LimbsLt 52 ⦄ := by
  rw [pow_p58_eq]
  exact spec_mono (Backend.powP58Body_spec Backend.U64 Backend.U64.pow22501_spec
    Backend.U64.mul_spec Backend.U64.pow2k_spec self hself)
    fun _ ⟨h, hb⟩ => ⟨Backend.mod_eq_of_toField_eq_pow h, hb⟩

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

theorem pow_p58_eq : pow_p58 = Backend.powP58Body Backend.U32 := rfl

@[step]
theorem pow_p58_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    pow_p58 self ⦃ (r : FieldElement2625) =>
      r.asNat % p = self.asNat ^ (2 ^ 252 - 3) % p ∧ r.LimbsLt 26 ⦄ := by
  rw [pow_p58_eq]
  exact spec_mono (Backend.powP58Body_spec Backend.U32 Backend.U32.pow22501_spec
    Backend.U32.mul_spec Backend.U32.pow2k_spec self hself)
    fun _ ⟨h, hb⟩ => ⟨Backend.mod_eq_of_toField_eq_pow h, hb⟩

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

theorem U64.powP58_spec : U64.PowP58Spec :=
  powP58Body_spec U64 U64.pow22501_spec U64.mul_spec U64.pow2k_spec

theorem U32.powP58_spec : U32.PowP58Spec :=
  powP58Body_spec U32 U32.pow22501_spec U32.mul_spec U32.pow2k_spec

end Curve25519Dalek.Backend
