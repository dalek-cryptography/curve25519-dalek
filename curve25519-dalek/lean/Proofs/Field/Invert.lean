/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Defs.FieldElement51
import Curve25519.Prime
import Mathlib.FieldTheory.Finite.Basic
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Pow2k
import Proofs.Field.Pow22501
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Pow2k
public import Curve25519.Basic
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
import Proofs.Helpers.ToField
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.field.FieldElement51

/-- The exponent computed by `invert`, plus one, is `p - 1`. -/
private theorem invert_exponent : (2 ^ 250 - 1) * 2 ^ 5 + 11 + 1 = p - 1 := by
  have h1 : 1 ≤ 2 ^ 250 := Nat.one_le_two_pow
  have h2 : 2 ^ 255 = 2 ^ 250 * 2 ^ 5 := by rw [← pow_add]
  have hp := p_add_nineteen
  generalize 2 ^ 250 = A at *
  generalize 2 ^ 255 = B at *
  omega

@[step]
theorem invert_spec (self : FieldElement51) (hself : self.LimbsLt 54) :
    invert self ⦃ (r : FieldElement51) =>
      (self.asNat % p ≠ 0 → r.asNat * self.asNat % p = 1) ∧
      (self.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 52 ⦄ := by
  unfold invert
  step as ⟨t19, t3, h19, h3, h19b, h3b⟩
  generalize hn : 2 ^ 250 - 1 = n at h19
  step as ⟨t20, h20, h20b⟩
  step as ⟨r, hr, hrb⟩
  subst hn
  set x := self.asNat
  have h : r.asNat ≡ x ^ ((2 ^ 250 - 1) * 2 ^ 5 + 11) [MOD p] := by
    rw [pow_add, pow_mul]
    exact Nat.ModEq.trans hr (Nat.ModEq.mul (Nat.ModEq.trans h20 (Nat.ModEq.pow _ h19)) h3)
  refine ⟨fun hx => ?_, fun hx => ?_, hrb⟩
  · have hx' : (x : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    have hrz : (r.asNat : ZMod p) = (x : ZMod p) ^ ((2 ^ 250 - 1) * 2 ^ 5 + 11) := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    have hone : ((r.asNat * x : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, hrz, ← pow_succ, invert_exponent, ZMod.pow_card_sub_one_eq_one hx',
        Nat.cast_one]
    rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp hone, Nat.mod_eq_of_lt p_prime.one_lt]
  · -- Hide the exponent behind a variable
    obtain ⟨N, hN⟩ : ∃ N, (2 ^ 250 - 1) * 2 ^ 5 + 11 = N + 1 := ⟨_, rfl⟩
    rw [hN] at h
    have hx0 : x ≡ 0 [MOD p] := hx
    have h0 := Nat.ModEq.trans h (Nat.ModEq.pow _ hx0)
    rwa [zero_pow (Nat.succ_ne_zero _)] at h0

end Curve25519Dalek.field.FieldElement51

namespace Curve25519Dalek.field.FieldElement2625

/-- The exponent computed by `invert`, plus one, is `p - 1`. -/
private theorem invert_exponent : (2 ^ 250 - 1) * 2 ^ 5 + 11 + 1 = p - 1 := by
  have h1 : 1 ≤ 2 ^ 250 := Nat.one_le_two_pow
  have h2 : 2 ^ 255 = 2 ^ 250 * 2 ^ 5 := by rw [← pow_add]
  have hp := p_add_nineteen
  generalize 2 ^ 250 = A at *
  generalize 2 ^ 255 = B at *
  omega

@[step]
theorem invert_spec (self : FieldElement2625) (hself : self.LimbsLt 27) :
    invert self ⦃ (r : FieldElement2625) =>
      (self.asNat % p ≠ 0 → r.asNat * self.asNat % p = 1) ∧
      (self.asNat % p = 0 → r.asNat % p = 0) ∧ r.LimbsLt 26 ⦄ := by
  unfold invert
  step as ⟨t19, t3, h19, h3, h19b, h3b⟩
  generalize hn : 2 ^ 250 - 1 = n at h19
  step as ⟨t20, h20, h20b⟩
  step as ⟨r, hr, hrb⟩
  subst hn
  set x := self.asNat
  have h : r.asNat ≡ x ^ ((2 ^ 250 - 1) * 2 ^ 5 + 11) [MOD p] := by
    rw [pow_add, pow_mul]
    exact Nat.ModEq.trans hr (Nat.ModEq.mul (Nat.ModEq.trans h20 (Nat.ModEq.pow _ h19)) h3)
  refine ⟨fun hx => ?_, fun hx => ?_, hrb⟩
  · have hx' : (x : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    have hrz : (r.asNat : ZMod p) = (x : ZMod p) ^ ((2 ^ 250 - 1) * 2 ^ 5 + 11) := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    have hone : ((r.asNat * x : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, hrz, ← pow_succ, invert_exponent, ZMod.pow_card_sub_one_eq_one hx',
        Nat.cast_one]
    rw [(ZMod.natCast_eq_natCast_iff' _ _ _).mp hone, Nat.mod_eq_of_lt p_prime.one_lt]
  · -- Hide the exponent behind a variable
    obtain ⟨N, hN⟩ : ∃ N, (2 ^ 250 - 1) * 2 ^ 5 + 11 = N + 1 := ⟨_, rfl⟩
    rw [hN] at h
    have hx0 : x ≡ 0 [MOD p] := hx
    have h0 := Nat.ModEq.trans h (Nat.ModEq.pow _ hx0)
    rwa [zero_pow (Nat.succ_ne_zero _)] at h0

end Curve25519Dalek.field.FieldElement2625

namespace Curve25519Dalek.Backend

theorem U64.invert_spec : U64.InvertSpec := fun a ha =>
  spec_mono (field.FieldElement51.invert_spec a ha) fun _ ⟨h1, h0, hb⟩ =>
    ⟨FieldElement51.toField_inv_of_mod h1 h0, hb⟩

theorem U32.invert_spec : U32.InvertSpec := fun a ha =>
  spec_mono (field.FieldElement2625.invert_spec a ha) fun _ ⟨h1, h0, hb⟩ =>
    ⟨FieldElement2625.toField_inv_of_mod h1 h0, hb⟩

end Curve25519Dalek.Backend
