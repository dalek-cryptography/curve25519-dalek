/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar52
import Curve25519.Prime
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U64.Scalar.AsMontgomery
import Proofs.Backend.Serial.U64.Scalar.FromMontgomery
import Proofs.Helpers.Scalar
import Proofs.Helpers.ZMod
import Proofs.Scalar.Scalar52MontgomeryInvert
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar52

@[step]
theorem invert_spec (self : backend.serial.u64.scalar.Scalar52)
    (hself : self.LimbsLt 52) :
    invert self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ∧ r.LimbsLt 52 ⦄ := by
  unfold invert
  have hR := montgomeryRadix_natCast_ne_zero
  step as ⟨s, hs, hsb⟩
  have hsL : s.asNat < L := hs ▸ Nat.mod_lt _ L_pos
  step as ⟨s1, hs1, hs10, hs1L, hs1b⟩
  step as ⟨r, hr, hrL, hrb⟩
  have hs' : (s.asNat : ZMod L) = self.asNat * montgomeryRadix := by
    exact_mod_cast (ZMod.natCast_eq_natCast_of_mod_eq hs.symm).symm
  have hr' : (r.asNat : ZMod L) * montgomeryRadix = s1.asNat := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hr
  refine ⟨fun h => ?_, fun h => ?_, hrL, hrb⟩
  · have hself : (self.asNat : ZMod L) ≠ 0 := fun h' => h (ZMod.natCast_eq_zero_iff_mod.mp h')
    have hsne : s.asNat % L ≠ 0 := fun h' =>
      mul_ne_zero hself hR (hs' ▸ ZMod.natCast_eq_zero_iff_mod.mpr h')
    have hs1' : (s1.asNat : ZMod L) * s.asNat = montgomeryRadix ^ 2 :=
      by exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (hs1 hsne)
    rw [← Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by decide) |>.trans two_pow_252_lt_L),
      ← ZMod.natCast_eq_natCast_iff']
    push_cast
    apply mul_right_cancel₀ (pow_ne_zero 2 hR)
    linear_combination ((self.asNat : ZMod L) * montgomeryRadix) * hr' -
      (s1.asNat : ZMod L) * hs' + hs1'
  · have hs0 : s.asNat % L = 0 := by
      rw [hs, Nat.mod_mod, Nat.mul_mod, h, zero_mul, Nat.zero_mod]
    rw [hs10 hs0, Nat.cast_zero] at hr'
    have h0 : (r.asNat : ZMod L) = 0 := (mul_eq_zero.mp hr').resolve_right hR
    have h0' := ZMod.natCast_eq_zero_iff_mod.mp h0
    rwa [Nat.mod_eq_of_lt hrL] at h0'

end Curve25519Dalek.scalar.Scalar52
