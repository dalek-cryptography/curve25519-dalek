/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Helpers.FieldMul
import Proofs.Helpers.Limbs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.square_limbs
@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ := by
  unfold m
  step*

@[local step]
private theorem LOW_51_BIT_MASK_spec : LOW_51_BIT_MASK ⦃ (r : U64) => r.val = 2 ^ 51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  step*
end Curve25519Dalek.backend.serial.u64.field.square_limbs

namespace Curve25519Dalek.backend.serial.u64.field

set_option linter.hashCommand false in
#decompose square_limbs square_limbs_eq
  letRange 0 37 => square_limbs.prod
  letRange 7 46 => square_limbs.carry

attribute [nolint docBlame defsWithUnderscore] square_limbs.prod square_limbs.carry

@[local step]
private theorem square_limbs.carry_spec (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128)
    (hc0 : c0.val < 77 * 2 ^ 108) (hc1 : c1.val < 77 * 2 ^ 108) (hc2 : c2.val < 77 * 2 ^ 108)
    (hc3 : c3.val < 77 * 2 ^ 108) (hc4 : c4.val < 5 * 2 ^ 108) :
    square_limbs.carry a c0 c1 c2 c3 c4 ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r % p =
        (c0.val + 2 ^ 51 * c1.val + 2 ^ 102 * c2.val + 2 ^ 153 * c3.val + 2 ^ 204 * c4.val) % p ∧
      FieldElement51.LimbsLt 52 r ⦄ := by
  have h : square_limbs.carry a c0 c1 c2 c3 c4 =
      carryChain square_limbs.LOW_51_BIT_MASK a c0 c1 c2 c3 c4 := by
    simp only [square_limbs.carry, carryChain, carryAdd, lowLimb, carryOut, carryFold,
      Std.bind_assoc]
  rw [h]
  simpa only [field.FieldElement51.asNat_def] using
    carryChain_spec _ a c0 c1 c2 c3 c4 square_limbs.LOW_51_BIT_MASK_spec
      hc0 hc1 hc2 hc3 hc4

@[local step]
private theorem square_limbs.m_lt_spec (x y : U64) (hx : x.val < 2 ^ 54)
    (hy : y.val < 19 * 2 ^ 54) :
    square_limbs.m x y ⦃ (r : U128) => r.val = x.val * y.val ∧ r.val < 19 * 2 ^ 108 ⦄ := by
  step*

private theorem square_coeffs_lt {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54)
    (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) < 77 * 2 ^ 108 ∧
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) < 77 * 2 ^ 108 ∧
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) < 77 * 2 ^ 108 ∧
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) < 77 * 2 ^ 108 ∧
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) < 5 * 2 ^ 108 := by
  simp only [Nat.mul_left_comm _ 19]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac +nonLin

private theorem square_coeffs_mod_p {a0 a1 a2 a3 a4 c0 c1 c2 c3 c4 : ℕ}
    (hc0 : c0 = a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)))
    (hc1 : c1 = a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)))
    (hc2 : c2 = a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)))
    (hc3 : c3 = a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2))
    (hc4 : c4 = a2 * a2 + 2 * (a0 * a4 + a1 * a3)) :
    (c0 + 2 ^ 51 * c1 + 2 ^ 102 * c2 + 2 ^ 153 * c3 + 2 ^ 204 * c4) % p =
      (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) ^ 2 % p := by
  rw [sq]
  exact mul_coeffs_mod_p (by rw [hc0]; ring) (by rw [hc1]; ring) (by rw [hc2]; ring)
    (by rw [hc3]; ring) (by rw [hc4]; ring)

@[local step]
private theorem square_limbs.prod_spec (a : Array U64 5#usize)
    (ha : FieldElement51.LimbsLt 54 a) :
    square_limbs.prod a ⦃ (a3 a4 a0 a1 a2 : U64) (c0 c1 c2 c3 c4 : U128) =>
      a0.val = a[0]!.val ∧ a1.val = a[1]!.val ∧ a2.val = a[2]!.val ∧ a3.val = a[3]!.val ∧
      a4.val = a[4]!.val ∧
      c0.val = a0.val * a0.val + 2 * (a1.val * (19 * a4.val) + a2.val * (19 * a3.val)) ∧
      c1.val = a3.val * (19 * a3.val) + 2 * (a0.val * a1.val + a2.val * (19 * a4.val)) ∧
      c2.val = a1.val * a1.val + 2 * (a0.val * a2.val + a4.val * (19 * a3.val)) ∧
      c3.val = a4.val * (19 * a4.val) + 2 * (a0.val * a3.val + a1.val * a2.val) ∧
      c4.val = a2.val * a2.val + 2 * (a0.val * a4.val + a1.val * a3.val) ∧
      c0.val < 77 * 2 ^ 108 ∧ c1.val < 77 * 2 ^ 108 ∧ c2.val < 77 * 2 ^ 108 ∧
      c3.val < 77 * 2 ^ 108 ∧ c4.val < 5 * 2 ^ 108 ⦄ := by
  unfold square_limbs.prod
  have h0 : a.val[0].val < 2 ^ 54 := by simpa [getElem!_pos] using ha 0
  have h1 : a.val[1].val < 2 ^ 54 := by simpa [getElem!_pos] using ha 1
  have h2 : a.val[2].val < 2 ^ 54 := by simpa [getElem!_pos] using ha 2
  have h3 : a.val[3].val < 2 ^ 54 := by simpa [getElem!_pos] using ha 3
  have h4 : a.val[4].val < 2 ^ 54 := by simpa [getElem!_pos] using ha 4
  have hc := square_coeffs_lt h0 h1 h2 h3 h4
  step*
  simpa [*] using hc

@[step]
theorem square_limbs_spec (a : Array U64 5#usize) (ha : FieldElement51.LimbsLt 54 a) :
    square_limbs a ⦃ (r : Array U64 5#usize) =>
      FieldElement51.asNat r % p = FieldElement51.asNat a ^ 2 % p ∧
      FieldElement51.LimbsLt 52 r ⦄ := by
  rw [square_limbs_eq]
  step*
  refine ⟨?_, by assumption⟩
  rw [FieldElement51.asNat_eq a]
  simp only [*]
  exact square_coeffs_mod_p rfl rfl rfl rfl rfl
end Curve25519Dalek.backend.serial.u64.field
