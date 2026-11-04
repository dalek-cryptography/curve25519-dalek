/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
import Proofs.Helpers.FieldMul
import Proofs.Helpers.Limbs
import Proofs.Helpers.Array
import Proofs.Helpers.StepSpecs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field
namespace MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
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
end MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
end Curve25519Dalek.backend.serial.u64.field

namespace Curve25519Dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithMulSharedAFieldElement51FieldElement51
open backend.serial.u64.field
open backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51

set_option linter.hashCommand false in
#decompose mul mul_eq
  letRange 0 59 => mul.prod
  letRange 13 47 => mul.carry

attribute [nolint docBlame] mul.prod mul.carry

@[local step]
private theorem mul.carry_spec (c0 c1 c2 c3 c4 : U128) (out : Array U64 5#usize)
    (hc0 : c0.val < 77 * 2 ^ 108) (hc1 : c1.val < 77 * 2 ^ 108) (hc2 : c2.val < 77 * 2 ^ 108)
    (hc3 : c3.val < 77 * 2 ^ 108) (hc4 : c4.val < 5 * 2 ^ 108) :
    mul.carry c0 c1 c2 c3 c4 out ⦃ (r : FieldElement51) =>
      r.asNat % p =
        (c0.val + 2 ^ 51 * c1.val + 2 ^ 102 * c2.val + 2 ^ 153 * c3.val + 2 ^ 204 * c4.val) % p ∧
      r.LimbsLt 52 ⦄ := by
  have h : mul.carry c0 c1 c2 c3 c4 out = carryChain mul.LOW_51_BIT_MASK out c0 c1 c2 c3 c4 := by
    simp only [mul.carry, carryChain, carryAdd, lowLimb, carryOut, carryFold, Std.bind_assoc,
      Std.bind_pure]
  rw [h]
  simpa only [backend.serial.u64.field.FieldElement51.asNat_def] using
    carryChain_spec _ out c0 c1 c2 c3 c4 mul.LOW_51_BIT_MASK_spec hc0 hc1 hc2 hc3 hc4

@[local step]
private theorem mul.m_lt_spec (x y : U64) (hx : x.val < 2 ^ 54) (hy : y.val < 19 * 2 ^ 54) :
    mul.m x y ⦃ (r : U128) => r.val = x.val * y.val ∧ r.val < 19 * 2 ^ 108 ⦄ := by
  step*

private theorem mul_coeffs_lt {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ} (ha0 : a0 < 2 ^ 54)
    (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54) (ha4 : a4 < 2 ^ 54)
    (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54) (hb3 : b3 < 2 ^ 54)
    (hb4 : b4 < 2 ^ 54) :
    a0 * b0 + a4 * (b1 * 19) + a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) < 77 * 2 ^ 108 ∧
    a1 * b0 + a0 * b1 + a4 * (b2 * 19) + a3 * (b3 * 19) + a2 * (b4 * 19) < 77 * 2 ^ 108 ∧
    a2 * b0 + a1 * b1 + a0 * b2 + a4 * (b3 * 19) + a3 * (b4 * 19) < 77 * 2 ^ 108 ∧
    a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + a4 * (b4 * 19) < 77 * 2 ^ 108 ∧
    a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4 < 5 * 2 ^ 108 := by
  simp only [← Nat.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac +nonLin

open scoped Helpers.IndexStep in
@[local step]
private theorem mul.prod_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    mul.prod self rhs ⦃ (b1 b2 b3 b4 a0 b0 a4 a3 a2 a1 : U64) (c0 c1 c2 c3 c4 : U128) =>
      a0.val = self[0]!.val ∧ a1.val = self[1]!.val ∧ a2.val = self[2]!.val ∧
      a3.val = self[3]!.val ∧ a4.val = self[4]!.val ∧
      b0.val = rhs[0]!.val ∧ b1.val = rhs[1]!.val ∧ b2.val = rhs[2]!.val ∧
      b3.val = rhs[3]!.val ∧ b4.val = rhs[4]!.val ∧
      c0.val = a0.val * b0.val + a4.val * (b1.val * 19) + a3.val * (b2.val * 19) +
        a2.val * (b3.val * 19) + a1.val * (b4.val * 19) ∧
      c1.val = a1.val * b0.val + a0.val * b1.val + a4.val * (b2.val * 19) +
        a3.val * (b3.val * 19) + a2.val * (b4.val * 19) ∧
      c2.val = a2.val * b0.val + a1.val * b1.val + a0.val * b2.val + a4.val * (b3.val * 19) +
        a3.val * (b4.val * 19) ∧
      c3.val = a3.val * b0.val + a2.val * b1.val + a1.val * b2.val + a0.val * b3.val +
        a4.val * (b4.val * 19) ∧
      c4.val = a4.val * b0.val + a3.val * b1.val + a2.val * b2.val + a1.val * b3.val +
        a0.val * b4.val ∧
      c0.val < 77 * 2 ^ 108 ∧ c1.val < 77 * 2 ^ 108 ∧ c2.val < 77 * 2 ^ 108 ∧
      c3.val < 77 * 2 ^ 108 ∧ c4.val < 5 * 2 ^ 108 ⦄ := by
  unfold mul.prod
  unfold FieldElement51.LimbsLt at hself hrhs
  rw [Nat.forall_lt_five] at hself hrhs
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ := hself
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hrhs
  have hc := mul_coeffs_lt ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4
  step*
  simpa [*] using hc

@[step]
theorem mul_spec (self rhs : FieldElement51)
    (hself : self.LimbsLt 54) (hrhs : rhs.LimbsLt 54) :
    mul self rhs ⦃ (r : FieldElement51) =>
      r.asNat % p = self.asNat * rhs.asNat % p ∧ r.LimbsLt 52 ⦄ := by
  rw [mul_eq]
  step*
  refine ⟨?_, by assumption⟩
  rw [FieldElement51.asNat_eq self, FieldElement51.asNat_eq rhs]
  simp only [*]
  exact mul_coeffs_mod_p (by ring) (by ring) (by ring) (by ring) (by ring)
end Curve25519Dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51

