/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.Backend
public import Proofs.Helpers.ToField2625
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Square2
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Constants.Aplus2OverFour
import Proofs.Backend.Serial.U32.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U32.Constants.EdwardsDMinusOneSquared
import Proofs.Backend.Serial.U32.Constants.MinusOne
import Proofs.Backend.Serial.U32.Constants.OneMinusEdwardsDSquared
import Proofs.Backend.Serial.U32.Constants.SqrtAdMinusOne
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Constants.SqrtM1
import Proofs.Backend.Serial.U32.Field.ConditionalAssign
import Proofs.Backend.Serial.U32.Field.ConditionalNegate
import Proofs.Backend.Serial.U32.Field.Pow2k
import Mathlib.Tactic.LinearCombination
public section

/-! # The `u32` field backend

`FieldElement2625`, the backend of `«i686-tables»` and `«i686-no-tables»`, as a `Backend`:
`Red`, `Sum2`, `MulIn`, `Niels` are `LimbsLt 26`, `27`, `MulBounded`, `LimbsLt 27`. The specs
are stated first on `FieldElement2625` (their proofs use the field specs, imported privately),
then bundled; those through the encoding (`eq`, `ct_eq`, `is_negative`, `is_zero`, `to_bytes`)
are in `Backend/U32/Bytes.lean`.
`Backend.U32.mul_spec : Backend.U32.MulSpec`, … by definition. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open Curve25519Dalek.SharedAFieldElement2625.Insts

namespace Curve25519Dalek.Backend.U32

theorem add_spec (a b : FieldElement2625) (ha : a.LimbsLt 26) (hb : b.LimbsLt 26) :
    CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ ⟨h, _⟩ => ⟨toField_add_of_limbs h, limbs_add_lt h ha hb⟩

theorem add_sum2_spec (a b : FieldElement2625) (ha : a.LimbsLt 27) (hb : b.LimbsLt 26) :
    CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.MulBounded ⦄ :=
  spec_mono (CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ ⟨h, _⟩ => ⟨toField_add_of_limbs h, mulBounded_add h ha hb⟩

theorem sub_spec (a b : FieldElement2625) (ha : a.MulBounded) (hb : b.MulBounded) :
    CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub a b ⦃ r =>
      r.toField = a.toField - b.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub_spec a b
    (limbsLt_of_mulBounded ha) (limbsLt_of_mulBounded hb))
    fun _ ⟨h, hr⟩ => ⟨toField_sub_of_mod h, hr⟩

theorem mul_spec (a b : FieldElement2625) (ha : a.MulBounded) (hb : b.MulBounded) :
    CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul a b ⦃ r =>
      r.toField = a.toField * b.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_mul_of_mod h, hr⟩

theorem square_spec (a : FieldElement2625) (ha : a.LimbsLt 27) :
    FieldElement2625.square a ⦃ r => r.toField = a.toField ^ 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (FieldElement2625.square_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_sq_of_mod h, hr⟩

theorem square2_spec (a : FieldElement2625) (ha : a.LimbsLt 27) :
    FieldElement2625.square2 a ⦃ r => r.toField = 2 * a.toField ^ 2 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono (FieldElement2625.square2_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_two_mul_sq_of_mod h, limbs_lt_of_le (by decide) hr⟩

theorem neg_spec (a : FieldElement2625) (ha : a.MulBounded) :
    CoreOpsArithNegFieldElement2625.neg a ⦃ r => r.toField = -a.toField ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (CoreOpsArithNegFieldElement2625.neg_spec a (limbsLt_of_mulBounded ha))
    fun _ ⟨h, hr⟩ => ⟨toField_neg_of_mod h, hr⟩

theorem edwardsD_spec :
    backend.serial.u32.constants.EDWARDS_D ⦃ (r : FieldElement2625) =>
      r.toField = d ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.EDWARDS_D_spec
    fun _ ⟨h, hr⟩ => ⟨toField_eq_d_of_asNat h, hr⟩

theorem red_sum2 {a : FieldElement2625} (h : a.LimbsLt 26) : a.LimbsLt 27 :=
  limbs_lt_of_le (by decide) h

theorem sum2_mulIn {a : FieldElement2625} (h : a.LimbsLt 27) : a.MulBounded :=
  mulBounded_of_limbsLt h

theorem pow2k_spec (a : FieldElement2625) (k : U32) (hk : 0 < k.val) (ha : a.LimbsLt 27) :
    FieldElement2625.pow2k a k ⦃ r => r.toField = a.toField ^ 2 ^ k.val ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (FieldElement2625.pow2k_spec a k hk ha) fun _ ⟨h, hr⟩ => ⟨toField_pow_of_mod h, hr⟩

theorem conditional_assign_spec (a b : FieldElement2625) (c : subtle.Choice) (hc : c.IsValid) :
    FieldElement2625.Insts.SubtleConditionallySelectable.conditional_assign a b c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄ :=
  FieldElement2625.Insts.SubtleConditionallySelectable.conditional_assign_spec a b c hc

theorem conditional_negate_spec (a : FieldElement2625) (c : subtle.Choice) (hc : c.IsValid)
    (ha : a.MulBounded) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      FieldElement2625.Insts.SubtleConditionallySelectable CoreOpsArithNegFieldElement2625 a c
      ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r.toField = -a.toField ∧ r.LimbsLt 26) ⦄ :=
  spec_mono (FieldElement2625.conditional_negate_spec a c hc (limbsLt_of_mulBounded ha))
    fun _ ⟨h0, h1⟩ =>
    ⟨h0, fun h => ⟨toField_neg_of_mod (h1 h).1, (h1 h).2⟩⟩

theorem sqrtM1_spec :
    backend.serial.u32.constants.SQRT_M1 ⦃ (r : FieldElement2625) =>
      r.toField = (curve25519.sqrtM1 : ZMod p) ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.SQRT_M1_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h], hr⟩

theorem one_spec :
    FieldElement2625.ONE ⦃ (r : FieldElement2625) => r.toField = 1 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono FieldElement2625.ONE_spec fun _ ⟨h, hr⟩ => ⟨toField_eq_one_of_asNat h, hr⟩

theorem minusOne_spec :
    backend.serial.u32.constants.MINUS_ONE ⦃ (r : FieldElement2625) =>
      r.toField = -1 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.MINUS_ONE_spec fun r ⟨h, hr⟩ => by
    refine ⟨?_, hr⟩
    have h' : ((r.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [h]; exact ZMod.natCast_self p
    push_cast at h'
    rw [toField_def]
    linear_combination h'

theorem oneMinusDSq_spec :
    backend.serial.u32.constants.ONE_MINUS_EDWARDS_D_SQUARED ⦃ (r : FieldElement2625) =>
      r.toField = 1 - d ^ 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.ONE_MINUS_EDWARDS_D_SQUARED_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h, ZMod.natCast_zmod_val], hr⟩

theorem dMinusOneSq_spec :
    backend.serial.u32.constants.EDWARDS_D_MINUS_ONE_SQUARED ⦃ (r : FieldElement2625) =>
      r.toField = (d - 1) ^ 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.EDWARDS_D_MINUS_ONE_SQUARED_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h, ZMod.natCast_zmod_val], hr⟩

theorem sqrtAdMinusOne_spec :
    backend.serial.u32.constants.SQRT_AD_MINUS_ONE ⦃ (r : FieldElement2625) =>
      r.toField = (curve25519.sqrtAdMinusOne : ZMod p) ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.SQRT_AD_MINUS_ONE_spec_eq fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h], hr⟩

theorem invsqrtAMinusD_spec :
    backend.serial.u32.constants.INVSQRT_A_MINUS_D ⦃ (r : FieldElement2625) =>
      r.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.INVSQRT_A_MINUS_D_spec fun r ⟨_, h6, hr⟩ => by
    refine ⟨?_, hr⟩
    have h := natCast_eq_natCast_of_mod_eq (h6.trans one_mod_p.symm)
    push_cast at h
    rw [ZMod.natCast_zmod_val, ← toField_def] at h
    have had : (a : ZMod p) - d ≠ 0 := fun h0 => by
      have h1 := invsqrtAMinusD_sq_mul
      rw [h0, mul_zero] at h1
      exact zero_ne_one h1
    apply mul_right_cancel₀ had
    rw [h, invsqrtAMinusD_sq_mul]

theorem aplus2OverFour_spec :
    backend.serial.u32.constants.APLUS2_OVER_FOUR ⦃ (r : FieldElement2625) =>
      r.toField * 4 = (A : ZMod p) + 2 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono backend.serial.u32.constants.APLUS2_OVER_FOUR_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def]; exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h, hr⟩

end Curve25519Dalek.Backend.U32

namespace Curve25519Dalek.Backend

/-- The `u32` backend (`FieldElement2625`). -/
@[expose] noncomputable def U32 : Backend where
  F := FieldElement2625
  asNat a := a.asNat
  toField a := a.toField
  toField_eq a := a.toField_def
  inhF := inferInstance
  Red a := a.LimbsLt 26
  Sum2 a := a.LimbsLt 27
  SqIn a := a.LimbsLt 27
  MulIn a := a.MulBounded
  Niels a := a.LimbsLt 27
  add := CoreOpsArithAddSharedBFieldElement2625FieldElement2625.add
  sub := CoreOpsArithSubSharedBFieldElement2625FieldElement2625.sub
  mul := CoreOpsArithMulSharedBFieldElement2625FieldElement2625.mul
  square := FieldElement2625.square
  square2 := FieldElement2625.square2
  pow2k := FieldElement2625.pow2k
  neg := CoreOpsArithNegFieldElement2625.neg
  eq := FieldElement2625.Insts.CoreCmpPartialEqFieldElement2625.eq
  ctEq := FieldElement2625.Insts.SubtleConstantTimeEq.ct_eq
  condAssign := FieldElement2625.Insts.SubtleConditionallySelectable.conditional_assign
  condNeg := subtle.ConditionallyNegatable.Blanket.conditional_negate
    FieldElement2625.Insts.SubtleConditionallySelectable CoreOpsArithNegFieldElement2625
  constEdwardsD := backend.serial.u32.constants.EDWARDS_D
  constSqrtM1 := backend.serial.u32.constants.SQRT_M1
  constOne := FieldElement2625.ONE
  constMinusOne := backend.serial.u32.constants.MINUS_ONE
  constOneMinusDSq := backend.serial.u32.constants.ONE_MINUS_EDWARDS_D_SQUARED
  constDMinusOneSq := backend.serial.u32.constants.EDWARDS_D_MINUS_ONE_SQUARED
  constSqrtAdMinusOne := backend.serial.u32.constants.SQRT_AD_MINUS_ONE
  constInvsqrtAMinusD := backend.serial.u32.constants.INVSQRT_A_MINUS_D
  constAplus2OverFour := backend.serial.u32.constants.APLUS2_OVER_FOUR
  toBytes := FieldElement2625.to_bytes
  isNegative := field.FieldElement2625.is_negative
  isZero := field.FieldElement2625.is_zero
  pow22501 := field.FieldElement2625.pow22501
  powP58 := field.FieldElement2625.pow_p58
  invert := field.FieldElement2625.invert
  sqrtRatioI := field.FieldElement2625.sqrt_ratio_i
  invsqrt := field.FieldElement2625.invsqrt
  invertBatchAlloc := field.FieldElement2625.invert_batch_alloc
  red_sum2 := U32.red_sum2
  sum2_sqIn h := h
  sqIn_mulIn := U32.sum2_mulIn
  red_niels := U32.red_sum2
  niels_mulIn := U32.sum2_mulIn

end Curve25519Dalek.Backend
