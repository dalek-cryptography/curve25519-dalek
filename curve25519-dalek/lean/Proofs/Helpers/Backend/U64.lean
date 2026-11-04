/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement51
public import Proofs.Helpers.Backend
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Square2
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Constants.Aplus2OverFour
import Proofs.Backend.Serial.U64.Constants.InvsqrtAMinusD
import Proofs.Backend.Serial.U64.Constants.EdwardsDMinusOneSquared
import Proofs.Backend.Serial.U64.Constants.MinusOne
import Proofs.Backend.Serial.U64.Constants.OneMinusEdwardsDSquared
import Proofs.Backend.Serial.U64.Constants.SqrtAdMinusOne
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Constants.SqrtM1
import Proofs.Backend.Serial.U64.Field.ConditionalAssign
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.Pow2k
import Proofs.Helpers.ToField
import Mathlib.Tactic.LinearCombination
public section

/-! # The `u64` field backend

`FieldElement51`, the backend of `«x86_64-tables»` and `«x86_64-no-tables»`, as a `Backend`:
`Red`, `Sum2`, `MulIn`, `Niels` are `LimbsLt 52`, `53`, `54`, `54`. The specs are stated first on
`FieldElement51` (their proofs use the field specs, imported privately), then bundled; those
through the encoding (`eq`, `ct_eq`, `is_negative`, `is_zero`, `to_bytes`) are in
`Backend/U64/Bytes.lean`.
`Backend.U64.mul_spec : Backend.U64.MulSpec`, … by definition. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.Shared0FieldElement51.Insts

namespace Curve25519Dalek.Backend.U64

theorem add_spec (a b : FieldElement51) (ha : a.LimbsLt 52) (hb : b.LimbsLt 52) :
    CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 53 ⦄ :=
  spec_mono (CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ h => ⟨toField_add_of_limbs h, limbs_add_lt h ha hb⟩

theorem add_sum2_spec (a b : FieldElement51) (ha : a.LimbsLt 53) (hb : b.LimbsLt 52) :
    CoreOpsArithAddSharedAFieldElement51FieldElement51.add a b ⦃ r =>
      r.toField = a.toField + b.toField ∧ r.LimbsLt 54 ⦄ :=
  spec_mono (CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec a b
    (limbs_lt_of_le (by decide) ha) (limbs_lt_of_le (by decide) hb))
    fun _ h => ⟨toField_add_of_limbs h, limbs_add_lt h ha (limbs_lt_of_le (by decide) hb)⟩

theorem sub_spec (a b : FieldElement51) (ha : a.LimbsLt 54) (hb : b.LimbsLt 54) :
    CoreOpsArithSubSharedAFieldElement51FieldElement51.sub a b ⦃ r =>
      r.toField = a.toField - b.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_sub_of_mod h, hr⟩

theorem mul_spec (a b : FieldElement51) (ha : a.LimbsLt 54) (hb : b.LimbsLt 54) :
    CoreOpsArithMulSharedAFieldElement51FieldElement51.mul a b ⦃ r =>
      r.toField = a.toField * b.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec a b ha hb)
    fun _ ⟨h, hr⟩ => ⟨toField_mul_of_mod h, hr⟩

theorem square_spec (a : FieldElement51) (ha : a.LimbsLt 54) :
    FieldElement51.square a ⦃ r => r.toField = a.toField ^ 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (FieldElement51.square_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_sq_of_mod h, hr⟩

theorem square2_spec (a : FieldElement51) (ha : a.LimbsLt 54) :
    FieldElement51.square2 a ⦃ r => r.toField = 2 * a.toField ^ 2 ∧ r.LimbsLt 53 ⦄ :=
  spec_mono (FieldElement51.square2_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_two_mul_sq_of_mod h, hr⟩

theorem neg_spec (a : FieldElement51) (ha : a.LimbsLt 54) :
    CoreOpsArithNegFieldElement51.neg a ⦃ r => r.toField = -a.toField ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (CoreOpsArithNegFieldElement51.neg_spec a ha)
    fun _ ⟨h, hr⟩ => ⟨toField_neg_of_mod h, hr⟩

theorem edwardsD_spec :
    backend.serial.u64.constants.EDWARDS_D ⦃ (r : FieldElement51) =>
      r.toField = d ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.EDWARDS_D_spec
    fun _ ⟨h, hr⟩ => ⟨toField_eq_d_of_asNat h, limbs_lt_of_le (by decide) hr⟩

theorem limbs_lt_mono {a : FieldElement51} {k l : ℕ} (hkl : k ≤ l) (h : a.LimbsLt k) :
    a.LimbsLt l :=
  limbs_lt_of_le hkl h

theorem pow2k_spec (a : FieldElement51) (k : U32) (hk : 0 < k.val) (ha : a.LimbsLt 54) :
    FieldElement51.pow2k a k ⦃ r => r.toField = a.toField ^ 2 ^ k.val ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (FieldElement51.pow2k_spec a k hk ha) fun _ ⟨h, hr⟩ => ⟨toField_pow_of_mod h, hr⟩

theorem conditional_assign_spec (a b : FieldElement51) (c : subtle.Choice) (hc : c.IsValid) :
    FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign a b c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄ :=
  FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign_spec a b c hc

theorem conditional_negate_spec (a : FieldElement51) (c : subtle.Choice) (hc : c.IsValid)
    (ha : a.LimbsLt 54) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      FieldElement51.Insts.SubtleConditionallySelectable CoreOpsArithNegFieldElement51 a c ⦃ r =>
      (c = 0#u8 → r = a) ∧ (c = 1#u8 → r.toField = -a.toField ∧ r.LimbsLt 52) ⦄ :=
  spec_mono (FieldElement51.conditional_negate_spec a c hc ha) fun _ ⟨h0, h1⟩ =>
    ⟨h0, fun h => ⟨toField_neg_of_mod (h1 h).1, (h1 h).2⟩⟩

theorem sqrtM1_spec :
    backend.serial.u64.constants.SQRT_M1 ⦃ (r : FieldElement51) =>
      r.toField = (curve25519.sqrtM1 : ZMod p) ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.SQRT_M1_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h], limbs_lt_of_le (by decide) hr⟩

theorem one_spec :
    FieldElement51.ONE ⦃ (r : FieldElement51) => r.toField = 1 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono FieldElement51.ONE_spec fun _ ⟨h, hr⟩ =>
    ⟨toField_eq_one_of_asNat h, limbs_lt_of_le (by decide) hr⟩

theorem minusOne_spec :
    backend.serial.u64.constants.MINUS_ONE ⦃ (r : FieldElement51) =>
      r.toField = -1 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.MINUS_ONE_spec fun r ⟨h, hr⟩ => by
    refine ⟨?_, limbs_lt_of_le (by decide) hr⟩
    have h' : ((r.asNat + 1 : ℕ) : ZMod p) = 0 := by rw [h]; exact ZMod.natCast_self p
    push_cast at h'
    rw [toField_def]
    linear_combination h'

theorem oneMinusDSq_spec :
    backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED ⦃ (r : FieldElement51) =>
      r.toField = 1 - d ^ 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h, ZMod.natCast_zmod_val], limbs_lt_of_le (by decide) hr⟩

theorem dMinusOneSq_spec :
    backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED ⦃ (r : FieldElement51) =>
      r.toField = (d - 1) ^ 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h, ZMod.natCast_zmod_val], limbs_lt_of_le (by decide) hr⟩

theorem sqrtAdMinusOne_spec :
    backend.serial.u64.constants.SQRT_AD_MINUS_ONE ⦃ (r : FieldElement51) =>
      r.toField = (curve25519.sqrtAdMinusOne : ZMod p) ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.SQRT_AD_MINUS_ONE_spec_eq fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def, h], limbs_lt_of_le (by decide) hr⟩

theorem invsqrtAMinusD_spec :
    backend.serial.u64.constants.INVSQRT_A_MINUS_D ⦃ (r : FieldElement51) =>
      r.toField ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.INVSQRT_A_MINUS_D_spec fun r ⟨_, h6, hr⟩ => by
    refine ⟨?_, limbs_lt_of_le (by decide) hr⟩
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
    backend.serial.u64.constants.APLUS2_OVER_FOUR ⦃ (r : FieldElement51) =>
      r.toField * 4 = (A : ZMod p) + 2 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono backend.serial.u64.constants.APLUS2_OVER_FOUR_spec fun _ ⟨h, hr⟩ =>
    ⟨by rw [toField_def]; exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h,
      limbs_lt_of_le (by decide) hr⟩

end Curve25519Dalek.Backend.U64

namespace Curve25519Dalek.Backend

/-- The `u64` backend (`FieldElement51`). -/
@[expose] noncomputable def U64 : Backend where
  F := FieldElement51
  asNat a := a.asNat
  toField a := a.toField
  toField_eq a := a.toField_def
  inhF := inferInstance
  Red a := a.LimbsLt 52
  Sum2 a := a.LimbsLt 53
  SqIn a := a.LimbsLt 54
  MulIn a := a.LimbsLt 54
  Niels a := a.LimbsLt 54
  add := CoreOpsArithAddSharedAFieldElement51FieldElement51.add
  sub := CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
  mul := CoreOpsArithMulSharedAFieldElement51FieldElement51.mul
  square := FieldElement51.square
  square2 := FieldElement51.square2
  pow2k := FieldElement51.pow2k
  neg := CoreOpsArithNegFieldElement51.neg
  eq := FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq
  ctEq := FieldElement51.Insts.SubtleConstantTimeEq.ct_eq
  condAssign := FieldElement51.Insts.SubtleConditionallySelectable.conditional_assign
  condNeg := subtle.ConditionallyNegatable.Blanket.conditional_negate
    FieldElement51.Insts.SubtleConditionallySelectable CoreOpsArithNegFieldElement51
  constEdwardsD := backend.serial.u64.constants.EDWARDS_D
  constSqrtM1 := backend.serial.u64.constants.SQRT_M1
  constOne := FieldElement51.ONE
  constMinusOne := backend.serial.u64.constants.MINUS_ONE
  constOneMinusDSq := backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED
  constDMinusOneSq := backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED
  constSqrtAdMinusOne := backend.serial.u64.constants.SQRT_AD_MINUS_ONE
  constInvsqrtAMinusD := backend.serial.u64.constants.INVSQRT_A_MINUS_D
  constAplus2OverFour := backend.serial.u64.constants.APLUS2_OVER_FOUR
  toBytes := FieldElement51.to_bytes
  isNegative := field.FieldElement51.is_negative
  isZero := field.FieldElement51.is_zero
  pow22501 := field.FieldElement51.pow22501
  powP58 := field.FieldElement51.pow_p58
  invert := field.FieldElement51.invert
  sqrtRatioI := field.FieldElement51.sqrt_ratio_i
  invsqrt := field.FieldElement51.invsqrt
  invertBatchAlloc := field.FieldElement51.invert_batch_alloc
  red_sum2 := U64.limbs_lt_mono (by decide)
  sum2_sqIn := U64.limbs_lt_mono (by decide)
  sqIn_mulIn h := h
  red_niels := U64.limbs_lt_mono (by decide)
  niels_mulIn h := h

end Curve25519Dalek.Backend
