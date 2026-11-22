/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.External.Zeroize.Instances
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«64bit-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem zeroize_toExtended (self : EdwardsPoint.«64bit-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 52, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 52⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec (self : EdwardsPoint.«64bit-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (zeroize_toExtended self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-tables».onCurve_iff,
      EdwardsPoint.«64bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-tables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«32bit-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem zeroize_toExtended (self : EdwardsPoint.«32bit-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 26, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 26⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec (self : EdwardsPoint.«32bit-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (zeroize_toExtended self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-tables».onCurve_iff,
      EdwardsPoint.«32bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-tables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«64bit-notables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem zeroize_toExtended (self : EdwardsPoint.«64bit-notables») :
    zeroize self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-notables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 52, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 52⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec (self : EdwardsPoint.«64bit-notables») :
    zeroize self ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (zeroize_toExtended self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-notables».onCurve_iff,
      EdwardsPoint.«64bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-notables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«32bit-notables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem zeroize_toExtended (self : EdwardsPoint.«32bit-notables») :
    zeroize self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-notables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 26, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 26⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec (self : EdwardsPoint.«32bit-notables») :
    zeroize self ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (zeroize_toExtended self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-notables».onCurve_iff,
      EdwardsPoint.«32bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-notables».Insts.ZeroizeZeroize

end Curve25519Dalek.edwards
