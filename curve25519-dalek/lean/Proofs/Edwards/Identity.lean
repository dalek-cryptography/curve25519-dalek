module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Zero
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Zero
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for EdwardsPoint`: `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem identity_toExtended :
    identity ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-tables».toExtended_def, Extended.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for EdwardsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-tables».onCurve_iff,
      EdwardsPoint.«64bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for EdwardsPoint`: `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem identity_toExtended :
    identity ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-tables».toExtended_def, Extended.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for EdwardsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-tables».onCurve_iff,
      EdwardsPoint.«32bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for EdwardsPoint`: `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem identity_toExtended :
    identity ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«64bit-notables».toExtended_def, Extended.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for EdwardsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-notables».onCurve_iff,
      EdwardsPoint.«64bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for EdwardsPoint`: `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem identity_toExtended :
    identity ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«32bit-notables».toExtended_def, Extended.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for EdwardsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-notables».onCurve_iff,
      EdwardsPoint.«32bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.edwards
