/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.CurveModels
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Zero
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Zero
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_toAffineNiels :
    identity ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«64bit-tables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono identity_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-tables».onCurve_iff,
      AffineNielsPoint.«64bit-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffineNielsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^27`. -/
@[step]
theorem identity_toAffineNiels :
    identity ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«32bit-tables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono identity_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-tables».onCurve_iff,
      AffineNielsPoint.«32bit-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffineNielsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_toAffineNiels :
    identity ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«64bit-notables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono identity_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«64bit-notables».onCurve_iff,
      AffineNielsPoint.«64bit-notables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace AffineNielsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffineNielsPoint`: `(1, 1, 0)`, limbs `< 2^27`. -/
@[step]
theorem identity_toAffineNiels :
    identity ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [AffineNielsPoint.«32bit-notables».toAffineNiels_def, AffineNiels.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for AffineNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffineNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono identity_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«32bit-notables».onCurve_iff,
      AffineNielsPoint.«32bit-notables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.backend.serial.curve_models
