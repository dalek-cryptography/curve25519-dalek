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

namespace ProjectiveNielsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_toProjectiveNiels :
    identity ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-tables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono identity_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectiveNielsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^27`. -/
@[step]
theorem identity_toProjectiveNiels :
    identity ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-tables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono identity_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectiveNielsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem identity_toProjectiveNiels :
    identity ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«64bit-notables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono identity_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectiveNielsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectiveNielsPoint`: `(1 : 1 : 1 : 0)`, limbs `< 2^27`. -/
@[step]
theorem identity_toProjectiveNiels :
    identity ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold identity
  step as ⟨one, hone, hone_lt⟩
  step as ⟨zero, hzero, hzero_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectiveNielsPoint.«32bit-notables».toProjectiveNiels_def,
      ProjectiveNiels.identity, toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_lt_of_le (by decide) hzero_lt⟩

/-- `Identity for ProjectiveNielsPoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono identity_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.backend.serial.curve_models
