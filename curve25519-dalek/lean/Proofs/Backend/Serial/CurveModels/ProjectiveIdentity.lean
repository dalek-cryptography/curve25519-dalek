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

namespace ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectivePoint`: `(0 : 1 : 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_toProjective :
    identity ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.toProjective = Projective.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«64bit-tables».toProjective_def, Projective.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for ProjectivePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectivePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_toProjective fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-tables».onCurve_iff,
      ProjectivePoint.«64bit-tables».toPoint_def, hr]
    exact ⟨Projective.onCurve_identity, Projective.toPoint_identity, hb⟩

end ProjectivePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectivePoint`: `(0 : 1 : 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_toProjective :
    identity ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.toProjective = Projective.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«32bit-tables».toProjective_def, Projective.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for ProjectivePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectivePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_toProjective fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-tables».onCurve_iff,
      ProjectivePoint.«32bit-tables».toPoint_def, hr]
    exact ⟨Projective.onCurve_identity, Projective.toPoint_identity, hb⟩

end ProjectivePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectivePoint`: `(0 : 1 : 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_toProjective :
    identity ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.toProjective = Projective.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«64bit-notables».toProjective_def, Projective.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for ProjectivePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectivePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_toProjective fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«64bit-notables».onCurve_iff,
      ProjectivePoint.«64bit-notables».toPoint_def, hr]
    exact ⟨Projective.onCurve_identity, Projective.toPoint_identity, hb⟩

end ProjectivePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectivePoint`: `(0 : 1 : 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_toProjective :
    identity ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.toProjective = Projective.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  refine ⟨?_, ?_⟩
  · simp only [ProjectivePoint.«32bit-notables».toProjective_def, Projective.identity,
      toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone]
  · exact ⟨limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for ProjectivePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : ProjectivePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_toProjective fun r ⟨hr, hb⟩ => by
    rw [ProjectivePoint.«32bit-notables».onCurve_iff,
      ProjectivePoint.«32bit-notables».toPoint_def, hr]
    exact ⟨Projective.onCurve_identity, Projective.toPoint_identity, hb⟩

end ProjectivePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.backend.serial.curve_models
