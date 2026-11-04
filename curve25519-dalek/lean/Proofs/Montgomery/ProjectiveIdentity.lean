/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Zero
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Zero
import Proofs.Helpers.ToField2625
public section

/-! # `Identity for ProjectivePoint` (Montgomery) -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek

namespace montgomery.ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectivePoint`: `(1 : 0)`, the point at infinity; limbs `< 2^52`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : montgomery.ProjectivePoint.«x86_64-tables») =>
      r.toXZ = ⟨1, 0⟩ ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨U, hU, hU_lt⟩
  step as ⟨W, hW, hW_lt⟩
  refine ⟨?_, limbs_lt_of_le (by decide) hU_lt, limbs_lt_of_le (by decide) hW_lt⟩
  rw [montgomery.ProjectivePoint.«x86_64-tables».toXZ_def, toField_eq_one_of_asNat hU,
    toField_eq_zero_of_asNat hW]

end montgomery.ProjectivePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace montgomery.ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectivePoint`: `(1 : 0)`, the point at infinity; limbs `< 2^26`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : montgomery.ProjectivePoint.«i686-tables») =>
      r.toXZ = ⟨1, 0⟩ ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨U, hU, hU_lt⟩
  step as ⟨W, hW, hW_lt⟩
  refine ⟨?_, limbs_lt_of_le (by decide) hU_lt, limbs_lt_of_le (by decide) hW_lt⟩
  rw [montgomery.ProjectivePoint.«i686-tables».toXZ_def, toField_eq_one_of_asNat hU,
    toField_eq_zero_of_asNat hW]

end montgomery.ProjectivePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

namespace montgomery.ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for ProjectivePoint`: `(1 : 0)`, the point at infinity; limbs `< 2^52`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : montgomery.ProjectivePoint.«x86_64-no-tables») =>
      r.toXZ = ⟨1, 0⟩ ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨U, hU, hU_lt⟩
  step as ⟨W, hW, hW_lt⟩
  refine ⟨?_, limbs_lt_of_le (by decide) hU_lt, limbs_lt_of_le (by decide) hW_lt⟩
  rw [montgomery.ProjectivePoint.«x86_64-no-tables».toXZ_def, toField_eq_one_of_asNat hU,
    toField_eq_zero_of_asNat hW]

end montgomery.ProjectivePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace montgomery.ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for ProjectivePoint`: `(1 : 0)`, the point at infinity; limbs `< 2^26`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : montgomery.ProjectivePoint.«i686-no-tables») =>
      r.toXZ = ⟨1, 0⟩ ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨U, hU, hU_lt⟩
  step as ⟨W, hW, hW_lt⟩
  refine ⟨?_, limbs_lt_of_le (by decide) hU_lt, limbs_lt_of_le (by decide) hW_lt⟩
  rw [montgomery.ProjectivePoint.«i686-no-tables».toXZ_def, toField_eq_one_of_asNat hU,
    toField_eq_zero_of_asNat hW]

end montgomery.ProjectivePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek
