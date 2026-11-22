/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_coords :
    identity ⦃ (r : AffinePoint.«64bit-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_coords fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«64bit-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«64bit-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«64bit-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_coords :
    identity ⦃ (r : AffinePoint.«32bit-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_coords fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«32bit-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«32bit-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«32bit-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_coords :
    identity ⦃ (r : AffinePoint.«64bit-notables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_coords fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«64bit-notables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«64bit-notables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«64bit-notables».toPoint_y hr, hy, zero_y]

end AffinePoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_coords :
    identity ⦃ (r : AffinePoint.«32bit-notables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_coords fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«32bit-notables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«32bit-notables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«32bit-notables».toPoint_y hr, hy, zero_y]

end AffinePoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.edwards.affine
