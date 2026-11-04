/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace AffinePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«x86_64-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffinePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_spec fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«x86_64-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«x86_64-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«x86_64-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«i686-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffinePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_spec fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«i686-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«i686-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«i686-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«x86_64-no-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffinePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono identity_spec fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«x86_64-no-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«x86_64-no-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«x86_64-no-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«x86_64-no-tables».Insts.Curve25519_dalekTraitsIdentity

namespace AffinePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Identity for AffinePoint`: `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem identity_spec :
    identity ⦃ (r : AffinePoint.«i686-no-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold identity
  step as ⟨zero, hzero, hzero_lt⟩
  step as ⟨one, hone, hone_lt⟩
  exact ⟨toField_eq_zero_of_asNat hzero, toField_eq_one_of_asNat hone,
    limbs_lt_of_le (by decide) hzero_lt, limbs_lt_of_le (by decide) hone_lt⟩

/-- `Identity for AffinePoint` represents the neutral element. -/
theorem identity_spec_point :
    identity ⦃ (r : AffinePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono identity_spec fun r ⟨hx, hy, hb⟩ => by
    have hr : r.OnCurve := by
      rw [AffinePoint.«i686-no-tables».onCurve_iff, hx, hy]
      exact curve25519.edwards.equation_zero_one
    refine ⟨hr, Point.ext ?_ ?_, hb⟩
    · rw [AffinePoint.«i686-no-tables».toPoint_x hr, hx, zero_x]
    · rw [AffinePoint.«i686-no-tables».toPoint_y hr, hy, zero_y]

end AffinePoint.«i686-no-tables».Insts.Curve25519_dalekTraitsIdentity

end Curve25519Dalek.edwards.affine
