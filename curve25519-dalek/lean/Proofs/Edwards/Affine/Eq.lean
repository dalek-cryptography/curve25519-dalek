/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Affine.CtEq
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«64bit-tables».Insts.«CoreCmpPartialEqAffinePoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_coords (self other : AffinePoint.«64bit-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffinePoint.«64bit-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_coords self other) fun _ hb => by
    rw [AffinePoint.«64bit-tables».toPoint_eq_mk hself,
      AffinePoint.«64bit-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«64bit-tables».Insts.«CoreCmpPartialEqAffinePoint64bit-tables»

namespace AffinePoint.«32bit-tables».Insts.«CoreCmpPartialEqAffinePoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_coords (self other : AffinePoint.«32bit-tables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffinePoint.«32bit-tables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_coords self other) fun _ hb => by
    rw [AffinePoint.«32bit-tables».toPoint_eq_mk hself,
      AffinePoint.«32bit-tables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«32bit-tables».Insts.«CoreCmpPartialEqAffinePoint32bit-tables»

namespace AffinePoint.«64bit-notables».Insts.«CoreCmpPartialEqAffinePoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_coords (self other : AffinePoint.«64bit-notables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffinePoint.«64bit-notables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_coords self other) fun _ hb => by
    rw [AffinePoint.«64bit-notables».toPoint_eq_mk hself,
      AffinePoint.«64bit-notables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«64bit-notables».Insts.«CoreCmpPartialEqAffinePoint64bit-notables»

namespace AffinePoint.«32bit-notables».Insts.«CoreCmpPartialEqAffinePoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `PartialEq for AffinePoint`: both coordinates agree modulo `p`. -/
@[step]
theorem eq_coords (self other : AffinePoint.«32bit-notables») :
    eq self other ⦃ (b : Bool) =>
      b = true ↔ self.x.toField = other.x.toField ∧ self.y.toField = other.y.toField ⦄ := by
  unfold eq
  step as ⟨c, hcv, hc⟩
  step as ⟨b, hb⟩
  rw [hb, ← hc]
  rcases hcv with rfl | rfl <;> decide

/-- `PartialEq for AffinePoint` on points: equality of the represented points. -/
theorem eq_spec (self other : AffinePoint.«32bit-notables») (hself : self.OnCurve)
    (hother : other.OnCurve) :
    eq self other ⦃ (r : Bool) => r = true ↔ self.toPoint = other.toPoint ⦄ :=
  spec_mono (eq_coords self other) fun _ hb => by
    rw [AffinePoint.«32bit-notables».toPoint_eq_mk hself,
      AffinePoint.«32bit-notables».toPoint_eq_mk hother, Point.ext_iff]
    exact hb

end AffinePoint.«32bit-notables».Insts.«CoreCmpPartialEqAffinePoint32bit-notables»

end Curve25519Dalek.edwards.affine
