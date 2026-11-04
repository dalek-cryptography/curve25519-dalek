/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Affine.Identity
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«x86_64-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem default_spec :
    default ⦃ (r : AffinePoint.«x86_64-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : AffinePoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec_point

end AffinePoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace AffinePoint.«i686-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem default_spec :
    default ⦃ (r : AffinePoint.«i686-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : AffinePoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec_point

end AffinePoint.«i686-tables».Insts.CoreDefaultDefault

namespace AffinePoint.«x86_64-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem default_spec :
    default ⦃ (r : AffinePoint.«x86_64-no-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : AffinePoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec_point

end AffinePoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace AffinePoint.«i686-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem default_spec :
    default ⦃ (r : AffinePoint.«i686-no-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : AffinePoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec_point

end AffinePoint.«i686-no-tables».Insts.CoreDefaultDefault

end Curve25519Dalek.edwards.affine
