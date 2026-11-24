module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Affine.Identity
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

namespace AffinePoint.«64bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem default_coords :
    default ⦃ (r : AffinePoint.«64bit-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffinePoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec

end AffinePoint.«64bit-tables».Insts.CoreDefaultDefault

namespace AffinePoint.«32bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem default_coords :
    default ⦃ (r : AffinePoint.«32bit-tables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffinePoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec

end AffinePoint.«32bit-tables».Insts.CoreDefaultDefault

namespace AffinePoint.«64bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^52`. -/
@[step]
theorem default_coords :
    default ⦃ (r : AffinePoint.«64bit-notables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffinePoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec

end AffinePoint.«64bit-notables».Insts.CoreDefaultDefault

namespace AffinePoint.«32bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffinePoint`: the identity `(0, 1)`, limbs `< 2^26`. -/
@[step]
theorem default_coords :
    default ⦃ (r : AffinePoint.«32bit-notables») =>
      r.x.toField = 0 ∧ r.y.toField = 1 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for AffinePoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffinePoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  exact Curve25519_dalekTraitsIdentity.identity_spec

end AffinePoint.«32bit-notables».Insts.CoreDefaultDefault

end Curve25519Dalek.edwards.affine
