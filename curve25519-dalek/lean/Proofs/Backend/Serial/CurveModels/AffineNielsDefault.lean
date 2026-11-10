/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.CurveModels
import Proofs.Backend.Serial.CurveModels.AffineNielsIdentity
public import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffineNielsPoint`: the identity `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem default_toAffineNiels :
    default ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for AffineNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffineNielsPoint`: the identity `(1, 1, 0)`, limbs `< 2^27`. -/
@[step]
theorem default_toAffineNiels :
    default ⦃ (r : AffineNielsPoint.«i686-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold default
  step*

/-- `Default for AffineNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffineNielsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono default_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«i686-tables».onCurve_iff,
      AffineNielsPoint.«i686-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault

namespace AffineNielsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for AffineNielsPoint`: the identity `(1, 1, 0)`, limbs `< 2^54`. -/
@[step]
theorem default_toAffineNiels :
    default ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for AffineNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«x86_64-no-tables».onCurve_iff,
      AffineNielsPoint.«x86_64-no-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace AffineNielsPoint.«i686-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for AffineNielsPoint`: the identity `(1, 1, 0)`, limbs `< 2^27`. -/
@[step]
theorem default_toAffineNiels :
    default ⦃ (r : AffineNielsPoint.«i686-no-tables») =>
      r.toAffineNiels = AffineNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold default
  step*

/-- `Default for AffineNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : AffineNielsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono default_toAffineNiels fun r ⟨hr, hb⟩ => by
    rw [AffineNielsPoint.«i686-no-tables».onCurve_iff,
      AffineNielsPoint.«i686-no-tables».toPoint_def, hr]
    exact ⟨AffineNiels.onCurve_identity, AffineNiels.toPoint_identity, hb⟩

end AffineNielsPoint.«i686-no-tables».Insts.CoreDefaultDefault

end Curve25519Dalek.backend.serial.curve_models
