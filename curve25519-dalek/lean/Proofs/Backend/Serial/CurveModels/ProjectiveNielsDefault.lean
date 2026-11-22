/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.CurveModels
import Proofs.Backend.Serial.CurveModels.ProjectiveNielsIdentity
public import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.backend.serial.curve_models

namespace ProjectiveNielsPoint.«64bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem default_toProjectiveNiels :
    default ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«64bit-tables».Insts.CoreDefaultDefault

namespace ProjectiveNielsPoint.«32bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^27`. -/
@[step]
theorem default_toProjectiveNiels :
    default ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono default_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-tables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-tables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«32bit-tables».Insts.CoreDefaultDefault

namespace ProjectiveNielsPoint.«64bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^54`. -/
@[step]
theorem default_toProjectiveNiels :
    default ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 54 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 54 ⦄ :=
  spec_mono default_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«64bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«64bit-notables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«64bit-notables».Insts.CoreDefaultDefault

namespace ProjectiveNielsPoint.«32bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for ProjectiveNielsPoint`: the identity `(1 : 1 : 1 : 0)`, limbs `< 2^27`. -/
@[step]
theorem default_toProjectiveNiels :
    default ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.toProjectiveNiels = ProjectiveNiels.identity ∧ r.LimbsLt 27 ⦄ := by
  unfold default
  step*

/-- `Default for ProjectiveNielsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 27 ⦄ :=
  spec_mono default_toProjectiveNiels fun r ⟨hr, hb⟩ => by
    rw [ProjectiveNielsPoint.«32bit-notables».onCurve_iff,
      ProjectiveNielsPoint.«32bit-notables».toPoint_def, hr]
    exact ⟨ProjectiveNiels.onCurve_identity, ProjectiveNiels.toPoint_identity, hb⟩

end ProjectiveNielsPoint.«32bit-notables».Insts.CoreDefaultDefault

end Curve25519Dalek.backend.serial.curve_models
