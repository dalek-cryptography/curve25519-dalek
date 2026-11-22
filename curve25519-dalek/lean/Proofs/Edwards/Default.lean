/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.Identity
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«64bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem default_toExtended :
    default ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono default_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-tables».onCurve_iff,
      EdwardsPoint.«64bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-tables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«32bit-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem default_toExtended :
    default ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono default_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-tables».onCurve_iff,
      EdwardsPoint.«32bit-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-tables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«64bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem default_toExtended :
    default ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono default_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«64bit-notables».onCurve_iff,
      EdwardsPoint.«64bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«64bit-notables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«32bit-notables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem default_toExtended :
    default ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono default_toExtended fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«32bit-notables».onCurve_iff,
      EdwardsPoint.«32bit-notables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«32bit-notables».Insts.CoreDefaultDefault

end Curve25519Dalek.edwards
