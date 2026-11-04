/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Edwards.Identity
import Proofs.Helpers.Coords
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff,
      EdwardsPoint.«x86_64-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«x86_64-tables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«i686-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-tables».onCurve_iff,
      EdwardsPoint.«i686-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«i686-tables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      EdwardsPoint.«x86_64-no-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«x86_64-no-tables».Insts.CoreDefaultDefault

namespace EdwardsPoint.«i686-no-tables».Insts.CoreDefaultDefault

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Default for EdwardsPoint`: the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem default_spec :
    default ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold default
  step*

/-- `Default for EdwardsPoint` represents the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono default_spec fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-no-tables».onCurve_iff,
      EdwardsPoint.«i686-no-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«i686-no-tables».Insts.CoreDefaultDefault

end Curve25519Dalek.edwards
