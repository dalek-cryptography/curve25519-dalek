/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Zeroize.Instances
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Helpers.ToField2625
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem zeroize_spec (self : EdwardsPoint.«x86_64-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 52, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 52⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec_point (self : EdwardsPoint.«x86_64-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (zeroize_spec self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff,
      EdwardsPoint.«x86_64-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«i686-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem zeroize_spec (self : EdwardsPoint.«i686-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«i686-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 26, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 26⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec_point (self : EdwardsPoint.«i686-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (zeroize_spec self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-tables».onCurve_iff,
      EdwardsPoint.«i686-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«i686-tables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^52`. -/
@[step]
theorem zeroize_spec (self : EdwardsPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 52, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 52⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec_point (self : EdwardsPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ :=
  spec_mono (zeroize_spec self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      EdwardsPoint.«x86_64-no-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

namespace EdwardsPoint.«i686-no-tables».Insts.ZeroizeZeroize

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `Zeroize for EdwardsPoint`: reset to the identity `(0 : 1 : 1 : 0)`, limbs `< 2^26`. -/
@[step]
theorem zeroize_spec (self : EdwardsPoint.«i686-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.toExtended = Extended.identity ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step as ⟨X, hX⟩
  step as ⟨one, hone, hone_lt⟩
  step as ⟨T, hT⟩
  subst hX hT
  refine ⟨?_, ?_⟩
  · simp only [EdwardsPoint.«i686-no-tables».toExtended_def, Extended.identity,
      toField_eq_one_of_asNat hone, toField_repeat_zero]
  · exact ⟨limbs_repeat_zero_lt 26, limbs_lt_of_le (by decide) hone_lt,
      limbs_lt_of_le (by decide) hone_lt, limbs_repeat_zero_lt 26⟩

/-- `Zeroize for EdwardsPoint` leaves the neutral element. -/
theorem zeroize_spec_point (self : EdwardsPoint.«i686-no-tables») :
    zeroize self ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ :=
  spec_mono (zeroize_spec self) fun r ⟨hr, hb⟩ => by
    rw [EdwardsPoint.«i686-no-tables».onCurve_iff,
      EdwardsPoint.«i686-no-tables».toPoint_def,
      hr]
    exact ⟨Extended.onCurve_identity, Extended.toPoint_identity, hb⟩

end EdwardsPoint.«i686-no-tables».Insts.ZeroizeZeroize

end Curve25519Dalek.edwards
