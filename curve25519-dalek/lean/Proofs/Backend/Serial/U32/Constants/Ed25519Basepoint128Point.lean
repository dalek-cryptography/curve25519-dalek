/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import all Curve25519.Basic
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.Coords
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.TableCertificate
public section

/-! # `ED25519_BASEPOINT_128_POINT`

The point `2^128 • B` in extended coordinates, certified by kernel computation: its coordinates
satisfy the curve equation and are projectively equal to `128` doublings of `B`
(`Proofs.Helpers.TableCertificate.checkPoint`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625
open Curve25519Dalek.TableCertificate

namespace Curve25519Dalek.backend.serial.u32.constants

namespace «i686-tables»

private theorem of_check (r : edwards.EdwardsPoint.«i686-tables»)
    (h : checkPoint edwards r.toExtended 128 = true) :
    r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint := by
  rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-tables».toPoint_def]
  exact checkPoint_sound h

/-- `ED25519_BASEPOINT_128_POINT`: the point `2^128 • B`; limbs `< 2^26`. -/
@[step]
theorem ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«i686-tables»
      ⦃ (r : edwards.EdwardsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold ED25519_BASEPOINT_128_POINT.«i686-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have key := of_check { X := X, Y := Y, Z := Z, T := T } (by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def]
    subst hX hY hZ hT
    simp only [toField_def, asNat_def, Array.asNat2625_make]
    rw [curve25519.Proofs.edwards_eq]
    decide +kernel)
  refine ⟨key.1, key.2, ?_⟩
  unfold edwards.EdwardsPoint.«i686-tables».LimbsLt
  subst hX hY hZ hT
  decide

end «i686-tables»

namespace «i686-no-tables»

private theorem of_check (r : edwards.EdwardsPoint.«i686-no-tables»)
    (h : checkPoint edwards r.toExtended 128 = true) :
    r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint := by
  rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-no-tables».toPoint_def]
  exact checkPoint_sound h

/-- `ED25519_BASEPOINT_128_POINT`: the point `2^128 • B`; limbs `< 2^26`. -/
@[step]
theorem ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«i686-no-tables»
      ⦃ (r : edwards.EdwardsPoint.«i686-no-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold ED25519_BASEPOINT_128_POINT.«i686-no-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have key := of_check { X := X, Y := Y, Z := Z, T := T } (by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
    subst hX hY hZ hT
    simp only [toField_def, asNat_def, Array.asNat2625_make]
    rw [curve25519.Proofs.edwards_eq]
    decide +kernel)
  refine ⟨key.1, key.2, ?_⟩
  unfold edwards.EdwardsPoint.«i686-no-tables».LimbsLt
  subst hX hY hZ hT
  decide

end «i686-no-tables»

end Curve25519Dalek.backend.serial.u32.constants
