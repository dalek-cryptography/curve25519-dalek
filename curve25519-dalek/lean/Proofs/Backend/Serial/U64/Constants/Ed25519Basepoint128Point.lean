/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basepoint
public import Curve25519Dalek.Funs
public import Defs.Edwards
import all Curve25519.Basic
import Proofs.Backend.Serial.U64.Field.FromLimbs
import Proofs.Helpers.Coords
import Proofs.Helpers.TableCertificate
public import Proofs.Helpers.ByteValues
public section

/-! # `ED25519_BASEPOINT_128_POINT`

The point `2^128 • B` in extended coordinates, certified by kernel computation: its coordinates
satisfy the curve equation and are projectively equal to `128` doublings of `B`
(`Proofs.Helpers.TableCertificate.checkPoint`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u64.field.FieldElement51
open Curve25519Dalek.TableCertificate

namespace Curve25519Dalek.backend.serial.u64.constants

namespace «x86_64-tables»

private theorem of_check (r : edwards.EdwardsPoint.«x86_64-tables»)
    (h : checkPoint edwards r.toExtended 128 = true) :
    r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint := by
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toPoint_def]
  exact checkPoint_sound h

/-- `ED25519_BASEPOINT_128_POINT`: the point `2^128 • B`; limbs `< 2^52`. -/
@[step]
theorem ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«x86_64-tables»
      ⦃ (r : edwards.EdwardsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold ED25519_BASEPOINT_128_POINT.«x86_64-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have key := of_check { X := X, Y := Y, Z := Z, T := T } (by
    rw [edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
    subst hX hY hZ hT
    simp only [toField_def, asNat_def, Array.asNat_def, Array.make_val]
    rw [curve25519.Proofs.edwards_eq]
    decide +kernel)
  refine ⟨key.1, key.2, ?_⟩
  unfold edwards.EdwardsPoint.«x86_64-tables».LimbsLt
  subst hX hY hZ hT
  decide

end «x86_64-tables»

namespace «x86_64-no-tables»

private theorem of_check (r : edwards.EdwardsPoint.«x86_64-no-tables»)
    (h : checkPoint edwards r.toExtended 128 = true) :
    r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint := by
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def]
  exact checkPoint_sound h

/-- `ED25519_BASEPOINT_128_POINT`: the point `2^128 • B`; limbs `< 2^52`. -/
@[step]
theorem ED25519_BASEPOINT_128_POINT_spec :
    ED25519_BASEPOINT_128_POINT.«x86_64-no-tables»
      ⦃ (r : edwards.EdwardsPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = 2 ^ 128 • basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold ED25519_BASEPOINT_128_POINT.«x86_64-no-tables»
  step as ⟨X, hX⟩
  step as ⟨Y, hY⟩
  step as ⟨Z, hZ⟩
  step as ⟨T, hT⟩
  have key := of_check { X := X, Y := Y, Z := Z, T := T } (by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
    subst hX hY hZ hT
    simp only [toField_def, asNat_def, Array.asNat_def, Array.make_val]
    rw [curve25519.Proofs.edwards_eq]
    decide +kernel)
  refine ⟨key.1, key.2, ?_⟩
  unfold edwards.EdwardsPoint.«x86_64-no-tables».LimbsLt
  subst hX hY hZ hT
  decide

end «x86_64-no-tables»

end Curve25519Dalek.backend.serial.u64.constants
