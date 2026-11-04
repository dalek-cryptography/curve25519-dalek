/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519Dalek.Funs
public import Defs.Montgomery
public import Defs.Scalar
import Proofs.Edwards.MulBase
import Proofs.Edwards.ToMontgomery
import Proofs.Helpers.Target
public section

/-! # `MontgomeryPoint::mul_base`

`EdwardsPoint::mul_base` followed by `to_montgomery`: the `u`-coordinate of `scalar • B'` for the
Montgomery basepoint `B'` (`u = 9`), the image of `B` under `edwardsToMontgomery`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.montgomery.MontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically. -/
@[step]
theorem mul_base.«x86_64-tables_spec» (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base.«x86_64-tables» scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄ := by
  unfold mul_base.«x86_64-tables»
  step as ⟨ep, hep_on, hep, hep_lt⟩
  step with edwards.«EdwardsPointx86_64-tables».to_montgomery_spec_point ep hep_lt hep_on as ⟨r, hr⟩
  rw [hr, hep, map_nsmul, montgomeryBasepoint_def]

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically. -/
@[step]
theorem mul_base.«i686-tables_spec» (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base.«i686-tables» scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄ := by
  unfold mul_base.«i686-tables»
  step as ⟨ep, hep_on, hep, hep_lt⟩
  step with edwards.«EdwardsPointi686-tables».to_montgomery_spec_point ep hep_lt hep_on as ⟨r, hr⟩
  rw [hr, hep, map_nsmul, montgomeryBasepoint_def]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically. -/
@[step]
theorem mul_base.«x86_64-no-tables_spec» (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255)
    :
    mul_base.«x86_64-no-tables» scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄ := by
  unfold mul_base.«x86_64-no-tables»
  step as ⟨ep, hep_on, hep, hep_lt⟩
  step with edwards.«EdwardsPointx86_64-no-tables».to_montgomery_spec_point ep hep_lt hep_on as ⟨r,
      hr⟩
  rw [hr, hep, map_nsmul, montgomeryBasepoint_def]

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically. -/
@[step]
theorem mul_base.«i686-no-tables_spec» (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255)
    :
    mul_base.«i686-no-tables» scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄ := by
  unfold mul_base.«i686-no-tables»
  step as ⟨ep, hep_on, hep, hep_lt⟩
  step with edwards.«EdwardsPointi686-no-tables».to_montgomery_spec_point ep hep_lt hep_on as ⟨r,
      hr⟩
  rw [hr, hep, map_nsmul, montgomeryBasepoint_def]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::mul_base`: the `u`-coordinate of `scalar • B` on the Montgomery model
(unreduced, `< 2^255`), encoded canonically (x86_64 targets). -/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar) (hscalar : scalar.asNat < 2 ^ 255) :
    mul_base scalar ⦃ (r : MontgomeryPoint) =>
      r.asNat = encodeU (scalar.asNat • montgomeryBasepoint).u ⦄ := by
  unfold mul_base
  exact dispatch_all_spec
    (mul_base.«x86_64-tables_spec» scalar hscalar)
    (mul_base.«x86_64-no-tables_spec» scalar hscalar)
    (mul_base.«i686-tables_spec» scalar hscalar)
    (mul_base.«i686-no-tables_spec» scalar hscalar)

end Curve25519Dalek.montgomery.MontgomeryPoint
