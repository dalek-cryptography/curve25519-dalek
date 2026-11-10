/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519.Ristretto.Encoding
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Ristretto
import Curve25519.Ristretto.Even
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U64.Constants.Ed25519BasepointTable
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointPoint
import Proofs.Backend.Serial.U32.Constants.Ed25519BasepointTable
public import Proofs.Helpers.ByteValues
public section

/-! # The Ristretto basepoint constants

`RISTRETTO_BASEPOINT_POINT` and `RISTRETTO_BASEPOINT_TABLE` are the Ed25519 basepoint and its
table (`RistrettoPoint` and `RistrettoBasepointTable` are aliases of the Edwards types);
`RISTRETTO_BASEPOINT_COMPRESSED` is RFC 9496's encoding of that point. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.constants

/-- `RISTRETTO_BASEPOINT_COMPRESSED`: RFC 9496's encoding of the basepoint. -/
theorem RISTRETTO_BASEPOINT_COMPRESSED_spec :
    RISTRETTO_BASEPOINT_COMPRESSED.toVector = Ristretto.encodeRep basepoint := by
  simp only [Curve25519Dalek.ristretto.CompressedRistretto.toVector_eq_encodeRep_iff]
  unfold RISTRETTO_BASEPOINT_COMPRESSED
  rw [ristretto.CompressedRistretto.asNat_def, Array.asNat_def, Array.make_val,
    Ristretto.encodeRepNat_basepoint]
  decide

namespace «x86_64-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-tables» ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«x86_64-tables»
  step with backend.serial.u64.constants.«x86_64-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^54`. -/
@[step]
theorem RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«x86_64-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«x86_64-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.LimbsLt 54 ⦄ := by
  unfold RISTRETTO_BASEPOINT_TABLE.«x86_64-tables»
  step with backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_spec as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «x86_64-tables»

namespace «i686-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-tables» ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«i686-tables»
  step with backend.serial.u32.constants.«i686-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^27`. -/
@[step]
theorem RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«i686-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«i686-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.LimbsLt 27 ⦄ := by
  unfold RISTRETTO_BASEPOINT_TABLE.«i686-tables»
  step with backend.serial.u32.constants.ED25519_BASEPOINT_TABLE_spec as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «i686-tables»

namespace «x86_64-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«x86_64-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«x86_64-no-tables»
  step with backend.serial.u64.constants.«x86_64-no-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

end «x86_64-no-tables»

namespace «i686-no-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«i686-no-tables»
      ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«i686-no-tables»
  step with backend.serial.u32.constants.«i686-no-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

end «i686-no-tables»

end Curve25519Dalek.constants
