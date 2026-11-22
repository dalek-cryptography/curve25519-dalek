/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Proofs.Curve25519.Ristretto.Encoding
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Array
import Proofs.Curve25519.Ristretto.Even
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

namespace «64bit-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«64bit-tables» ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«64bit-tables»
  step with backend.serial.u64.constants.«64bit-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^54`. -/
@[step]
theorem RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«64bit-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«64bit-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.LimbsLt 54 ⦄ := by
  unfold RISTRETTO_BASEPOINT_TABLE.«64bit-tables»
  step with backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_spec as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «64bit-tables»

namespace «32bit-tables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«32bit-tables» ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«32bit-tables»
  step with backend.serial.u32.constants.«32bit-tables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

/-- `RISTRETTO_BASEPOINT_TABLE`: a table representing the basepoint; limbs `< 2^27`. -/
@[step]
theorem RISTRETTO_BASEPOINT_TABLE_spec :
    RISTRETTO_BASEPOINT_TABLE.«32bit-tables»
      ⦃ (r : ristretto.RistrettoBasepointTable.«32bit-tables») =>
        r.IsTable ∧ r.point = basepoint ∧ r.LimbsLt 27 ⦄ := by
  unfold RISTRETTO_BASEPOINT_TABLE.«32bit-tables»
  step with backend.serial.u32.constants.ED25519_BASEPOINT_TABLE_spec as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end «32bit-tables»

namespace «64bit-notables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^52`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«64bit-notables»
      ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 52 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«64bit-notables»
  step with backend.serial.u64.constants.«64bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

end «64bit-notables»

namespace «32bit-notables»

/-- `RISTRETTO_BASEPOINT_POINT`: the basepoint, an even point (a ristretto255 representative);
limbs `< 2^26`. -/
@[step]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT.«32bit-notables»
      ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
        r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = basepoint ∧ r.LimbsLt 26 ⦄ := by
  unfold RISTRETTO_BASEPOINT_POINT.«32bit-notables»
  step with backend.serial.u32.constants.«32bit-notables».ED25519_BASEPOINT_POINT_spec
    as ⟨r, h1, h2, h3⟩
  exact ⟨h1, by rw [h2]; exact even_basepoint, h2, h3⟩

end «32bit-notables»

end Curve25519Dalek.constants
