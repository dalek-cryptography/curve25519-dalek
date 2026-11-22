/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
public import Proofs.Representation.Scalar29
public import Proofs.Representation.Scalar52
import Proofs.Backend.Serial.U64.Scalar.FromBytes
import Proofs.Backend.Serial.U32.Scalar.FromBytes
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«64bit-tables_spec» (self : Scalar) :
    unpack.«64bit-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ r.LimbsLt 52 ⦄ := by
  unfold unpack.«64bit-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u64.scalar.Scalar52.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«64bit-notables_spec» (self : Scalar) :
    unpack.«64bit-notables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ r.LimbsLt 52 ⦄ := by
  unfold unpack.«64bit-notables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u64.scalar.Scalar52.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«32bit-tables_spec» (self : Scalar) :
    unpack.«32bit-tables» self ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      r.asNat = self.asNat ∧ r.LimbsLt 29 ⦄ := by
  unfold unpack.«32bit-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u32.scalar.Scalar29.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«32bit-notables_spec» (self : Scalar) :
    unpack.«32bit-notables» self ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      r.asNat = self.asNat ∧ r.LimbsLt 29 ⦄ := by
  unfold unpack.«32bit-notables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u32.scalar.Scalar29.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar
