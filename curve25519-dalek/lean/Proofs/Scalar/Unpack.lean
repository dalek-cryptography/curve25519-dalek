/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Hoang Le Truong
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
public import Defs.Scalar52
import Proofs.Backend.Serial.U64.Scalar.FromBytes
import Proofs.Backend.Serial.U32.Scalar.FromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-tables_spec» (self : Scalar) :
    unpack.«x86_64-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ r.LimbsLt 52 ⦄ := by
  unfold unpack.«x86_64-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u64.scalar.Scalar52.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«x86_64-no-tables_spec» (self : Scalar) :
    unpack.«x86_64-no-tables» self ⦃ (r : backend.serial.u64.scalar.Scalar52) =>
      r.asNat = self.asNat ∧ r.LimbsLt 52 ⦄ := by
  unfold unpack.«x86_64-no-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u64.scalar.Scalar52.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«i686-tables_spec» (self : Scalar) :
    unpack.«i686-tables» self ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      r.asNat = self.asNat ∧ r.LimbsLt 29 ⦄ := by
  unfold unpack.«i686-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u32.scalar.Scalar29.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem unpack.«i686-no-tables_spec» (self : Scalar) :
    unpack.«i686-no-tables» self ⦃ (r : backend.serial.u32.scalar.Scalar29) =>
      r.asNat = self.asNat ∧ r.LimbsLt 29 ⦄ := by
  unfold unpack.«i686-no-tables»
  step as ⟨r, hr, hrb⟩
  refine ⟨?_, hrb⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u32.scalar.Scalar29.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar
