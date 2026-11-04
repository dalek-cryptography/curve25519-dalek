/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar29
import Curve25519.Basic
import Proofs.Backend.Serial.U32.Scalar.ToBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u32.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar29

@[step]
theorem pack_spec (self : backend.serial.u32.scalar.Scalar29)
    (hself : self.LimbsLt 29) (hself' : self.asNat < 2 ^ 256) :
    pack self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄ := by
  unfold pack
  step as ⟨r, hr⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u32.scalar.Scalar29.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar29
