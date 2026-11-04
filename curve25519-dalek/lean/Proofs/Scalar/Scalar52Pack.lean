/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Curve25519.Basic
import Proofs.Backend.Serial.U64.Scalar.ToBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar52

@[step]
theorem pack_spec (self : backend.serial.u64.scalar.Scalar52)
    (hself : self.LimbsLt 52) (hself' : self.asNat < 2 ^ 256) :
    pack self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄ := by
  unfold pack
  step as ⟨r, hr⟩
  simpa only [scalar.Scalar.asNat_def, backend.serial.u64.scalar.Scalar52.asNat_def] using hr

end Curve25519Dalek.scalar.Scalar52
