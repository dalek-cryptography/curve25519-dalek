/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar.Scalar29

theorem ZERO_spec :
    Scalar29.asNat ZERO = 0 ∧ ZERO.LimbsLt 29 := by
  unfold ZERO
  simp only [scalar.Scalar29.asNat_def, Array.asNat_def]
  decide

end Curve25519Dalek.backend.serial.u32.scalar.Scalar29
