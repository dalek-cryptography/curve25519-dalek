/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar52
public import Defs.FieldElement51
public import Defs.Scalar
import Proofs.Helpers.Montgomery
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar.Scalar52

theorem ZERO_spec :
    Scalar52.asNat ZERO = 0 ∧ ZERO.LimbsLt 52 := by
  unfold ZERO
  simp only [scalar.Scalar52.asNat_def, Array.asNat_def]
  decide

end Curve25519Dalek.backend.serial.u64.scalar.Scalar52
