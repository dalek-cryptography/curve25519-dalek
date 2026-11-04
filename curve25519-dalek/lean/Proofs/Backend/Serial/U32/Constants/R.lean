/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
import Proofs.Helpers.Scalar29
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29 montgomeryRadix)

namespace Curve25519Dalek.backend.serial.u32.constants

theorem R_spec :
    Scalar29.asNat R = montgomeryRadix % curve25519.L ∧ R.LimbsLt 29 := by
  unfold R
  simp only [scalar.Scalar29.asNat_def, Array.asNat_def]
  rw [scalar.montgomeryRadix_mod_L]
  decide

end Curve25519Dalek.backend.serial.u32.constants
