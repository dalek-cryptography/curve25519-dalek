/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.FieldElement51
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.backend.serial.u64.field.FieldElement51
@[step]
theorem from_limbs_spec (limbs : Array U64 5#usize) :
    from_limbs limbs ⦃ (r : FieldElement51) =>
      r = limbs ⦄ := by
  unfold from_limbs
  step*
end Curve25519Dalek.backend.serial.u64.field.FieldElement51
