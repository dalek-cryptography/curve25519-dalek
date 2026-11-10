/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Theodore Ehrenborg, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar29
public import Curve25519.Basic
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u32.scalar (Scalar29)

namespace Curve25519Dalek.backend.serial.u32.scalar

@[step]
theorem m_spec (x y : U32) :
    m x y ⦃ (r : U64) =>
      r.val = x.val * y.val ⦄ := by
  unfold m
  step*

/-- `m` on factors below `2 ^ 30` (limbs, and sums of two limbs). -/
theorem m_lt_spec (x y : U32) (hx : x.val < 2 ^ 30) (hy : y.val < 2 ^ 30) :
    m x y ⦃ (r : U64) => r.val = x.val * y.val ∧ r.val < 2 ^ 60 ⦄ := by
  step*

end Curve25519Dalek.backend.serial.u32.scalar

/- Registered once, here; activated with `open scoped Helpers.M32LtStep`. -/
namespace Helpers.M32LtStep
attribute [scoped step] Curve25519Dalek.backend.serial.u32.scalar.m_lt_spec
end Helpers.M32LtStep
