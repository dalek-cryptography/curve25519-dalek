/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Theodore Ehrenborg, Liao Zhang
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Basic
public import Defs.Scalar52
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.scalar (Scalar52)

namespace Curve25519Dalek.backend.serial.u64.scalar

@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ := by
  unfold m
  step*

/-- `m` on a 53-bit and a 52-bit factor, with the bound on the product (for the limb products,
activated with `open scoped Helpers.MLtStep`). -/
theorem m_lt_spec (x y : U64) (hx : x.val < 2 ^ 53) (hy : y.val < 2 ^ 52) :
    m x y ⦃ (r : U128) => r.val = x.val * y.val ∧ r.val < 2 ^ 105 ⦄ := by
  step*

end Curve25519Dalek.backend.serial.u64.scalar

/- Registered once, here; activated with `open scoped Helpers.MLtStep`. -/
namespace Helpers.MLtStep
attribute [scoped step] Curve25519Dalek.backend.serial.u64.scalar.m_lt_spec
end Helpers.MLtStep
