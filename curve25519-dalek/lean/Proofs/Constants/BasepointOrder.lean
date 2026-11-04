/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public section

open Aeneas Aeneas.Std

namespace Curve25519Dalek.constants

/-- `BASEPOINT_ORDER`: the bytes of the group order `L` (an unreduced `Scalar`). -/
theorem BASEPOINT_ORDER_spec : BASEPOINT_ORDER.asNat = curve25519.L := by
  unfold BASEPOINT_ORDER
  rw [scalar.Scalar.asNat_def, Array.asNat_def, Array.make_val, curve25519.L_eq_numeral]
  decide

end Curve25519Dalek.constants
