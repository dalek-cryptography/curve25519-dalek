/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Types
public section

/-! # `MontgomeryPoint`

A `MontgomeryPoint` is 32 bytes, the encoding of a `u`-coordinate; the theorems use them through
`Array.toVector`. Only the default value is needed here. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek.montgomery

/-- Needed for `v[i]!` on vectors of points; the default is never observed for in-range
indices. -/
instance MontgomeryPoint.instInhabited : Inhabited MontgomeryPoint :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

end Curve25519Dalek.montgomery
