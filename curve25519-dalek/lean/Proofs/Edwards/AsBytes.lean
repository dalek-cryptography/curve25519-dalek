/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::as_bytes`: the bytes. -/
@[step]
theorem as_bytes_spec (self : CompressedEdwardsY) :
    as_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄ := by
  unfold as_bytes
  step*

end Curve25519Dalek.edwards.CompressedEdwardsY
