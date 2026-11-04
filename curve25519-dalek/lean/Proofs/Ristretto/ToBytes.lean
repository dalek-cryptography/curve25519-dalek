/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Ristretto
public section

/-! # `CompressedRistretto::to_bytes` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.CompressedRistretto

/-- `CompressedRistretto::to_bytes`: the bytes. -/
@[step]
theorem to_bytes_spec (self : CompressedRistretto) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄ := by
  unfold to_bytes
  step*

end Curve25519Dalek.ristretto.CompressedRistretto
