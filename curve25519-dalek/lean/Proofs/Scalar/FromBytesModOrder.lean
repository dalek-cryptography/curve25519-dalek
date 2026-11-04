/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Helpers.Scalar
import Proofs.Scalar.Index
import Proofs.Scalar.Reduce
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem from_bytes_mod_order_spec (bytes : Array U8 32#usize) :
    from_bytes_mod_order bytes ⦃ (r : Scalar) =>
      r.asNat = bytes.asNat 8 % L ⦄ := by
  unfold from_bytes_mod_order
  step as ⟨s, hs⟩
  have hsL : s.asNat < L := hs ▸ Nat.mod_lt _ L_pos
  step as ⟨i, hi⟩
  have hi31 : i.val < 2 ^ 5 := hi ▸ Scalar.bytes_31_lt (hsL.trans L_lt_two_pow_253)
  step*
  simpa only [Scalar.asNat_def] using hs

end Curve25519Dalek.scalar.Scalar
