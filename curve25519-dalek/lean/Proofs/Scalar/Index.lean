/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Helpers.Array
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

@[step]
theorem index_spec (self : Scalar) (index : Usize) (hindex : index.val < 32) :
    CoreOpsIndexIndexUsizeU8.index self index ⦃ (r : U8) =>
      r = self.bytes[index.val]! ⦄ := by
  unfold CoreOpsIndexIndexUsizeU8.index
  step with Array.index_usize_getElem!_spec as ⟨r, hr⟩
  exact hr

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8
