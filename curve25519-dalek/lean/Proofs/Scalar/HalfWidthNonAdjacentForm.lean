/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Scalar.NonAdjacentForm
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.HalfWidthScalar

@[step]
theorem non_adjacent_form_spec (self : HalfWidthScalar) (w : Usize)
    (hw : 2 ≤ w.val ∧ w.val ≤ 8) (hself : self.asNat < 2 ^ 255) :
    non_adjacent_form self w ⦃ (r : Array I8 256#usize) =>
      r.asInt 1 = self.asNat ∧
      (∀ i : ℕ, i < 256 → r[i]!.val ≠ 0 → r[i]!.val % 2 = 1 ∧ 2 * |r[i]!.val| < 2 ^ w.val) ∧
      ∀ i : ℕ, i < 256 → ∀ j : ℕ, j < 256 → i < j → j < i + w.val → r[i]!.val ≠ 0 →
        r[j]!.val = 0 ⦄ := by
  unfold non_adjacent_form
  simpa only [scalar.HalfWidthScalar.asNat_def] using
    Scalar.non_adjacent_form_spec self w hw
      (by simpa only [scalar.HalfWidthScalar.asNat_def] using hself)

end Curve25519Dalek.scalar.HalfWidthScalar
