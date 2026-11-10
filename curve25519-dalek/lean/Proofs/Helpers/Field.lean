/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
public section

/-! # Lemmas shared by the proofs of `field.rs` -/

namespace Curve25519Dalek.field

open curve25519

theorem one_mod_p : 1 % p = 1 :=
  Nat.mod_eq_of_lt (by have := p_add_nineteen; omega)

end Curve25519Dalek.field
