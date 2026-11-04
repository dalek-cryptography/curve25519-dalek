/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Subtle
import Proofs.Helpers.Array
import Proofs.Helpers.Scalar
import Proofs.Scalar.IsCanonical
import Subtle.Lemmas
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem from_canonical_bytes_spec (bytes : Array U8 32#usize) :
    from_canonical_bytes bytes ⦃ (r : subtle.CtOption Scalar) =>
      r.is_some.IsValid ∧ r.value.bytes = bytes ∧
      (bytes.asNat 8 < L → r.is_some = 1#u8) ∧ (L ≤ bytes.asNat 8 → r.is_some = 0#u8) ⦄ := by
  unfold from_canonical_bytes
  step with Array.index_usize_getElem!_spec as ⟨i, hi⟩
  step as ⟨i1, hi1, _⟩
  step as ⟨hb, hbv, hbeq⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c1, hc1v, hc1eq⟩
  step as ⟨r, hr⟩
  subst hr
  refine ⟨hc1v, rfl, fun h => ?_, fun h => ?_⟩
  · have hS : Scalar.asNat ⟨bytes⟩ < L := by rw [Scalar.asNat_def]; exact h
    have hi31 : i.val < 2 ^ 5 := hi ▸ Scalar.bytes_31_lt (s := ⟨bytes⟩) (hS.trans L_lt_two_pow_253)
    have hi10 : i1 = 0#u8 := by
      apply UScalar.eq_of_val_eq
      rw [hi1, Nat.shiftRight_eq_div_pow]
      simp only [UScalar.ofNatCore_val_eq]
      omega
    rw [hc1eq, hbeq, ite_eq_left hi10, hc1 hS]
    rfl
  · rw [hc1eq, hc0 (by rw [Scalar.asNat_def]; exact h), hbv.and_zero]

end Curve25519Dalek.scalar.Scalar
