/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- An array whose first `m` digits are those of `b` and whose other digits are zero has the
value of `b`. -/
private theorem Aeneas.Std.Array.asNat_eq_of_prefix {ty : UScalarTy} {n m : Usize} (bits : ℕ)
    (a : Array (UScalar ty) n) (b : Array (UScalar ty) m) (hmn : m.val ≤ n.val)
    (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (hz : ∀ j, m.val ≤ j → j < n.val → a[j]!.val = 0) :
    a.asNat bits = b.asNat bits := by
  rw [Array.asNat_eq_sum, Array.asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn]
  have h0 : ∑ j ∈ Finset.Ico m.val n.val, 2 ^ (bits * j) * a[j]!.val = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_Ico] at hj
      rw [hz j hj.1 hj.2, Nat.mul_zero]
  rw [h0, Nat.add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]

namespace Curve25519Dalek.scalar.HalfWidthScalar

open scoped Helpers.IndexStep Helpers.UpdateStep in
/-- The loop of `from_bytes` copies the 16 bytes to the front of the zero array. -/
@[local step]
private theorem from_bytes_loop_spec (bytes : Array U8 16#usize) (s_bytes : Array U8 32#usize)
    (i : Usize) (hi : i.val ≤ 16) (hlo : ∀ j < i.val, s_bytes[j]! = bytes[j]!)
    (hhi : ∀ j, i.val ≤ j → j < 32 → s_bytes[j]! = 0#u8) :
    from_bytes_loop bytes s_bytes i ⦃ (r : Array U8 32#usize) =>
      (∀ j : ℕ, j < 16 → r[j]! = bytes[j]!) ∧ ∀ j : ℕ, 16 ≤ j → j < 32 → r[j]! = 0#u8 ⦄ := by
  unfold from_bytes_loop
  apply loop.spec_decr_nat (measure := fun (_, i) => 16 - i.val)
    (inv := fun (s, i) => i.val ≤ 16 ∧ (∀ j < i.val, s[j]! = bytes[j]!) ∧
      ∀ j, i.val ≤ j → j < 32 → s[j]! = 0#u8)
  · rintro ⟨s, k⟩ ⟨hk, hslo, hshi⟩
    unfold from_bytes_loop.body
    by_cases hlt : k.val < 16
    · simp only [show k < 16#usize by scalar_tac, ite_true]
      step as ⟨x, hx⟩
      step as ⟨s1, hs1, hs1ne⟩
      step as ⟨k1, hk1⟩
      refine ⟨by scalar_tac, fun j hj => ?_, fun j hj hj32 => ?_, by scalar_tac⟩
      · by_cases hjk : j = k.val
        · rw [hjk, hs1, hx]
        · rw [hs1ne j hjk]
          exact hslo j (by scalar_tac)
      · rw [hs1ne j (by scalar_tac)]
        exact hshi j (by scalar_tac) hj32
    · simp only [show ¬ k < 16#usize by scalar_tac, ite_false, WP.spec_ok]
      exact ⟨fun j hj => hslo j (by scalar_tac), fun j hj hj32 => hshi j (by scalar_tac) hj32⟩
  · exact ⟨hi, hlo, hhi⟩

@[step]
theorem from_bytes_spec (bytes : Array U8 16#usize) :
    from_bytes bytes ⦃ (r : HalfWidthScalar) =>
      r.asNat = bytes.asNat 8 ⦄ := by
  unfold from_bytes
  step with from_bytes_loop_spec as ⟨r, hlo, hhi⟩
  · intro j _ hj
    rw [Array.getElem!_Nat_eq, Array.repeat_val, List.getElem!_replicate _ (by simpa using hj)]
  · rw [HalfWidthScalar.asNat_def, Scalar.asNat_def]
    exact Array.asNat_eq_of_prefix 8 r bytes (by simp)
      (fun j hj => by rw [hlo j hj]) (fun j hj hj32 => by rw [hhi j hj hj32]; rfl)

end Curve25519Dalek.scalar.HalfWidthScalar
