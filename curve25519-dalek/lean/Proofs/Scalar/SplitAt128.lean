/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Scalar
import Proofs.Helpers.AsNat
import Proofs.Scalar.HalfWidthFromBytes
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- Splitting the digits of an array into its first `m` and its last `k` digits. -/
private theorem Aeneas.Std.Array.asNat_eq_split {ty : UScalarTy} {n m k : Usize} (bits : ℕ)
    (a : Array (UScalar ty) n) (b : Array (UScalar ty) m) (c : Array (UScalar ty) k)
    (h : m.val + k.val = n.val) (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (hc : ∀ j < k.val, a[m.val + j]!.val = c[j]!.val) :
    a.asNat bits = b.asNat bits + 2 ^ (bits * m.val) * c.asNat bits := by
  rw [Array.asNat_eq_sum, Array.asNat_eq_sum, Array.asNat_eq_sum, ← h, Finset.sum_range_add,
    Finset.mul_sum]
  fcongr 1
  · exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [hc j (Finset.mem_range.mp hj), Nat.mul_add, Nat.pow_add, Nat.mul_assoc]

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem split_at_128_spec (self : Scalar) :
    split_at_128 self ⦃ (lo hi : HalfWidthScalar) =>
      lo.asNat + 2 ^ 128 * hi.asNat = self.asNat ∧ lo.asNat < 2 ^ 128 ∧ hi.asNat < 2 ^ 128 ⦄ := by
  unfold split_at_128
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, hs1, hs1len⟩
  step as ⟨s2, hs2⟩
  step as ⟨s3, back1, hs3, hback1⟩
  step as ⟨s4, hs4, hs4len⟩
  step as ⟨s5, hs5⟩
  step as ⟨lo, hlo⟩
  step as ⟨hi, hhi⟩
  have hsplit := Array.asNat_eq_split 8 self.bytes (back s2) (back1 s5) (by simp)
    (fun j hj => ?_) (fun j hj => ?_)
  · rw [hlo, hhi, Scalar.asNat_def, hsplit]
    have hlt (a : Array U8 16#usize) : a.asNat 8 < 2 ^ 128 :=
      Array.asNat_lt 8 a fun j _ => (a[j]!).hBounds
    exact ⟨rfl, hlt _, hlt _⟩
  · have hj16 : j < 16 := by simpa using hj
    simp [hback, hs2, hs1, Array.from_slice, List.getElem?_take_of_lt hj16]
  · simp [hback1, hs5, hs4, Array.from_slice]

end Curve25519Dalek.scalar.Scalar
