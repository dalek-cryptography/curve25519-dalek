/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Scalar
public import Defs.Scalar52
import Proofs.Helpers.AsNat
import Subtle
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

/-- The first `m` digits of an array, with digits below `2 ^ bits`, give its value modulo
`2 ^ (bits * m)`. -/
private theorem Aeneas.Std.Array.asNat_mod_of_prefix {ty : UScalarTy} {n m : Usize} (bits : ℕ)
    (a : Array (UScalar ty) n) (b : Array (UScalar ty) m) (hmn : m.val ≤ n.val)
    (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits % 2 ^ (bits * m.val) = b.asNat bits := by
  rw [Array.asNat_mod_pow_eq_sum bits m.val a hmn ha, Array.asNat_eq_sum]
  exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]

namespace Curve25519Dalek.scalar.HalfWidthScalar

@[step]
theorem to_bytes_spec (self : HalfWidthScalar) :
    to_bytes self ⦃ (r : Array U8 16#usize) =>
      r.asNat 8 = self.asNat % 2 ^ 128 ⦄ := by
  unfold to_bytes
  step as ⟨s, back, hs, hback⟩
  step as ⟨s1, hs1, hs1len⟩
  step as ⟨s2, hs2⟩
  rw [HalfWidthScalar.asNat_def, Scalar.asNat_def]
  refine (Array.asNat_mod_of_prefix 8 self.bytes _ (by simp) (fun j hj => ?_)
    (fun j _ => (self.bytes[j]!).hBounds)).symm
  have hj16 : j < 16 := by simpa using hj
  simp [hback, hs2, hs1, Array.from_slice, List.getElem?_take_of_lt hj16]

end Curve25519Dalek.scalar.HalfWidthScalar
