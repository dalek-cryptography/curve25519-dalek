/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Helpers.AsNat
import Proofs.Helpers.Array
public import Proofs.Helpers.ByteValues
public section

/-! # The bytes of a `CompressedEdwardsY`

Its value is below `2^256`, and the top bit of its last byte is bit `255` of the value (the sign
bit of `decompress`). -/

open curve25519 TwistedEdwardsModel

namespace Curve25519Dalek.edwards

namespace CompressedEdwardsY

theorem asNat_lt (self : CompressedEdwardsY) : self.asNat < 2 ^ 256 := by
  rw [asNat_def]
  exact Aeneas.Std.Array.asNat_lt 8 self fun i _ => by scalar_tac

theorem asNat_div_two_pow_le_one (self : CompressedEdwardsY) : self.asNat / 2 ^ 255 ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact self.asNat_lt))

/-- The top bit of the last byte is bit `255` of the value. -/
theorem getElem!_31_shiftRight_7 (self : CompressedEdwardsY) :
    self[31]!.val >>> 7 = self.asNat / 2 ^ 255 := by
  have h := Aeneas.Std.Array.getElem!_last_eq_asNat_div 8 self (fun i _ => by scalar_tac)
    (by decide)
  rw [show (32#usize).val - 1 = 31 from rfl] at h
  rw [h, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, asNat_def]
  norm_num

end CompressedEdwardsY

end Curve25519Dalek.edwards
