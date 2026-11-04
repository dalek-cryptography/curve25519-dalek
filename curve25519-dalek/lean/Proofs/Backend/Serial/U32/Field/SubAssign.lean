/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Némedy Varga
-/
module
public import Curve25519Dalek.Funs
public import Defs.FieldElement2625
public import Proofs.Helpers.FieldElement2625
import Proofs.Backend.Serial.U32.Field.Reduce
public section

/-!
# Spec theorem for `sub_assign`

`sub_assign self rhs` computes `self - rhs` as `(self + 16 * p) - rhs` limbwise in `u32`, to
avoid underflow. The limbs of `16 * p` in the alternating `2^26/2^25` radix are
`0x3ffffed << 4` for limb `0`, `0x1ffffff << 4` for odd limbs and `0x3ffffff << 4` for the other
even limbs. The ten differences are widened to `u64` and passed to `reduce`, so the result
represents `self - rhs` modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 87:4-105:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
namespace CoreOpsArithSubAssignSharedBFieldElement2625

-- Note: the arithmetic also admits a looser bound (rhs[i] < 8 * 2^26, roughly);
-- 3 * 2^26 is kept to match mul, since every caller in the crate meets it.
@[step]
theorem sub_assign_spec (self rhs : FieldElement2625)
    (hself : self.LimbsLt 28) (hrhs : rhs.LimbsLt 28) :
    sub_assign self rhs ⦃ (r : FieldElement2625) =>
      (r.asNat + rhs.asNat) % p = self.asNat % p ∧ r.LimbsLt 26 ⦄ := by
  have hs0 : self[0]!.val < 2 ^ 28 := hself 0 (by decide)
  have hs1 : self[1]!.val < 2 ^ 28 := hself 1 (by decide)
  have hs2 : self[2]!.val < 2 ^ 28 := hself 2 (by decide)
  have hs3 : self[3]!.val < 2 ^ 28 := hself 3 (by decide)
  have hs4 : self[4]!.val < 2 ^ 28 := hself 4 (by decide)
  have hs5 : self[5]!.val < 2 ^ 28 := hself 5 (by decide)
  have hs6 : self[6]!.val < 2 ^ 28 := hself 6 (by decide)
  have hs7 : self[7]!.val < 2 ^ 28 := hself 7 (by decide)
  have hs8 : self[8]!.val < 2 ^ 28 := hself 8 (by decide)
  have hs9 : self[9]!.val < 2 ^ 28 := hself 9 (by decide)
  have hr0 : rhs[0]!.val < 2 ^ 28 := hrhs 0 (by decide)
  have hr1 : rhs[1]!.val < 2 ^ 28 := hrhs 1 (by decide)
  have hr2 : rhs[2]!.val < 2 ^ 28 := hrhs 2 (by decide)
  have hr3 : rhs[3]!.val < 2 ^ 28 := hrhs 3 (by decide)
  have hr4 : rhs[4]!.val < 2 ^ 28 := hrhs 4 (by decide)
  have hr5 : rhs[5]!.val < 2 ^ 28 := hrhs 5 (by decide)
  have hr6 : rhs[6]!.val < 2 ^ 28 := hrhs 6 (by decide)
  have hr7 : rhs[7]!.val < 2 ^ 28 := hrhs 7 (by decide)
  have hr8 : rhs[8]!.val < 2 ^ 28 := hrhs 8 (by decide)
  have hr9 : rhs[9]!.val < 2 ^ 28 := hrhs 9 (by decide)
  clear hself hrhs
  unfold sub_assign
  simp only [index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq]
  step*
  all_goals
    have hc0 : i1.val = 2 ^ 30 - 304 := by
      simp [i1_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc1 : i7.val = 2 ^ 29 - 16 := by
      simp [i7_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc2 : i13.val = 2 ^ 30 - 16 := by
      simp [i13_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hz0 : i5.val = self[0]!.val + (2 ^ 30 - 304) - rhs[0]!.val := by
      rw [i5_post, U32.cast_U64_val_eq, i4_post, i2_post, hc0]
    have hz1 : i11.val = self[1]!.val + (2 ^ 29 - 16) - rhs[1]!.val := by
      rw [i11_post, U32.cast_U64_val_eq, i10_post, i8_post, hc1]
    have hz2 : i17.val = self[2]!.val + (2 ^ 30 - 16) - rhs[2]!.val := by
      rw [i17_post, U32.cast_U64_val_eq, i16_post, i14_post, hc2]
    have hz3 : i22.val = self[3]!.val + (2 ^ 29 - 16) - rhs[3]!.val := by
      rw [i22_post, U32.cast_U64_val_eq, i21_post, i19_post, hc1]
    have hz4 : i27.val = self[4]!.val + (2 ^ 30 - 16) - rhs[4]!.val := by
      rw [i27_post, U32.cast_U64_val_eq, i26_post, i24_post, hc2]
    have hz5 : i32.val = self[5]!.val + (2 ^ 29 - 16) - rhs[5]!.val := by
      rw [i32_post, U32.cast_U64_val_eq, i31_post, i29_post, hc1]
    have hz6 : i37.val = self[6]!.val + (2 ^ 30 - 16) - rhs[6]!.val := by
      rw [i37_post, U32.cast_U64_val_eq, i36_post, i34_post, hc2]
    have hz7 : i42.val = self[7]!.val + (2 ^ 29 - 16) - rhs[7]!.val := by
      rw [i42_post, U32.cast_U64_val_eq, i41_post, i39_post, hc1]
    have hz8 : i47.val = self[8]!.val + (2 ^ 30 - 16) - rhs[8]!.val := by
      rw [i47_post, U32.cast_U64_val_eq, i46_post, i44_post, hc2]
    have hz9 : i52.val = self[9]!.val + (2 ^ 29 - 16) - rhs[9]!.val := by
      rw [i52_post, U32.cast_U64_val_eq, i51_post, i49_post, hc1]
  · exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨?_, fe_post1⟩
    rw [Nat.add_mod, fe_post, ← Nat.add_mod, Array.asNat2625_make,
      ← Nat.add_mul_mod_self_right self.asNat 16 p]
    apply congrArg (· % p)
    rw [asNat_expand, asNat_expand, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    have := p_add_nineteen
    omega

end CoreOpsArithSubAssignSharedBFieldElement2625
end Curve25519Dalek.backend.serial.u32.field.FieldElement2625.Insts
