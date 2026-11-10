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
# Spec theorem for `negate`

`negate self` computes `-self` as `16 * p - self` limbwise in `u32`, to avoid underflow. The limbs
of `16 * p` in the alternating `2^26/2^25` radix are `0x3ffffed << 4` for limb `0`,
`0x1ffffff << 4` for odd limbs and `0x3ffffff << 4` for the other even limbs. The ten differences
are widened to `u64` and passed to `reduce`, so the result represents `-self` modulo `p`.
Source: 'curve25519-dalek/src/backend/serial/u32/field.rs', lines 302:4-317:5
-/

open Aeneas Aeneas.Std curve25519 Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.u32.field.FieldElement2625

@[step]
theorem negate_spec (self : FieldElement2625) (hself : self.LimbsLt 28) :
    negate self ⦃ (r : FieldElement2625) =>
      (r.asNat + self.asNat) % p = 0 ∧ r.LimbsLt 26 ⦄ := by
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
  clear hself
  unfold negate
  simp only [index_usize_eq, Nat.reduceLT, UScalar.ofNatCore_val_eq]
  step*
  all_goals
    have hc0 : i.val = 2 ^ 30 - 304 := by
      simp [i_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc1 : i4.val = 2 ^ 29 - 16 := by
      simp [i4_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hc2 : i8.val = 2 ^ 30 - 16 := by
      simp [i8_post, U32.size, U32.numBits_eq, Nat.shiftLeft_eq]
    have hz0 : i3.val = 2 ^ 30 - 304 - self[0]!.val := by
      rw [i3_post, U32.cast_U64_val_eq, i2_post, hc0]
    have hz1 : i7.val = 2 ^ 29 - 16 - self[1]!.val := by
      rw [i7_post, U32.cast_U64_val_eq, i6_post, hc1]
    have hz2 : i11.val = 2 ^ 30 - 16 - self[2]!.val := by
      rw [i11_post, U32.cast_U64_val_eq, i10_post, hc2]
    have hz3 : i14.val = 2 ^ 29 - 16 - self[3]!.val := by
      rw [i14_post, U32.cast_U64_val_eq, i13_post, hc1]
    have hz4 : i17.val = 2 ^ 30 - 16 - self[4]!.val := by
      rw [i17_post, U32.cast_U64_val_eq, i16_post, hc2]
    have hz5 : i20.val = 2 ^ 29 - 16 - self[5]!.val := by
      rw [i20_post, U32.cast_U64_val_eq, i19_post, hc1]
    have hz6 : i23.val = 2 ^ 30 - 16 - self[6]!.val := by
      rw [i23_post, U32.cast_U64_val_eq, i22_post, hc2]
    have hz7 : i26.val = 2 ^ 29 - 16 - self[7]!.val := by
      rw [i26_post, U32.cast_U64_val_eq, i25_post, hc1]
    have hz8 : i29.val = 2 ^ 30 - 16 - self[8]!.val := by
      rw [i29_post, U32.cast_U64_val_eq, i28_post, hc2]
    have hz9 : i32.val = 2 ^ 29 - 16 - self[9]!.val := by
      rw [i32_post, U32.cast_U64_val_eq, i31_post, hc1]
  · exact getElem!_make_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine ⟨?_, neg_post1⟩
    rw [Nat.add_mod, neg_post, ← Nat.add_mod, Array.asNat2625_make]
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨16, ?_⟩
    rw [asNat_expand, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9]
    have := p_add_nineteen
    omega

end Curve25519Dalek.backend.serial.u32.field.FieldElement2625
