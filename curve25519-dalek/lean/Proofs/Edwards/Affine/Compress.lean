/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.IsNegative
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Coords
import Proofs.Helpers.Edwards
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards.affine

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Setting bit `7` of a byte below `128`. -/
private theorem xor_128_of_lt {x : ℕ} (hx : x < 128) : x ^^^ 128 = x + 128 := by
  revert x
  decide

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The last byte of a canonical field element (`< 2^255`) is below `128`. -/
private theorem getElem!_31_lt {s : Array U8 32#usize} (hs : s.asNat 8 < 2 ^ 255) :
    s[31]!.val < 128 := by
  have h := Array.getElem!_last_eq_asNat_div 8 s (fun i _ => by scalar_tac) (by decide)
  rw [show (32#usize).val - 1 = 31 from rfl] at h
  rw [h]
  refine Nat.div_lt_of_lt_mul ?_
  rw [show (2 : ℕ) ^ (8 * 31) * 128 = 2 ^ 255 from by norm_num]
  exact hs

namespace «AffinePointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::compress`: the canonical `y` with the sign of `x` in bit `255`. -/
@[step]
theorem compress_asNat (self : AffinePoint.«x86_64-tables») :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = self.y.toField.val + 2 ^ 255 * (if self.x.toField.IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨s, hs⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step with Array.index_usize_getElem!_spec as ⟨i2, hi2⟩
  step as ⟨i3, hi3, hi3bv⟩
  step as ⟨s1, hs1⟩
  subst hi2 hs1
  rw [hi] at hi1
  have hsval : s.asNat 8 = self.y.toField.val := asNat_eq_val_of_mod hs
  have hslt : s.asNat 8 < 2 ^ 255 := by
    rw [hsval]
    exact (ZMod.val_lt _).trans p_lt_two_pow_255
  have h31 := getElem!_31_lt hslt
  have hset : (s.set 31#usize i3).asNat 8 + 2 ^ (8 * 31) * s[31]!.val
      = s.asNat 8 + 2 ^ (8 * 31) * i3.val :=
    Array.asNat_set_add 8 s 31#usize i3 (by simp)
  have hsign : (if self.x.toField.IsNeg then 1 else 0) = c.val := by
    rcases hcv with rfl | rfl
    · rw [ite_eq_right ((eq_zero_iff_not_isNeg_toField (Or.inl rfl) hc).mp rfl)]
      rfl
    · rw [ite_eq_left ((eq_one_iff_isNeg_toField hc).mp rfl)]
      rfl
  have hi3v : i3.val = s[31]!.val + 128 * c.val := by
    rw [hi3, UScalar.val_xor, hi1, Nat.shiftLeft_eq]
    rcases hcv with rfl | rfl
    · simp
    · rw [show (1#u8).val * 2 ^ 7 % U8.size = 128 from by simp [U8.size, U8.numBits]]
      exact xor_128_of_lt h31
  rw [CompressedEdwardsY.asNat_def, hsign]
  omega

/-- `AffinePoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : AffinePoint.«x86_64-tables») (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encodeNat self.toPoint ⦄ :=
  spec_mono (compress_asNat self) fun r hr => by
    rw [hr, encodeNat_eq, AffinePoint.«x86_64-tables».toPoint_x hon,
      AffinePoint.«x86_64-tables».toPoint_y hon]

end «AffinePointx86_64-tables»

namespace «AffinePointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::compress`: the canonical `y` with the sign of `x` in bit `255`. -/
@[step]
theorem compress_asNat (self : AffinePoint.«i686-tables») :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = self.y.toField.val + 2 ^ 255 * (if self.x.toField.IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨s, hs⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step with Array.index_usize_getElem!_spec as ⟨i2, hi2⟩
  step as ⟨i3, hi3, hi3bv⟩
  step as ⟨s1, hs1⟩
  subst hi2 hs1
  rw [hi] at hi1
  have hsval : s.asNat 8 = self.y.toField.val := asNat_eq_val_of_mod hs
  have hslt : s.asNat 8 < 2 ^ 255 := by
    rw [hsval]
    exact (ZMod.val_lt _).trans p_lt_two_pow_255
  have h31 := getElem!_31_lt hslt
  have hset : (s.set 31#usize i3).asNat 8 + 2 ^ (8 * 31) * s[31]!.val
      = s.asNat 8 + 2 ^ (8 * 31) * i3.val :=
    Array.asNat_set_add 8 s 31#usize i3 (by simp)
  have hsign : (if self.x.toField.IsNeg then 1 else 0) = c.val := by
    rcases hcv with rfl | rfl
    · rw [ite_eq_right ((eq_zero_iff_not_isNeg_toField (Or.inl rfl) hc).mp rfl)]
      rfl
    · rw [ite_eq_left ((eq_one_iff_isNeg_toField hc).mp rfl)]
      rfl
  have hi3v : i3.val = s[31]!.val + 128 * c.val := by
    rw [hi3, UScalar.val_xor, hi1, Nat.shiftLeft_eq]
    rcases hcv with rfl | rfl
    · simp
    · rw [show (1#u8).val * 2 ^ 7 % U8.size = 128 from by simp [U8.size, U8.numBits]]
      exact xor_128_of_lt h31
  rw [CompressedEdwardsY.asNat_def, hsign]
  omega

/-- `AffinePoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : AffinePoint.«i686-tables») (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encodeNat self.toPoint ⦄ :=
  spec_mono (compress_asNat self) fun r hr => by
    rw [hr, encodeNat_eq, AffinePoint.«i686-tables».toPoint_x hon,
      AffinePoint.«i686-tables».toPoint_y hon]

end «AffinePointi686-tables»

namespace «AffinePointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `AffinePoint::compress`: the canonical `y` with the sign of `x` in bit `255`. -/
@[step]
theorem compress_asNat (self : AffinePoint.«x86_64-no-tables») :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = self.y.toField.val + 2 ^ 255 * (if self.x.toField.IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨s, hs⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step with Array.index_usize_getElem!_spec as ⟨i2, hi2⟩
  step as ⟨i3, hi3, hi3bv⟩
  step as ⟨s1, hs1⟩
  subst hi2 hs1
  rw [hi] at hi1
  have hsval : s.asNat 8 = self.y.toField.val := asNat_eq_val_of_mod hs
  have hslt : s.asNat 8 < 2 ^ 255 := by
    rw [hsval]
    exact (ZMod.val_lt _).trans p_lt_two_pow_255
  have h31 := getElem!_31_lt hslt
  have hset : (s.set 31#usize i3).asNat 8 + 2 ^ (8 * 31) * s[31]!.val
      = s.asNat 8 + 2 ^ (8 * 31) * i3.val :=
    Array.asNat_set_add 8 s 31#usize i3 (by simp)
  have hsign : (if self.x.toField.IsNeg then 1 else 0) = c.val := by
    rcases hcv with rfl | rfl
    · rw [ite_eq_right ((eq_zero_iff_not_isNeg_toField (Or.inl rfl) hc).mp rfl)]
      rfl
    · rw [ite_eq_left ((eq_one_iff_isNeg_toField hc).mp rfl)]
      rfl
  have hi3v : i3.val = s[31]!.val + 128 * c.val := by
    rw [hi3, UScalar.val_xor, hi1, Nat.shiftLeft_eq]
    rcases hcv with rfl | rfl
    · simp
    · rw [show (1#u8).val * 2 ^ 7 % U8.size = 128 from by simp [U8.size, U8.numBits]]
      exact xor_128_of_lt h31
  rw [CompressedEdwardsY.asNat_def, hsign]
  omega

/-- `AffinePoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : AffinePoint.«x86_64-no-tables») (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encodeNat self.toPoint ⦄ :=
  spec_mono (compress_asNat self) fun r hr => by
    rw [hr, encodeNat_eq, AffinePoint.«x86_64-no-tables».toPoint_x hon,
      AffinePoint.«x86_64-no-tables».toPoint_y hon]

end «AffinePointx86_64-no-tables»

namespace «AffinePointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `AffinePoint::compress`: the canonical `y` with the sign of `x` in bit `255`. -/
@[step]
theorem compress_asNat (self : AffinePoint.«i686-no-tables») :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = self.y.toField.val + 2 ^ 255 * (if self.x.toField.IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨s, hs⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  step with Array.index_usize_getElem!_spec as ⟨i2, hi2⟩
  step as ⟨i3, hi3, hi3bv⟩
  step as ⟨s1, hs1⟩
  subst hi2 hs1
  rw [hi] at hi1
  have hsval : s.asNat 8 = self.y.toField.val := asNat_eq_val_of_mod hs
  have hslt : s.asNat 8 < 2 ^ 255 := by
    rw [hsval]
    exact (ZMod.val_lt _).trans p_lt_two_pow_255
  have h31 := getElem!_31_lt hslt
  have hset : (s.set 31#usize i3).asNat 8 + 2 ^ (8 * 31) * s[31]!.val
      = s.asNat 8 + 2 ^ (8 * 31) * i3.val :=
    Array.asNat_set_add 8 s 31#usize i3 (by simp)
  have hsign : (if self.x.toField.IsNeg then 1 else 0) = c.val := by
    rcases hcv with rfl | rfl
    · rw [ite_eq_right ((eq_zero_iff_not_isNeg_toField (Or.inl rfl) hc).mp rfl)]
      rfl
    · rw [ite_eq_left ((eq_one_iff_isNeg_toField hc).mp rfl)]
      rfl
  have hi3v : i3.val = s[31]!.val + 128 * c.val := by
    rw [hi3, UScalar.val_xor, hi1, Nat.shiftLeft_eq]
    rcases hcv with rfl | rfl
    · simp
    · rw [show (1#u8).val * 2 ^ 7 % U8.size = 128 from by simp [U8.size, U8.numBits]]
      exact xor_128_of_lt h31
  rw [CompressedEdwardsY.asNat_def, hsign]
  omega

/-- `AffinePoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : AffinePoint.«i686-no-tables») (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.asNat = curve25519.encodeNat self.toPoint ⦄ :=
  spec_mono (compress_asNat self) fun r hr => by
    rw [hr, encodeNat_eq, AffinePoint.«i686-no-tables».toPoint_x hon,
      AffinePoint.«i686-no-tables».toPoint_y hon]

end «AffinePointi686-no-tables»

end Curve25519Dalek.edwards.affine
