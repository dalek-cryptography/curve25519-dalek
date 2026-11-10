/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Curve25519.X25519
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
public import Proofs.Field.Invert
import Proofs.Backend.Serial.U64.Field.MinusOne
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Edwards.Decompress
import Proofs.Helpers.AsNat
import Proofs.Helpers.StepSpecs
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.MinusOne
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Helpers.ToField2625
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public import Proofs.Helpers.ByteValues
import Mathlib.Tactic.IntervalCases
public section

/-! # `MontgomeryPoint::to_edwards`

The birational map `y = (u - 1) / (u + 1)` from the Montgomery `u`-line to the Edwards
`y`-line, followed by `CompressedEdwardsY::decompress` of the canonical bytes of `y` with the sign
bit set to `sign mod 2` (`sign << 7` keeps only bit `0` of `sign`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.montgomery.MontgomeryPoint

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Changing only the top byte of 32 bytes changes their value by `2^248` times the change. -/
private theorem asNat_of_eq_but_top (a b : Array U8 32#usize) (h : ∀ j, j ≠ 31 → b[j]! = a[j]!) :
    b.asNat 8 + 2 ^ 248 * a[31]!.val = a.asNat 8 + 2 ^ 248 * b[31]!.val := by
  rw [Array.asNat_eq_sum, Array.asNat_eq_sum, show (32#usize).val = 31 + 1 from rfl,
    Finset.sum_range_succ (fun x => 2 ^ (8 * x) * b[x]!.val) 31,
    Finset.sum_range_succ (fun x => 2 ^ (8 * x) * a[x]!.val) 31]
  have hs : ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * b[x]!.val =
      ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * a[x]!.val :=
    Finset.sum_congr rfl fun x hx => by rw [h x (by simp at hx; omega)]
  rw [hs]
  ring

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The top byte of a value below `2^255` is below `2^7`. -/
private theorem top_byte_lt (a : Array U8 32#usize) (ha : a.asNat 8 < 2 ^ 255) :
    a[31]!.val < 2 ^ 7 := by
  rw [← Array.asNat_div_pow_mod 8 a (fun i _ => a[i]!.hBounds) 31]
  calc a.asNat 8 / 2 ^ (8 * 31) % 2 ^ 8 ≤ a.asNat 8 / 2 ^ (8 * 31) := Nat.mod_le _ _
    _ < 2 ^ 7 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc
        a.asNat 8 < 2 ^ 255 := ha
        _ = 2 ^ 7 * 2 ^ (8 * 31) := by norm_num

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- Setting bit `7` of a byte below `2^7` adds `2^7`. -/
private theorem xor_top_bit (b c : ℕ) (hb : b < 2 ^ 7) (hc : c < 2) :
    b ^^^ (2 ^ 7 * c) = b + 2 ^ 7 * c := by
  interval_cases c
  · simp
  · revert b; decide


end Curve25519Dalek.montgomery.MontgomeryPoint

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `MontgomeryPoint::to_edwards` after `u = from_bytes`, over a backend: `decompress` is
`CompressedEdwardsY::decompress` to the points `E`, `minusOne` is `FieldElement::MINUS_ONE`. -/
@[expose] def toEdwardsTail {E : Type}
    (decompress : edwards.CompressedEdwardsY → Result (Option E)) (minusOne : Result B.F) (u : B.F)
    (sign : U8) : Result (Option E) := do
  let fe ← minusOne
  let b ← B.eq u fe
  if b
  then ok none
  else
    let one ← B.constOne
    let fe1 ← B.sub u one
    let fe2 ← B.add u one
    let fe3 ← B.invert fe2
    let y ← B.mul fe1 fe3
    let y_bytes ← B.toBytes y
    let i ← sign <<< 7#i32
    let i1 ← Array.index_usize y_bytes 31#usize
    let i2 ← lift (i1 ^^^ i)
    let y_bytes1 ← Array.update y_bytes 31#usize i2
    decompress y_bytes1

open scoped Helpers.IndexStep Helpers.UpdateStep in
/-- `toEdwardsTail`: `none` for `u = -1`, otherwise the lenient decoding of `y = (u - 1) / (u + 1)`
with sign bit `sign mod 2`, for a `decompress` with the spec of `CompressedEdwardsY::decompress`
(model `toPt`, invariant `Good`). -/
theorem toEdwardsTail_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (heq : B.EqSpec) (hone : B.OneSpec) (hinv : B.InvertSpec)
    (htb : B.ToBytesSpec) {E : Type} (decompress : edwards.CompressedEdwardsY → Result (Option E))
    (toPt : E → edwards.Point) (Good : E → Prop) (minusOne : Result B.F)
    (hm1 : minusOne ⦃ (r : B.F) => B.toField r = -1 ⦄)
    (hdec : ∀ s, decompress s ⦃ (r : Option E) =>
      r.map toPt = curve25519.decodeLenientNat (edwards.CompressedEdwardsY.asNat s) ∧
      ∀ q, r = some q → Good q ⦄)
    (u : B.F) (sign : U8) (hu : B.Red u) :
    B.toEdwardsTail decompress minusOne u sign ⦃ (r : Option E) =>
      r.map toPt =
        (if B.toField u = -1 then none
        else curve25519.decodeLenientNat
          (((B.toField u - 1) / (B.toField u + 1)).val + 2 ^ 255 * (sign.val % 2))) ∧
      ∀ q, r = some q → Good q ⦄ := by
  unfold toEdwardsTail
  apply spec_bind hm1
  intro m1 hm1f
  step with heq u m1 as ⟨b, hb⟩
  split
  · next hbt =>
    have hu1 : B.toField u = -1 := by rw [← hm1f]; exact hb.mp hbt
    rw [WP.spec_ok]
    exact ⟨by rw [ite_eq_left hu1]; rfl, fun q hq => by cases hq⟩
  · next hbf =>
    have hu1 : B.toField u ≠ -1 := fun h => hbf (hb.mpr (by rw [h, hm1f]))
    apply spec_bind hone
    rintro one ⟨hone1, honeb⟩
    step with hsub u one (B.red_mulIn hu) (B.red_mulIn honeb) as ⟨fe1, fe1_post, fe1b⟩
    step with hadd u one hu honeb as ⟨fe2, fe2_post, fe2b⟩
    step with hinv fe2 (B.sum2_sqIn fe2b) as ⟨fe3, fe3_post, fe3b⟩
    step with hmul fe1 fe3 (B.red_mulIn fe1b) (B.red_mulIn fe3b) as ⟨y, y_post, yb⟩
    step with htb y as ⟨y_bytes, y_bytes_post⟩
    step as ⟨i, i_post, i_bv⟩
    step as ⟨i1, i1_post⟩
    step as ⟨i2, i2_val, i2_bv⟩
    step as ⟨y_bytes1, y31, y_rest⟩
    step with hdec y_bytes1 as ⟨r, r_post, r_post1⟩
    refine ⟨?_, r_post1⟩
    rw [ite_eq_right hu1, r_post]
    congr 1
    -- the value of the bytes: the canonical `y` with the sign in bit `255`
    have hy : B.toField y = (B.toField u - 1) / (B.toField u + 1) := by
      rw [y_post, fe1_post, fe3_post, fe2_post, hone1, div_eq_mul_inv]
    have hyb : y_bytes.asNat 8 = ((B.toField u - 1) / (B.toField u + 1)).val := by
      rw [y_bytes_post, ← hy]
    have htop := montgomery.MontgomeryPoint.top_byte_lt y_bytes
      (by rw [hyb]; exact lt_trans (ZMod.val_lt _) p_lt_two_pow_255)
    have hi : i.val = 2 ^ 7 * (sign.val % 2) := by
      rw [i_post, Nat.shiftLeft_eq, show U8.size = 2 ^ 7 * 2 by simp [U8.size, U8.numBits],
          Nat.mul_comm _ (2 ^ 7),
        Nat.mul_mod_mul_left]
    have hi2 : i2.val = y_bytes[31]!.val + 2 ^ 7 * (sign.val % 2) := by
      rw [i2_val, UScalar.val_xor, i1_post, hi]
      exact montgomery.MontgomeryPoint.xor_top_bit _ _ htop (Nat.mod_lt _ (by norm_num))
    have hset := montgomery.MontgomeryPoint.asNat_of_eq_but_top y_bytes y_bytes1 y_rest
    rw [y31, hi2] at hset
    rw [edwards.CompressedEdwardsY.asNat_def, ← hyb]
    omega

end Curve25519Dalek.Backend

namespace Curve25519Dalek.montgomery.MontgomeryPoint

/-- Setting bit `7` of a byte below `128`. -/
private theorem xor_128_of_lt {x : ℕ} (hx : x < 128) : x ^^^ 128 = x + 128 := by
  revert x
  decide

/-- The bytes `to_edwards` decompresses (`y.to_bytes()` with `y_bytes[31] ^= sign << 7`) are those
of `encodeU y + 2 ^ 255 (sign mod 2)`. -/
private theorem toEdwards_bytes (y : ZMod p) (s : ℕ) :
    (encodeUCoordinate y).set 31 ((encodeUCoordinate y)[31] ^^^ (UInt8.ofNat s <<< 7)) =
      encodeLittleEndian 32 (encodeU y + 2 ^ 255 * (s % 2)) := by
  have hv : encodeU y < 2 ^ 255 := (encodeU_lt y).trans p_lt_two_pow_255
  apply Vector.ext
  intro i hi
  apply UInt8.toNat_inj.mp
  simp only [encodeUCoordinate, encodeLittleEndian, Vector.getElem_set, Vector.getElem_ofFn]
  split_ifs with h
  · subst h
    simp only [UInt8.toNat_xor, UInt8.toNat_shiftLeft, UInt8.toNat_ofNat']
    have ha : encodeU y / 256 ^ 31 < 128 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      exact hv.trans_eq (by norm_num)
    have hshift : (s % 2 ^ 8) <<< (UInt8.toNat 7 % 8) % 2 ^ 8 = 128 * (s % 2) := by
      rw [Nat.shiftLeft_eq, show UInt8.toNat 7 % 8 = 7 from rfl]
      omega
    have hdiv : (encodeU y + 2 ^ 255 * (s % 2)) / 256 ^ 31 =
        encodeU y / 256 ^ 31 + 128 * (s % 2) := by
      rw [show 2 ^ 255 * (s % 2) = 128 * (s % 2) * 256 ^ 31 by ring,
        Nat.add_mul_div_right _ _ (by positivity)]
    rw [hshift, hdiv]
    rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
    · rw [h0]
      norm_num
    · rw [h1, mul_one, Nat.mod_eq_of_lt (ha.trans (by norm_num)), xor_128_of_lt ha]
      omega
  · simp only [UInt8.toNat_ofNat']
    have hi' : i ≤ 30 := by omega
    interval_cases i <;> norm_num <;> omega

/-- The value of the bytes `to_edwards` decompresses is below `256 ^ 32`. -/
private theorem toEdwards_bytes_lt (y : ZMod p) (sign : U8) :
    encodeU y + 2 ^ 255 * (sign.val % 2) < 256 ^ 32 := by
  have hy := (encodeU_lt y).trans p_lt_two_pow_255
  have hs : sign.val % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ two_pos)
  calc encodeU y + 2 ^ 255 * (sign.val % 2) < 2 ^ 255 + 2 ^ 255 * 1 :=
        Nat.add_lt_add_of_lt_of_le hy (Nat.mul_le_mul_left _ hs)
    _ = 256 ^ 32 := by norm_num

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem «x86_64-tables».to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-tables»)) =>
      let u := decodeUCoordinate self.toVector
      r.map edwards.EdwardsPoint.«x86_64-tables».toPoint =
        (if u = -1 then none
        else curve25519.decodeLenient
          ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
            ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
              (UInt8.ofNat sign.val <<< 7)))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  dsimp only
  rw [toEdwards_bytes, curve25519.decodeLenient, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (toEdwards_bytes_lt _ _)]
  unfold curve25519.encodeU
  unfold to_edwards.«x86_64-tables»
  step as ⟨u, hu, hu_lt⟩
  have hU : u.toField = decodeUCoordinate self.toVector := by
    rw [MontgomeryPoint.decodeUCoordinate_toVector, decodeU, toField_def, hu,
        MontgomeryPoint.asNat_def]
  have hm1 : backend.serial.u64.field.FieldElement51.MINUS_ONE
      ⦃ (r : Backend.U64.F) => Backend.U64.toField r = -1 ⦄ :=
    spec_mono backend.serial.u64.field.FieldElement51.MINUS_ONE_spec fun m1 ⟨hm1, _⟩ => by
      change m1.toField = -1
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
      rw [toField_def]
      exact eq_neg_of_add_eq_zero_left h
  have hU' : Backend.U64.toField u = decodeUCoordinate self.toVector := hU
  apply spec_mono (Backend.toEdwardsTail_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.eq_spec Backend.U64.one_spec
    Backend.U64.invert_spec Backend.U64.to_bytes_spec _
    edwards.EdwardsPoint.«x86_64-tables».toPoint
    (fun q => q.OnCurve ∧ q.LimbsLt 52) _ hm1
    (fun s => by
      simpa only [edwards.CompressedEdwardsY.decodeLenient_toVector] using
        edwards.CompressedEdwardsY.«x86_64-tables».decompress_spec s) u sign
    (limbs_lt_of_le (by decide) hu_lt))
  intro r hr
  rw [hU'] at hr
  exact hr

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem «i686-tables».to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-tables» self sign ⦃ (r : Option (edwards.EdwardsPoint.«i686-tables»)) =>
      let u := decodeUCoordinate self.toVector
      r.map edwards.EdwardsPoint.«i686-tables».toPoint =
        (if u = -1 then none
        else curve25519.decodeLenient
          ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
            ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
              (UInt8.ofNat sign.val <<< 7)))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  dsimp only
  rw [toEdwards_bytes, curve25519.decodeLenient, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (toEdwards_bytes_lt _ _)]
  unfold curve25519.encodeU
  unfold to_edwards.«i686-tables»
  step as ⟨u, hu, hu_lt⟩
  have hU : u.toField = decodeUCoordinate self.toVector := by
    rw [MontgomeryPoint.decodeUCoordinate_toVector, decodeU, toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  have hm1 : backend.serial.u32.field.FieldElement2625.MINUS_ONE
      ⦃ (r : Backend.U32.F) => Backend.U32.toField r = -1 ⦄ :=
    spec_mono backend.serial.u32.field.FieldElement2625.MINUS_ONE_spec fun m1 ⟨hm1, _⟩ => by
      change m1.toField = -1
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
      rw [toField_def]
      exact eq_neg_of_add_eq_zero_left h
  have hU' : Backend.U32.toField u = decodeUCoordinate self.toVector := hU
  apply spec_mono (Backend.toEdwardsTail_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.eq_spec Backend.U32.one_spec
    Backend.U32.invert_spec Backend.U32.to_bytes_spec _
    edwards.EdwardsPoint.«i686-tables».toPoint
    (fun q => q.OnCurve ∧ q.LimbsLt 26) _ hm1
    (fun s => by
      simpa only [edwards.CompressedEdwardsY.decodeLenient_toVector] using
        edwards.CompressedEdwardsY.«i686-tables».decompress_spec s) u sign
    (limbs_lt_of_le (by decide) hu_lt))
  intro r hr
  rw [hU'] at hr
  exact hr

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem «x86_64-no-tables».to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«x86_64-no-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«x86_64-no-tables»)) =>
      let u := decodeUCoordinate self.toVector
      r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint =
        (if u = -1 then none
        else curve25519.decodeLenient
          ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
            ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
              (UInt8.ofNat sign.val <<< 7)))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  dsimp only
  rw [toEdwards_bytes, curve25519.decodeLenient, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (toEdwards_bytes_lt _ _)]
  unfold curve25519.encodeU
  unfold to_edwards.«x86_64-no-tables»
  step as ⟨u, hu, hu_lt⟩
  have hU : u.toField = decodeUCoordinate self.toVector := by
    rw [MontgomeryPoint.decodeUCoordinate_toVector, decodeU, toField_def, hu,
        MontgomeryPoint.asNat_def]
  have hm1 : backend.serial.u64.field.FieldElement51.MINUS_ONE
      ⦃ (r : Backend.U64.F) => Backend.U64.toField r = -1 ⦄ :=
    spec_mono backend.serial.u64.field.FieldElement51.MINUS_ONE_spec fun m1 ⟨hm1, _⟩ => by
      change m1.toField = -1
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
      rw [toField_def]
      exact eq_neg_of_add_eq_zero_left h
  have hU' : Backend.U64.toField u = decodeUCoordinate self.toVector := hU
  apply spec_mono (Backend.toEdwardsTail_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.eq_spec Backend.U64.one_spec
    Backend.U64.invert_spec Backend.U64.to_bytes_spec _
    edwards.EdwardsPoint.«x86_64-no-tables».toPoint
    (fun q => q.OnCurve ∧ q.LimbsLt 52) _ hm1
    (fun s => by
      simpa only [edwards.CompressedEdwardsY.decodeLenient_toVector] using
        edwards.CompressedEdwardsY.«x86_64-no-tables».decompress_spec s) u sign
    (limbs_lt_of_le (by decide) hu_lt))
  intro r hr
  rw [hU'] at hr
  exact hr

open scoped Helpers.IndexStep Helpers.UpdateStep in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `MontgomeryPoint::to_edwards`: `none` for `u = -1`; otherwise the lenient decoding (as
`CompressedEdwardsY::decompress`) of `y = (u - 1) / (u + 1)` with sign bit `sign mod 2`. -/
@[step]
theorem «i686-no-tables».to_edwards_spec (self : MontgomeryPoint) (sign : U8) :
    to_edwards.«i686-no-tables» self sign
      ⦃ (r : Option (edwards.EdwardsPoint.«i686-no-tables»)) =>
      let u := decodeUCoordinate self.toVector
      r.map edwards.EdwardsPoint.«i686-no-tables».toPoint =
        (if u = -1 then none
        else curve25519.decodeLenient
          ((encodeUCoordinate ((u - 1) / (u + 1))).set 31
            ((encodeUCoordinate ((u - 1) / (u + 1)))[31] ^^^
              (UInt8.ofNat sign.val <<< 7)))) ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  dsimp only
  rw [toEdwards_bytes, curve25519.decodeLenient, decodeLittleEndian_encodeLittleEndian,
    Nat.mod_eq_of_lt (toEdwards_bytes_lt _ _)]
  unfold curve25519.encodeU
  unfold to_edwards.«i686-no-tables»
  step as ⟨u, hu, hu_lt⟩
  have hU : u.toField = decodeUCoordinate self.toVector := by
    rw [MontgomeryPoint.decodeUCoordinate_toVector, decodeU, toField_def, MontgomeryPoint.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hu
  have hm1 : backend.serial.u32.field.FieldElement2625.MINUS_ONE
      ⦃ (r : Backend.U32.F) => Backend.U32.toField r = -1 ⦄ :=
    spec_mono backend.serial.u32.field.FieldElement2625.MINUS_ONE_spec fun m1 ⟨hm1, _⟩ => by
      change m1.toField = -1
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hm1
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
      rw [toField_def]
      exact eq_neg_of_add_eq_zero_left h
  have hU' : Backend.U32.toField u = decodeUCoordinate self.toVector := hU
  apply spec_mono (Backend.toEdwardsTail_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.eq_spec Backend.U32.one_spec
    Backend.U32.invert_spec Backend.U32.to_bytes_spec _
    edwards.EdwardsPoint.«i686-no-tables».toPoint
    (fun q => q.OnCurve ∧ q.LimbsLt 26) _ hm1
    (fun s => by
      simpa only [edwards.CompressedEdwardsY.decodeLenient_toVector] using
        edwards.CompressedEdwardsY.«i686-no-tables».decompress_spec s) u sign
    (limbs_lt_of_le (by decide) hu_lt))
  intro r hr
  rw [hU'] at hr
  exact hr

end Curve25519Dalek.montgomery.MontgomeryPoint
