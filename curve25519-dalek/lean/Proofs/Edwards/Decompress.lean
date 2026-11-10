/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Encoding
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Proofs.Field.SqrtRatioI
public import Proofs.Helpers.Backend.U32
public import Proofs.Helpers.Backend.U64
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Edwards.AsBytes
import Proofs.Helpers.Array
import Proofs.Helpers.Coords
import Proofs.Helpers.Edwards
import Proofs.Helpers.ToField
import Subtle.Lemmas
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Helpers.ToField2625
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards

namespace decompress

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `d y² + 1 ≠ 0`: `-1/d` is not a square. -/
private theorem d_mul_sq_add_one_ne_zero (y : ZMod p) : curve25519.d * y ^ 2 + 1 ≠ 0 := by
  have h := d_mul_sq_sub_a_ne_zero (E := curve25519.edwards) y
  rwa [edwards_d, edwards_a_eq_neg_one, sub_neg_eq_add] at h

end decompress

end Curve25519Dalek.edwards

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `decompress::step_1` after `Y = from_bytes`, over a backend. -/
@[expose] def edStep1Tail (Y : B.F) : Result (subtle.Choice × B.F × B.F × B.F) := do
  let Z ← B.constOne
  let YY ← B.square Y
  let u ← B.sub YY Z
  let fe ← B.constEdwardsD
  let fe1 ← B.mul YY fe
  let v ← B.add fe1 Z
  let (is_valid_y_coord, X) ← B.sqrtRatioI u v
  ok (is_valid_y_coord, X, Y, Z)

/-- `edStep1Tail`: `Z = 1` and `(c, X) = sqrt_ratio_i (Y² - 1) (d Y² + 1)`: `c = 1` iff
`xSq Y` is a square, and then `X` is its non-negative root. -/
theorem edStep1Tail_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (hsq : B.SquareSpec) (hD : B.EdwardsDSpec) (hone : B.OneSpec) (hsr : B.SqrtRatioISpec)
    (Y : B.F) (hY : B.Red Y) :
    B.edStep1Tail Y ⦃ (c : subtle.Choice) (X Y' Z : B.F) =>
      c.IsValid ∧ Y' = Y ∧ B.toField Z = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq (B.toField Y))) ∧
      (c = 1#u8 → B.toField X ^ 2 = curve25519.edwards.xSq (B.toField Y)) ∧
      ¬ (B.toField X).IsNeg ∧ B.Red X ∧ B.Red Z ⦄ := by
  unfold edStep1Tail
  apply spec_bind hone
  rintro Z ⟨hZ, hZb⟩
  step with hsq Y (B.red_sqIn hY) as ⟨YY, hYY, hYYb⟩
  step with hsub YY Z (B.red_mulIn hYYb) (B.red_mulIn hZb) as ⟨u, hu, hub⟩
  apply spec_bind hD
  rintro D ⟨hDf, hDb⟩
  step with hmul YY D (B.red_mulIn hYYb) (B.red_mulIn hDb) as ⟨YYD, hYYD, hYYDb⟩
  step with hadd YYD Z hYYDb hZb as ⟨v, hv, hvb⟩
  step with hsr u v (B.red_sqIn hub) (B.sum2_sqIn hvb) as ⟨c, X, hcv, _h0, _h1, h2, h3, hpar, hXb⟩
  have hvf : B.toField v = curve25519.d * B.toField Y ^ 2 + 1 := by
    rw [hv, hYYD, hYY, hDf, hZ]
    ring
  have hv0 : B.toField v ≠ 0 := hvf ▸ edwards.decompress.d_mul_sq_add_one_ne_zero _
  have hxSq : curve25519.edwards.xSq (B.toField Y) = B.toField u / B.toField v := by
    rw [edwards_xSq, hu, hYY, hZ, hvf]
  have hsqiff : IsSquare (B.toField u / B.toField v) ↔
      ∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u := by
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [sq, ← eq_div_iff hv0, hr]⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [← sq, div_eq_iff hv0, hr]⟩
  have hsq1 : c = 1#u8 → ∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u := fun hc => by
    by_contra hns
    rw [(h3 hv0 hns).1] at hc
    exact absurd hc (by decide)
  refine ⟨hcv, hZ, ?_, fun hc => ?_, fun h =>
    absurd ((show (B.toField X).val % 2 = 1 from h).symm.trans hpar) (by decide), hXb, hZb⟩
  · rw [hxSq, hsqiff]
    exact ⟨hsq1, fun ⟨x, hx⟩ => (h2 hv0 x hx).1⟩
  · rw [hxSq, eq_div_iff hv0]
    obtain ⟨x, hx⟩ := hsq1 hc
    exact (h2 hv0 x hx).2

/-- `decompress::step_2` over a backend: `X` negated when bit `255` is set, `T = X Y`. -/
@[expose] def edStep2Body {P : Type} (mk : B.F → B.F → B.F → B.F → P)
    (repr : edwards.CompressedEdwardsY) (X Y Z : B.F) : Result P := do
  let a ← edwards.CompressedEdwardsY.as_bytes repr
  let i ← Array.index_usize a 31#usize
  let i1 ← i >>> 7#i32
  let compressed_sign_bit ← subtle.Choice.Insts.CoreConvertFromU8.from i1
  let X1 ← B.condNeg X compressed_sign_bit
  let fe ← B.mul X1 Y
  ok (mk X1 Y Z fe)

/-- `edStep2Body`: `X` negated when bit `255` is set, `T = X Y`. -/
theorem edStep2Body_spec (hmul : B.MulSpec) (hcng : B.CondNegSpec) {P : Type}
    (mk : B.F → B.F → B.F → B.F → P) (repr : edwards.CompressedEdwardsY) (X Y Z : B.F)
    (hX : B.Red X) (hY : B.Red Y) :
    B.edStep2Body mk repr X Y Z ⦃ (r : P) => ∃ X1 T, r = mk X1 Y Z T ∧
      (edwards.CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 → X1 = X) ∧
      (edwards.CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 → B.toField X1 = -B.toField X) ∧
      B.toField T = B.toField X1 * B.toField Y ∧ B.Red X1 ∧ B.Red T ⦄ := by
  unfold edStep2Body
  step as ⟨a, ha⟩
  step with Array.index_usize_getElem!_spec as ⟨i, hi⟩
  step as ⟨i1, hi1, hi1bv⟩
  have hi1v : i1.val = edwards.CompressedEdwardsY.asNat repr / 2 ^ 255 := by
    rw [hi1, hi, ha, edwards.CompressedEdwardsY.getElem!_31_shiftRight_7]
  have hi1' : i1 = 0#u8 ∨ i1 = 1#u8 := by
    have hle := edwards.CompressedEdwardsY.asNat_div_two_pow_le_one repr
    rw [← hi1v] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl (UScalar.eq_of_val_eq h)
    · exact Or.inr (UScalar.eq_of_val_eq h)
  step as ⟨csb, hcsbv, hcsb⟩
  step with hcng X csb hcsbv (B.red_mulIn hX) as ⟨X1, hX10, hX11⟩
  rw [hcsb] at hX10 hX11
  have hX1b : B.Red X1 := by
    rcases hi1' with h | h
    · rw [hX10 h]
      exact hX
    · exact (hX11 h).2
  step with hmul X1 Y (B.red_mulIn hX1b) (B.red_mulIn hY) as ⟨T, hT, hTb⟩
  refine ⟨X1, T, rfl, fun h0 => ?_, fun h1 => ?_, hT, hX1b, hTb⟩
  · exact hX10 (UScalar.eq_of_val_eq (by rw [hi1v, h0]; rfl))
  · exact (hX11 (UScalar.eq_of_val_eq (by rw [hi1v, h1]; rfl))).1

end Curve25519Dalek.Backend

namespace Curve25519Dalek.edwards

namespace decompress.«x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«x86_64-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement51) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.IsNeg ∧
      X.LimbsLt 52 ∧ Y.LimbsLt 52 ∧
      Z.LimbsLt 52 ⦄ := by
  unfold step_1.«x86_64-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hY, CompressedEdwardsY.asNat_def]
  apply spec_mono (Backend.edStep1Tail_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.square_spec Backend.U64.edwardsD_spec Backend.U64.one_spec
    Backend.U64.sqrtRatioI_spec Y
    (limbs_lt_of_le (by decide) hY_lt))
  rintro ⟨c, X, Y', Z⟩ ⟨hcv, rfl, hZf, hc, hX, hXneg, hXb, hZb⟩
  exact ⟨hcv, hYf, hZf, hc, hX, hXneg, hXb, limbs_lt_of_le (by decide) hY_lt, hZb⟩

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^52`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement51)
    (hX : X.LimbsLt 52) (hY : Y.LimbsLt 52)
    (hZ : Z.LimbsLt 52) :
    step_2.«x86_64-tables» repr X Y Z ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 52 ⦄ := by
  rw [show step_2.«x86_64-tables» repr X Y Z = Backend.U64.edStep2Body
      (fun X Y Z T => ({ X, Y, Z, T } : EdwardsPoint.«x86_64-tables»)) repr X Y Z from rfl]
  apply spec_mono (Backend.edStep2Body_spec Backend.U64 Backend.U64.mul_spec
    Backend.U64.conditional_negate_spec _ repr X Y Z hX hY)
  rintro _ ⟨X1, T, rfl, h0, h1, hT, hX1b, hTb⟩
  have hT' : T.toField = X1.toField * Y.toField := hT
  refine ⟨fun h => ?_, fun h => ?_, ⟨hX1b, hY, hZ, hTb⟩⟩
  · rw [h0 h] at hT' ⊢
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, hT']
  · have hx : X1.toField = -X.toField := (h1 h)
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, hT', hx]

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«x86_64-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«x86_64-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«x86_64-tables».toPoint_x hon]
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«x86_64-tables».toPoint_y hon]
    simp only [EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-tables»

namespace decompress.«i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«i686-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement2625) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.IsNeg ∧
      X.LimbsLt 26 ∧ Y.LimbsLt 26 ∧
      Z.LimbsLt 26 ⦄ := by
  unfold step_1.«i686-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, CompressedEdwardsY.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hY
  apply spec_mono (Backend.edStep1Tail_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.square_spec Backend.U32.edwardsD_spec Backend.U32.one_spec
    Backend.U32.sqrtRatioI_spec Y
    (limbs_lt_of_le (by decide) hY_lt))
  rintro ⟨c, X, Y', Z⟩ ⟨hcv, rfl, hZf, hc, hX, hXneg, hXb, hZb⟩
  exact ⟨hcv, hYf, hZf, hc, hX, hXneg, hXb, limbs_lt_of_le (by decide) hY_lt, hZb⟩

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^26`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement2625)
    (hX : X.LimbsLt 26) (hY : Y.LimbsLt 26)
    (hZ : Z.LimbsLt 26) :
    step_2.«i686-tables» repr X Y Z ⦃ (r : EdwardsPoint.«i686-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 26 ⦄ := by
  rw [show step_2.«i686-tables» repr X Y Z = Backend.U32.edStep2Body
      (fun X Y Z T => ({ X, Y, Z, T } : EdwardsPoint.«i686-tables»)) repr X Y Z from rfl]
  apply spec_mono (Backend.edStep2Body_spec Backend.U32 Backend.U32.mul_spec
    Backend.U32.conditional_negate_spec _ repr X Y Z hX hY)
  rintro _ ⟨X1, T, rfl, h0, h1, hT, hX1b, hTb⟩
  have hT' : T.toField = X1.toField * Y.toField := hT
  refine ⟨fun h => ?_, fun h => ?_, ⟨hX1b, hY, hZ, hTb⟩⟩
  · rw [h0 h] at hT' ⊢
    simp only [EdwardsPoint.«i686-tables».toExtended_def, hT']
  · have hx : X1.toField = -X.toField := (h1 h)
    simp only [EdwardsPoint.«i686-tables».toExtended_def, hT', hx]

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«i686-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«i686-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«i686-tables».toPoint_x hon]
    simp only [EdwardsPoint.«i686-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«i686-tables».toPoint_y hon]
    simp only [EdwardsPoint.«i686-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«i686-tables»

namespace CompressedEdwardsY.«x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenientNat` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-tables»)) =>
      r.map EdwardsPoint.«x86_64-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.decodeLenient_toVector]
  unfold decompress.«x86_64-tables»
  step with decompress.«x86_64-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenientNat_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«x86_64-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«x86_64-tables»

namespace CompressedEdwardsY.«i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenientNat` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^26`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«i686-tables» self ⦃ (r : Option (EdwardsPoint.«i686-tables»)) =>
      r.map EdwardsPoint.«i686-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.decodeLenient_toVector]
  unfold decompress.«i686-tables»
  step with decompress.«i686-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenientNat_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«i686-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«i686-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«i686-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«i686-tables»

namespace decompress.«x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«x86_64-no-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement51) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.IsNeg ∧
      X.LimbsLt 52 ∧ Y.LimbsLt 52 ∧
      Z.LimbsLt 52 ⦄ := by
  unfold step_1.«x86_64-no-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, hY, CompressedEdwardsY.asNat_def]
  apply spec_mono (Backend.edStep1Tail_spec Backend.U64 Backend.U64.add_spec Backend.U64.sub_spec
    Backend.U64.mul_spec Backend.U64.square_spec Backend.U64.edwardsD_spec Backend.U64.one_spec
    Backend.U64.sqrtRatioI_spec Y
    (limbs_lt_of_le (by decide) hY_lt))
  rintro ⟨c, X, Y', Z⟩ ⟨hcv, rfl, hZf, hc, hX, hXneg, hXb, hZb⟩
  exact ⟨hcv, hYf, hZf, hc, hX, hXneg, hXb, limbs_lt_of_le (by decide) hY_lt, hZb⟩

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^52`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement51)
    (hX : X.LimbsLt 52) (hY : Y.LimbsLt 52)
    (hZ : Z.LimbsLt 52) :
    step_2.«x86_64-no-tables» repr X Y Z ⦃ (r : EdwardsPoint.«x86_64-no-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 52 ⦄ := by
  rw [show step_2.«x86_64-no-tables» repr X Y Z = Backend.U64.edStep2Body
      (fun X Y Z T => ({ X, Y, Z, T } : EdwardsPoint.«x86_64-no-tables»)) repr X Y Z from rfl]
  apply spec_mono (Backend.edStep2Body_spec Backend.U64 Backend.U64.mul_spec
    Backend.U64.conditional_negate_spec _ repr X Y Z hX hY)
  rintro _ ⟨X1, T, rfl, h0, h1, hT, hX1b, hTb⟩
  have hT' : T.toField = X1.toField * Y.toField := hT
  refine ⟨fun h => ?_, fun h => ?_, ⟨hX1b, hY, hZ, hTb⟩⟩
  · rw [h0 h] at hT' ⊢
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, hT']
  · have hx : X1.toField = -X.toField := (h1 h)
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, hT', hx]

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«x86_64-no-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«x86_64-no-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«x86_64-no-tables».toPoint_x hon]
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«x86_64-no-tables».toPoint_y hon]
    simp only [EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-no-tables»

namespace decompress.«i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `decompress::step_1`: `Y` from the low `255` bits, `Z = 1`, and `(c, X) = sqrt_ratio_i (Y² - 1)
(d Y² + 1)`: `c = 1` iff `xSq Y` is a square, and then `X` is its non-negative root. -/
private theorem step_1_spec (repr : CompressedEdwardsY) :
    step_1.«i686-no-tables» repr ⦃ (c : subtle.Choice) (X Y Z : FieldElement2625) =>
      c.IsValid ∧ Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) ∧
      Z.toField = 1 ∧
      (c = 1#u8 ↔ IsSquare (curve25519.edwards.xSq Y.toField)) ∧
      (c = 1#u8 → X.toField ^ 2 = curve25519.edwards.xSq Y.toField) ∧ ¬ X.toField.IsNeg ∧
      X.LimbsLt 26 ∧ Y.LimbsLt 26 ∧
      Z.LimbsLt 26 ⦄ := by
  unfold step_1.«i686-no-tables»
  step as ⟨a, ha⟩
  step as ⟨Y, hY, hY_lt⟩
  rw [ha] at hY
  have hYf : Y.toField = ((CompressedEdwardsY.asNat repr % 2 ^ 255 : ℕ) : ZMod p) := by
    rw [toField_def, CompressedEdwardsY.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hY
  apply spec_mono (Backend.edStep1Tail_spec Backend.U32 Backend.U32.add_spec Backend.U32.sub_spec
    Backend.U32.mul_spec Backend.U32.square_spec Backend.U32.edwardsD_spec Backend.U32.one_spec
    Backend.U32.sqrtRatioI_spec Y
    (limbs_lt_of_le (by decide) hY_lt))
  rintro ⟨c, X, Y', Z⟩ ⟨hcv, rfl, hZf, hc, hX, hXneg, hXb, hZb⟩
  exact ⟨hcv, hYf, hZf, hc, hX, hXneg, hXb, limbs_lt_of_le (by decide) hY_lt, hZb⟩

/-- `decompress::step_2`: `X` negated when bit `255` is set, `T = X Y`; limbs `< 2^26`. -/
private theorem step_2_spec (repr : CompressedEdwardsY) (X Y Z : FieldElement2625)
    (hX : X.LimbsLt 26) (hY : Y.LimbsLt 26)
    (hZ : Z.LimbsLt 26) :
    step_2.«i686-no-tables» repr X Y Z ⦃ (r : EdwardsPoint.«i686-no-tables») =>
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 0 →
        r.toExtended = ⟨X.toField, Y.toField, Z.toField, X.toField * Y.toField⟩) ∧
      (CompressedEdwardsY.asNat repr / 2 ^ 255 = 1 →
        r.toExtended = ⟨-X.toField, Y.toField, Z.toField, -X.toField * Y.toField⟩) ∧
      r.LimbsLt 26 ⦄ := by
  rw [show step_2.«i686-no-tables» repr X Y Z = Backend.U32.edStep2Body
      (fun X Y Z T => ({ X, Y, Z, T } : EdwardsPoint.«i686-no-tables»)) repr X Y Z from rfl]
  apply spec_mono (Backend.edStep2Body_spec Backend.U32 Backend.U32.mul_spec
    Backend.U32.conditional_negate_spec _ repr X Y Z hX hY)
  rintro _ ⟨X1, T, rfl, h0, h1, hT, hX1b, hTb⟩
  have hT' : T.toField = X1.toField * Y.toField := hT
  refine ⟨fun h => ?_, fun h => ?_, ⟨hX1b, hY, hZ, hTb⟩⟩
  · rw [h0 h] at hT' ⊢
    simp only [EdwardsPoint.«i686-no-tables».toExtended_def, hT']
  · have hx : X1.toField = -X.toField := (h1 h)
    simp only [EdwardsPoint.«i686-no-tables».toExtended_def, hT', hx]

/-- The decompressed point `(x : y : 1 : x y)` with `x² = xSq y` is on the curve. -/
private theorem onCurve_and_toPoint_of_toExtended {ep : EdwardsPoint.«i686-no-tables»}
    {x y : ZMod p} (hx : x ^ 2 = curve25519.edwards.xSq y)
    (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [EdwardsPoint.«i686-no-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact equation_iff_sq_eq_xSq.mpr hx
  refine ⟨hon, ?_, ?_⟩
  · rw [EdwardsPoint.«i686-no-tables».toPoint_x hon]
    simp only [EdwardsPoint.«i686-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [EdwardsPoint.«i686-no-tables».toPoint_y hon]
    simp only [EdwardsPoint.«i686-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«i686-no-tables»

namespace CompressedEdwardsY.«x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenientNat` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^52`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option (EdwardsPoint.«x86_64-no-tables»)) =>
      r.map EdwardsPoint.«x86_64-no-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 52 ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.decodeLenient_toVector]
  unfold decompress.«x86_64-no-tables»
  step with decompress.«x86_64-no-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenientNat_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«x86_64-no-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-no-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«x86_64-no-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«x86_64-no-tables»

namespace CompressedEdwardsY.«i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `CompressedEdwardsY::decompress`: dalek's lenient decoding `decodeLenientNat` of the bytes'
value (`y` reduced modulo `p`, `x = 0` accepted with either sign); the point is on the curve with
limbs `< 2^26`. -/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress.«i686-no-tables» self ⦃ (r : Option (EdwardsPoint.«i686-no-tables»)) =>
      r.map EdwardsPoint.«i686-no-tables».toPoint = decodeLenient self.toVector ∧
      ∀ q, r = some q → q.OnCurve ∧ q.LimbsLt 26 ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.decodeLenient_toVector]
  unfold decompress.«i686-no-tables»
  step with decompress.«i686-no-tables».step_1_spec
    as ⟨c, X, Y, Z, hcv, hYf, hZf, hc, hX, hXneg, hX_lt, hY_lt, hZ_lt⟩
  step as ⟨b, hb⟩
  rcases hcv with rfl | rfl
  · simp only [hb, bne_self_eq_false, Bool.false_eq_true, ite_false, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, decodeLenientNat_eq_none_iff, ← hYf]
    exact fun hs => absurd (hc.mpr hs) (by decide)
  · simp only [hb, show (1#u8 != 0#u8) = true from by decide, ite_true]
    step with decompress.«i686-no-tables».step_2_spec as ⟨ep, hep0, hep1, hepb⟩
    rw [hZf] at hep0 hep1
    have hsq := hX rfl
    have hle := self.asNat_div_two_pow_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«i686-no-tables».onCurve_and_toPoint_of_toExtended hsq (hep0 h0)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf]) (fun _ => hpx)
        (fun h => absurd (h0.symm.trans h) (by decide)) hle
    · obtain ⟨hon, hpx, hpy⟩ :=
        edwards.decompress.«i686-no-tables».onCurve_and_toPoint_of_toExtended
          (by rw [neg_sq]; exact hsq) (hep1 h1)
      refine ⟨?_, fun q hq => Option.some.inj hq ▸ ⟨hon, hepb⟩⟩
      rw [Option.map_some, eq_comm]
      exact decodeLenientNat_eq_some_of_sign hXneg ep.toPoint (by rw [hpy, hYf])
        (fun h => absurd (h1.symm.trans h) (by decide)) (fun _ => hpx) hle

end CompressedEdwardsY.«i686-no-tables»

end Curve25519Dalek.edwards
