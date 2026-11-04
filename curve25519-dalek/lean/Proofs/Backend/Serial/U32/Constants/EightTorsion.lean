/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Torsion
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Backend.Serial.U32.Field.FromLimbs
import Proofs.Helpers.Coords
import Proofs.Helpers.FieldElement2625
import Proofs.Helpers.ToField2625
public section

/-! # `EIGHT_TORSION`

Entry `i` is the point `eightTorsion i = i • torsion8` of `curve25519` in the extended coordinates
`(x : y : 1 : x y)`; the limbs are compared with the coordinates of
`Curve25519/Edwards/Torsion.lean` as numbers. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

namespace Curve25519Dalek.backend.serial.u32.constants

namespace «i686-tables»

/-- `EIGHT_TORSION`: entry `i` has the extended coordinates `(x : y : 1 : x y)` of
`eightTorsion i = i • torsion8`; limbs `< 2^26`. -/
@[step]
theorem EIGHT_TORSION_spec :
    EIGHT_TORSION.«i686-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.toExtended = (eightTorsion i).toExtended ∧ r[i.val]!.LimbsLt 26 ⦄ := by
  unfold EIGHT_TORSION.«i686-tables» EIGHT_TORSION_INNER_DOC_HIDDEN.«i686-tables»
  step as ⟨f0, h0⟩
  step as ⟨f1, h1⟩
  step as ⟨f2, h2⟩
  step as ⟨f3, h3⟩
  step as ⟨f4, h4⟩
  step as ⟨f5, h5⟩
  step as ⟨f6, h6⟩
  step as ⟨f7, h7⟩
  step as ⟨f8, h8⟩
  step as ⟨f9, h9⟩
  step as ⟨f10, h10⟩
  step as ⟨f11, h11⟩
  step as ⟨f12, h12⟩
  step as ⟨f13, h13⟩
  step as ⟨f14, h14⟩
  step as ⟨f15, h15⟩
  step as ⟨f16, h16⟩
  step as ⟨f17, h17⟩
  have hz : ∀ f : FieldElement2625, f = Array.repeat 10#usize 0#u32 → f.toField = 0 :=
    fun f hf => hf ▸ toField_repeat_zero
  have f1n : f1.asNat = 1 := by rw [h1, asNat_def, Array.asNat2625_make]; decide
  have f3n : f3.asNat =
      14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
    rw [h3, asNat_def, Array.asNat2625_make]; decide
  have f4n : f4.asNat =
      55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
    rw [h4, asNat_def, Array.asNat2625_make]; decide
  have f6n : f6.asNat =
      38214883241950591754978413199355411911188925816896391856984770930832735035197 := by
    rw [h6, asNat_def, Array.asNat2625_make]; decide
  have f9n : f9.asNat =
      2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
    rw [h9, asNat_def, Array.asNat2625_make]; decide
  have f12n : f12.asNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
    rw [h12, asNat_def, Array.asNat2625_make]; decide
  have f14n : f14.asNat =
      43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
    rw [h14, asNat_def, Array.asNat2625_make]; decide
  have f15n : f15.asNat =
      19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
    rw [h15, asNat_def, Array.asNat2625_make]; decide
  have hT5 : f5.asNat % p = f3.asNat * f4.asNat % p := by
    rw [f3n, f4n, h5, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT10 : f10.asNat % p = f3.asNat * f9.asNat % p := by
    rw [f3n, f9n, h10, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT5' : f5.asNat % p = f14.asNat * f9.asNat % p := by
    rw [f14n, f9n, h5, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT10' : f10.asNat % p = f14.asNat * f4.asNat % p := by
    rw [f14n, f4n, h10, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have b0 : f0.LimbsLt 26 := by rw [h0]; decide
  have b1 : f1.LimbsLt 26 := by rw [h1]; decide
  have b2 : f2.LimbsLt 26 := by rw [h2]; decide
  have b3 : f3.LimbsLt 26 := by rw [h3]; decide
  have b4 : f4.LimbsLt 26 := by rw [h4]; decide
  have b5 : f5.LimbsLt 26 := by rw [h5]; decide
  have b6 : f6.LimbsLt 26 := by rw [h6]; decide
  have b7 : f7.LimbsLt 26 := by rw [h7]; decide
  have b8 : f8.LimbsLt 26 := by rw [h8]; decide
  have b9 : f9.LimbsLt 26 := by rw [h9]; decide
  have b10 : f10.LimbsLt 26 := by rw [h10]; decide
  have b11 : f11.LimbsLt 26 := by rw [h11]; decide
  have b12 : f12.LimbsLt 26 := by rw [h12]; decide
  have b13 : f13.LimbsLt 26 := by rw [h13]; decide
  have b14 : f14.LimbsLt 26 := by rw [h14]; decide
  have b15 : f15.LimbsLt 26 := by rw [h15]; decide
  have b16 : f16.LimbsLt 26 := by rw [h16]; decide
  have b17 : f17.LimbsLt 26 := by rw [h17]; decide
  have e0 : (⟨f0, f1, f1, f2⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 0).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended, eightTorsion_zero,
      zero_x, zero_y, hz f2 h2, hz f0 h0, toField_eq_one_of_asNat f1n]
    rw [zero_mul]
  have e1 : (⟨f3, f4, f1, f5⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 1).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended, eightTorsion_one,
      torsion8_x_eq, torsion8_y_eq, toField_mul_of_mod hT5, toField_eq_ofNat_of_asNat f3n,
      toField_eq_ofNat_of_asNat f4n, toField_eq_one_of_asNat f1n]
  have e2 : (⟨f6, f7, f1, f8⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 2).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_two_x_eq, eightTorsion_two_y_eq, hz f8 h8, toField_eq_ofNat_of_asNat f6n,
      hz f7 h7, toField_eq_one_of_asNat f1n]
    rw [mul_zero]
  have e3 : (⟨f3, f9, f1, f10⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 3).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_three_x_eq, eightTorsion_three_y_eq, toField_mul_of_mod hT10,
      toField_eq_ofNat_of_asNat f3n, toField_eq_ofNat_of_asNat f9n, toField_eq_one_of_asNat f1n]
  have e4 : (⟨f11, f12, f1, f13⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 4).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_four_x_eq, eightTorsion_four_y_eq, hz f13 h13, hz f11 h11,
      toField_eq_ofNat_of_asNat f12n, toField_eq_one_of_asNat f1n]
    rw [zero_mul]
  have e5 : (⟨f14, f9, f1, f5⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 5).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_five_x_eq, eightTorsion_five_y_eq, toField_mul_of_mod hT5',
      toField_eq_ofNat_of_asNat f14n, toField_eq_ofNat_of_asNat f9n, toField_eq_one_of_asNat f1n]
  have e6 : (⟨f15, f16, f1, f17⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 6).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_six_x_eq, eightTorsion_six_y_eq, hz f17 h17, toField_eq_ofNat_of_asNat f15n,
      hz f16 h16, toField_eq_one_of_asNat f1n]
    rw [mul_zero]
  have e7 : (⟨f14, f4, f1, f10⟩ : edwards.EdwardsPoint.«i686-tables»).toExtended =
      (eightTorsion 7).toExtended := by
    rw [edwards.EdwardsPoint.«i686-tables».toExtended_def, Point.toExtended,
      eightTorsion_seven_x_eq, eightTorsion_seven_y_eq, toField_mul_of_mod hT10',
      toField_eq_ofNat_of_asNat f14n, toField_eq_ofNat_of_asNat f4n, toField_eq_one_of_asNat f1n]
  intro i
  fin_cases i
  · exact ⟨e0, b0, b1, b1, b2⟩
  · exact ⟨e1, b3, b4, b1, b5⟩
  · exact ⟨e2, b6, b7, b1, b8⟩
  · exact ⟨e3, b3, b9, b1, b10⟩
  · exact ⟨e4, b11, b12, b1, b13⟩
  · exact ⟨e5, b14, b9, b1, b5⟩
  · exact ⟨e6, b15, b16, b1, b17⟩
  · exact ⟨e7, b14, b4, b1, b10⟩

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
theorem EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«i686-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧
        r[i.val]!.LimbsLt 26 ⦄ :=
  spec_mono EIGHT_TORSION_spec fun r h i => by
    obtain ⟨hr, hb⟩ := h i
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «i686-tables»

namespace «i686-no-tables»

/-- `EIGHT_TORSION`: entry `i` has the extended coordinates `(x : y : 1 : x y)` of
`eightTorsion i = i • torsion8`; limbs `< 2^26`. -/
@[step]
theorem EIGHT_TORSION_spec :
    EIGHT_TORSION.«i686-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.toExtended = (eightTorsion i).toExtended ∧ r[i.val]!.LimbsLt 26 ⦄ := by
  unfold EIGHT_TORSION.«i686-no-tables» EIGHT_TORSION_INNER_DOC_HIDDEN.«i686-no-tables»
  step as ⟨f0, h0⟩
  step as ⟨f1, h1⟩
  step as ⟨f2, h2⟩
  step as ⟨f3, h3⟩
  step as ⟨f4, h4⟩
  step as ⟨f5, h5⟩
  step as ⟨f6, h6⟩
  step as ⟨f7, h7⟩
  step as ⟨f8, h8⟩
  step as ⟨f9, h9⟩
  step as ⟨f10, h10⟩
  step as ⟨f11, h11⟩
  step as ⟨f12, h12⟩
  step as ⟨f13, h13⟩
  step as ⟨f14, h14⟩
  step as ⟨f15, h15⟩
  step as ⟨f16, h16⟩
  step as ⟨f17, h17⟩
  have hz : ∀ f : FieldElement2625, f = Array.repeat 10#usize 0#u32 → f.toField = 0 :=
    fun f hf => hf ▸ toField_repeat_zero
  have f1n : f1.asNat = 1 := by rw [h1, asNat_def, Array.asNat2625_make]; decide
  have f3n : f3.asNat =
      14399317868200118260347934320527232580618823971194345261214217575416788799818 := by
    rw [h3, asNat_def, Array.asNat2625_make]; decide
  have f4n : f4.asNat =
      55188659117513257062467267217118295137698188065244968500265048394206261417927 := by
    rw [h4, asNat_def, Array.asNat2625_make]; decide
  have f6n : f6.asNat =
      38214883241950591754978413199355411911188925816896391856984770930832735035197 := by
    rw [h6, asNat_def, Array.asNat2625_make]; decide
  have f9n : f9.asNat =
      2707385501144840649318225287225658788936804267575313519463743609750303402022 := by
    rw [h9, asNat_def, Array.asNat2625_make]; decide
  have f12n : f12.asNat =
      57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
    rw [h12, asNat_def, Array.asNat2625_make]; decide
  have f14n : f14.asNat =
      43496726750457979451437558183816721346016168361625936758514574428539776020131 := by
    rw [h14, asNat_def, Array.asNat2625_make]; decide
  have f15n : f15.asNat =
      19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
    rw [h15, asNat_def, Array.asNat2625_make]; decide
  have hT5 : f5.asNat % p = f3.asNat * f4.asNat % p := by
    rw [f3n, f4n, h5, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT10 : f10.asNat % p = f3.asNat * f9.asNat % p := by
    rw [f3n, f9n, h10, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT5' : f5.asNat % p = f14.asNat * f9.asNat % p := by
    rw [f14n, f9n, h5, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have hT10' : f10.asNat % p = f14.asNat * f4.asNat % p := by
    rw [f14n, f4n, h10, asNat_def, Array.asNat2625_make, p_eq_numeral]; decide
  have b0 : f0.LimbsLt 26 := by rw [h0]; decide
  have b1 : f1.LimbsLt 26 := by rw [h1]; decide
  have b2 : f2.LimbsLt 26 := by rw [h2]; decide
  have b3 : f3.LimbsLt 26 := by rw [h3]; decide
  have b4 : f4.LimbsLt 26 := by rw [h4]; decide
  have b5 : f5.LimbsLt 26 := by rw [h5]; decide
  have b6 : f6.LimbsLt 26 := by rw [h6]; decide
  have b7 : f7.LimbsLt 26 := by rw [h7]; decide
  have b8 : f8.LimbsLt 26 := by rw [h8]; decide
  have b9 : f9.LimbsLt 26 := by rw [h9]; decide
  have b10 : f10.LimbsLt 26 := by rw [h10]; decide
  have b11 : f11.LimbsLt 26 := by rw [h11]; decide
  have b12 : f12.LimbsLt 26 := by rw [h12]; decide
  have b13 : f13.LimbsLt 26 := by rw [h13]; decide
  have b14 : f14.LimbsLt 26 := by rw [h14]; decide
  have b15 : f15.LimbsLt 26 := by rw [h15]; decide
  have b16 : f16.LimbsLt 26 := by rw [h16]; decide
  have b17 : f17.LimbsLt 26 := by rw [h17]; decide
  have e0 : (⟨f0, f1, f1, f2⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 0).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended, eightTorsion_zero,
      zero_x, zero_y, hz f2 h2, hz f0 h0, toField_eq_one_of_asNat f1n]
    rw [zero_mul]
  have e1 : (⟨f3, f4, f1, f5⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 1).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended, eightTorsion_one,
      torsion8_x_eq, torsion8_y_eq, toField_mul_of_mod hT5, toField_eq_ofNat_of_asNat f3n,
      toField_eq_ofNat_of_asNat f4n, toField_eq_one_of_asNat f1n]
  have e2 : (⟨f6, f7, f1, f8⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 2).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_two_x_eq, eightTorsion_two_y_eq, hz f8 h8, toField_eq_ofNat_of_asNat f6n,
      hz f7 h7, toField_eq_one_of_asNat f1n]
    rw [mul_zero]
  have e3 : (⟨f3, f9, f1, f10⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 3).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_three_x_eq, eightTorsion_three_y_eq, toField_mul_of_mod hT10,
      toField_eq_ofNat_of_asNat f3n, toField_eq_ofNat_of_asNat f9n, toField_eq_one_of_asNat f1n]
  have e4 : (⟨f11, f12, f1, f13⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 4).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_four_x_eq, eightTorsion_four_y_eq, hz f13 h13, hz f11 h11,
      toField_eq_ofNat_of_asNat f12n, toField_eq_one_of_asNat f1n]
    rw [zero_mul]
  have e5 : (⟨f14, f9, f1, f5⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 5).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_five_x_eq, eightTorsion_five_y_eq, toField_mul_of_mod hT5',
      toField_eq_ofNat_of_asNat f14n, toField_eq_ofNat_of_asNat f9n, toField_eq_one_of_asNat f1n]
  have e6 : (⟨f15, f16, f1, f17⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 6).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_six_x_eq, eightTorsion_six_y_eq, hz f17 h17, toField_eq_ofNat_of_asNat f15n,
      hz f16 h16, toField_eq_one_of_asNat f1n]
    rw [mul_zero]
  have e7 : (⟨f14, f4, f1, f10⟩ : edwards.EdwardsPoint.«i686-no-tables»).toExtended =
      (eightTorsion 7).toExtended := by
    rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Point.toExtended,
      eightTorsion_seven_x_eq, eightTorsion_seven_y_eq, toField_mul_of_mod hT10',
      toField_eq_ofNat_of_asNat f14n, toField_eq_ofNat_of_asNat f4n, toField_eq_one_of_asNat f1n]
  intro i
  fin_cases i
  · exact ⟨e0, b0, b1, b1, b2⟩
  · exact ⟨e1, b3, b4, b1, b5⟩
  · exact ⟨e2, b6, b7, b1, b8⟩
  · exact ⟨e3, b3, b9, b1, b10⟩
  · exact ⟨e4, b11, b12, b1, b13⟩
  · exact ⟨e5, b14, b9, b1, b5⟩
  · exact ⟨e6, b15, b16, b1, b17⟩
  · exact ⟨e7, b14, b4, b1, b10⟩

/-- `EIGHT_TORSION`: entry `i` represents `eightTorsion i = i • torsion8`. -/
theorem EIGHT_TORSION_spec_point :
    EIGHT_TORSION.«i686-no-tables»
      ⦃ (r : Array edwards.EdwardsPoint.«i686-no-tables» 8#usize) =>
      ∀ i : Fin 8, r[i.val]!.OnCurve ∧ r[i.val]!.toPoint = eightTorsion i ∧
        r[i.val]!.LimbsLt 26 ⦄ :=
  spec_mono EIGHT_TORSION_spec fun r h i => by
    obtain ⟨hr, hb⟩ := h i
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toPoint_def, hr]
    exact ⟨Point.onCurve_toExtended _, Point.toPoint_toExtended _, hb⟩

end «i686-no-tables»

end Curve25519Dalek.backend.serial.u32.constants
