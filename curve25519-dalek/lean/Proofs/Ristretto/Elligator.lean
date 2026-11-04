/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Map
public import Defs.CurveModels
public import Defs.Edwards
import Proofs.Backend.Serial.U64.Field.FromBytes
public import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Helpers.ToField2625
public import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
public import Proofs.Field.SqrtRatioI
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # The Ristretto Elligator map (`ristretto/elligator.rs`)

`elligator_ristretto_flavor` is RFC 9496 §4.3.4 `MAP` (`Ristretto.mapRep`) step by step, the
point `(w0 : w2 : w1 : w3)` being formed as a completed point; `map_to_curve` applies it to the
low `255` bits of the bytes, reduced modulo `p`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `RistrettoPoint::elligator_ristretto_flavor` over a backend. -/
@[expose] def elligatorBody {P : Type} (mk : B.F → B.F → B.F → B.F → P) (r_0 : B.F) :
    Result P := do
  let fe ← B.constSqrtM1
  let fe1 ← B.constEdwardsD
  let fe2 ← B.constOneMinusDSq
  let fe3 ← B.constDMinusOneSq
  let c ← B.constMinusOne
  let one ← B.constOne
  let fe4 ← B.square r_0
  let r ← B.mul fe fe4
  let fe5 ← B.add r one
  let N_s ← B.mul fe5 fe2
  let fe6 ← B.mul fe1 r
  let fe7 ← B.sub c fe6
  let fe8 ← B.add r fe1
  let D ← B.mul fe7 fe8
  let (Ns_D_is_sq, s) ← B.sqrtRatioI N_s D
  let s_prime ← B.mul s r_0
  let c1 ← B.isNegative s_prime
  let s_prime_is_pos ← subtle.Choice.Insts.CoreOpsBitNotChoice.not c1
  let s_prime1 ← B.condNeg s_prime s_prime_is_pos
  let c2 ← subtle.Choice.Insts.CoreOpsBitNotChoice.not Ns_D_is_sq
  let s1 ← B.condAssign s s_prime1 c2
  let c3 ← B.condAssign c r c2
  let fe9 ← B.sub r one
  let fe10 ← B.mul c3 fe9
  let fe11 ← B.mul fe10 fe3
  let N_t ← B.sub fe11 D
  let s_sq ← B.square s1
  let fe12 ← B.add s1 s1
  let fe13 ← B.mul fe12 D
  let fe14 ← B.constSqrtAdMinusOne
  let fe15 ← B.mul N_t fe14
  let fe16 ← B.sub one s_sq
  let fe17 ← B.add one s_sq
  let ep ← B.completedAsExtended mk fe13 fe16 fe15 fe17
  ok ep

/-- `elligatorBody` is RFC 9496's `MAP(r₀)`, as an extended point. -/
theorem elligatorBody_spec (hadd : B.AddSpec) (hsub : B.SubSpec)
    (hmul : B.MulSpec) (hsq : B.SquareSpec) (hm1 : B.SqrtM1Spec) (hd : B.EdwardsDSpec)
    (h1d : B.OneMinusDSqSpec) (hd1 : B.DMinusOneSqSpec) (hmo : B.MinusOneSpec)
    (hone : B.OneSpec) (hsr : B.SqrtRatioISpec) (hisn : B.IsNegativeSpec)
    (hcn : B.CondNegSpec) (hca : B.CondAssignSpec) (hk : B.SqrtAdMinusOneSpec)
    {P : Type} (mk : B.F → B.F → B.F → B.F → P) (r_0 : B.F) (hr_0 : B.SqIn r_0) :
    B.elligatorBody mk r_0 ⦃ r => ∃ a b c d, r = mk a b c d ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Extended).OnCurve ∧
      (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Extended).toPoint =
        Ristretto.mapRep (B.toField r_0) ∧
      B.Red a ∧ B.Red b ∧ B.Red c ∧ B.Red d ⦄ := by
  unfold elligatorBody
  apply spec_bind hm1
  rintro fi ⟨Fi, hfib⟩
  apply spec_bind hd
  rintro fd ⟨Fd, hfdb⟩
  apply spec_bind h1d
  rintro f1d ⟨F1d, hf1db⟩
  apply spec_bind hd1
  rintro fd1 ⟨Fd1, hfd1b⟩
  apply spec_bind hmo
  rintro c ⟨C, hcb⟩
  apply spec_bind hone
  rintro one ⟨One, honeb⟩
  step with hsq r_0 hr_0 as ⟨fe4, hfe4, hfe4b⟩
  step with hmul fi fe4 (B.red_mulIn hfib) (B.red_mulIn hfe4b) as ⟨r, hr, hrb⟩
  step with hadd r one hrb honeb as ⟨fe5, hfe5, hfe5b⟩
  step with hmul fe5 f1d (B.sum2_mulIn hfe5b) (B.red_mulIn hf1db) as ⟨Ns, hNs, hNsb⟩
  step with hmul fd r (B.red_mulIn hfdb) (B.red_mulIn hrb) as ⟨fe6, hfe6, hfe6b⟩
  step with hsub c fe6 (B.red_mulIn hcb) (B.red_mulIn hfe6b) as ⟨fe7, hfe7, hfe7b⟩
  step with hadd r fd hrb hfdb as ⟨fe8, hfe8, hfe8b⟩
  step with hmul fe7 fe8 (B.red_mulIn hfe7b) (B.sum2_mulIn hfe8b) as ⟨D, hD, hDb⟩
  step with hsr Ns D (B.red_sqIn hNsb) (B.red_sqIn hDb) as
    ⟨sq, s, hsqv, hs0, hs1, hs2, hs3, hspar, hsb⟩
  step with hmul s r_0 (B.red_mulIn hsb) (B.sqIn_mulIn hr_0) as ⟨sp, hsp, hspb⟩
  step with hisn sp as ⟨c1, hc1v, hc1⟩
  step as ⟨pos, hposv, hpos⟩
  step with hcn sp pos hposv (B.red_mulIn hspb) as ⟨sp1, hsp10, hsp11⟩
  step as ⟨c2, hc2v, hc2⟩
  step with hca s sp1 c2 hc2v as ⟨s1, hs10, hs11⟩
  step with hca c r c2 hc2v as ⟨c3, hc30, hc31⟩
  have hsp1b : B.Red sp1 := by
    rcases hposv with h | h
    · rw [hsp10 h]; exact hspb
    · exact (hsp11 h).2
  have hs1b : B.Red s1 := by
    rcases hc2v with h | h
    · rw [hs10 h]; exact hsb
    · rw [hs11 h]; exact hsp1b
  have hc3b : B.Red c3 := by
    rcases hc2v with h | h
    · rw [hc30 h]; exact hcb
    · rw [hc31 h]; exact hrb
  step with hsub r one (B.red_mulIn hrb) (B.red_mulIn honeb) as ⟨fe9, hfe9, hfe9b⟩
  step with hmul c3 fe9 (B.red_mulIn hc3b) (B.red_mulIn hfe9b) as ⟨fe10, hfe10, hfe10b⟩
  step with hmul fe10 fd1 (B.red_mulIn hfe10b) (B.red_mulIn hfd1b) as ⟨fe11, hfe11, hfe11b⟩
  step with hsub fe11 D (B.red_mulIn hfe11b) (B.red_mulIn hDb) as ⟨Nt, hNt, hNtb⟩
  step with hsq s1 (B.red_sqIn hs1b) as ⟨ssq, hssq, hssqb⟩
  step with hadd s1 s1 hs1b hs1b as ⟨fe12, hfe12, hfe12b⟩
  step with hmul fe12 D (B.sum2_mulIn hfe12b) (B.red_mulIn hDb) as ⟨fe13, hfe13, hfe13b⟩
  apply spec_bind hk
  rintro fK ⟨K, hfKb⟩
  step with hmul Nt fK (B.red_mulIn hNtb) (B.red_mulIn hfKb) as ⟨fe15, hfe15, hfe15b⟩
  step with hsub one ssq (B.red_mulIn honeb) (B.red_mulIn hssqb) as ⟨fe16, hfe16, hfe16b⟩
  step with hadd one ssq honeb hssqb as ⟨fe17, hfe17, hfe17b⟩
  -- RFC 9496 §4.3.4 step by step
  set r' : ZMod p := sqrtM1 * B.toField r_0 ^ 2 with hr'
  have R : B.toField r = r' := by rw [hr, Fi, hfe4]
  set u' : ZMod p := (r' + 1) * (oneMinusDSq : ZMod p) with hu'
  have U : B.toField Ns = u' := by rw [hNs, hfe5, R, One, F1d, ← oneMinusDSq_eq]
  set v' : ZMod p := (-1 - r' * curve25519.d) * (r' + curve25519.d) with hv'
  have V : B.toField D = v' := by
    rw [hD, hfe7, hfe6, hfe8, C, Fd, R]
    ring
  have SQ := sqrtRatioM1_eq hs0 hs1 (fun h ⟨x, hx⟩ => hs2 h x hx) hs3 hspar
  rw [U, V] at SQ
  have S0 : B.toField s = (sqrtRatioM1 u' v').2 := by rw [SQ]
  have SQ1 : sq = 1#u8 ↔ (sqrtRatioM1 u' v').1 = true := by rw [SQ]; simp
  have Sp : B.toField sp = (sqrtRatioM1 u' v').2 * B.toField r_0 := by rw [hsp, S0]
  have Pos : pos = 1#u8 ↔ ¬ (B.toField sp).IsNeg := by
    rw [hpos, ← eq_one_iff_isNeg hc1]
    rcases hc1v with rfl | rfl <;> decide
  have Sp1 : B.toField sp1 = -((sqrtRatioM1 u' v').2 * B.toField r_0).abs := by
    have h := eq_ite_of_choice hposv Pos (fun h => by rw [hsp10 h]) (fun h => (hsp11 h).1)
    rw [h, ← Sp]
    by_cases hn : (B.toField sp).IsNeg
    · rw [ite_eq_right (not_not.mpr hn), ZMod.abs_of_isNeg hn, neg_neg]
    · rw [ite_eq_left hn, ZMod.abs_of_not_isNeg hn]
  have C2 : c2 = 1#u8 ↔ ¬ (sqrtRatioM1 u' v').1 = true := by
    rw [hc2, ← SQ1]
    rcases hsqv with rfl | rfl <;> decide
  set S : ZMod p := if (sqrtRatioM1 u' v').1 then (sqrtRatioM1 u' v').2
    else -((sqrtRatioM1 u' v').2 * B.toField r_0).abs with hS
  have S1 : B.toField s1 = S := by
    have h : B.toField s1 =
        if ¬ (sqrtRatioM1 u' v').1 = true then B.toField sp1 else B.toField s :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hs10 h]) (fun h => by rw [hs11 h])
    rw [h, Sp1, S0, hS]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set Cc : ZMod p := if (sqrtRatioM1 u' v').1 then -1 else r' with hCc
  have C3 : B.toField c3 = Cc := by
    have h : B.toField c3 =
        if ¬ (sqrtRatioM1 u' v').1 = true then B.toField r else B.toField c :=
      eq_ite_of_choice hc2v C2 (fun h => by rw [hc30 h]) (fun h => by rw [hc31 h])
    rw [h, C, R, hCc]
    by_cases hb : (sqrtRatioM1 u' v').1 = true
    · rw [ite_eq_right (not_not.mpr hb), ite_eq_left hb]
    · rw [ite_eq_left hb, ite_eq_right hb]
  set N : ZMod p := Cc * (r' - 1) * (dMinusOneSq : ZMod p) - v' with hN
  have NT : B.toField Nt = N := by
    rw [hNt, hfe11, hfe10, C3, hfe9, R, One, Fd1, ← dMinusOneSq_eq, V]
  have X13 : B.toField fe13 = 2 * S * v' := by
    rw [hfe13, hfe12, S1, V]
    ring
  have Z15 : B.toField fe15 = N * sqrtAdMinusOne := by rw [hfe15, NT, K]
  have Y16 : B.toField fe16 = 1 - S ^ 2 := by rw [hfe16, One, hssq, S1]
  have T17 : B.toField fe17 = 1 + S ^ 2 := by rw [hfe17, One, hssq, S1]
  have hon : (⟨B.toField fe13, B.toField fe16, B.toField fe15, B.toField fe17⟩ :
      edwards.Completed).OnCurve := by
    change _ ∧ _ ∧ _
    dsimp only
    rw [X13, Z15, Y16, T17]
    exact ⟨Ristretto.mapRep_den_ne_zero _, Ristretto.mapRep_one_add_sq_ne_zero _,
      Ristretto.mapRep_equation _⟩
  apply spec_bind (completedAsExtended_spec B hmul mk fe13 fe16 fe15 fe17
    (B.red_mulIn hfe13b) (B.red_mulIn hfe16b) (B.red_mulIn hfe15b) (B.sum2_mulIn hfe17b))
  rintro _ ⟨a, b, c, d, rfl, h, ha, hb, hc, hd⟩
  rw [spec_ok]
  refine ⟨a, b, c, d, rfl, ?_, ?_, ha, hb, hc, hd⟩
  · rw [h]
    exact Completed.onCurve_toExtended hon
  · rw [h, Completed.toPoint_toExtended hon]
    apply Point.ext
    · rw [Completed.toPoint_x hon, Ristretto.mapRep_x]
      dsimp only
      rw [X13, Z15]
    · rw [Completed.toPoint_y hon, Ristretto.mapRep_y]
      dsimp only
      rw [Y16, T17]

end Curve25519Dalek.Backend

namespace Curve25519Dalek.ristretto.elligator

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem elligator_ristretto_flavor_eq (r_0 : FieldElement51) :
    elligator_ristretto_flavor r_0 = Backend.elligatorBody Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-tables»)) r_0 := rfl

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^54` in,
`< 2^52` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement51) (hr_0 : r_0.LimbsLt 54) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 52 ⦄ := by
  rw [elligator_ristretto_flavor_eq]
  apply spec_mono (Backend.elligatorBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.sqrtM1_spec Backend.U64.edwardsD_spec Backend.U64.oneMinusDSq_spec
    Backend.U64.dMinusOneSq_spec Backend.U64.minusOne_spec Backend.U64.one_spec
    Backend.U64.sqrtRatioI_spec Backend.U64.is_negative_spec Backend.U64.conditional_negate_spec
    Backend.U64.conditional_assign_spec Backend.U64.sqrtAdMinusOne_spec _ r_0 hr_0)
  rintro _ ⟨a, b, c, d, rfl, hon, hpt, ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ha, hb, hc, hd⟩
  · rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
    exact hon
  · rw [edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
      edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
    exact hpt

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`): an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧
        r.LimbsLt 52 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact Ristretto.even_mapRep _, h, h3⟩) ?_
  rw [h2, toField_eq_decodeU_of_asNat_eq hfe]

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem elligator_ristretto_flavor_eq (r_0 : FieldElement2625) :
    elligator_ristretto_flavor r_0 = Backend.elligatorBody Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-tables»)) r_0 := rfl

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^27` in,
`< 2^26` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement2625) (hr_0 : r_0.LimbsLt 27) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 26 ⦄ := by
  rw [elligator_ristretto_flavor_eq]
  apply spec_mono (Backend.elligatorBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.sqrtM1_spec Backend.U32.edwardsD_spec Backend.U32.oneMinusDSq_spec
    Backend.U32.dMinusOneSq_spec Backend.U32.minusOne_spec Backend.U32.one_spec
    Backend.U32.sqrtRatioI_spec Backend.U32.is_negative_spec Backend.U32.conditional_negate_spec
    Backend.U32.conditional_assign_spec Backend.U32.sqrtAdMinusOne_spec _ r_0 hr_0)
  rintro _ ⟨a, b, c, d, rfl, hon, hpt, ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ha, hb, hc, hd⟩
  · rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-tables».toExtended_def]
    exact hon
  · rw [edwards.EdwardsPoint.«i686-tables».toPoint_def,
      edwards.EdwardsPoint.«i686-tables».toExtended_def]
    exact hpt

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`): an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧
        r.LimbsLt 26 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact Ristretto.even_mapRep _, h, h3⟩) ?_
  rw [h2, toField_eq_decodeU_of_mod hfe]

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem elligator_ristretto_flavor_eq (r_0 : FieldElement51) :
    elligator_ristretto_flavor r_0 = Backend.elligatorBody Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-no-tables»)) r_0 := rfl

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^54` in,
`< 2^52` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement51) (hr_0 : r_0.LimbsLt 54) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 52 ⦄ := by
  rw [elligator_ristretto_flavor_eq]
  apply spec_mono (Backend.elligatorBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.sqrtM1_spec Backend.U64.edwardsD_spec Backend.U64.oneMinusDSq_spec
    Backend.U64.dMinusOneSq_spec Backend.U64.minusOne_spec Backend.U64.one_spec
    Backend.U64.sqrtRatioI_spec Backend.U64.is_negative_spec Backend.U64.conditional_negate_spec
    Backend.U64.conditional_assign_spec Backend.U64.sqrtAdMinusOne_spec _ r_0 hr_0)
  rintro _ ⟨a, b, c, d, rfl, hon, hpt, ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ha, hb, hc, hd⟩
  · rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
    exact hon
  · rw [edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
      edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
    exact hpt

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`): an even point (a ristretto255 representative); limbs `< 2^52`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧
        r.LimbsLt 52 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact Ristretto.even_mapRep _, h, h3⟩) ?_
  rw [h2, toField_eq_decodeU_of_asNat_eq hfe]

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem elligator_ristretto_flavor_eq (r_0 : FieldElement2625) :
    elligator_ristretto_flavor r_0 = Backend.elligatorBody Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-no-tables»)) r_0 := rfl

/-- `RistrettoPoint::elligator_ristretto_flavor`: RFC 9496's `MAP(r₀)`; limbs `< 2^27` in,
`< 2^26` out. -/
@[step]
theorem elligator_ristretto_flavor_spec (r_0 : FieldElement2625) (hr_0 : r_0.LimbsLt 27) :
    elligator_ristretto_flavor r_0 ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = Ristretto.mapRep r_0.toField ∧ r.LimbsLt 26 ⦄ := by
  rw [elligator_ristretto_flavor_eq]
  apply spec_mono (Backend.elligatorBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.sqrtM1_spec Backend.U32.edwardsD_spec Backend.U32.oneMinusDSq_spec
    Backend.U32.dMinusOneSq_spec Backend.U32.minusOne_spec Backend.U32.one_spec
    Backend.U32.sqrtRatioI_spec Backend.U32.is_negative_spec Backend.U32.conditional_negate_spec
    Backend.U32.conditional_assign_spec Backend.U32.sqrtAdMinusOne_spec _ r_0 hr_0)
  rintro _ ⟨a, b, c, d, rfl, hon, hpt, ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ha, hb, hc, hd⟩
  · rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
      edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
    exact hon
  · rw [edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
      edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
    exact hpt

/-- `RistrettoPoint::map_to_curve`: RFC 9496's `MAP` of the low `255` bits of the bytes, reduced
modulo `p` (`decodeU`): an even point (a ristretto255 representative); limbs `< 2^26`. -/
@[step]
theorem map_to_curve_spec (bytes : Array U8 32#usize) :
    map_to_curve bytes ⦃ (r : RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ Even r.toPoint ∧ r.toPoint = Ristretto.mapRep (decodeU (bytes.asNat 8)) ∧
        r.LimbsLt 26 ⦄ := by
  unfold map_to_curve
  step as ⟨fe, hfe, hfeb⟩
  step as ⟨r, h1, h2, h3⟩
  refine (fun h => ⟨h1, by rw [h]; exact Ristretto.even_mapRep _, h, h3⟩) ?_
  rw [h2, toField_eq_decodeU_of_mod hfe]

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto.elligator
