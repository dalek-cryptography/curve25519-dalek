/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Encoding
public import Defs.Edwards
public import Defs.Ristretto
import Proofs.Backend.Serial.U64.Constants.EdwardsD
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.ConditionalNegate
import Proofs.Backend.Serial.U64.Field.FromBytes
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Neg
import Proofs.Backend.Serial.U64.Field.One
import Proofs.Backend.Serial.U64.Field.Square
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.Invsqrt
import Proofs.Field.IsNegative
import Proofs.Field.IsZero
import Proofs.Helpers.Array
import Proofs.Helpers.AsNat
import Proofs.Helpers.Coords
import Proofs.Helpers.ToField
import Proofs.Ristretto.AsBytes
import Subtle.Instances
import Mathlib.Tactic.LinearCombination
import Proofs.Backend.Serial.U32.Constants.EdwardsD
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.ConditionalNegate
import Proofs.Backend.Serial.U32.Field.FromBytes
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Neg
import Proofs.Backend.Serial.U32.Field.One
import Proofs.Backend.Serial.U32.Field.Square
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public import Proofs.Field.Invsqrt
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # `CompressedRistretto::decompress`

RFC 9496 §4.3.1: `step_1` reads `s` and checks that the encoding is canonical (`s < p`) and
non-negative; `step_2` computes the candidate point and the three rejection tests. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.ristretto

namespace decompress

/-! The quantities of RFC 9496 §4.3.1 as functions of `s`. -/

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
private noncomputable def dU1 (s : ZMod p) : ZMod p := 1 - s ^ 2
private noncomputable def dU2 (s : ZMod p) : ZMod p := 1 + s ^ 2
private noncomputable def dV (s : ZMod p) : ZMod p := -(d * dU1 s ^ 2) - dU2 s ^ 2
private noncomputable def dW (s : ZMod p) : ZMod p := dV s * dU2 s ^ 2
private noncomputable def dR (s : ZMod p) : ZMod p := (sqrtRatioM1 1 (dW s)).2
private noncomputable def dX (s : ZMod p) : ZMod p := (2 * s * (dR s * dU2 s)).abs
private noncomputable def dY (s : ZMod p) : ZMod p := dU1 s * (dR s * (dR s * dU2 s) * dV s)

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- The bytes are the canonical encoding of the low `255` bits reduced modulo `p` iff their value
is below `p`. -/
private theorem mod_mod_eq_iff (n : ℕ) : n % 2 ^ 255 % p = n ↔ n < p := by
  constructor
  · intro h
    rw [← h]
    exact Nat.mod_lt _ p_pos
  · intro h
    rw [Nat.mod_eq_of_lt (h.trans p_lt_two_pow_255), Nat.mod_eq_of_lt h]

open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- When `v u2²` has an inverse square root, the candidate point is on the curve and
`y = (1 - s²) / (1 + s²)`. -/
private theorem candidate_facts {s : ZMod p} (h : (sqrtRatioM1 1 (dW s)).1 = true) :
    edwards.Equation (dX s) (dY s) ∧ dY s = (1 - s ^ 2) / (1 + s ^ 2) := by
  have hr : dW s * dR s ^ 2 = 1 := sqrtRatioM1_one_of_fst h
  refine ⟨Ristretto.decodeRep_equation s (dR s) hr, ?_⟩
  have hu2 : dU2 s ≠ 0 := fun h0 => by
    unfold dW at hr
    rw [h0] at hr
    simp at hr
  rw [eq_div_iff (show 1 + s ^ 2 ≠ 0 from hu2)]
  unfold dW dV at hr
  unfold dY dV dU1 dU2 at *
  linear_combination (1 - s ^ 2) * hr


/-- `decompress::step_2` over a backend. -/
@[expose] def step2Body (B : Backend) {P : Type} (mk : B.F → B.F → B.F → B.F → P) (s : B.F) :
    Result (subtle.Choice × subtle.Choice × subtle.Choice × P) := do
  let one ← B.constOne
  let ss ← B.square s
  let u1 ← B.sub one ss
  let u2 ← B.add one ss
  let u2_sqr ← B.square u2
  let fe ← B.constEdwardsD
  let fe1 ← B.neg fe
  let fe2 ← B.square u1
  let fe3 ← B.mul fe1 fe2
  let v ← B.sub fe3 u2_sqr
  let fe4 ← B.mul v u2_sqr
  let (ok1, I) ← B.invsqrt fe4
  let Dx ← B.mul I u2
  let fe5 ← B.mul Dx v
  let Dy ← B.mul I fe5
  let fe6 ← B.add s s
  let x ← B.mul fe6 Dx
  let x_neg ← B.isNegative x
  let x1 ← B.condNeg x x_neg
  let y ← B.mul u1 Dy
  let t ← B.mul x1 y
  let c ← B.isNegative t
  let c1 ← B.isZero y
  ok (ok1, c, c1, mk x1 y one t)

/-- `step2Body`: the candidate point `(x, y, 1, x y)` of RFC 9496 §4.3.1 and its three tests. -/
private theorem step2Body_spec (B : Backend) (hadd : B.AddSpec) (hsub : B.SubSpec)
    (hmul : B.MulSpec) (hsq : B.SquareSpec) (hneg : B.NegSpec) (hD : B.EdwardsDSpec)
    (hone : B.OneSpec) (hinv : B.InvsqrtSpec) (hisn : B.IsNegativeSpec) (hcng : B.CondNegSpec)
    (hisz : B.IsZeroSpec) {P : Type} (mk : B.F → B.F → B.F → B.F → P) (s : B.F)
    (hs : B.Red s) :
    step2Body B mk s ⦃ (ok1 : subtle.Choice) (tn : subtle.Choice) (yz : subtle.Choice)
        (res : P) =>
      ok1.IsValid ∧ (ok1 = 1#u8 ↔ (sqrtRatioM1 1 (dW (B.toField s))).1 = true) ∧
      tn.IsValid ∧ (tn = 1#u8 ↔ (dX (B.toField s) * dY (B.toField s)).IsNeg) ∧
      yz.IsValid ∧ (yz = 1#u8 ↔ dY (B.toField s) = 0) ∧
      ∃ a b c d, res = mk a b c d ∧
        (⟨B.toField a, B.toField b, B.toField c, B.toField d⟩ : edwards.Extended) =
          ⟨dX (B.toField s), dY (B.toField s), 1, dX (B.toField s) * dY (B.toField s)⟩ ∧
        B.Red a ∧ B.Red b ∧ B.Red c ∧ B.Red d ⦄ := by
  unfold step2Body
  apply spec_bind hone
  rintro one ⟨F1, honeb⟩
  step with hsq s (B.red_sqIn hs) as ⟨ss, hss, hssb⟩
  step with hsub one ss (B.red_mulIn honeb) (B.red_mulIn hssb) as ⟨u1, hu1, hu1b⟩
  step with hadd one ss honeb hssb as ⟨u2, hu2, hu2b⟩
  step with hsq u2 (B.sum2_sqIn hu2b) as ⟨u2s, hu2s, hu2sb⟩
  apply spec_bind hD
  rintro fd ⟨Fd, hfdb⟩
  step with hneg fd (B.red_mulIn hfdb) as ⟨fe1, hfe1, hfe1b⟩
  step with hsq u1 (B.red_sqIn hu1b) as ⟨fe2, hfe2, hfe2b⟩
  step with hmul fe1 fe2 (B.red_mulIn hfe1b) (B.red_mulIn hfe2b) as ⟨fe3, hfe3, hfe3b⟩
  step with hsub fe3 u2s (B.red_mulIn hfe3b) (B.red_mulIn hu2sb) as ⟨v, hv, hvb⟩
  step with hmul v u2s (B.red_mulIn hvb) (B.red_mulIn hu2sb) as ⟨fe4, hfe4, hfe4b⟩
  step with hinv fe4 (B.red_sqIn hfe4b) as ⟨ok1, I, hInv, hokv, hIb⟩
  step with hmul I u2 (B.red_mulIn hIb) (B.sum2_mulIn hu2b) as ⟨Dx, hDx, hDxb⟩
  step with hmul Dx v (B.red_mulIn hDxb) (B.red_mulIn hvb) as ⟨fe5, hfe5, hfe5b⟩
  step with hmul I fe5 (B.red_mulIn hIb) (B.red_mulIn hfe5b) as ⟨Dy, hDy, hDyb⟩
  step with hadd s s hs hs as ⟨fe6, hfe6, hfe6b⟩
  step with hmul fe6 Dx (B.sum2_mulIn hfe6b) (B.red_mulIn hDxb) as ⟨x, hx, hxb⟩
  step with hisn x as ⟨xn, hxnv, hxn⟩
  step with hcng x xn hxnv (B.red_mulIn hxb) as ⟨x1, hx10, hx11⟩
  step with hmul u1 Dy (B.red_mulIn hu1b) (B.red_mulIn hDyb) as ⟨y, hy, hyb⟩
  have hx1b : B.Red x1 := by
    rcases hxnv with h | h
    · rw [hx10 h]; exact hxb
    · exact (hx11 h).2
  step with hmul x1 y (B.red_mulIn hx1b) (B.red_mulIn hyb) as ⟨t, ht, htb⟩
  step with hisn t as ⟨c, hcv, hc⟩
  step with hisz y as ⟨c1, hc1v, hc11, hc10⟩
  have U1 : B.toField u1 = 1 - B.toField s ^ 2 := by rw [hu1, F1, hss]
  have U2 : B.toField u2 = 1 + B.toField s ^ 2 := by rw [hu2, F1, hss]
  have V : B.toField v = dV (B.toField s) := by
    rw [hv, hfe3, hfe1, Fd, hfe2, hu2s, U1, U2]
    unfold dV dU1 dU2
    ring
  have W : B.toField fe4 = dW (B.toField s) := by
    rw [hfe4, V, hu2s, U2]
    rfl
  rw [W] at hInv
  have R : B.toField I = dR (B.toField s) := by unfold dR; rw [hInv]
  have X1 : B.toField x1 = dX (B.toField s) := by
    have h := Backend.eq_ite_of_choice hxnv (Backend.eq_one_iff_isNeg hxn)
      (fun h => by rw [hx10 h]) (fun h => (hx11 h).1)
    rw [h, show (if (B.toField x).IsNeg then -B.toField x else B.toField x) =
      (B.toField x).abs from rfl, hx, hfe6, hDx, R, U2]
    unfold dX dU2
    ring_nf
  have Y : B.toField y = dY (B.toField s) := by
    rw [hy, hDy, hfe5, hDx, R, U1, U2, V]
    unfold dY dU1 dU2
    ring
  refine ⟨hokv, ?_, hcv, ?_, hc1v, ?_, x1, y, one, t, rfl, ?_, hx1b, hyb, honeb, htb⟩
  · rw [hInv]
    simp
  · rw [Backend.eq_one_iff_isNeg hc, ht, X1, Y]
  · rw [← Y]
    refine ⟨fun h => ?_, hc11⟩
    by_contra hne
    rw [hc10 hne] at h
    exact absurd h (by decide)
  · rw [ht, X1, Y, F1]

end decompress

namespace decompress.«x86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `decompress::step_1`: `s` from the low `255` bits; the first choice is `1` iff the bytes are
canonical (value `< p`), the second iff `s` is negative. -/
private theorem step_1_spec (repr : CompressedRistretto) :
    step_1.«x86_64-tables» repr
      ⦃ (c1 : subtle.Choice) (c2 : subtle.Choice) (s : FieldElement51) =>
      c1.IsValid ∧ (c1 = 1#u8 ↔ repr.asNat < p) ∧ c2.IsValid ∧ (c2 = 1#u8 ↔ s.toField.IsNeg) ∧
      s.toField = ((repr.asNat % 2 ^ 255 : ℕ) : ZMod p) ∧ s.LimbsLt 51 ⦄ := by
  unfold step_1.«x86_64-tables»
  step as ⟨a, ha⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sb, hsb'⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c2, hc2v, hc2⟩
  subst ha hs1 hs2
  have hcanon : sb = a ↔ CompressedRistretto.asNat a < p := by
    rw [← decompress.mod_mod_eq_iff, CompressedRistretto.asNat_def, ← hs, ← hsb']
    exact ⟨fun h => by rw [h], fun h => Array.eq_of_asNat_eq h⟩
  refine ⟨hcv, ?_, hc2v, eq_one_iff_isNeg_toField hc2, ?_, hsb⟩
  · rw [← hcanon]
    constructor
    · intro hc
      by_contra hne
      rw [hc0 fun h => hne (Array.eq_of_to_slice_eq h)] at hc
      exact absurd hc (by decide)
    · intro h
      exact hc1 (by rw [h])
  · rw [toField_def, hs, CompressedRistretto.asNat_def]

private theorem step_2_eq (s : FieldElement51) :
    step_2.«x86_64-tables» s = decompress.step2Body Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-tables»)) s := rfl

open decompress in
/-- `decompress::step_2`: the candidate point `(x, y, 1, x y)` of RFC 9496 §4.3.1 and its three
tests (`was_square`, `x y` negative, `y = 0`); limbs `< 2^52`. -/
private theorem step_2_spec (s : FieldElement51) (hs : s.LimbsLt 52) :
    step_2.«x86_64-tables» s ⦃ (ok1 : subtle.Choice) (tn : subtle.Choice) (yz : subtle.Choice)
        (res : RistrettoPoint.«x86_64-tables») =>
      ok1.IsValid ∧ (ok1 = 1#u8 ↔ (sqrtRatioM1 1 (dW s.toField)).1 = true) ∧
      tn.IsValid ∧ (tn = 1#u8 ↔ (dX s.toField * dY s.toField).IsNeg) ∧
      yz.IsValid ∧ (yz = 1#u8 ↔ dY s.toField = 0) ∧
      res.toExtended = ⟨dX s.toField, dY s.toField, 1, dX s.toField * dY s.toField⟩ ∧
      res.LimbsLt 52 ⦄ := by
  rw [step_2_eq]
  apply spec_mono (decompress.step2Body_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.neg_spec Backend.U64.edwardsD_spec Backend.U64.one_spec Backend.U64.invsqrt_spec
    Backend.U64.is_negative_spec Backend.U64.conditional_negate_spec Backend.U64.is_zero_spec _ s
    hs)
  rintro ⟨ok1, tn, yz, res⟩ ⟨h1, h2, h3, h4, h5, h6, a, b, c, d, rfl, he, ha, hb, hc, hd⟩
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ha, hb, hc, hd⟩
  rw [edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
  exact he

/-- The point `(x : y : 1 : x y)` with `(x, y)` on the curve: on the curve, with these
coordinates. -/
private theorem onCurve_and_toPoint {ep : RistrettoPoint.«x86_64-tables»} {x y : ZMod p}
    (hxy : curve25519.edwards.Equation x y) (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact hxy
  refine ⟨hon, ?_, ?_⟩
  · rw [edwards.EdwardsPoint.«x86_64-tables».toPoint_x hon]
    simp only [edwards.EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [edwards.EdwardsPoint.«x86_64-tables».toPoint_y hon]
    simp only [edwards.EdwardsPoint.«x86_64-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-tables»

namespace decompress.«i686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `decompress::step_1`: `s` from the low `255` bits; the first choice is `1` iff the bytes are
canonical (value `< p`), the second iff `s` is negative. -/
private theorem step_1_spec (repr : CompressedRistretto) :
    step_1.«i686-tables» repr
      ⦃ (c1 : subtle.Choice) (c2 : subtle.Choice) (s : FieldElement2625) =>
      c1.IsValid ∧ (c1 = 1#u8 ↔ repr.asNat < p) ∧ c2.IsValid ∧ (c2 = 1#u8 ↔ s.toField.IsNeg) ∧
      s.toField = ((repr.asNat % 2 ^ 255 : ℕ) : ZMod p) ∧ s.LimbsLt 26 ⦄ := by
  unfold step_1.«i686-tables»
  step as ⟨a, ha⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sb, hsb'⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c2, hc2v, hc2⟩
  subst ha hs1 hs2
  have hcanon : sb = a ↔ CompressedRistretto.asNat a < p := by
    rw [← decompress.mod_mod_eq_iff, CompressedRistretto.asNat_def, ← hs, ← hsb']
    exact ⟨fun h => by rw [h], fun h => Array.eq_of_asNat_eq h⟩
  refine ⟨hcv, ?_, hc2v, eq_one_iff_isNeg_toField hc2, ?_, hsb⟩
  · rw [← hcanon]
    constructor
    · intro hc
      by_contra hne
      rw [hc0 fun h => hne (Array.eq_of_to_slice_eq h)] at hc
      exact absurd hc (by decide)
    · intro h
      exact hc1 (by rw [h])
  · rw [toField_def, CompressedRistretto.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hs

private theorem step_2_eq (s : FieldElement2625) :
    step_2.«i686-tables» s = decompress.step2Body Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-tables»)) s := rfl

open decompress in
/-- `decompress::step_2`: the candidate point `(x, y, 1, x y)` of RFC 9496 §4.3.1 and its three
tests (`was_square`, `x y` negative, `y = 0`); limbs `< 2^26`. -/
private theorem step_2_spec (s : FieldElement2625) (hs : s.LimbsLt 26) :
    step_2.«i686-tables» s ⦃ (ok1 : subtle.Choice) (tn : subtle.Choice) (yz : subtle.Choice)
        (res : RistrettoPoint.«i686-tables») =>
      ok1.IsValid ∧ (ok1 = 1#u8 ↔ (sqrtRatioM1 1 (dW s.toField)).1 = true) ∧
      tn.IsValid ∧ (tn = 1#u8 ↔ (dX s.toField * dY s.toField).IsNeg) ∧
      yz.IsValid ∧ (yz = 1#u8 ↔ dY s.toField = 0) ∧
      res.toExtended = ⟨dX s.toField, dY s.toField, 1, dX s.toField * dY s.toField⟩ ∧
      res.LimbsLt 26 ⦄ := by
  rw [step_2_eq]
  apply spec_mono (decompress.step2Body_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.neg_spec Backend.U32.edwardsD_spec Backend.U32.one_spec Backend.U32.invsqrt_spec
    Backend.U32.is_negative_spec Backend.U32.conditional_negate_spec Backend.U32.is_zero_spec _ s
    hs)
  rintro ⟨ok1, tn, yz, res⟩ ⟨h1, h2, h3, h4, h5, h6, a, b, c, d, rfl, he, ha, hb, hc, hd⟩
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ha, hb, hc, hd⟩
  rw [edwards.EdwardsPoint.«i686-tables».toExtended_def]
  exact he

/-- The point `(x : y : 1 : x y)` with `(x, y)` on the curve: on the curve, with these
coordinates. -/
private theorem onCurve_and_toPoint {ep : RistrettoPoint.«i686-tables»} {x y : ZMod p}
    (hxy : curve25519.edwards.Equation x y) (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact hxy
  refine ⟨hon, ?_, ?_⟩
  · rw [edwards.EdwardsPoint.«i686-tables».toPoint_x hon]
    simp only [edwards.EdwardsPoint.«i686-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [edwards.EdwardsPoint.«i686-tables».toPoint_y hon]
    simp only [edwards.EdwardsPoint.«i686-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«i686-tables»

namespace decompress.«x86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `decompress::step_1`: `s` from the low `255` bits; the first choice is `1` iff the bytes are
canonical (value `< p`), the second iff `s` is negative. -/
private theorem step_1_spec (repr : CompressedRistretto) :
    step_1.«x86_64-no-tables» repr
      ⦃ (c1 : subtle.Choice) (c2 : subtle.Choice) (s : FieldElement51) =>
      c1.IsValid ∧ (c1 = 1#u8 ↔ repr.asNat < p) ∧ c2.IsValid ∧ (c2 = 1#u8 ↔ s.toField.IsNeg) ∧
      s.toField = ((repr.asNat % 2 ^ 255 : ℕ) : ZMod p) ∧ s.LimbsLt 51 ⦄ := by
  unfold step_1.«x86_64-no-tables»
  step as ⟨a, ha⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sb, hsb'⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c2, hc2v, hc2⟩
  subst ha hs1 hs2
  have hcanon : sb = a ↔ CompressedRistretto.asNat a < p := by
    rw [← decompress.mod_mod_eq_iff, CompressedRistretto.asNat_def, ← hs, ← hsb']
    exact ⟨fun h => by rw [h], fun h => Array.eq_of_asNat_eq h⟩
  refine ⟨hcv, ?_, hc2v, eq_one_iff_isNeg_toField hc2, ?_, hsb⟩
  · rw [← hcanon]
    constructor
    · intro hc
      by_contra hne
      rw [hc0 fun h => hne (Array.eq_of_to_slice_eq h)] at hc
      exact absurd hc (by decide)
    · intro h
      exact hc1 (by rw [h])
  · rw [toField_def, hs, CompressedRistretto.asNat_def]

private theorem step_2_eq (s : FieldElement51) :
    step_2.«x86_64-no-tables» s = decompress.step2Body Backend.U64
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«x86_64-no-tables»)) s := rfl

open decompress in
/-- `decompress::step_2`: the candidate point `(x, y, 1, x y)` of RFC 9496 §4.3.1 and its three
tests (`was_square`, `x y` negative, `y = 0`); limbs `< 2^52`. -/
private theorem step_2_spec (s : FieldElement51) (hs : s.LimbsLt 52) :
    step_2.«x86_64-no-tables» s ⦃ (ok1 : subtle.Choice) (tn : subtle.Choice) (yz : subtle.Choice)
        (res : RistrettoPoint.«x86_64-no-tables») =>
      ok1.IsValid ∧ (ok1 = 1#u8 ↔ (sqrtRatioM1 1 (dW s.toField)).1 = true) ∧
      tn.IsValid ∧ (tn = 1#u8 ↔ (dX s.toField * dY s.toField).IsNeg) ∧
      yz.IsValid ∧ (yz = 1#u8 ↔ dY s.toField = 0) ∧
      res.toExtended = ⟨dX s.toField, dY s.toField, 1, dX s.toField * dY s.toField⟩ ∧
      res.LimbsLt 52 ⦄ := by
  rw [step_2_eq]
  apply spec_mono (decompress.step2Body_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.neg_spec Backend.U64.edwardsD_spec Backend.U64.one_spec Backend.U64.invsqrt_spec
    Backend.U64.is_negative_spec Backend.U64.conditional_negate_spec Backend.U64.is_zero_spec _ s
    hs)
  rintro ⟨ok1, tn, yz, res⟩ ⟨h1, h2, h3, h4, h5, h6, a, b, c, d, rfl, he, ha, hb, hc, hd⟩
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ha, hb, hc, hd⟩
  rw [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
  exact he

/-- The point `(x : y : 1 : x y)` with `(x, y)` on the curve: on the curve, with these
coordinates. -/
private theorem onCurve_and_toPoint {ep : RistrettoPoint.«x86_64-no-tables»} {x y : ZMod p}
    (hxy : curve25519.edwards.Equation x y) (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact hxy
  refine ⟨hon, ?_, ?_⟩
  · rw [edwards.EdwardsPoint.«x86_64-no-tables».toPoint_x hon]
    simp only [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [edwards.EdwardsPoint.«x86_64-no-tables».toPoint_y hon]
    simp only [edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«x86_64-no-tables»

namespace decompress.«i686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `decompress::step_1`: `s` from the low `255` bits; the first choice is `1` iff the bytes are
canonical (value `< p`), the second iff `s` is negative. -/
private theorem step_1_spec (repr : CompressedRistretto) :
    step_1.«i686-no-tables» repr
      ⦃ (c1 : subtle.Choice) (c2 : subtle.Choice) (s : FieldElement2625) =>
      c1.IsValid ∧ (c1 = 1#u8 ↔ repr.asNat < p) ∧ c2.IsValid ∧ (c2 = 1#u8 ↔ s.toField.IsNeg) ∧
      s.toField = ((repr.asNat % 2 ^ 255 : ℕ) : ZMod p) ∧ s.LimbsLt 26 ⦄ := by
  unfold step_1.«i686-no-tables»
  step as ⟨a, ha⟩
  step as ⟨s, hs, hsb⟩
  step as ⟨sb, hsb'⟩
  step as ⟨s1, hs1⟩
  step as ⟨s2, hs2⟩
  step as ⟨c, hcv, hc1, hc0⟩
  step as ⟨c2, hc2v, hc2⟩
  subst ha hs1 hs2
  have hcanon : sb = a ↔ CompressedRistretto.asNat a < p := by
    rw [← decompress.mod_mod_eq_iff, CompressedRistretto.asNat_def, ← hs, ← hsb']
    exact ⟨fun h => by rw [h], fun h => Array.eq_of_asNat_eq h⟩
  refine ⟨hcv, ?_, hc2v, eq_one_iff_isNeg_toField hc2, ?_, hsb⟩
  · rw [← hcanon]
    constructor
    · intro hc
      by_contra hne
      rw [hc0 fun h => hne (Array.eq_of_to_slice_eq h)] at hc
      exact absurd hc (by decide)
    · intro h
      exact hc1 (by rw [h])
  · rw [toField_def, CompressedRistretto.asNat_def]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hs

private theorem step_2_eq (s : FieldElement2625) :
    step_2.«i686-no-tables» s = decompress.step2Body Backend.U32
      (fun X Y Z T => (⟨X, Y, Z, T⟩ : edwards.EdwardsPoint.«i686-no-tables»)) s := rfl

open decompress in
/-- `decompress::step_2`: the candidate point `(x, y, 1, x y)` of RFC 9496 §4.3.1 and its three
tests (`was_square`, `x y` negative, `y = 0`); limbs `< 2^26`. -/
private theorem step_2_spec (s : FieldElement2625) (hs : s.LimbsLt 26) :
    step_2.«i686-no-tables» s ⦃ (ok1 : subtle.Choice) (tn : subtle.Choice) (yz : subtle.Choice)
        (res : RistrettoPoint.«i686-no-tables») =>
      ok1.IsValid ∧ (ok1 = 1#u8 ↔ (sqrtRatioM1 1 (dW s.toField)).1 = true) ∧
      tn.IsValid ∧ (tn = 1#u8 ↔ (dX s.toField * dY s.toField).IsNeg) ∧
      yz.IsValid ∧ (yz = 1#u8 ↔ dY s.toField = 0) ∧
      res.toExtended = ⟨dX s.toField, dY s.toField, 1, dX s.toField * dY s.toField⟩ ∧
      res.LimbsLt 26 ⦄ := by
  rw [step_2_eq]
  apply spec_mono (decompress.step2Body_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.neg_spec Backend.U32.edwardsD_spec Backend.U32.one_spec Backend.U32.invsqrt_spec
    Backend.U32.is_negative_spec Backend.U32.conditional_negate_spec Backend.U32.is_zero_spec _ s
    hs)
  rintro ⟨ok1, tn, yz, res⟩ ⟨h1, h2, h3, h4, h5, h6, a, b, c, d, rfl, he, ha, hb, hc, hd⟩
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ha, hb, hc, hd⟩
  rw [edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
  exact he

/-- The point `(x : y : 1 : x y)` with `(x, y)` on the curve: on the curve, with these
coordinates. -/
private theorem onCurve_and_toPoint {ep : RistrettoPoint.«i686-no-tables»} {x y : ZMod p}
    (hxy : curve25519.edwards.Equation x y) (h : ep.toExtended = ⟨x, y, 1, x * y⟩) :
    ep.OnCurve ∧ ep.toPoint.x = x ∧ ep.toPoint.y = y := by
  have hon : ep.OnCurve := by
    rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff, h]
    refine ⟨one_ne_zero, (one_mul _).symm, ?_⟩
    rw [div_one, div_one]
    exact hxy
  refine ⟨hon, ?_, ?_⟩
  · rw [edwards.EdwardsPoint.«i686-no-tables».toPoint_x hon]
    simp only [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.1, h.2.2.1, div_one]
  · rw [edwards.EdwardsPoint.«i686-no-tables».toPoint_y hon]
    simp only [edwards.EdwardsPoint.«i686-no-tables».toExtended_def, Extended.mk.injEq] at h
    rw [h.2.1, h.2.2.1, div_one]

end decompress.«i686-no-tables»

namespace CompressedRistretto

open _root_.Curve25519Dalek.ristretto.decompress in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `CompressedRistretto::decompress`: RFC 9496's decoding of the bytes' value (`none` unless it
is the canonical, non-negative encoding of a point of the class); the point is on the curve,
even (a ristretto255 representative) and has limbs `< 2^52`. -/
@[step]
theorem «x86_64-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«x86_64-tables» self ⦃ (r : Option RistrettoPoint.«x86_64-tables») =>
      r.map edwards.EdwardsPoint.«x86_64-tables».toPoint = Ristretto.decodeRep self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress.«x86_64-tables»
  step with decompress.«x86_64-tables».step_1_spec
    as ⟨c1, c2, s, hc1v, hc1, hc2v, hc2, hsf, hsb⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨cc, hccv, hcc⟩
  step as ⟨b, hb⟩
  have hbiff : b = true ↔ ¬ (self.asNat < p ∧ ¬ s.toField.IsNeg) := by
    rw [← hc1, ← hc2]
    subst hc hcc hb
    rcases hc1v with rfl | rfl <;> rcases hc2v with rfl | rfl <;> decide
  by_cases hgood1 : self.asNat < p ∧ ¬ s.toField.IsNeg
  · have hb' : b = false := by
      cases b
      · rfl
      · exact absurd hgood1 (hbiff.mp rfl)
    have hs' : s.toField = (self.asNat : ZMod p) := by rw [hsf, Nat.mod_eq_of_lt
      (hgood1.1.trans p_lt_two_pow_255)]
    simp only [hb', Bool.false_eq_true, ite_false]
    step with decompress.«x86_64-tables».step_2_spec s (limbs_lt_of_le (by decide) hsb)
      as ⟨ok1, tn, yz, res, hokv, hok, htnv, htn, hyzv, hyz, hres, hresb⟩
    step as ⟨c2', hc2'v, hc2'⟩
    step as ⟨c3, hc3v, hc3⟩
    step as ⟨c4, hc4v, hc4⟩
    step as ⟨b1, hb1⟩
    rw [hs'] at hok htn hyz hres
    have hb1iff : b1 = true ↔ ¬ ((sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        ¬ dY (self.asNat : ZMod p) = 0) := by
      rw [← hok, ← htn, ← hyz]
      subst hc2' hc3 hc4 hb1
      rcases hokv with rfl | rfl <;> rcases htnv with rfl | rfl <;>
        rcases hyzv with rfl | rfl <;> decide
    by_cases hgood2 : (sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        dY (self.asNat : ZMod p) ≠ 0
    · have hb1' : b1 = false := by
        cases b1
        · rfl
        · exact absurd hgood2 (hb1iff.mp rfl)
      simp only [hb1', Bool.false_eq_true, ite_false, WP.spec_ok]
      obtain ⟨heq, hy⟩ := candidate_facts hgood2.1
      obtain ⟨hon, hpx, hpy⟩ := decompress.«x86_64-tables».onCurve_and_toPoint heq hres
      have hdec : Ristretto.decodeRep self.asNat =
          some (edwards.EdwardsPoint.«x86_64-tables».toPoint res) := by
        rw [Ristretto.decodeRep_eq_some_iff]
        refine ⟨hgood1.1, by rw [← hs']; exact hgood1.2, by rw [hpy, hy], ?_, ?_, ?_⟩
        · rw [hpx]
          exact ZMod.not_isNeg_abs _
        · rw [hpx, hpy]
          exact hgood2.2.1
        · rw [hpy]
          exact hgood2.2.2
      refine ⟨by rw [Option.map_some, hdec], fun q hq =>
        Option.some.inj hq ▸ ⟨hon, Ristretto.even_decodeRep hdec, hresb⟩⟩
    · have hb1' : b1 = true := hb1iff.mpr hgood2
      simp only [hb1', ite_true, WP.spec_ok]
      refine ⟨?_, fun q hq => by cases hq⟩
      rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
      right; right
      rw [not_and_or, not_and_or, not_not, not_not] at hgood2
      rcases hgood2 with h | h | h
      · exact Or.inl (Bool.eq_false_iff.mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · have hb' : b = true := hbiff.mpr hgood1
    simp only [hb', ite_true, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
    rw [not_and_or, not_not] at hgood1
    rcases hgood1 with h | h
    · exact Or.inl (not_lt.mp h)
    · by_cases hlt : self.asNat < p
      · right; left
        rwa [hsf, Nat.mod_eq_of_lt (hlt.trans p_lt_two_pow_255)] at h
      · exact Or.inl (not_lt.mp hlt)

open _root_.Curve25519Dalek.ristretto.decompress in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `CompressedRistretto::decompress`: RFC 9496's decoding of the bytes' value (`none` unless it
is the canonical, non-negative encoding of a point of the class); the point is on the curve,
even (a ristretto255 representative) and has limbs `< 2^26`. -/
@[step]
theorem «i686-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«i686-tables» self ⦃ (r : Option RistrettoPoint.«i686-tables») =>
      r.map edwards.EdwardsPoint.«i686-tables».toPoint = Ristretto.decodeRep self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress.«i686-tables»
  step with decompress.«i686-tables».step_1_spec
    as ⟨c1, c2, s, hc1v, hc1, hc2v, hc2, hsf, hsb⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨cc, hccv, hcc⟩
  step as ⟨b, hb⟩
  have hbiff : b = true ↔ ¬ (self.asNat < p ∧ ¬ s.toField.IsNeg) := by
    rw [← hc1, ← hc2]
    subst hc hcc hb
    rcases hc1v with rfl | rfl <;> rcases hc2v with rfl | rfl <;> decide
  by_cases hgood1 : self.asNat < p ∧ ¬ s.toField.IsNeg
  · have hb' : b = false := by
      cases b
      · rfl
      · exact absurd hgood1 (hbiff.mp rfl)
    have hs' : s.toField = (self.asNat : ZMod p) := by rw [hsf, Nat.mod_eq_of_lt
      (hgood1.1.trans p_lt_two_pow_255)]
    simp only [hb', Bool.false_eq_true, ite_false]
    step with decompress.«i686-tables».step_2_spec s (limbs_lt_of_le (by decide) hsb)
      as ⟨ok1, tn, yz, res, hokv, hok, htnv, htn, hyzv, hyz, hres, hresb⟩
    step as ⟨c2', hc2'v, hc2'⟩
    step as ⟨c3, hc3v, hc3⟩
    step as ⟨c4, hc4v, hc4⟩
    step as ⟨b1, hb1⟩
    rw [hs'] at hok htn hyz hres
    have hb1iff : b1 = true ↔ ¬ ((sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        ¬ dY (self.asNat : ZMod p) = 0) := by
      rw [← hok, ← htn, ← hyz]
      subst hc2' hc3 hc4 hb1
      rcases hokv with rfl | rfl <;> rcases htnv with rfl | rfl <;>
        rcases hyzv with rfl | rfl <;> decide
    by_cases hgood2 : (sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        dY (self.asNat : ZMod p) ≠ 0
    · have hb1' : b1 = false := by
        cases b1
        · rfl
        · exact absurd hgood2 (hb1iff.mp rfl)
      simp only [hb1', Bool.false_eq_true, ite_false, WP.spec_ok]
      obtain ⟨heq, hy⟩ := candidate_facts hgood2.1
      obtain ⟨hon, hpx, hpy⟩ := decompress.«i686-tables».onCurve_and_toPoint heq hres
      have hdec : Ristretto.decodeRep self.asNat =
          some (edwards.EdwardsPoint.«i686-tables».toPoint res) := by
        rw [Ristretto.decodeRep_eq_some_iff]
        refine ⟨hgood1.1, by rw [← hs']; exact hgood1.2, by rw [hpy, hy], ?_, ?_, ?_⟩
        · rw [hpx]
          exact ZMod.not_isNeg_abs _
        · rw [hpx, hpy]
          exact hgood2.2.1
        · rw [hpy]
          exact hgood2.2.2
      refine ⟨by rw [Option.map_some, hdec], fun q hq =>
        Option.some.inj hq ▸ ⟨hon, Ristretto.even_decodeRep hdec, hresb⟩⟩
    · have hb1' : b1 = true := hb1iff.mpr hgood2
      simp only [hb1', ite_true, WP.spec_ok]
      refine ⟨?_, fun q hq => by cases hq⟩
      rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
      right; right
      rw [not_and_or, not_and_or, not_not, not_not] at hgood2
      rcases hgood2 with h | h | h
      · exact Or.inl (Bool.eq_false_iff.mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · have hb' : b = true := hbiff.mpr hgood1
    simp only [hb', ite_true, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
    rw [not_and_or, not_not] at hgood1
    rcases hgood1 with h | h
    · exact Or.inl (not_lt.mp h)
    · by_cases hlt : self.asNat < p
      · right; left
        rwa [hsf, Nat.mod_eq_of_lt (hlt.trans p_lt_two_pow_255)] at h
      · exact Or.inl (not_lt.mp hlt)


open _root_.Curve25519Dalek.ristretto.decompress in
open Curve25519Dalek.backend.serial.u64.field.FieldElement51 in
/-- `CompressedRistretto::decompress`: RFC 9496's decoding of the bytes' value (`none` unless it
is the canonical, non-negative encoding of a point of the class); the point is on the curve,
even (a ristretto255 representative) and has limbs `< 2^52`. -/
@[step]
theorem «x86_64-no-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«x86_64-no-tables» self ⦃ (r : Option RistrettoPoint.«x86_64-no-tables») =>
      r.map edwards.EdwardsPoint.«x86_64-no-tables».toPoint = Ristretto.decodeRep self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.LimbsLt 52 ⦄ := by
  unfold decompress.«x86_64-no-tables»
  step with decompress.«x86_64-no-tables».step_1_spec
    as ⟨c1, c2, s, hc1v, hc1, hc2v, hc2, hsf, hsb⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨cc, hccv, hcc⟩
  step as ⟨b, hb⟩
  have hbiff : b = true ↔ ¬ (self.asNat < p ∧ ¬ s.toField.IsNeg) := by
    rw [← hc1, ← hc2]
    subst hc hcc hb
    rcases hc1v with rfl | rfl <;> rcases hc2v with rfl | rfl <;> decide
  by_cases hgood1 : self.asNat < p ∧ ¬ s.toField.IsNeg
  · have hb' : b = false := by
      cases b
      · rfl
      · exact absurd hgood1 (hbiff.mp rfl)
    have hs' : s.toField = (self.asNat : ZMod p) := by rw [hsf, Nat.mod_eq_of_lt
      (hgood1.1.trans p_lt_two_pow_255)]
    simp only [hb', Bool.false_eq_true, ite_false]
    step with decompress.«x86_64-no-tables».step_2_spec s (limbs_lt_of_le (by decide) hsb)
      as ⟨ok1, tn, yz, res, hokv, hok, htnv, htn, hyzv, hyz, hres, hresb⟩
    step as ⟨c2', hc2'v, hc2'⟩
    step as ⟨c3, hc3v, hc3⟩
    step as ⟨c4, hc4v, hc4⟩
    step as ⟨b1, hb1⟩
    rw [hs'] at hok htn hyz hres
    have hb1iff : b1 = true ↔ ¬ ((sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        ¬ dY (self.asNat : ZMod p) = 0) := by
      rw [← hok, ← htn, ← hyz]
      subst hc2' hc3 hc4 hb1
      rcases hokv with rfl | rfl <;> rcases htnv with rfl | rfl <;>
        rcases hyzv with rfl | rfl <;> decide
    by_cases hgood2 : (sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        dY (self.asNat : ZMod p) ≠ 0
    · have hb1' : b1 = false := by
        cases b1
        · rfl
        · exact absurd hgood2 (hb1iff.mp rfl)
      simp only [hb1', Bool.false_eq_true, ite_false, WP.spec_ok]
      obtain ⟨heq, hy⟩ := candidate_facts hgood2.1
      obtain ⟨hon, hpx, hpy⟩ := decompress.«x86_64-no-tables».onCurve_and_toPoint heq hres
      have hdec : Ristretto.decodeRep self.asNat =
          some (edwards.EdwardsPoint.«x86_64-no-tables».toPoint res) := by
        rw [Ristretto.decodeRep_eq_some_iff]
        refine ⟨hgood1.1, by rw [← hs']; exact hgood1.2, by rw [hpy, hy], ?_, ?_, ?_⟩
        · rw [hpx]
          exact ZMod.not_isNeg_abs _
        · rw [hpx, hpy]
          exact hgood2.2.1
        · rw [hpy]
          exact hgood2.2.2
      refine ⟨by rw [Option.map_some, hdec], fun q hq =>
        Option.some.inj hq ▸ ⟨hon, Ristretto.even_decodeRep hdec, hresb⟩⟩
    · have hb1' : b1 = true := hb1iff.mpr hgood2
      simp only [hb1', ite_true, WP.spec_ok]
      refine ⟨?_, fun q hq => by cases hq⟩
      rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
      right; right
      rw [not_and_or, not_and_or, not_not, not_not] at hgood2
      rcases hgood2 with h | h | h
      · exact Or.inl (Bool.eq_false_iff.mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · have hb' : b = true := hbiff.mpr hgood1
    simp only [hb', ite_true, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
    rw [not_and_or, not_not] at hgood1
    rcases hgood1 with h | h
    · exact Or.inl (not_lt.mp h)
    · by_cases hlt : self.asNat < p
      · right; left
        rwa [hsf, Nat.mod_eq_of_lt (hlt.trans p_lt_two_pow_255)] at h
      · exact Or.inl (not_lt.mp hlt)

open _root_.Curve25519Dalek.ristretto.decompress in
open Curve25519Dalek.backend.serial.u32.field.FieldElement2625 in
/-- `CompressedRistretto::decompress`: RFC 9496's decoding of the bytes' value (`none` unless it
is the canonical, non-negative encoding of a point of the class); the point is on the curve,
even (a ristretto255 representative) and has limbs `< 2^26`. -/
@[step]
theorem «i686-no-tables».decompress_spec (self : CompressedRistretto) :
    decompress.«i686-no-tables» self ⦃ (r : Option RistrettoPoint.«i686-no-tables») =>
      r.map edwards.EdwardsPoint.«i686-no-tables».toPoint = Ristretto.decodeRep self.asNat ∧
      ∀ q, r = some q → q.OnCurve ∧ Even q.toPoint ∧ q.LimbsLt 26 ⦄ := by
  unfold decompress.«i686-no-tables»
  step with decompress.«i686-no-tables».step_1_spec
    as ⟨c1, c2, s, hc1v, hc1, hc2v, hc2, hsf, hsb⟩
  step as ⟨c, hcv, hc⟩
  step as ⟨cc, hccv, hcc⟩
  step as ⟨b, hb⟩
  have hbiff : b = true ↔ ¬ (self.asNat < p ∧ ¬ s.toField.IsNeg) := by
    rw [← hc1, ← hc2]
    subst hc hcc hb
    rcases hc1v with rfl | rfl <;> rcases hc2v with rfl | rfl <;> decide
  by_cases hgood1 : self.asNat < p ∧ ¬ s.toField.IsNeg
  · have hb' : b = false := by
      cases b
      · rfl
      · exact absurd hgood1 (hbiff.mp rfl)
    have hs' : s.toField = (self.asNat : ZMod p) := by rw [hsf, Nat.mod_eq_of_lt
      (hgood1.1.trans p_lt_two_pow_255)]
    simp only [hb', Bool.false_eq_true, ite_false]
    step with decompress.«i686-no-tables».step_2_spec s (limbs_lt_of_le (by decide) hsb)
      as ⟨ok1, tn, yz, res, hokv, hok, htnv, htn, hyzv, hyz, hres, hresb⟩
    step as ⟨c2', hc2'v, hc2'⟩
    step as ⟨c3, hc3v, hc3⟩
    step as ⟨c4, hc4v, hc4⟩
    step as ⟨b1, hb1⟩
    rw [hs'] at hok htn hyz hres
    have hb1iff : b1 = true ↔ ¬ ((sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        ¬ dY (self.asNat : ZMod p) = 0) := by
      rw [← hok, ← htn, ← hyz]
      subst hc2' hc3 hc4 hb1
      rcases hokv with rfl | rfl <;> rcases htnv with rfl | rfl <;>
        rcases hyzv with rfl | rfl <;> decide
    by_cases hgood2 : (sqrtRatioM1 1 (dW (self.asNat : ZMod p))).1 = true ∧
        ¬ (dX (self.asNat : ZMod p) * dY (self.asNat : ZMod p)).IsNeg ∧
        dY (self.asNat : ZMod p) ≠ 0
    · have hb1' : b1 = false := by
        cases b1
        · rfl
        · exact absurd hgood2 (hb1iff.mp rfl)
      simp only [hb1', Bool.false_eq_true, ite_false, WP.spec_ok]
      obtain ⟨heq, hy⟩ := candidate_facts hgood2.1
      obtain ⟨hon, hpx, hpy⟩ := decompress.«i686-no-tables».onCurve_and_toPoint heq hres
      have hdec : Ristretto.decodeRep self.asNat =
          some (edwards.EdwardsPoint.«i686-no-tables».toPoint res) := by
        rw [Ristretto.decodeRep_eq_some_iff]
        refine ⟨hgood1.1, by rw [← hs']; exact hgood1.2, by rw [hpy, hy], ?_, ?_, ?_⟩
        · rw [hpx]
          exact ZMod.not_isNeg_abs _
        · rw [hpx, hpy]
          exact hgood2.2.1
        · rw [hpy]
          exact hgood2.2.2
      refine ⟨by rw [Option.map_some, hdec], fun q hq =>
        Option.some.inj hq ▸ ⟨hon, Ristretto.even_decodeRep hdec, hresb⟩⟩
    · have hb1' : b1 = true := hb1iff.mpr hgood2
      simp only [hb1', ite_true, WP.spec_ok]
      refine ⟨?_, fun q hq => by cases hq⟩
      rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
      right; right
      rw [not_and_or, not_and_or, not_not, not_not] at hgood2
      rcases hgood2 with h | h | h
      · exact Or.inl (Bool.eq_false_iff.mpr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · have hb' : b = true := hbiff.mpr hgood1
    simp only [hb', ite_true, WP.spec_ok]
    refine ⟨?_, fun q hq => by cases hq⟩
    rw [Option.map_none, eq_comm, Ristretto.decodeRep_eq_none_iff]
    rw [not_and_or, not_not] at hgood1
    rcases hgood1 with h | h
    · exact Or.inl (not_lt.mp h)
    · by_cases hlt : self.asNat < p
      · right; left
        rwa [hsf, Nat.mod_eq_of_lt (hlt.trans p_lt_two_pow_255)] at h
      · exact Or.inl (not_lt.mp hlt)

end CompressedRistretto

end Curve25519Dalek.ristretto
