/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Ristretto.Encoding
public import Defs.Edwards
public import Defs.Ristretto
import Proofs.Helpers.Coords
import Proofs.Helpers.RistrettoCompress
public import Proofs.Field.Invsqrt
import Proofs.Helpers.Backend.U32.Bytes
import Proofs.Helpers.Backend.U64.Bytes
public section

/-! # `RistrettoPoint::compress`

The code is RFC 9496 §4.3.2 on the extended coordinates of the representative
(`RistrettoCompress.compressProj`), which equals `encodeRep` of the represented point
(`RistrettoCompress.compressProj_eq_encodeRep`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.Backend

variable (B : Backend)

/-- `RistrettoPoint::compress` over a backend. -/
@[expose] def compressBody (X Y Z T : B.F) : Result ristretto.CompressedRistretto := do
  let fe ← B.add Z Y
  let fe1 ← B.sub Z Y
  let u1 ← B.mul fe fe1
  let u2 ← B.mul X Y
  let fe2 ← B.square u2
  let fe3 ← B.mul u1 fe2
  let (_, invsqrt) ← B.invsqrt fe3
  let i1 ← B.mul invsqrt u1
  let i2 ← B.mul invsqrt u2
  let fe4 ← B.mul i2 T
  let z_inv ← B.mul i1 fe4
  let fe5 ← B.constSqrtM1
  let iX ← B.mul X fe5
  let iY ← B.mul Y fe5
  let fe6 ← B.constInvsqrtAMinusD
  let enchanted_denominator ← B.mul i1 fe6
  let fe7 ← B.mul T z_inv
  let rotate ← B.isNegative fe7
  let X' ← B.condAssign X iY rotate
  let Y' ← B.condAssign Y iX rotate
  let i21 ← B.condAssign i2 enchanted_denominator rotate
  let fe8 ← B.mul X' z_inv
  let c ← B.isNegative fe8
  let Y1 ← B.condNeg Y' c
  let fe9 ← B.sub Z Y1
  let s ← B.mul i21 fe9
  let s_is_negative ← B.isNegative s
  let s1 ← B.condNeg s s_is_negative
  let a ← B.toBytes s1
  ok a

/-- `compressBody` is RFC 9496's encoding of the represented point. -/
theorem compressBody_spec (hadd : B.AddSpec) (hsub : B.SubSpec) (hmul : B.MulSpec)
    (hsq : B.SquareSpec) (hinv : B.InvsqrtSpec) (hm1 : B.SqrtM1Spec)
    (hiad : B.InvsqrtAMinusDSpec) (hisn : B.IsNegativeSpec) (hca : B.CondAssignSpec)
    (hcng : B.CondNegSpec) (htb : B.ToBytesSpec) (X Y Z T : B.F) (hX : B.Red X)
    (hY : B.Red Y) (hZ : B.Red Z) (hT : B.Red T)
    (hon : (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Extended).OnCurve) :
    B.compressBody X Y Z T ⦃ (r : ristretto.CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep
        (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ : edwards.Extended).toPoint ⦄ := by
  have hx : (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ :
      edwards.Extended).toPoint.x = B.toField X / B.toField Z :=
    TwistedEdwardsModel.Extended.toPoint_x hon
  have hy : (⟨B.toField X, B.toField Y, B.toField Z, B.toField T⟩ :
      edwards.Extended).toPoint.y = B.toField Y / B.toField Z :=
    TwistedEdwardsModel.Extended.toPoint_y hon
  obtain ⟨hZ0, hXYZT, -⟩ := hon
  unfold compressBody
  step with hadd Z Y hZ hY as ⟨fe, Fe, hfeb⟩
  step with hsub Z Y (B.red_mulIn hZ) (B.red_mulIn hY) as ⟨fe1, Fe1, hfe1b⟩
  step with hmul fe fe1 (B.sum2_mulIn hfeb) (B.red_mulIn hfe1b) as ⟨u1, hu1, hu1b⟩
  step with hmul X Y (B.red_mulIn hX) (B.red_mulIn hY) as ⟨u2, hu2, hu2b⟩
  step with hsq u2 (B.red_sqIn hu2b) as ⟨fe2, hfe2, hfe2b⟩
  step with hmul u1 fe2 (B.red_mulIn hu1b) (B.red_mulIn hfe2b) as ⟨fe3, hfe3, hfe3b⟩
  step with hinv fe3 (B.red_sqIn hfe3b) as ⟨c0, invsqrt, hInv, hc0v, hib⟩
  have Inv : B.toField invsqrt = (sqrtRatioM1 1 (B.toField fe3)).2 := by rw [hInv]
  step with hmul invsqrt u1 (B.red_mulIn hib) (B.red_mulIn hu1b) as ⟨i1, hi1', hi1b⟩
  step with hmul invsqrt u2 (B.red_mulIn hib) (B.red_mulIn hu2b) as ⟨i2, hi2', hi2b⟩
  step with hmul i2 T (B.red_mulIn hi2b) (B.red_mulIn hT) as ⟨fe4, hfe4, hfe4b⟩
  step with hmul i1 fe4 (B.red_mulIn hi1b) (B.red_mulIn hfe4b) as ⟨z_inv, hz, hzb⟩
  apply spec_bind hm1
  rintro fe5 ⟨Fe5, hfe5b⟩
  step with hmul X fe5 (B.red_mulIn hX) (B.red_mulIn hfe5b) as ⟨iX, hiX, hiXb⟩
  step with hmul Y fe5 (B.red_mulIn hY) (B.red_mulIn hfe5b) as ⟨iY, hiY, hiYb⟩
  apply spec_bind hiad
  rintro fe6 ⟨Fe6, hfe6b⟩
  step with hmul i1 fe6 (B.red_mulIn hi1b) (B.red_mulIn hfe6b) as ⟨ench, hench, henchb⟩
  step with hmul T z_inv (B.red_mulIn hT) (B.red_mulIn hzb) as ⟨fe7, hfe7, hfe7b⟩
  step with hisn fe7 as ⟨rot, hrotv, hrot⟩
  step with hca X iY rot hrotv as ⟨X', hX0, hX1⟩
  step with hca Y iX rot hrotv as ⟨Y', hY0, hY1⟩
  step with hca i2 ench rot hrotv as ⟨i21, hi210, hi211⟩
  have hXb : B.Red X' := by
    rcases hrotv with h | h
    · rw [hX0 h]; exact hX
    · rw [hX1 h]; exact hiYb
  have hYb : B.Red Y' := by
    rcases hrotv with h | h
    · rw [hY0 h]; exact hY
    · rw [hY1 h]; exact hiXb
  have hi21b : B.Red i21 := by
    rcases hrotv with h | h
    · rw [hi210 h]; exact hi2b
    · rw [hi211 h]; exact henchb
  step with hmul X' z_inv (B.red_mulIn hXb) (B.red_mulIn hzb) as ⟨fe8, hfe8, hfe8b⟩
  step with hisn fe8 as ⟨cn, hcnv, hcn⟩
  step with hcng Y' cn hcnv (B.red_mulIn hYb) as ⟨Y1, hY10, hY11⟩
  have hY1b : B.Red Y1 := by
    rcases hcnv with h | h
    · rw [hY10 h]; exact hYb
    · exact (hY11 h).2
  step with hsub Z Y1 (B.red_mulIn hZ) (B.red_mulIn hY1b) as ⟨fe9, hfe9, hfe9b⟩
  step with hmul i21 fe9 (B.red_mulIn hi21b) (B.red_mulIn hfe9b) as ⟨s, hs, hsb⟩
  step with hisn s as ⟨sn, hsnv, hsn⟩
  step with hcng s sn hsnv (B.red_mulIn hsb) as ⟨s1, hs10, hs11⟩
  step with htb s1 as ⟨r, hr⟩
  -- the code's values as field elements
  have Xsel : B.toField X' = if (B.toField fe7).IsNeg then B.toField iY else B.toField X :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg hrot) (fun h => by rw [hX0 h])
      (fun h => by rw [hX1 h])
  have Ysel : B.toField Y' = if (B.toField fe7).IsNeg then B.toField iX else B.toField Y :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg hrot) (fun h => by rw [hY0 h])
      (fun h => by rw [hY1 h])
  have I21sel : B.toField i21 =
      if (B.toField fe7).IsNeg then B.toField ench else B.toField i2 :=
    eq_ite_of_choice hrotv (eq_one_iff_isNeg hrot) (fun h => by rw [hi210 h])
      (fun h => by rw [hi211 h])
  have Y1sel : B.toField Y1 = if (B.toField fe8).IsNeg then -B.toField Y' else B.toField Y' :=
    eq_ite_of_choice hcnv (eq_one_iff_isNeg hcn) (fun h => by rw [hY10 h])
      (fun h => (hY11 h).1)
  have S1 : B.toField s1 = (B.toField s).abs :=
    eq_ite_of_choice hsnv (eq_one_iff_isNeg hsn) (fun h => by rw [hs10 h])
      (fun h => (hs11 h).1)
  rw [ristretto.CompressedRistretto.asNat_def, hr, S1,
    ← RistrettoCompress.compressProj_eq_encodeRep _ Fe6 hZ0 hXYZT hx hy]
  congr 1
  rw [hs, I21sel, hfe9, Y1sel, Ysel, hfe8, Xsel, hench, hfe7, hz, hfe4, hi1', hi2', hiY, hiX,
    Fe5, Inv, hfe3, hfe2, hu1, hu2, Fe, Fe1]
  rfl

end Curve25519Dalek.Backend

namespace Curve25519Dalek.ristretto

namespace «RistrettoPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem compress_eq (self : RistrettoPoint.«x86_64-tables») :
    compress self = Backend.compressBody Backend.U64 self.X self.Y self.Z self.T :=
  rfl

open edwards.EdwardsPoint.«x86_64-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^52`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  rw [edwards.EdwardsPoint.«x86_64-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def] at hon
  rw [compress_eq, edwards.EdwardsPoint.«x86_64-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-tables».toExtended_def]
  exact Backend.compressBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.invsqrt_spec Backend.U64.sqrtM1_spec Backend.U64.invsqrtAMinusD_spec
    Backend.U64.is_negative_spec Backend.U64.conditional_assign_spec
    Backend.U64.conditional_negate_spec Backend.U64.to_bytes_spec _ _ _ _ hX hY hZ hT hon

end «RistrettoPointx86_64-tables»

namespace «RistrettoPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem compress_eq (self : RistrettoPoint.«i686-tables») :
    compress self = Backend.compressBody Backend.U32 self.X self.Y self.Z self.T :=
  rfl

open edwards.EdwardsPoint.«i686-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^26`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  rw [edwards.EdwardsPoint.«i686-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-tables».toExtended_def] at hon
  rw [compress_eq, edwards.EdwardsPoint.«i686-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-tables».toExtended_def]
  exact Backend.compressBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.invsqrt_spec Backend.U32.sqrtM1_spec Backend.U32.invsqrtAMinusD_spec
    Backend.U32.is_negative_spec Backend.U32.conditional_assign_spec
    Backend.U32.conditional_negate_spec Backend.U32.to_bytes_spec _ _ _ _ hX hY hZ hT hon

end «RistrettoPointi686-tables»

namespace «RistrettoPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

theorem compress_eq (self : RistrettoPoint.«x86_64-no-tables») :
    compress self = Backend.compressBody Backend.U64 self.X self.Y self.Z self.T :=
  rfl

open edwards.EdwardsPoint.«x86_64-no-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^52`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  rw [edwards.EdwardsPoint.«x86_64-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def] at hon
  rw [compress_eq, edwards.EdwardsPoint.«x86_64-no-tables».toPoint_def,
    edwards.EdwardsPoint.«x86_64-no-tables».toExtended_def]
  exact Backend.compressBody_spec Backend.U64
    Backend.U64.add_spec Backend.U64.sub_spec Backend.U64.mul_spec Backend.U64.square_spec
    Backend.U64.invsqrt_spec Backend.U64.sqrtM1_spec Backend.U64.invsqrtAMinusD_spec
    Backend.U64.is_negative_spec Backend.U64.conditional_assign_spec
    Backend.U64.conditional_negate_spec Backend.U64.to_bytes_spec _ _ _ _ hX hY hZ hT hon

end «RistrettoPointx86_64-no-tables»

namespace «RistrettoPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

theorem compress_eq (self : RistrettoPoint.«i686-no-tables») :
    compress self = Backend.compressBody Backend.U32 self.X self.Y self.Z self.T :=
  rfl

open edwards.EdwardsPoint.«i686-no-tables» in
/-- `RistrettoPoint::compress`: RFC 9496's encoding of the represented point; limbs `< 2^26`. -/
@[step]
theorem compress_spec (self : RistrettoPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedRistretto) =>
      r.asNat = Ristretto.encodeRep self.toPoint ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  rw [edwards.EdwardsPoint.«i686-no-tables».onCurve_iff,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def] at hon
  rw [compress_eq, edwards.EdwardsPoint.«i686-no-tables».toPoint_def,
    edwards.EdwardsPoint.«i686-no-tables».toExtended_def]
  exact Backend.compressBody_spec Backend.U32
    Backend.U32.add_spec Backend.U32.sub_spec Backend.U32.mul_spec Backend.U32.square_spec
    Backend.U32.invsqrt_spec Backend.U32.sqrtM1_spec Backend.U32.invsqrtAMinusD_spec
    Backend.U32.is_negative_spec Backend.U32.conditional_assign_spec
    Backend.U32.conditional_negate_spec Backend.U32.to_bytes_spec _ _ _ _ hX hY hZ hT hon

end «RistrettoPointi686-no-tables»

end Curve25519Dalek.ristretto
