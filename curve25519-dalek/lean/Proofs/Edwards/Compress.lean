/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Curve25519.Edwards.Encoding
public import Defs.Edwards
import Proofs.Edwards.Affine.Compress
import Proofs.Edwards.ToAffine
import Proofs.Helpers.Coords
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«x86_64-tables».toPoint_x hon,
        EdwardsPoint.«x86_64-tables».toPoint_y hon]

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«i686-tables».toPoint_x hon,
        EdwardsPoint.«i686-tables».toPoint_y hon]

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«x86_64-no-tables».toPoint_x hon,
        EdwardsPoint.«x86_64-no-tables».toPoint_y hon]

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«i686-no-tables».toPoint_x hon,
        EdwardsPoint.«i686-no-tables».toPoint_y hon]

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
