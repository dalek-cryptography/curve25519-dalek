module
public import Curve25519Dalek.Funs
public import Proofs.Curve25519.Edwards.Encoding
public import Proofs.Representation.Edwards
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

namespace «EdwardsPoint64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«64bit-tables».toPoint_x hon,
        EdwardsPoint.«64bit-tables».toPoint_y hon]

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«32bit-tables».toPoint_x hon,
        EdwardsPoint.«32bit-tables».toPoint_y hon]

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^52`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«64bit-notables».toPoint_x hon,
        EdwardsPoint.«64bit-notables».toPoint_y hon]

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::compress`: the canonical `y = Y / Z` with the sign of `x = X / Z` in
bit `255`; limbs `< 2^26`. -/
@[step]
theorem compress_asNat (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26) :
    compress self ⦃ (r : CompressedEdwardsY) =>
      r.asNat = (self.Y.toField / self.Z.toField).val +
        2 ^ 255 * (if (self.X.toField / self.Z.toField).IsNeg then 1 else 0) ⦄ := by
  unfold compress
  step as ⟨ap, hx, hy, hb⟩
  step as ⟨r, hr⟩
  rw [hr, hx, hy]

/-- `EdwardsPoint::compress` is RFC 8032's encoding of the represented point. -/
theorem compress_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    compress self ⦃ (r : CompressedEdwardsY) => r.toVector = curve25519.encode self.toPoint ⦄ := by
  simp only [Curve25519Dalek.edwards.CompressedEdwardsY.toVector_eq_encode_iff]
  exact spec_mono (compress_asNat self hself) fun r hr => by
      rw [hr, encodeNat_eq, EdwardsPoint.«32bit-notables».toPoint_x hon,
        EdwardsPoint.«32bit-notables».toPoint_y hon]

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
