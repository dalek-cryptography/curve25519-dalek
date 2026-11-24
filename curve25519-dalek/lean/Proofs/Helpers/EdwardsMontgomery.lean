module
public import Proofs.Curve25519.Montgomery
public import Proofs.Representation.Edwards
import Proofs.Helpers.Coords
public section

/-! # The Montgomery `u`-coordinate of a represented point

`to_montgomery` computes `(Z + Y) / (Z - Y)`; for a point on the curve this is `(1 + y) / (1 - y)`
with `y = Y / Z`, the `u`-coordinate of the image under `edwardsToMontgomery` (both are `0` when
`Z = Y`). -/

open curve25519

namespace Curve25519Dalek.edwards

/-- `(Z + Y) / (Z - Y)` is `(1 + y) / (1 - y)` for `y = Y / Z` (both `0` if `Z = Y`). -/
theorem div_eq_one_add_div_one_sub {Y Z : ZMod p} (hZ : Z ≠ 0) :
    (Z + Y) / (Z - Y) = (1 + Y / Z) / (1 - Y / Z) := by
  rw [← div_self hZ, ← add_div, ← sub_div, div_div_div_cancel_right₀ hZ]

theorem EdwardsPoint.«64bit-tables».u_edwardsToMontgomery {self : EdwardsPoint.«64bit-tables»}
    (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«64bit-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«64bit-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«32bit-tables».u_edwardsToMontgomery {self : EdwardsPoint.«32bit-tables»}
    (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«32bit-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«32bit-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«64bit-notables».u_edwardsToMontgomery
    {self : EdwardsPoint.«64bit-notables»} (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«64bit-notables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«64bit-notables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«32bit-notables».u_edwardsToMontgomery
    {self : EdwardsPoint.«32bit-notables»} (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«32bit-notables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«32bit-notables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

end Curve25519Dalek.edwards
