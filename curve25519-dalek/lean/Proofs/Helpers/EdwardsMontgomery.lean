/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Defs.Edwards
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

theorem EdwardsPoint.«x86_64-tables».u_edwardsToMontgomery {self : EdwardsPoint.«x86_64-tables»}
    (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«x86_64-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«x86_64-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«i686-tables».u_edwardsToMontgomery {self : EdwardsPoint.«i686-tables»}
    (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«i686-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«i686-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«x86_64-no-tables».u_edwardsToMontgomery
    {self : EdwardsPoint.«x86_64-no-tables»} (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«x86_64-no-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«x86_64-no-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

theorem EdwardsPoint.«i686-no-tables».u_edwardsToMontgomery
    {self : EdwardsPoint.«i686-no-tables»} (hon : self.OnCurve) :
    (edwardsToMontgomery self.toPoint).u =
      (self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField) := by
  obtain ⟨hZ, -, -⟩ := (EdwardsPoint.«i686-no-tables».onCurve_iff_equation self).mp hon
  rw [curve25519.u_edwardsToMontgomery, EdwardsPoint.«i686-no-tables».toPoint_y hon,
    div_eq_one_add_div_one_sub hZ]

end Curve25519Dalek.edwards
