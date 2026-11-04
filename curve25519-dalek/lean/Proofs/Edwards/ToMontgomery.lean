/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Montgomery
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Montgomery
import Proofs.Backend.Serial.U64.Field.Add
import Proofs.Backend.Serial.U64.Field.Mul
import Proofs.Backend.Serial.U64.Field.Sub
import Proofs.Backend.Serial.U64.Field.ToBytes
import Proofs.Field.Invert
import Proofs.Helpers.EdwardsMontgomery
import Proofs.Helpers.ToField
import Proofs.Backend.Serial.U32.Field.Add
import Proofs.Backend.Serial.U32.Field.Mul
import Proofs.Backend.Serial.U32.Field.Sub
import Proofs.Backend.Serial.U32.Field.ToBytes
import Proofs.Helpers.ToField2625
public section

/-! # `EdwardsPoint::to_montgomery`

The code computes `u = (Z + Y) / (Z - Y)` (`0` when `Z = Y`, since `invert 0 = 0`), which is
`(1 + y) / (1 - y)` for `y = Y / Z`: the `u`-coordinate of the image under the birational
equivalence, `0` at the identity (whose image is the point at infinity). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery`: the canonical bytes of `(Z + Y) / (Z - Y)` (`0` if
`Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = ((self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField)).val ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_montgomery
  step as ⟨U, hU⟩
  step as ⟨W, hW, hWb⟩
  step as ⟨fe, hfe1, hfe0, hfeb⟩
  step as ⟨u, hu, hub⟩
  step as ⟨a, ha⟩
  rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
    toField_inv_of_mod hfe1 hfe0, toField_add_of_limbs hU, toField_sub_of_mod hW, div_eq_mul_inv]

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
theorem to_montgomery_spec_point (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄ :=
  spec_mono (to_montgomery_spec self hself) fun r hr => by
    rw [hr, EdwardsPoint.«x86_64-tables».u_edwardsToMontgomery hon]
    rfl

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery`: the canonical bytes of `(Z + Y) / (Z - Y)` (`0` if
`Z = Y`); limbs `< 2^26`. -/
@[step]
theorem to_montgomery_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = ((self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField)).val ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_montgomery
  step as ⟨U, hU⟩
  step as ⟨W, hW, hWb⟩
  step as ⟨fe, hfe1, hfe0, hfeb⟩
  step as ⟨u, hu, hub⟩
  step as ⟨a, ha⟩
  rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
    toField_inv_of_mod hfe1 hfe0, toField_add_of_limbs hU, toField_sub_of_mod hW, div_eq_mul_inv]

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
theorem to_montgomery_spec_point (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄ :=
  spec_mono (to_montgomery_spec self hself) fun r hr => by
    rw [hr, EdwardsPoint.«i686-tables».u_edwardsToMontgomery hon]
    rfl

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `EdwardsPoint::to_montgomery`: the canonical bytes of `(Z + Y) / (Z - Y)` (`0` if
`Z = Y`); limbs `< 2^52`. -/
@[step]
theorem to_montgomery_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = ((self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField)).val ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_montgomery
  step as ⟨U, hU⟩
  step as ⟨W, hW, hWb⟩
  step as ⟨fe, hfe1, hfe0, hfeb⟩
  step as ⟨u, hu, hub⟩
  step as ⟨a, ha⟩
  rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
    toField_inv_of_mod hfe1 hfe0, toField_add_of_limbs hU, toField_sub_of_mod hW, div_eq_mul_inv]

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
theorem to_montgomery_spec_point (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄ :=
  spec_mono (to_montgomery_spec self hself) fun r hr => by
    rw [hr, EdwardsPoint.«x86_64-no-tables».u_edwardsToMontgomery hon]
    rfl

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `EdwardsPoint::to_montgomery`: the canonical bytes of `(Z + Y) / (Z - Y)` (`0` if
`Z = Y`); limbs `< 2^26`. -/
@[step]
theorem to_montgomery_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = ((self.Z.toField + self.Y.toField) / (self.Z.toField - self.Y.toField)).val ⦄ := by
  obtain ⟨hX, hY, hZ, hT⟩ := hself
  unfold to_montgomery
  step as ⟨U, hU⟩
  step as ⟨W, hW, hWb⟩
  step as ⟨fe, hfe1, hfe0, hfeb⟩
  step as ⟨u, hu, hub⟩
  step as ⟨a, ha⟩
  rw [montgomery.MontgomeryPoint.asNat_def, asNat_eq_val_of_mod ha, toField_mul_of_mod hu,
    toField_inv_of_mod hfe1 hfe0, toField_add_of_limbs hU, toField_sub_of_mod hW, div_eq_mul_inv]

/-- `EdwardsPoint::to_montgomery`: RFC 7748's encoding of the `u`-coordinate of the
Montgomery image of the represented point (`0` for the identity). -/
theorem to_montgomery_spec_point (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    to_montgomery self ⦃ (r : montgomery.MontgomeryPoint) =>
      r.asNat = encodeU (edwardsToMontgomery self.toPoint).u ⦄ :=
  spec_mono (to_montgomery_spec self hself) fun r hr => by
    rw [hr, EdwardsPoint.«i686-no-tables».u_edwardsToMontgomery hon]
    rfl

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
