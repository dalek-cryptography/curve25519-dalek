/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Edwards.CtEq
import Proofs.Edwards.Identity
import Proofs.Traits.IsIdentity
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519 TwistedEdwardsModel
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)
open Curve25519Dalek.backend.serial.u32.field (FieldElement2625)
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards

namespace EdwardsPoint.«64bit-tables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^52`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«64bit-tables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (r : Bool) =>
      r = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«64bit-tables»

namespace EdwardsPoint.«32bit-tables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^26`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«32bit-tables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (r : Bool) =>
      r = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«32bit-tables»

namespace EdwardsPoint.«64bit-notables»

open Curve25519Dalek.backend.serial.u64.field.FieldElement51

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^52`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«64bit-notables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«64bit-notables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (r : Bool) =>
      r = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«64bit-notables»

namespace EdwardsPoint.«32bit-notables»

open Curve25519Dalek.backend.serial.u32.field.FieldElement2625

/-- `IsIdentity::is_identity` (the blanket implementation of `traits.rs`) at `EdwardsPoint`:
`ct_eq` with the identity; limbs `< 2^26`. -/
@[step]
theorem is_identity_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    traits.IsIdentity.Blanket.is_identity
      EdwardsPoint.«32bit-notables».Insts.SubtleConstantTimeEq
      EdwardsPoint.«32bit-notables».Insts.Curve25519_dalekTraitsIdentity self ⦃ (r : Bool) =>
      r = true ↔ self.toPoint = 0 ⦄ :=
  traits.IsIdentity.Blanket.is_identity_spec _ _ self _ _
    Insts.Curve25519_dalekTraitsIdentity.identity_spec fun e ⟨heon, he, heb⟩ =>
      spec_mono (Insts.SubtleConstantTimeEq.ct_eq_spec self e hself heb hon heon)
        fun _ ⟨hcv, hc⟩ => ⟨hcv, he ▸ hc⟩

end EdwardsPoint.«32bit-notables»

end Curve25519Dalek.edwards
