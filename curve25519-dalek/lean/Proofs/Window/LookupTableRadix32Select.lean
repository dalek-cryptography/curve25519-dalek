module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Window
import Proofs.Backend.Serial.CurveModels.AffineNielsConditionalAssign
import Proofs.Backend.Serial.CurveModels.AffineNielsIdentity
import Proofs.Backend.Serial.CurveModels.AffineNielsNeg
import Proofs.Backend.Serial.CurveModels.ProjectiveNielsConditionalAssign
import Proofs.Backend.Serial.CurveModels.ProjectiveNielsIdentity
import Proofs.Backend.Serial.CurveModels.ProjectiveNielsNeg
import Proofs.Helpers.Window
public section

/-! # `LookupTableRadix32::select`

`select` is generic in the entry type; the specs below are its instances at the projective and
affine Niels points, through the generic `window.select_spec` (`Proofs/Helpers/Window.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open ProjectiveNielsPoint.«64bit-tables».Insts
open «Shared0ProjectiveNielsPoint64bit-tables».Insts

namespace «LookupTableRadix32ProjectiveNielsPoint64bit-tables»

/-- `LookupTableRadix32::select` on projective Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 ProjectiveNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint64bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableRadix32ProjectiveNielsPoint64bit-tables»

end

section
open ProjectiveNielsPoint.«32bit-tables».Insts
open «Shared0ProjectiveNielsPoint32bit-tables».Insts

namespace «LookupTableRadix32ProjectiveNielsPoint32bit-tables»

/-- `LookupTableRadix32::select` on projective Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 ProjectiveNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint32bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableRadix32ProjectiveNielsPoint32bit-tables»

end

section
open AffineNielsPoint.«64bit-tables».Insts
open «Shared0AffineNielsPoint64bit-tables».Insts

namespace «LookupTableRadix32AffineNielsPoint64bit-tables»

/-- `LookupTableRadix32::select` on affine Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 AffineNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint64bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableRadix32AffineNielsPoint64bit-tables»

end

section
open AffineNielsPoint.«32bit-tables».Insts
open «Shared0AffineNielsPoint32bit-tables».Insts

namespace «LookupTableRadix32AffineNielsPoint32bit-tables»

/-- `LookupTableRadix32::select` on affine Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 AffineNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint32bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableRadix32AffineNielsPoint32bit-tables»

end

end Curve25519Dalek.window
