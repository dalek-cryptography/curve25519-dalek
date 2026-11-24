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

/-! # `LookupTable::select`

`select` is generic in the entry type; the specs below are its instances at the projective and
affine Niels points, through the generic `window.select_spec` (`Proofs/Helpers/Window.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open ProjectiveNielsPoint.«64bit-tables».Insts
open «Shared0ProjectiveNielsPoint64bit-tables».Insts

namespace «LookupTableProjectiveNielsPoint64bit-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint64bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableProjectiveNielsPoint64bit-tables»

end

section
open ProjectiveNielsPoint.«32bit-tables».Insts
open «Shared0ProjectiveNielsPoint32bit-tables».Insts

namespace «LookupTableProjectiveNielsPoint32bit-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint32bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableProjectiveNielsPoint32bit-tables»

end

section
open AffineNielsPoint.«64bit-tables».Insts
open «Shared0AffineNielsPoint64bit-tables».Insts

namespace «LookupTableAffineNielsPoint64bit-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint64bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableAffineNielsPoint64bit-tables»

end

section
open AffineNielsPoint.«32bit-tables».Insts
open «Shared0AffineNielsPoint32bit-tables».Insts

namespace «LookupTableAffineNielsPoint32bit-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint32bit-tables».neg_spec
    self P hself hP x hx

end «LookupTableAffineNielsPoint32bit-tables»

end

section
open ProjectiveNielsPoint.«64bit-notables».Insts
open «Shared0ProjectiveNielsPoint64bit-notables».Insts

namespace «LookupTableProjectiveNielsPoint64bit-notables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«64bit-notables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint64bit-notables»)
      self x ⦃ (r : ProjectiveNielsPoint.«64bit-notables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint64bit-notables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint64bit-notables».neg_spec
    self P hself hP x hx

end «LookupTableProjectiveNielsPoint64bit-notables»

end

section
open ProjectiveNielsPoint.«32bit-notables».Insts
open «Shared0ProjectiveNielsPoint32bit-notables».Insts

namespace «LookupTableProjectiveNielsPoint32bit-notables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«32bit-notables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint32bit-notables»)
      self x ⦃ (r : ProjectiveNielsPoint.«32bit-notables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint32bit-notables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint32bit-notables».neg_spec
    self P hself hP x hx

end «LookupTableProjectiveNielsPoint32bit-notables»

end

section
open AffineNielsPoint.«64bit-notables».Insts
open «Shared0AffineNielsPoint64bit-notables».Insts

namespace «LookupTableAffineNielsPoint64bit-notables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«64bit-notables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-notables»)
      self x ⦃ (r : AffineNielsPoint.«64bit-notables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint64bit-notables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint64bit-notables».neg_spec
    self P hself hP x hx

end «LookupTableAffineNielsPoint64bit-notables»

end

section
open AffineNielsPoint.«32bit-notables».Insts
open «Shared0AffineNielsPoint32bit-notables».Insts

namespace «LookupTableAffineNielsPoint32bit-notables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«32bit-notables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-notables»)
      self x ⦃ (r : AffineNielsPoint.«32bit-notables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint32bit-notables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint32bit-notables».neg_spec
    self P hself hP x hx

end «LookupTableAffineNielsPoint32bit-notables»

end

end Curve25519Dalek.window
