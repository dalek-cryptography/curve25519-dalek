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

/-! # `LookupTableRadix256::select`

`select` is generic in the entry type; the specs below are its instances at the projective and
affine Niels points, through the generic `window.select_spec` (`Proofs/Helpers/Window.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open ProjectiveNielsPoint.«64bit-tables».Insts
open «Shared0ProjectiveNielsPoint64bit-tables».Insts

namespace «LookupTableRadix256ProjectiveNielsPoint64bit-tables»

/-- `LookupTableRadix256::select` on projective Niels points: a representative of `x • P`, for
any `x : i8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix256 ProjectiveNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint64bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-128)#i8 128#i16 129#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint64bit-tables».neg_spec
    self P hself hP x ⟨by scalar_tac, by scalar_tac⟩

end «LookupTableRadix256ProjectiveNielsPoint64bit-tables»

end

section
open ProjectiveNielsPoint.«32bit-tables».Insts
open «Shared0ProjectiveNielsPoint32bit-tables».Insts

namespace «LookupTableRadix256ProjectiveNielsPoint32bit-tables»

/-- `LookupTableRadix256::select` on projective Niels points: a representative of `x • P`, for
any `x : i8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix256 ProjectiveNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPoint32bit-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-128)#i8 128#i16 129#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPoint32bit-tables».neg_spec
    self P hself hP x ⟨by scalar_tac, by scalar_tac⟩

end «LookupTableRadix256ProjectiveNielsPoint32bit-tables»

end

section
open AffineNielsPoint.«64bit-tables».Insts
open «Shared0AffineNielsPoint64bit-tables».Insts

namespace «LookupTableRadix256AffineNielsPoint64bit-tables»

/-- `LookupTableRadix256::select` on affine Niels points: a representative of `x • P`, for
any `x : i8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix256 AffineNielsPoint.«64bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint64bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«64bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-128)#i8 128#i16 129#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint64bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint64bit-tables».neg_spec
    self P hself hP x ⟨by scalar_tac, by scalar_tac⟩

end «LookupTableRadix256AffineNielsPoint64bit-tables»

end

section
open AffineNielsPoint.«32bit-tables».Insts
open «Shared0AffineNielsPoint32bit-tables».Insts

namespace «LookupTableRadix256AffineNielsPoint32bit-tables»

/-- `LookupTableRadix256::select` on affine Niels points: a representative of `x • P`, for
any `x : i8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix256 AffineNielsPoint.«32bit-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    LookupTableRadix256.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPoint32bit-tables»)
      self x ⦃ (r : AffineNielsPoint.«32bit-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-128)#i8 128#i16 129#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPoint32bit-tables»
    Curve25519_dalekTraitsIdentity.identity_spec
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPoint32bit-tables».neg_spec
    self P hself hP x ⟨by scalar_tac, by scalar_tac⟩

end «LookupTableRadix256AffineNielsPoint32bit-tables»

end

end Curve25519Dalek.window
