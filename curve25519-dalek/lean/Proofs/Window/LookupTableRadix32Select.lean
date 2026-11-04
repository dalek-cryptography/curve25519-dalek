/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Window
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
open ProjectiveNielsPoint.«x86_64-tables».Insts
open «Shared0ProjectiveNielsPointx86_64-tables».Insts

namespace «LookupTableRadix32ProjectiveNielsPointx86_64-tables»

/-- `LookupTableRadix32::select` on projective Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 ProjectiveNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointx86_64-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix32ProjectiveNielsPointx86_64-tables»

end

section
open ProjectiveNielsPoint.«i686-tables».Insts
open «Shared0ProjectiveNielsPointi686-tables».Insts

namespace «LookupTableRadix32ProjectiveNielsPointi686-tables»

/-- `LookupTableRadix32::select` on projective Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 ProjectiveNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointi686-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix32ProjectiveNielsPointi686-tables»

end

section
open AffineNielsPoint.«x86_64-tables».Insts
open «Shared0AffineNielsPointx86_64-tables».Insts

namespace «LookupTableRadix32AffineNielsPointx86_64-tables»

/-- `LookupTableRadix32::select` on affine Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 AffineNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»)
      self x ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix32AffineNielsPointx86_64-tables»

end

section
open AffineNielsPoint.«i686-tables».Insts
open «Shared0AffineNielsPointi686-tables».Insts

namespace «LookupTableRadix32AffineNielsPointi686-tables»

/-- `LookupTableRadix32::select` on affine Niels points: a representative of `x • P`, for
`-16 ≤ x ≤ 16`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix32 AffineNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -16 ≤ x.val ∧ x.val ≤ 16) :
    LookupTableRadix32.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»)
      self x ⦃ (r : AffineNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-16)#i8 16#i16 17#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix32AffineNielsPointi686-tables»

end

end Curve25519Dalek.window
