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

/-! # `LookupTable::select`

`select` is generic in the entry type; the specs below are its instances at the projective and
affine Niels points, through the generic `window.select_spec` (`Proofs/Helpers/Window.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open ProjectiveNielsPoint.«x86_64-tables».Insts
open «Shared0ProjectiveNielsPointx86_64-tables».Insts

namespace «LookupTableProjectiveNielsPointx86_64-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointx86_64-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableProjectiveNielsPointx86_64-tables»

end

section
open ProjectiveNielsPoint.«i686-tables».Insts
open «Shared0ProjectiveNielsPointi686-tables».Insts

namespace «LookupTableProjectiveNielsPointi686-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointi686-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableProjectiveNielsPointi686-tables»

end

section
open AffineNielsPoint.«x86_64-tables».Insts
open «Shared0AffineNielsPointx86_64-tables».Insts

namespace «LookupTableAffineNielsPointx86_64-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»)
      self x ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableAffineNielsPointx86_64-tables»

end

section
open AffineNielsPoint.«i686-tables».Insts
open «Shared0AffineNielsPointi686-tables».Insts

namespace «LookupTableAffineNielsPointi686-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»)
      self x ⦃ (r : AffineNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableAffineNielsPointi686-tables»

end

section
open ProjectiveNielsPoint.«x86_64-no-tables».Insts
open «Shared0ProjectiveNielsPointx86_64-no-tables».Insts

namespace «LookupTableProjectiveNielsPointx86_64-no-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«x86_64-no-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointx86_64-no-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableProjectiveNielsPointx86_64-no-tables»

end

section
open ProjectiveNielsPoint.«i686-no-tables».Insts
open «Shared0ProjectiveNielsPointi686-no-tables».Insts

namespace «LookupTableProjectiveNielsPointi686-no-tables»

/-- `LookupTable::select` on projective Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable ProjectiveNielsPoint.«i686-no-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointi686-no-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«i686-no-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointi686-no-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointi686-no-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableProjectiveNielsPointi686-no-tables»

end

section
open AffineNielsPoint.«x86_64-no-tables».Insts
open «Shared0AffineNielsPointx86_64-no-tables».Insts

namespace «LookupTableAffineNielsPointx86_64-no-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«x86_64-no-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-no-tables»)
      self x ⦃ (r : AffineNielsPoint.«x86_64-no-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointx86_64-no-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointx86_64-no-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableAffineNielsPointx86_64-no-tables»

end

section
open AffineNielsPoint.«i686-no-tables».Insts
open «Shared0AffineNielsPointi686-no-tables».Insts

namespace «LookupTableAffineNielsPointi686-no-tables»

/-- `LookupTable::select` on affine Niels points: a representative of `x • P`, for
`-8 ≤ x ≤ 8`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTable AffineNielsPoint.«i686-no-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -8 ≤ x.val ∧ x.val ≤ 8) :
    LookupTable.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-no-tables»)
      self x ⦃ (r : AffineNielsPoint.«i686-no-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-8)#i8 8#i16 9#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointi686-no-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointi686-no-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableAffineNielsPointi686-no-tables»

end

end Curve25519Dalek.window
