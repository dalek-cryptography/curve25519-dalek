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

/-! # `LookupTableRadix64::select`

`select` is generic in the entry type; the specs below are its instances at the projective and
affine Niels points, through the generic `window.select_spec` (`Proofs/Helpers/Window.lean`). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.window

section
open ProjectiveNielsPoint.«x86_64-tables».Insts
open «Shared0ProjectiveNielsPointx86_64-tables».Insts

namespace «LookupTableRadix64ProjectiveNielsPointx86_64-tables»

/-- `LookupTableRadix64::select` on projective Niels points: a representative of `x • P`, for
`-32 ≤ x ≤ 32`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix64 ProjectiveNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -32 ≤ x.val ∧ x.val ≤ 32) :
    LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointx86_64-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-32)#i8 32#i16 33#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix64ProjectiveNielsPointx86_64-tables»

end

section
open ProjectiveNielsPoint.«i686-tables».Insts
open «Shared0ProjectiveNielsPointi686-tables».Insts

namespace «LookupTableRadix64ProjectiveNielsPointi686-tables»

/-- `LookupTableRadix64::select` on projective Niels points: a representative of `x • P`, for
`-32 ≤ x ≤ 32`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix64 ProjectiveNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -32 ≤ x.val ∧ x.val ≤ 32) :
    LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegProjectiveNielsPointi686-tables»)
      self x ⦃ (r : ProjectiveNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-32)#i8 32#i16 33#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegProjectiveNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegProjectiveNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix64ProjectiveNielsPointi686-tables»

end

section
open AffineNielsPoint.«x86_64-tables».Insts
open «Shared0AffineNielsPointx86_64-tables».Insts

namespace «LookupTableRadix64AffineNielsPointx86_64-tables»

/-- `LookupTableRadix64::select` on affine Niels points: a representative of `x • P`, for
`-32 ≤ x ≤ 32`; limbs `< 2^54`. -/
@[step]
theorem select_spec (self : LookupTableRadix64 AffineNielsPoint.«x86_64-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P)
    (hx : -32 ≤ x.val ∧ x.val ≤ 32) :
    LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointx86_64-tables»)
      self x ⦃ (r : AffineNielsPoint.«x86_64-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 54 ⦄ :=
  window.select_spec (-32)#i8 32#i16 33#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointx86_64-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointx86_64-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix64AffineNielsPointx86_64-tables»

end

section
open AffineNielsPoint.«i686-tables».Insts
open «Shared0AffineNielsPointi686-tables».Insts

namespace «LookupTableRadix64AffineNielsPointi686-tables»

/-- `LookupTableRadix64::select` on affine Niels points: a representative of `x • P`, for
`-32 ≤ x ≤ 32`; limbs `< 2^27`. -/
@[step]
theorem select_spec (self : LookupTableRadix64 AffineNielsPoint.«i686-tables») (x : I8)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P)
    (hx : -32 ≤ x.val ∧ x.val ≤ 32) :
    LookupTableRadix64.select Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
      (subtle.ConditionallyNegatable.Blanket SubtleConditionallySelectable
        «CoreOpsArithNegAffineNielsPointi686-tables»)
      self x ⦃ (r : AffineNielsPoint.«i686-tables») =>
        r.OnCurve ∧ r.toPoint = x.val • P ∧ r.LimbsLt 27 ⦄ :=
  window.select_spec (-32)#i8 32#i16 33#usize (by decide) (by decide) (by decide) (by decide)
    Curve25519_dalekTraitsIdentity SubtleConditionallySelectable
    «CoreOpsArithNegAffineNielsPointi686-tables»
    Curve25519_dalekTraitsIdentity.identity_spec_point
    SubtleConditionallySelectable.conditional_assign_spec
    «CoreOpsArithNegAffineNielsPointi686-tables».neg_spec_point
    self P hself hP x hx

end «LookupTableRadix64AffineNielsPointi686-tables»

end

end Curve25519Dalek.window
