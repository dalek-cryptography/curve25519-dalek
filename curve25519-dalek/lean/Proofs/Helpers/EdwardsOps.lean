/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Edwards.Basic
public import Defs.Window
public import Aeneas
public section

/-! # Point operations, for loop proofs shared by all configurations

The point layer one level above `Backend`: the scalar-multiplication loops (Pippenger, Straus,
…) call point functions (`EdwardsPoint + EdwardsPoint`, `+= `, `mul_by_pow_2`, `EdwardsPoint ±
ProjectiveNielsPoint`, `CompletedPoint::as_extended`, …) whose types differ per configuration.
An `EdwardsOps` bundles the point types (`E` extended, `N` projective Niels, `C` completed), their
model maps (`OnCurve`, `toPoint`) and limb bounds, and the operations as `Result` functions; the
operations' specs are propositions (`AddSpec`, …), stated exactly as the configurations'
`*_spec_point` theorems, which prove them (`Proofs/Helpers/EdwardsOps/Instances.lean`).

A loop then has a generic counterpart (same body, point calls through the interface) with a
generic spec, proved once; the translated loop of each configuration is `rfl`-equal to the
generic one at the instance. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

/-- The point types of a configuration, their models and bounds, and the point operations. -/
structure EdwardsOps where
  /-- `EdwardsPoint` -/
  E : Type
  /-- `ProjectiveNielsPoint` -/
  N : Type
  /-- `CompletedPoint` -/
  C : Type
  /-- `ProjectivePoint` -/
  Pr : Type
  /-- `AffineNielsPoint` -/
  An : Type
  /-- for `getElem!` on vectors of points -/
  inhE : Inhabited E
  /-- for `getElem!` on vectors of tables -/
  inhN : Inhabited N
  /-- for the affine Niels tables -/
  inhA : Inhabited An
  /-- the table entries' models and bounds (`OnCurve`, `toPoint`, `LimbsLt` of `N`) -/
  reprN : PointRepr N
  /-- `Copy for ProjectiveNielsPoint`, for the tables' `select` -/
  copyN : core.marker.Copy N
  /-- the affine Niels points' models and bounds -/
  reprA : PointRepr An
  /-- `Copy for AffineNielsPoint` -/
  copyA : core.marker.Copy An
  /-- the limb bound of an `AffineNielsPoint` is `LimbsLt aB` (`54` / `27`) -/
  aB : ℕ
  /-- the coordinates represent a point -/
  OnCurve : E → Prop
  /-- the represented point -/
  toPoint : E → edwards.Point
  /-- the limb bound of an `EdwardsPoint` (`LimbsLt 52` / `LimbsLt 26`) -/
  Bnd : E → Prop
  /-- the limb bound of a `ProjectiveNielsPoint` is `LimbsLt nB` (`54` / `27`) -/
  nB : ℕ
  /-- the projective coordinates represent a point -/
  pOnCurve : Pr → Prop
  /-- the point represented by projective coordinates -/
  pToPoint : Pr → edwards.Point
  /-- the limb bound of a `ProjectivePoint` (`LimbsLt 52` / `LimbsLt 26`) -/
  pBnd : Pr → Prop
  /-- the completed coordinates represent a point -/
  cOnCurve : C → Prop
  /-- the point represented by completed coordinates -/
  cToPoint : C → edwards.Point
  /-- the limb bound of a `CompletedPoint` (`LimbsLt 54` / `MulBounded`) -/
  cBnd : C → Prop
  /-- `Identity for EdwardsPoint` -/
  identity : Result E
  /-- `Add<&EdwardsPoint> for &EdwardsPoint` -/
  add : E → E → Result E
  /-- `AddAssign<&EdwardsPoint> for EdwardsPoint` -/
  addAssign : E → E → Result E
  /-- `EdwardsPoint::mul_by_pow_2` -/
  mulByPow2 : E → U32 → Result E
  /-- `Add<&ProjectiveNielsPoint> for &EdwardsPoint` -/
  addN : E → N → Result C
  /-- `Sub<&ProjectiveNielsPoint> for &EdwardsPoint` -/
  subN : E → N → Result C
  /-- `CompletedPoint::as_extended` -/
  asExtended : C → Result E
  /-- `Add<&AffineNielsPoint> for &EdwardsPoint` -/
  addA : E → An → Result C
  /-- `Sub<&AffineNielsPoint> for &EdwardsPoint` -/
  subA : E → An → Result C
  /-- `EdwardsPoint::as_projective_niels` -/
  asProjectiveNiels : E → Result N
  /-- `Identity for ProjectivePoint` -/
  pIdentity : Result Pr
  /-- `ProjectivePoint::double` -/
  pDouble : Pr → Result C
  /-- `CompletedPoint::as_projective` -/
  cAsProjective : C → Result Pr
  /-- `ProjectivePoint::as_extended` -/
  pAsExtended : Pr → Result E
  /-- `From<&EdwardsPoint> for NafLookupTable5<ProjectiveNielsPoint>` -/
  nafTable5 : E → Result (window.NafLookupTable5 N)
  /-- `LookupTable<ProjectiveNielsPoint>::select` -/
  ltSelect : window.LookupTable N → I8 → Result N
  /-- `From<&EdwardsPoint> for LookupTable<ProjectiveNielsPoint>` -/
  ltFrom : E → Result (window.LookupTable N)

namespace EdwardsOps

variable (P : EdwardsOps)

instance : Inhabited P.E := P.inhE

instance : Inhabited P.N := P.inhN

instance : Inhabited P.An := P.inhA

instance : PointRepr P.N := P.reprN

instance : PointRepr P.An := P.reprA

/-- The affine Niels point `n` represents a point. -/
abbrev aOnCurve (n : P.An) : Prop := PointRepr.OnCurve n

/-- The point represented by the affine Niels point `n`. -/
abbrev aToPoint (n : P.An) : edwards.Point := PointRepr.toPoint n

/-- The limb bound of the affine Niels point `n`. -/
abbrev aBnd (n : P.An) : Prop := PointRepr.LimbsLt P.aB n

/-- The entry `n` represents a point. -/
abbrev nOnCurve (n : P.N) : Prop := PointRepr.OnCurve n

/-- The point represented by the entry `n`. -/
abbrev nToPoint (n : P.N) : edwards.Point := PointRepr.toPoint n

/-- The limb bound of the entry `n`. -/
abbrev nBnd (n : P.N) : Prop := PointRepr.LimbsLt P.nB n

/-- `identity` is the neutral point. -/
abbrev IdentitySpec : Prop :=
  P.identity ⦃ r => P.OnCurve r ∧ P.toPoint r = 0 ∧ P.Bnd r ⦄

/-- `add` adds the represented points. -/
abbrev AddSpec : Prop := ∀ a b, P.Bnd a → P.Bnd b → P.OnCurve a → P.OnCurve b →
  P.add a b ⦃ r => P.OnCurve r ∧ P.toPoint r = P.toPoint a + P.toPoint b ∧ P.Bnd r ⦄

/-- `addAssign` adds the represented points. -/
abbrev AddAssignSpec : Prop := ∀ a b, P.Bnd a → P.Bnd b → P.OnCurve a → P.OnCurve b →
  P.addAssign a b ⦃ r => P.OnCurve r ∧ P.toPoint r = P.toPoint a + P.toPoint b ∧ P.Bnd r ⦄

/-- `mulByPow2 a k` is `2^k • a`. -/
abbrev MulByPow2Spec : Prop := ∀ a (k : U32), P.Bnd a → P.OnCurve a → 0 < k.val →
  P.mulByPow2 a k ⦃ r => P.OnCurve r ∧ P.toPoint r = 2 ^ k.val • P.toPoint a ∧ P.Bnd r ⦄

/-- `addN` adds a projective Niels point. -/
abbrev AddNSpec : Prop := ∀ a n, P.Bnd a → P.nBnd n → P.OnCurve a → P.nOnCurve n →
  P.addN a n ⦃ r => P.cOnCurve r ∧ P.cToPoint r = P.toPoint a + P.nToPoint n ∧ P.cBnd r ⦄

/-- `subN` subtracts a projective Niels point. -/
abbrev SubNSpec : Prop := ∀ a n, P.Bnd a → P.nBnd n → P.OnCurve a → P.nOnCurve n →
  P.subN a n ⦃ r => P.cOnCurve r ∧ P.cToPoint r = P.toPoint a - P.nToPoint n ∧ P.cBnd r ⦄

/-- `addA` adds an affine Niels point. -/
abbrev AddASpec : Prop := ∀ a n, P.Bnd a → P.aBnd n → P.OnCurve a → P.aOnCurve n →
  P.addA a n ⦃ r => P.cOnCurve r ∧ P.cToPoint r = P.toPoint a + P.aToPoint n ∧ P.cBnd r ⦄

/-- `subA` subtracts an affine Niels point. -/
abbrev SubASpec : Prop := ∀ a n, P.Bnd a → P.aBnd n → P.OnCurve a → P.aOnCurve n →
  P.subA a n ⦃ r => P.cOnCurve r ∧ P.cToPoint r = P.toPoint a - P.aToPoint n ∧ P.cBnd r ⦄

/-- `asExtended` represents the same point. -/
abbrev AsExtendedSpec : Prop := ∀ c, P.cBnd c → P.cOnCurve c →
  P.asExtended c ⦃ r => P.OnCurve r ∧ P.toPoint r = P.cToPoint c ∧ P.Bnd r ⦄

/-- `asProjectiveNiels` represents the same point. -/
abbrev AsProjectiveNielsSpec : Prop := ∀ a, P.Bnd a → P.OnCurve a →
  P.asProjectiveNiels a ⦃ r => P.nOnCurve r ∧ P.nToPoint r = P.toPoint a ∧ P.nBnd r ⦄

/-- `pIdentity` is the neutral point. -/
abbrev PIdentitySpec : Prop :=
  P.pIdentity ⦃ r => P.pOnCurve r ∧ P.pToPoint r = 0 ∧ P.pBnd r ⦄

/-- `pDouble` doubles the represented point. -/
abbrev PDoubleSpec : Prop := ∀ a, P.pBnd a → P.pOnCurve a →
  P.pDouble a ⦃ r => P.cOnCurve r ∧ P.cToPoint r = 2 • P.pToPoint a ∧ P.cBnd r ⦄

/-- `cAsProjective` represents the same point. -/
abbrev CAsProjectiveSpec : Prop := ∀ c, P.cBnd c → P.cOnCurve c →
  P.cAsProjective c ⦃ r => P.pOnCurve r ∧ P.pToPoint r = P.cToPoint c ∧ P.pBnd r ⦄

/-- `pAsExtended` represents the same point. -/
abbrev PAsExtendedSpec : Prop := ∀ a, P.pBnd a → P.pOnCurve a →
  P.pAsExtended a ⦃ r => P.OnCurve r ∧ P.toPoint r = P.pToPoint a ∧ P.Bnd r ⦄

/-- `nafTable5 a` holds the odd multiples of `a`. -/
abbrev NafTable5Spec : Prop := ∀ a, P.Bnd a → P.OnCurve a →
  P.nafTable5 a ⦃ r => r.Represents (P.toPoint a) ∧ r.LimbsLt P.nB ⦄

/-- `ltSelect t x` represents `x • P` for a table `t` of the multiples of `P`, `|x| ≤ 8`. -/
abbrev LtSelectSpec : Prop := ∀ (t : window.LookupTable P.N) (x : I8) (Q : edwards.Point),
  t.LimbsLt P.nB → t.Represents Q → -8 ≤ x.val ∧ x.val ≤ 8 →
  P.ltSelect t x ⦃ r => P.nOnCurve r ∧ P.nToPoint r = x.val • Q ∧ P.nBnd r ⦄

/-- `ltFrom a` holds the multiples `1 • a, …, 8 • a`. -/
abbrev LtFromSpec : Prop := ∀ a, P.Bnd a → P.OnCurve a →
  P.ltFrom a ⦃ r => r.Represents (P.toPoint a) ∧ r.LimbsLt P.nB ⦄

end EdwardsOps

end Curve25519Dalek
