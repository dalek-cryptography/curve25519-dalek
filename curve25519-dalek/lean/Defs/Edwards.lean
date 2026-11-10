/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Window
public import ToAeneas.Array
public section

/-! # `edwards.rs`: points, the compressed form, the lenient decoder, the basepoint tables
(audited)

- `EdwardsPoint` implements the extended coordinates `(X : Y : Z : T)` of `curve25519.edwards`
  on radix-`2^51` limbs (x86_64) or radix-`2^25.5` limbs (i686): `toExtended` (hidden,
  `toExtended_def`), `OnCurve` (exposed), `toPoint` (hidden, `toPoint_def`), `LimbsLt n` (all
  limbs `< 2^n`, exposed), `IsBounded` (exposed: `LimbsLt 52` on x86_64, the bound forced by
  the mixed affine-Niels addition, `LimbsLt 26` on i686; the bound every public function
  assumes and preserves) and `ProjEq` (exposed), the projective equality that `ct_eq`
  computes.
- `AffinePoint` (`edwards/affine.rs`) is the affine point itself: `OnCurve` is the curve
  equation, `toPoint` the point (`0` off the curve), `LimbsLt n` as for `EdwardsPoint`.
- `CompressedEdwardsY` is 32 bytes; `toVector` gives them as a `Vector UInt8 32`, the byte
  string of RFC 8032 (`curve25519.encode`, `decodeLenient`).
- The basepoint tables `EdwardsBasepointTable{,Radix32,Radix64,Radix128,Radix256}` (radix
  `2^w`, `w = 4, 5, 6, 7, 8`) hold `32` rows of `2^(w-1)` affine Niels points. `t.point` is the
  point of entry `0` of row `0`, and `t.IsTable`, the invariant of the Rust type (whose tables
  come only from `BasepointTable::create`), says that entry `j` of row `i` is on the curve and
  is `(j + 1) • 2^(2 w i) • t.point`. `t.IsBounded`: every limb of every entry is `< 2^54`
  (x86_64) or `< 2^27` (i686).
  They exist only in the `tables` configuration.

`RistrettoPoint` is `EdwardsPoint`; see `Defs.Ristretto`. -/

open Aeneas Aeneas.Std
open curve25519 (p)
open Curve25519Dalek.backend.serial.u64.field (FieldElement51)

namespace Curve25519Dalek.edwards

/-! ### `EdwardsPoint` (`x86_64-tables`) -/

namespace EdwardsPoint.«x86_64-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«x86_64-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toExtended_def (self : EdwardsPoint.«x86_64-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«x86_64-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

theorem toPoint_def (self : EdwardsPoint.«x86_64-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of an `EdwardsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

/-- The bound on the limbs of an `EdwardsPoint` that every public function assumes and preserves:
every limb is `< 2^52`. -/
@[expose] def IsBounded (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.LimbsLt 52

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«x86_64-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end EdwardsPoint.«x86_64-tables»

namespace EdwardsPoint.«i686-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«i686-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toExtended_def (self : EdwardsPoint.«i686-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«i686-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«i686-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

theorem toPoint_def (self : EdwardsPoint.«i686-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of an `EdwardsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : EdwardsPoint.«i686-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

/-- The bound on the limbs of an `EdwardsPoint` that every public function assumes and preserves:
every limb is `< 2^26`. -/
@[expose] def IsBounded (self : EdwardsPoint.«i686-tables») : Prop :=
  self.LimbsLt 26

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«i686-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«i686-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end EdwardsPoint.«i686-tables»

/-! ### `AffinePoint` (`x86_64-tables`) -/

namespace affine.AffinePoint.«x86_64-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«x86_64-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«x86_64-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«x86_64-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«x86_64-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«x86_64-tables»

namespace affine.AffinePoint.«i686-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«i686-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«i686-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«i686-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«i686-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«i686-tables»

/-! ### `EdwardsPoint` (`x86_64-no-tables`) -/

namespace EdwardsPoint.«x86_64-no-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«x86_64-no-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toExtended_def (self : EdwardsPoint.«x86_64-no-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«x86_64-no-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«x86_64-no-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

theorem toPoint_def (self : EdwardsPoint.«x86_64-no-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of an `EdwardsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : EdwardsPoint.«x86_64-no-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

/-- The bound on the limbs of an `EdwardsPoint` that every public function assumes and preserves:
every limb is `< 2^52`. -/
@[expose] def IsBounded (self : EdwardsPoint.«x86_64-no-tables») : Prop :=
  self.LimbsLt 52

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«x86_64-no-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«x86_64-no-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end EdwardsPoint.«x86_64-no-tables»

namespace EdwardsPoint.«i686-no-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«i686-no-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

theorem toExtended_def (self : EdwardsPoint.«i686-no-tables») :
    self.toExtended = ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩ := by
  unfold toExtended
  rfl

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«i686-no-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«i686-no-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

theorem toPoint_def (self : EdwardsPoint.«i686-no-tables») :
    self.toPoint = self.toExtended.toPoint := by
  unfold toPoint
  rfl

/-- Every limb of an `EdwardsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : EdwardsPoint.«i686-no-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

/-- The bound on the limbs of an `EdwardsPoint` that every public function assumes and preserves:
every limb is `< 2^26`. -/
@[expose] def IsBounded (self : EdwardsPoint.«i686-no-tables») : Prop :=
  self.LimbsLt 26

/-- Projective equality `X₁ Z₂ = X₂ Z₁ ∧ Y₁ Z₂ = Y₂ Z₁` (`T` ignored): what `ct_eq` computes.
Equality of the represented points when both are on the curve
(`Proofs/Helpers/Coords.lean`). -/
@[expose] def ProjEq (self other : EdwardsPoint.«i686-no-tables») : Prop :=
  self.toExtended.ProjEq other.toExtended

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«i686-no-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end EdwardsPoint.«i686-no-tables»

/-! ### `AffinePoint` (`x86_64-no-tables`) -/

namespace affine.AffinePoint.«x86_64-no-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«x86_64-no-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«x86_64-no-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«x86_64-no-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«x86_64-no-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«x86_64-no-tables»

namespace affine.AffinePoint.«i686-no-tables»

/-- `(x, y)` is on the curve. -/
@[expose] def OnCurve (self : AffinePoint.«i686-no-tables») : Prop :=
  curve25519.edwards.Equation self.x.toField self.y.toField

open scoped Classical in
/-- The point `(x, y)` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : AffinePoint.«i686-no-tables») : curve25519.edwards.Point :=
  if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0

open scoped Classical in
theorem toPoint_def (self : AffinePoint.«i686-no-tables») :
    self.toPoint =
      if h : self.OnCurve then ⟨self.x.toField, self.y.toField, h⟩ else 0 := by
  unfold toPoint
  rfl

/-- Every limb of an `AffinePoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : AffinePoint.«i686-no-tables») : Prop :=
  self.x.LimbsLt n ∧ self.y.LimbsLt n

end affine.AffinePoint.«i686-no-tables»

/-! ### `CompressedEdwardsY` -/

/-- Needed for `v[i]!` on vectors and arrays of compressed points; the default is never
observed for in-range indices. -/
instance CompressedEdwardsY.instInhabited : Inhabited CompressedEdwardsY :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

/-! ### The basepoint tables (`tables` configurations only) -/

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTable.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix32.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix64.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix128.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix256.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The point the radix-`16` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTable.«x86_64-tables».point
    (self : EdwardsBasepointTable.«x86_64-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`16` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(8 i) • self.point`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».IsTable
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  ∀ i < 32, ∀ j < 8, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (8 * i) • self.point)

/-- The bound on the limbs of the radix-`16` table that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The point the radix-`16` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTable.«i686-tables».point
    (self : EdwardsBasepointTable.«i686-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`16` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(8 i) • self.point`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».IsTable
    (self : EdwardsBasepointTable.«i686-tables») : Prop :=
  ∀ i < 32, ∀ j < 8, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (8 * i) • self.point)

/-- The bound on the limbs of the radix-`16` table that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».IsBounded
    (self : EdwardsBasepointTable.«i686-tables») : Prop :=
  self.LimbsLt 27

/-- The point the radix-`32` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix32.«x86_64-tables».point
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`32` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(10 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».IsTable
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  ∀ i < 32, ∀ j < 16, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (10 * i) • self.point)

/-- The bound on the limbs of the radix-`32` table that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The point the radix-`32` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix32.«i686-tables».point
    (self : EdwardsBasepointTableRadix32.«i686-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`32` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(10 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».IsTable
    (self : EdwardsBasepointTableRadix32.«i686-tables») : Prop :=
  ∀ i < 32, ∀ j < 16, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (10 * i) • self.point)

/-- The bound on the limbs of the radix-`32` table that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».IsBounded
    (self : EdwardsBasepointTableRadix32.«i686-tables») : Prop :=
  self.LimbsLt 27

/-- The point the radix-`64` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix64.«x86_64-tables».point
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`64` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(12 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».IsTable
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  ∀ i < 32, ∀ j < 32, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (12 * i) • self.point)

/-- The bound on the limbs of the radix-`64` table that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The point the radix-`64` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix64.«i686-tables».point
    (self : EdwardsBasepointTableRadix64.«i686-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`64` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(12 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».IsTable
    (self : EdwardsBasepointTableRadix64.«i686-tables») : Prop :=
  ∀ i < 32, ∀ j < 32, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (12 * i) • self.point)

/-- The bound on the limbs of the radix-`64` table that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».IsBounded
    (self : EdwardsBasepointTableRadix64.«i686-tables») : Prop :=
  self.LimbsLt 27

/-- The point the radix-`128` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix128.«x86_64-tables».point
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`128` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(14 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».IsTable
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  ∀ i < 32, ∀ j < 64, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (14 * i) • self.point)

/-- The bound on the limbs of the radix-`128` table that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The point the radix-`128` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix128.«i686-tables».point
    (self : EdwardsBasepointTableRadix128.«i686-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`128` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(14 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».IsTable
    (self : EdwardsBasepointTableRadix128.«i686-tables») : Prop :=
  ∀ i < 32, ∀ j < 64, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (14 * i) • self.point)

/-- The bound on the limbs of the radix-`128` table that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».IsBounded
    (self : EdwardsBasepointTableRadix128.«i686-tables») : Prop :=
  self.LimbsLt 27

/-- The point the radix-`256` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix256.«x86_64-tables».point
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`256` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(16 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».IsTable
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  ∀ i < 32, ∀ j < 128, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (16 * i) • self.point)

/-- The bound on the limbs of the radix-`256` table that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The point the radix-`256` table is for: the point of entry `0` of row `0`. -/
@[expose] noncomputable def EdwardsBasepointTableRadix256.«i686-tables».point
    (self : EdwardsBasepointTableRadix256.«i686-tables») :
    curve25519.edwards.Point :=
  PointRepr.toPoint (self[0]!)[0]!

/-- The invariant of the radix-`256` table: entry `j` of row `i` is on the curve and is
`(j + 1) • 2^(16 i) • self.point`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».IsTable
    (self : EdwardsBasepointTableRadix256.«i686-tables») : Prop :=
  ∀ i < 32, ∀ j < 128, PointRepr.OnCurve (self[i]!)[j]! ∧
    PointRepr.toPoint (self[i]!)[j]! = (j + 1) • (2 ^ (16 * i) • self.point)

/-- The bound on the limbs of the radix-`256` table that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».IsBounded
    (self : EdwardsBasepointTableRadix256.«i686-tables») : Prop :=
  self.LimbsLt 27

end Curve25519Dalek.edwards
