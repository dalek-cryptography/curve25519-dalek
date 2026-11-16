/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Curve25519.Edwards.Basic
public import ForHumans.Specs.Representation.CurveModels
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

`RistrettoPoint` is `EdwardsPoint`. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek.edwards

/-- Needed for `v[i]!` on vectors and arrays of compressed points; the default is never
observed for in-range indices. -/
instance CompressedEdwardsY.instInhabited : Inhabited CompressedEdwardsY :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

end Curve25519Dalek.edwards

-- BEGIN PER-CONFIG

namespace Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»

/-- The extended coordinates `(X : Y : Z : T)` as field elements. -/
noncomputable def toExtended (self : EdwardsPoint.«x86_64-tables») :
    curve25519.edwards.Extended :=
  ⟨self.X.toField, self.Y.toField, self.Z.toField, self.T.toField⟩

/-- `self` represents a point: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)` is on the curve. -/
@[expose] def OnCurve (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.toExtended.OnCurve

/-- The point represented by `self` (`0` if `¬ self.OnCurve`). -/
noncomputable def toPoint (self : EdwardsPoint.«x86_64-tables») : curve25519.edwards.Point :=
  self.toExtended.toPoint

/-- Every limb of an `EdwardsPoint` is `< 2^n`. -/
@[expose] def LimbsLt (n : ℕ) (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.X.LimbsLt n ∧ self.Y.LimbsLt n ∧ self.Z.LimbsLt n ∧ self.T.LimbsLt n

/-- The bound on the limbs of an `EdwardsPoint` that every public function assumes and preserves:
every limb is `< 2^52` (`< 2^26` on i686). -/
@[expose] def IsBounded (self : EdwardsPoint.«x86_64-tables») : Prop :=
  self.LimbsLt 52  -- i686: self.LimbsLt 26

/-- Needed for `a[i]!` on arrays of points; the default is never observed for in-range
indices. -/
instance instInhabited : Inhabited (EdwardsPoint.«x86_64-tables») :=
  ⟨⟨default, default, default, default⟩⟩

end Curve25519Dalek.edwards.EdwardsPoint.«x86_64-tables»

-- BEGIN TABLES-ONLY

namespace Curve25519Dalek.edwards

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

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The bound on the limbs of the radix-`16` table that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on i686). -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  self.LimbsLt 54  -- i686: self.LimbsLt 27

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

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The bound on the limbs of the radix-`32` table that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on i686). -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  self.LimbsLt 54  -- i686: self.LimbsLt 27

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

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The bound on the limbs of the radix-`64` table that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on i686). -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  self.LimbsLt 54  -- i686: self.LimbsLt 27

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

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The bound on the limbs of the radix-`128` table that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on i686). -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  self.LimbsLt 54  -- i686: self.LimbsLt 27

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

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- The bound on the limbs of the radix-`256` table that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on i686). -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».IsBounded
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  self.LimbsLt 54  -- i686: self.LimbsLt 27

end Curve25519Dalek.edwards

-- END TABLES-ONLY

-- END PER-CONFIG
