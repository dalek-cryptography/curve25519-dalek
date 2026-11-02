/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Window
public section

/-! # `edwards.rs`: points, the compressed form, the lenient decoder, the basepoint tables
(audited)

- `EdwardsPoint` implements the extended coordinates `(X : Y : Z : T)` of `curve25519.edwards`
  on radix-`2^51` limbs (x86_64) or radix-`2^25.5` limbs (i686): `toExtended` (hidden,
  `toExtended_def`), `OnCurve` (exposed), `toPoint` (hidden, `toPoint_def`), `LimbsLt n` (all
  limbs `< 2^n`, exposed; the x86_64 specs use `LimbsLt 52`, the bound forced by the mixed
  affine-Niels addition) and `ProjEq` (exposed), the projective equality that `ct_eq` computes.
- `AffinePoint` (`edwards/affine.rs`) is the affine point itself: `OnCurve` is the curve
  equation, `toPoint` the point (`0` off the curve), `LimbsLt n` as for `EdwardsPoint`.
- `CompressedEdwardsY` is 32 bytes; `asNat` is their little-endian value, RFC 8032's encoding
  `curve25519.encode` of a point.
- `decodeLenient` is dalek's `CompressedEdwardsY::decompress` on the value `n` of the bytes:
  `y := n % 2^255` reduced modulo `p` (a non-canonical `y ≥ p` is accepted), sign `n / 2^255`;
  `none` iff no point has this `y`; otherwise the point `(x, y)` whose `x` has the given sign,
  where `x = 0` is accepted with either sign (`-0 = 0`). It differs from the strict RFC 8032
  decoder `curve25519.decode` exactly on these two leniencies
  (`Proofs/Helpers/Edwards.lean`).
- The basepoint tables `EdwardsBasepointTable{,Radix32,Radix64,Radix128,Radix256}` (radix
  `2^w`, `w = 4, 5, 6, 7, 8`) hold `32` lookup tables of affine Niels points: `Represents t P`
  says that row `i` is the lookup table of `2^(2 w i) • P`, i.e. entry `j` of row `i`
  represents `(j + 1) • 2^(2 w i) • P` (`BasepointTable::create`).
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

/-- The little-endian value of the 32 bytes. -/
def CompressedEdwardsY.asNat (self : CompressedEdwardsY) : ℕ :=
  Aeneas.Std.Array.asNat 8 self

theorem CompressedEdwardsY.asNat_def (self : CompressedEdwardsY) :
    self.asNat = Aeneas.Std.Array.asNat 8 self := by
  unfold CompressedEdwardsY.asNat
  rfl

/-- Needed for `v[i]!` on vectors and arrays of compressed points; the default is never
observed for in-range indices. -/
instance CompressedEdwardsY.instInhabited : Inhabited CompressedEdwardsY :=
  inferInstanceAs (Inhabited (Array U8 32#usize))

/-! ### The lenient decoder -/

open scoped Classical in
/-- Dalek's `CompressedEdwardsY::decompress` on the value `n` of the bytes: `y := n % 2^255`
reduced modulo `p`, sign `s := n / 2^255`; `none` if no point has this `y`, otherwise the point
`(x, y)` with `x = 0` or `x` of sign `s`. Unlike RFC 8032's `curve25519.decode`, it accepts
`y ≥ p` (reduced) and `x = 0` with `s = 1`. -/
noncomputable def decodeLenient (n : ℕ) : Option curve25519.edwards.Point :=
  if h : ∃ x : ZMod p, curve25519.edwards.Equation x ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
      (x = 0 ∨ (x.IsNeg ↔ n / 2 ^ 255 = 1)) then
    some ⟨Classical.choose h, ((n % 2 ^ 255 : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
  else none

open scoped Classical in
theorem decodeLenient_def (n : ℕ) :
    decodeLenient n =
      if h : ∃ x : ZMod p, curve25519.edwards.Equation x ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
          (x = 0 ∨ (x.IsNeg ↔ n / 2 ^ 255 = 1)) then
        some ⟨Classical.choose h, ((n % 2 ^ 255 : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
      else none := by
  unfold decodeLenient
  rfl

/-! ### The basepoint tables (`tables` configurations only) -/

/-- Row `i` of the radix-`16` table is the lookup table of `2^(8 i) • P`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».Represents
    (self : EdwardsBasepointTable.«x86_64-tables») (P : curve25519.edwards.Point) : Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)

/-- Row `i` of the radix-`16` table is the lookup table of `2^(8 i) • P`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».Represents
    (self : EdwardsBasepointTable.«i686-tables») (P : curve25519.edwards.Point) : Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (8 * i) • P)

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTable.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTable.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTable.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTable.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Row `i` of the radix-`32` table is the lookup table of `2^(10 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)

/-- Row `i` of the radix-`32` table is the lookup table of `2^(10 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix32.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (10 * i) • P)

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix32.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix32.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix32.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix32.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Row `i` of the radix-`64` table is the lookup table of `2^(12 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)

/-- Row `i` of the radix-`64` table is the lookup table of `2^(12 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix64.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (12 * i) • P)

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix64.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix64.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix64.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix64.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Row `i` of the radix-`128` table is the lookup table of `2^(14 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)

/-- Row `i` of the radix-`128` table is the lookup table of `2^(14 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix128.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (14 * i) • P)

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix128.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix128.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix128.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix128.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Row `i` of the radix-`256` table is the lookup table of `2^(16 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».Represents
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)

/-- Row `i` of the radix-`256` table is the lookup table of `2^(16 i) • P`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».Represents
    (self : EdwardsBasepointTableRadix256.«i686-tables») (P : curve25519.edwards.Point) :
    Prop :=
  ∀ i < 32, (self[i]!).Represents (2 ^ (16 * i) • P)

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix256.«x86_64-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix256.«x86_64-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

/-- Every limb of every entry of every row is `< 2^n`. -/
@[expose] def EdwardsBasepointTableRadix256.«i686-tables».LimbsLt (n : ℕ)
    (self : EdwardsBasepointTableRadix256.«i686-tables») : Prop :=
  ∀ i < 32, (self[i]!).LimbsLt n

end Curve25519Dalek.edwards
