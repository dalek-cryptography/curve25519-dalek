/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Window
public section

/-! # The precomputations of `backend/serial/scalar_mul/precomputed_straus.rs` (audited)

`VartimePrecomputedStraus` holds one `NafLookupTable8` of affine Niels points per static point,
and `self.LimbsLt n` says that every limb of every entry is `< 2^n`. The backend enum
`backend.VartimePrecomputedStraus` (whose only variant is `Scalar`), and its aliases
`edwards.VartimeEdwardsPrecomputation` and `ristretto.VartimeRistrettoPrecomputation`, forward to
it; on the enum, `points` are the static points (the point of entry `0` of each table),
`IsValid`, the invariant of the Rust type (whose values come only from `new`), says that entry
`k` of each table is on the curve and is `(2 k + 1)` times that point, and `IsBounded` that every
limb is `< 2^54` (x86_64) or `< 2^27` (i686). -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace backend.serial.scalar_mul.precomputed_straus

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«x86_64-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«i686-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«x86_64-no-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«i686-no-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

end backend.serial.scalar_mul.precomputed_straus

namespace backend

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«x86_64-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«i686-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«x86_64-no-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«i686-no-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The static points of the precomputation: the point of entry `0` of each NAF table, in
order. -/
@[expose] noncomputable def VartimePrecomputedStraus.«x86_64-tables».points :
    VartimePrecomputedStraus.«x86_64-tables» → List curve25519.edwards.Point
  | .Scalar pre => pre.static_lookup_tables.val.map fun t => PointRepr.toPoint t[0]!

/-- The invariant of the precomputation: entry `k` of table `n` is on the curve and is the odd
multiple `(2 k + 1) • P` of the point `P` of its entry `0`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».IsValid :
    VartimePrecomputedStraus.«x86_64-tables» → Prop
  | .Scalar pre => ∀ n < pre.static_lookup_tables.length, ∀ k < 64,
      PointRepr.OnCurve (pre.static_lookup_tables[n]!)[k]! ∧
        PointRepr.toPoint (pre.static_lookup_tables[n]!)[k]! =
          (2 * k + 1) • PointRepr.toPoint (pre.static_lookup_tables[n]!)[0]!

/-- The bound on the limbs of the precomputation that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».IsBounded
    (self : VartimePrecomputedStraus.«x86_64-tables») : Prop :=
  self.LimbsLt 54

/-- The static points of the precomputation: the point of entry `0` of each NAF table, in
order. -/
@[expose] noncomputable def VartimePrecomputedStraus.«i686-tables».points :
    VartimePrecomputedStraus.«i686-tables» → List curve25519.edwards.Point
  | .Scalar pre => pre.static_lookup_tables.val.map fun t => PointRepr.toPoint t[0]!

/-- The invariant of the precomputation: entry `k` of table `n` is on the curve and is the odd
multiple `(2 k + 1) • P` of the point `P` of its entry `0`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».IsValid :
    VartimePrecomputedStraus.«i686-tables» → Prop
  | .Scalar pre => ∀ n < pre.static_lookup_tables.length, ∀ k < 64,
      PointRepr.OnCurve (pre.static_lookup_tables[n]!)[k]! ∧
        PointRepr.toPoint (pre.static_lookup_tables[n]!)[k]! =
          (2 * k + 1) • PointRepr.toPoint (pre.static_lookup_tables[n]!)[0]!

/-- The bound on the limbs of the precomputation that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».IsBounded
    (self : VartimePrecomputedStraus.«i686-tables») : Prop :=
  self.LimbsLt 27

/-- The static points of the precomputation: the point of entry `0` of each NAF table, in
order. -/
@[expose] noncomputable def VartimePrecomputedStraus.«x86_64-no-tables».points :
    VartimePrecomputedStraus.«x86_64-no-tables» → List curve25519.edwards.Point
  | .Scalar pre => pre.static_lookup_tables.val.map fun t => PointRepr.toPoint t[0]!

/-- The invariant of the precomputation: entry `k` of table `n` is on the curve and is the odd
multiple `(2 k + 1) • P` of the point `P` of its entry `0`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».IsValid :
    VartimePrecomputedStraus.«x86_64-no-tables» → Prop
  | .Scalar pre => ∀ n < pre.static_lookup_tables.length, ∀ k < 64,
      PointRepr.OnCurve (pre.static_lookup_tables[n]!)[k]! ∧
        PointRepr.toPoint (pre.static_lookup_tables[n]!)[k]! =
          (2 * k + 1) • PointRepr.toPoint (pre.static_lookup_tables[n]!)[0]!

/-- The bound on the limbs of the precomputation that every public function assumes and
preserves: every limb of every entry is `< 2^54`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».IsBounded
    (self : VartimePrecomputedStraus.«x86_64-no-tables») : Prop :=
  self.LimbsLt 54

/-- The static points of the precomputation: the point of entry `0` of each NAF table, in
order. -/
@[expose] noncomputable def VartimePrecomputedStraus.«i686-no-tables».points :
    VartimePrecomputedStraus.«i686-no-tables» → List curve25519.edwards.Point
  | .Scalar pre => pre.static_lookup_tables.val.map fun t => PointRepr.toPoint t[0]!

/-- The invariant of the precomputation: entry `k` of table `n` is on the curve and is the odd
multiple `(2 k + 1) • P` of the point `P` of its entry `0`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».IsValid :
    VartimePrecomputedStraus.«i686-no-tables» → Prop
  | .Scalar pre => ∀ n < pre.static_lookup_tables.length, ∀ k < 64,
      PointRepr.OnCurve (pre.static_lookup_tables[n]!)[k]! ∧
        PointRepr.toPoint (pre.static_lookup_tables[n]!)[k]! =
          (2 * k + 1) • PointRepr.toPoint (pre.static_lookup_tables[n]!)[0]!

/-- The bound on the limbs of the precomputation that every public function assumes and
preserves: every limb of every entry is `< 2^27`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».IsBounded
    (self : VartimePrecomputedStraus.«i686-no-tables») : Prop :=
  self.LimbsLt 27

end backend

end Curve25519Dalek
