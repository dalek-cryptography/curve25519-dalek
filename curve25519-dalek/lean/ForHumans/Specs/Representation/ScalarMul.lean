module
public import Proofs.Curve25519.Edwards.Basic
public import ForHumans.Specs.Representation.CurveModels
public section

/-! # The precomputations of `backend/serial/scalar_mul/precomputed_straus.rs` (audited)

`VartimePrecomputedStraus` holds one `NafLookupTable8` of affine Niels points per static point,
and `self.LimbsLt n` says that every limb of every entry is `< 2^n`. The backend enum
`backend.VartimePrecomputedStraus` (whose only variant is `Scalar`), and its aliases
`edwards.VartimeEdwardsPrecomputation` and `ristretto.VartimeRistrettoPrecomputation`, forward to
it; on the enum, `points` are the static points (the point of entry `0` of each table),
`IsValid`, the invariant of the Rust type (whose values come only from `new`), says that entry
`k` of each table is on the curve and is `(2 k + 1)` times that point, and `IsBounded` that every
limb is `< 2^54` (64-bit) or `< 2^27` (32-bit). -/

open Aeneas Aeneas.Std

-- BEGIN PER-CONFIG

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«64bit-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«64bit-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace Curve25519Dalek.backend

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«64bit-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«64bit-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The static points of the precomputation: the point of entry `0` of each NAF table, in
order. -/
@[expose] noncomputable def VartimePrecomputedStraus.«64bit-tables».points :
    VartimePrecomputedStraus.«64bit-tables» → List curve25519.edwards.Point
  | .Scalar pre => pre.static_lookup_tables.val.map fun t => PointRepr.toPoint t[0]!

/-- The invariant of the precomputation: entry `k` of table `n` is on the curve and is the odd
multiple `(2 k + 1) • P` of the point `P` of its entry `0`. -/
@[expose] def VartimePrecomputedStraus.«64bit-tables».IsValid :
    VartimePrecomputedStraus.«64bit-tables» → Prop
  | .Scalar pre => ∀ n < pre.static_lookup_tables.length, ∀ k < 64,
      PointRepr.OnCurve (pre.static_lookup_tables[n]!)[k]! ∧
        PointRepr.toPoint (pre.static_lookup_tables[n]!)[k]! =
          (2 * k + 1) • PointRepr.toPoint (pre.static_lookup_tables[n]!)[0]!

/-- The bound on the limbs of the precomputation that every public function assumes and
preserves: every limb of every entry is `< 2^54` (`< 2^27` on 32-bit). -/
@[expose] def VartimePrecomputedStraus.«64bit-tables».IsBounded
    (self : VartimePrecomputedStraus.«64bit-tables») : Prop :=
  self.LimbsLt 54  -- 32bit: self.LimbsLt 27

end Curve25519Dalek.backend

-- END PER-CONFIG
