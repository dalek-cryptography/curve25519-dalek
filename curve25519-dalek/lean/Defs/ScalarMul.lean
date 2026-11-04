/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Defs.Window
public section

/-! # The precomputations of `backend/serial/scalar_mul/precomputed_straus.rs` (audited)

`VartimePrecomputedStraus` holds one `NafLookupTable8` of affine Niels points per static point;
`Represents self ps` says that these tables are, in order, the NAF tables of the points `ps`,
and `self.LimbsLt n` that every limb of every entry is `< 2^n`. The
backend enum `backend.VartimePrecomputedStraus` (whose only variant is `Scalar`) and its alias
`edwards.VartimeEdwardsPrecomputation` forward to it. -/

open Aeneas Aeneas.Std

namespace Curve25519Dalek

namespace backend.serial.scalar_mul.precomputed_straus

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-tables».Represents
    (self : VartimePrecomputedStraus.«i686-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«x86_64-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

/-- Every limb of every entry of every table of `self` is `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».LimbsLt (n : ℕ)
    (self : VartimePrecomputedStraus.«i686-tables») : Prop :=
  ∀ t ∈ self.static_lookup_tables.val, window.NafLookupTable8.LimbsLt n t

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents
    (self : VartimePrecomputedStraus.«x86_64-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

/-- The tables of `self` are the NAF tables of the points `ps`, in order (same length). -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».Represents
    (self : VartimePrecomputedStraus.«i686-no-tables») (ps : List curve25519.edwards.Point) :
    Prop :=
  List.Forall₂ window.NafLookupTable8.Represents self.static_lookup_tables.val ps

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

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».Represents :
    VartimePrecomputedStraus.«x86_64-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».Represents :
    VartimePrecomputedStraus.«i686-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«x86_64-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«i686-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».Represents :
    VartimePrecomputedStraus.«x86_64-no-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The serial precomputation inside the backend enum represents `ps`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».Represents :
    VartimePrecomputedStraus.«i686-no-tables» → List curve25519.edwards.Point → Prop
  | .Scalar pre, ps => pre.Represents ps

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«x86_64-no-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«x86_64-no-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

/-- The limbs of the serial precomputation inside the backend enum are `< 2^n`. -/
@[expose] def VartimePrecomputedStraus.«i686-no-tables».LimbsLt (n : ℕ) :
    VartimePrecomputedStraus.«i686-no-tables» → Prop
  | .Scalar pre => pre.LimbsLt n

end backend

end Curve25519Dalek
