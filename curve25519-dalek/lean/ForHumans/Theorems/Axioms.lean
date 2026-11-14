/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ForHumans.Theorems
import Lean

/-! # The axioms of the specs

Every theorem in `Specs` may use only Lean's three axioms and the contracts of the external crates
that curve25519-dalek calls:

* `propext`, `Classical.choice`, `Quot.sound`: Lean's axioms;
* `RustAx.subtle` (`ForHumans/Specs/External/Subtle/Contract.lean`): the `subtle` crate meets its
  contract;
* `RustAx.zeroize` (`ForHumans/Specs/External/Zeroize/Contract.lean`): the `zeroize` crate meets
  its contract;
* `RustAx.alloc` (`Curve25519Dalek/FunsExternal.lean`): `alloc` meets its contract.

The check below fails if one does not, or if a theorem uses `sorryAx`. -/

open Lean Elab Command

/-- Lean's axioms and the contracts of the external crates. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``RustAx.alloc, ``RustAx.subtle, ``RustAx.zeroize]

/-- The theorems of `Specs`. -/
def specTheorems (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n c =>
    if (`Theorems).isPrefixOf n && c matches .thmInfo _ && !n.isInternal then acc.push n else acc

/-- info: 372 spec theorems, all using only the allowed axioms -/
#guard_msgs in
run_cmd do
  let names := (specTheorems (← getEnv)).qsort Name.lt
  for n in names do
    let axioms ← liftCoreM (collectAxioms n)
    let bad := axioms.filter (· ∉ allowedAxioms)
    unless bad.isEmpty do
      throwError "{n} uses {bad.toList}"
  logInfo m!"{names.size} spec theorems, all using only the allowed axioms"
