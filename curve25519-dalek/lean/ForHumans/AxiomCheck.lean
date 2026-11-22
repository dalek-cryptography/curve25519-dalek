/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ForHumans
import Lean

open Lean Elab Command

/-- Lean's axioms and the contracts of the external crates. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``RustAx.alloc, ``RustAx.subtle, ``RustAx.zeroize]

/-- The theorems of `ForHumans/Theorems/` and `ForHumans/TestVectors.lean`. -/
def specTheorems (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n c =>
    let ours := (`Theorems).isPrefixOf n || (`TestVectors).isPrefixOf n
    if ours && c matches .thmInfo _ && !n.isInternal then acc.push n else acc

/-- info: 454 theorems, all using only the allowed axioms -/
#guard_msgs in
run_cmd do
  let names := (specTheorems (← getEnv)).qsort Name.lt
  for n in names do
    let axioms ← liftCoreM (collectAxioms n)
    let bad := axioms.filter (· ∉ allowedAxioms)
    unless bad.isEmpty do
      throwError "{n} uses {bad.toList}"
  logInfo m!"{names.size} theorems, all using only the allowed axioms"
