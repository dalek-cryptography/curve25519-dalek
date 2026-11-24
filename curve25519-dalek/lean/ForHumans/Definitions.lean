import ForHumans
import Lean

open Lean Meta Elab Command

/-- The theorems of `ForHumans/Theorems/` and `ForHumans/TestVectors.lean`. -/
def statementRoots (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n c =>
    let ours := (`Theorems).isPrefixOf n || (`TestVectors).isPrefixOf n
    if ours && c matches .thmInfo _ && !n.isInternal then acc.push n else acc

/-- The definitions of `Proofs/` that the statements depend on, each with a constant that uses
it. -/
def proofsDefinitionsUsed : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let moduleRoot (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!.getRoot
  let mut todo : Array (Name × Name) := #[]
  for r in statementRoots env do
    if let some c := env.find? r then
      todo := todo ++ c.type.getUsedConstants.map (·, r)
  let mut seen : NameSet := {}
  let mut found := #[]
  while h : todo.size > 0 do
    let (n, user) := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    -- Libraries are trusted; only this package's modules are followed.
    let root := moduleRoot n
    unless root == some `ForHumans || root == some `Curve25519Dalek || root == some `Proofs do
      continue
    let some c := env.find? n | continue
    if c matches .thmInfo _ then continue
    if ← isProp c.type then continue
    if root == some `Proofs && !n.isInternal then found := found.push (n, user)
    todo := todo ++ c.type.getUsedConstants.map (·, n)
    if let some v := c.value? (allowOpaque := true) then
      todo := todo ++ v.getUsedConstants.map (·, n)
  return found

/-- info: the statements use no definition of `Proofs/` -/
#guard_msgs in
run_cmd do
  let found ← liftTermElabM proofsDefinitionsUsed
  unless found.isEmpty do
    let lines := found.qsort (·.1.lt ·.1) |>.toList.map fun (n, u) => m!"{n} (used by {u})"
    throwError "the statements use definitions of `Proofs/`:\n{MessageData.joinSep lines "\n"}"
  logInfo m!"the statements use no definition of `Proofs/`"
