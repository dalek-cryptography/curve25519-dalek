import ForHumans
import Lean

open Lean Meta Elab Command

namespace Coverage

/-- The four configurations of the translation. -/
def configs : List String := ["64bit-tables", "32bit-tables", "64bit-notables", "32bit-notables"]

/-- Returns a list of types along with the invariants that must appear in the postcondition of every
function returning that type. `c` is the current configuration of word size and precomputed-tables
feature. -/
def watched (c : String) : List (Name × List Name) :=
  let cfg (s : String) : Name := .str (("Curve25519Dalek." ++ s).toName) c
  let inv (s : String) (ps : List String) := ps.map (cfg s).str
  let point := inv "edwards.EdwardsPoint" ["OnCurve", "IsBounded"]
  let pre := inv "backend.VartimePrecomputedStraus" ["IsValid", "IsBounded"]
  let table (s : String) := inv s ["IsTable", "IsBounded"]
  [(cfg "edwards.EdwardsPoint", point), (cfg "ristretto.RistrettoPoint", point),
   (cfg "backend.VartimePrecomputedStraus", pre),
   (cfg "edwards.VartimeEdwardsPrecomputation", pre),
   (cfg "ristretto.VartimeRistrettoPrecomputation", pre),
   (cfg "ristretto.RistrettoBasepointTable", table "edwards.EdwardsBasepointTable")] ++
  (["", "Radix32", "Radix64", "Radix128", "Radix256"].map fun r =>
    let t := "edwards.EdwardsBasepointTable" ++ r
    (cfg t, table t))

/-- All the watched types, in all configurations, and `Scalar`. -/
def allWatched : List (Name × List Name) :=
  configs.flatMap watched ++
    [(`Curve25519Dalek.scalar.Scalar, [`Curve25519Dalek.scalar.Scalar.IsCanonical])]

/-- Rust source files (prefixes) whose items are not callable from outside the crate. -/
def exemptFiles : List (String × String) := [
  ("curve25519-dalek/src/backend",
    "`pub(crate) mod backend` (lib.rs; `pub` only when building the documentation)"),
  ("curve25519-dalek/src/edwards/affine.rs",
    "`mod affine` is private; `AffinePoint` is returned only by `pub(crate) fn to_affine`")]

/-- Files under an exempt prefix whose public items are public: `constants.rs` re-exports them. -/
def unexemptFiles : List String :=
  ["curve25519-dalek/src/backend/serial/u64/constants.rs",
   "curve25519-dalek/src/backend/serial/u32/constants.rs"]

/-- Functions not callable from outside the crate, by their name for `64bit-tables` (the other
configurations are matched by renaming). -/
def exemptNames : List (String × String) := [
  ("edwards.«EdwardsPoint64bit-tables».double", "`pub(crate) fn double`"),
  ("edwards.«EdwardsPoint64bit-tables».mul_by_pow_2", "`pub(crate) fn mul_by_pow_2`"),
  ("edwards.decompress.step_2.«64bit-tables»", "private `mod decompress`"),
  ("ristretto.decompress.step_2.«64bit-tables»", "private `mod decompress`"),
  ("ristretto.«RistrettoPoint64bit-tables».coset4", "private `fn coset4`"),
  ("ristretto.elligator.«RistrettoPoint64bit-tables».elligator_ristretto_flavor",
    "`pub(crate) fn elligator_ristretto_flavor`"),
  ("P.Insts.«CoreOpsFunctionFnOnceTupleEdwardsPoint64bit-tablesRistrettoPoint64bit-tables»\
      .call_once",
    "the constructor `RistrettoPoint(·)` as a function; its field is `pub(crate)`"),
  ("ristretto.«VartimeMultiscalarMulRistrettoPoint64bit-tablesRistrettoPoint64bit-tables»\
      .optional_multiscalar_mul.closure.Insts\
      .«CoreOpsFunctionFnOnceTupleRistrettoPoint64bit-tablesEdwardsPoint64bit-tables».call_once",
    "a closure inside `optional_multiscalar_mul`"),
  ("ristretto.«VartimePrecomputedMultiscalarMul\
      VartimeRistrettoPrecomputation64bit-tablesRistrettoPoint64bit-tables»\
      .optional_mixed_multiscalar_mul.closure.Insts\
      .«CoreOpsFunctionFnOnceTupleRistrettoPoint64bit-tablesEdwardsPoint64bit-tables».call_once",
    "a closure inside `optional_mixed_multiscalar_mul`"),
  ("scalar.Scalar.reduce", "private `fn reduce`"),
  ("scalar.Scalar.invert_batch_internal.«64bit-tables»", "private `fn invert_batch_internal`"),
  ("scalar.Scalar29.pack", "private `fn pack` of the internal `UnpackedScalar`"),
  ("scalar.Scalar52.pack", "private `fn pack` of the internal `UnpackedScalar`"),
  ("backend.serial.u64.constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN", "private `static`"),
  ("backend.serial.u32.constants.ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN", "private `static`")]

/-- `n` with every configuration renamed to `64bit-tables`. -/
def normalize (n : Name) : String :=
  let s := (n.toString.drop "Curve25519Dalek.".length).toString
  configs.foldl (fun s c => s.replace c "64bit-tables") s

/-- The Rust source file of a translated function, from the docstring Aeneas writes. -/
def sourceFile (env : Environment) (n : Name) : IO (Option String) := do
  let some doc ← findDocString? env n | return none
  let some rest := (doc.splitOn "Source: '")[1]? | return none
  return (rest.splitOn "'")[0]?

/-- The constants a theorem's statement mentions, looking through the definitions of
`ForHumans/Theorems/` (the abbreviations naming the operator variants). -/
def statementConstants (env : Environment) (type : Expr) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := type.getUsedConstants
  while h : todo.size > 0 do
    let k := todo.back
    todo := todo.pop
    if seen.contains k then continue
    seen := seen.insert k
    if (`Theorems).isPrefixOf k then
      if let some (.defnInfo d) := env.find? k then todo := todo ++ d.value.getUsedConstants
  return seen

/-- The statement concludes that a result is one of the arguments: `fun r => r = x`. -/
def returnsArgument (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs body =>
    return (body.find? fun e => match e with
      | .lam _ _ b _ => b.isAppOfArity ``Eq 3 && b.appFn!.appArg! == .bvar 0 &&
          xs.contains b.appArg!
      | _ => false).isSome

/-- The translation of `f` is `fun x => ok x`. -/
def returnsItsArgument (f : Expr) : MetaM Bool :=
  lambdaTelescope f fun xs b =>
    return xs.size == 1 && b.isAppOfArity ``Aeneas.Std.Result.ok 2 && b.appArg! == xs[0]!

/-- The exemption of `n`, if any: the exemption's key and its reason. -/
def exemption (env : Environment) (n : Name) : IO (Option (String × String)) := do
  if let some f ← sourceFile env n then
    if let some e := exemptFiles.find? (f.startsWith ·.1) then
      unless unexemptFiles.contains f do return some e
  return exemptNames.find? (·.1 == normalize n)

/-- The uncovered functions, each with the reason it is exempt (if it is), and the exemptions
that match nothing. -/
def check : MetaM (Array (Name × Option String) × List String) := do
  let env ← getEnv
  let some funs := env.getModuleIdx? `Curve25519Dalek.Funs | throwError "no translation"
  let inFuns (n : Name) := env.getModuleIdxFor? n == some funs
  -- the theorems of `ForHumans/Theorems/`: what each mentions, and whether it returns an argument
  let mut about : Std.HashMap Name (Array (NameSet × Bool)) := {}
  for (n, c) in env.constants.toList do
    unless (`Theorems).isPrefixOf n && c matches .thmInfo _ do continue
    let used := statementConstants env c.type
    let concl ← forallTelescope c.type fun _ b => return statementConstants env b
    let arg ← returnsArgument c.type
    for u in used do
      if inFuns u then about := about.insert u ((about.getD u #[]).push (concl, arg))
  -- the dispatchers of each per-configuration copy
  let mut dispatchers : Std.HashMap Name (Array Name) := {}
  for (n, c) in env.constants.toList do
    unless inFuns n do continue
    let some v := c.value? | continue
    let used := v.getUsedConstants
    unless used.contains ``Aeneas.Std.get_target do continue
    for u in used do
      if inFuns u then dispatchers := dispatchers.insert u ((dispatchers.getD u #[]).push n)
  let mut used : Std.HashSet String := {}
  let mut out := #[]
  -- dispatchers before their copies, so that a copy can use its dispatcher's verdict
  let producers ← env.constants.toList.filterMapM fun (n, c) => do
    unless inFuns n && c matches .defnInfo _ && !n.isInternal do return none
    if (n.toString.splitOn "_loop").length > 1 then return none
    let res ← forallTelescope c.type fun _ r => pure r
    unless res.isAppOf ``Aeneas.Std.Result do return none
    let inRes := res.getUsedConstants
    let reqs := allWatched.filter (inRes.contains ·.1)
    if reqs.isEmpty then return none
    if ← returnsItsArgument c.value! then return none
    return some (n, reqs.flatMap (·.2))
  let mut verdict : Std.HashMap Name Bool := {}
  let isDispatcher (n : Name) := dispatchers.valuesArray.any (·.contains n)
  for (n, need) in producers.toArray.qsort (fun a b => isDispatcher a.1 && !isDispatcher b.1) do
    let covered := (about.getD n #[]).any fun (s, arg) => arg || need.all s.contains
    let e ← exemption env n
    if let some (k, _) := e then used := used.insert k
    let exempt? := e.map (·.2)
    let viaDispatcher := (dispatchers.getD n #[]).any (verdict.getD · false)
    verdict := verdict.insert n (covered || exempt?.isSome || viaDispatcher)
    unless covered || viaDispatcher do out := out.push (n, exempt?)
  let stale := (exemptFiles.map (·.1) ++ exemptNames.map (·.1)).filter (!used.contains ·)
  return (out, stale)

end Coverage

/-- info: every producer has a theorem or a listed exemption -/
#guard_msgs in
run_cmd do
  let (out, stale) ← liftTermElabM Coverage.check
  let missing := out.filter (·.2.isNone)
  unless missing.isEmpty do
    let lines := missing.qsort (·.1.lt ·.1) |>.toList.map (m!"{·.1}")
    throwError "no theorem about these functions, which return values with invariants:\n\
      {MessageData.joinSep lines "\n"}"
  unless stale.isEmpty do
    throwError "these exemptions match no uncovered function: {stale}"
  logInfo m!"every producer has a theorem or a listed exemption"
