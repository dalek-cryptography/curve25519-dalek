module
public import ForHumans.Theorems.Constants
public import ForHumans.Theorems.Constants.I686NoTables
public import ForHumans.Theorems.Constants.I686Tables
public import ForHumans.Theorems.Constants.X86_64NoTables
public import ForHumans.Theorems.Edwards
public import ForHumans.Theorems.Edwards.I686NoTables
public import ForHumans.Theorems.Edwards.I686Tables
public import ForHumans.Theorems.Edwards.X86_64NoTables
public import ForHumans.Theorems.Montgomery
public import ForHumans.Theorems.Montgomery.I686NoTables
public import ForHumans.Theorems.Montgomery.I686Tables
public import ForHumans.Theorems.Montgomery.X86_64NoTables
public import ForHumans.Theorems.Ristretto
public import ForHumans.Theorems.Ristretto.I686NoTables
public import ForHumans.Theorems.Ristretto.I686Tables
public import ForHumans.Theorems.Ristretto.X86_64NoTables
public import ForHumans.Theorems.Scalar
public import ForHumans.Theorems.Traits

/-! # The theorems

One file per Rust file with items in the crate's public API, each public item's statement as a
theorem. Each file's copies for the other three configurations are generated in the
subdirectory of the same name. `Axioms.lean` checks the axioms, `Definitions.lean` the
definitions the statements use, `Coverage.lean` that every producer of a value with invariants
has a theorem. -/
