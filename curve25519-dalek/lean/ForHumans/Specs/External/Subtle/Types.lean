module
public import Aeneas.Std.Scalar.Core
import Batteries.Tactic.Lint.Basic
import Mathlib.Tactic.Linter.Style
@[expose] public section
set_option linter.style.whitespace false
open Aeneas Aeneas.Std

/-! # Types of the `subtle` crate (subtle-2.6.1) — TRUSTED

Types only: this file is imported by `Curve25519Dalek/Types.lean`. They are what Aeneas
emits when it translates the type definitions of `subtle`. Functions and their specs are in
`ForHumans/Specs/External/Subtle/Contract.lean`. -/

/-- [subtle::Choice]
    Source: 'subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]

`pub struct Choice(u8);` Aeneas translates a single-field tuple struct to a reducible alias of
the field type (cf. `edwards.CompressedEdwardsY := Array Std.U8 32#usize`). The 0/1 invariant
is therefore not part of the type; see the module doc of
`ForHumans/Specs/External/Subtle/Contract.lean`. -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8

/-- [subtle::CtOption]
    Source: 'subtle-2.6.1/src/lib.rs', lines 647:0-647:22
    Name pattern: [subtle::CtOption]

`pub struct CtOption<T> { value: T, is_some: Choice }` -/
@[rust_type "subtle::CtOption"]
structure subtle.CtOption (T : Type) where
  /-- The wrapped value; meaningful only when `is_some` is `Choice(1)`. -/
  value : T
  /-- Whether the option holds a value: `Choice(1)` if so, `Choice(0)` if not. -/
  is_some : subtle.Choice

attribute [nolint defsWithUnderscore] subtle.CtOption.is_some
