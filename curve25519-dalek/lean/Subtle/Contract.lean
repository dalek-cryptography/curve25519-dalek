/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Alessandro D'Angelo, Hoang Le Truong,
  Markus Ferdinand Dablander
-/
module
public import Curve25519Dalek.Types
@[expose] public section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-! # Functions of the `subtle` crate (subtle-2.6.1)

This file and `Subtle/Types.lean` are the trusted base for `subtle`.

* Signatures: Each external function that Aeneas expects is an `opaque` constant with the
  required name, type and `@[rust_fun]` attribute.
* Contracts: Each function used by the proofs has one predicate `….Contract : Prop` that restates
  the Rust documentation. Specs that call trait methods of a generic `T` assume the behaviour of
  those methods as a hypothesis.
* Axiom: The single axiom `RustAx.subtle` states that all the contracts hold.

**`Choice` validity.** `Choice` is a plain `u8`. The crate maintains the invariant that it is `0` or
`1` (`subtle.Choice.IsValid` below). Every contract with a `Choice` argument `c` assumes
`c.IsValid`, and every contract returning a `Choice` states that the result is valid.
-/

/-! ## `Choice` -/

/-- A `Choice` is valid when its byte is `0` or `1`. -/
abbrev subtle.Choice.IsValid (c : subtle.Choice) : Prop := c = 0#u8 ∨ c = 1#u8

/-- [subtle::{subtle::Choice}::unwrap_u8]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 133:4-133:33
    Name pattern: [subtle::{subtle::Choice}::unwrap_u8] -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
opaque subtle.Choice.unwrap_u8 : subtle.Choice → Result Std.U8

/-- "Unwrap the `Choice` wrapper to reveal the underlying `u8`." (lib.rs:123) -/
@[nolint defsWithUnderscore]
def subtle.Choice.unwrap_u8.Contract : Prop :=
  ∀ (c : subtle.Choice) (hc : c.IsValid),
    subtle.Choice.unwrap_u8 c ⦃ r => r = c ⦄

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from] -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
opaque Bool.Insts.CoreConvertFromChoice.from : subtle.Choice → Result Bool

/-- "Convert the `Choice` wrapper into a `bool`, depending on whether the underlying `u8` was a `0`
or a `1`." (lib.rs:139-140). Body: `debug_assert!((source.0 == 0u8) | (source.0 == 1u8));
source.0 != 0`. -/
def Bool.Insts.CoreConvertFromChoice.from.Contract : Prop :=
  ∀ (c : subtle.Choice)
    (hc : c.IsValid),
    Bool.Insts.CoreConvertFromChoice.from c ⦃ b => b = (c != 0#u8) ⦄

/-- [subtle::{impl core::ops::bit::BitAnd<subtle::Choice, subtle::Choice>
    for subtle::Choice}::bitand]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 162:4-162:42
    Name pattern:
    [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand] -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
opaque subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand :
  subtle.Choice → subtle.Choice → Result subtle.Choice

/-- "The `Choice` struct implements operators for AND, OR, XOR, and NOT, to allow combining `Choice`
values. These operations do not short-circuit." (lib.rs:114-115). Body:
`(self.0 & rhs.0).into()`; the `.into()` asserts validity (debug semantics). -/
def subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand.Contract : Prop :=
  ∀ (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid),
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃ c =>
      c.IsValid ∧ c = a &&& b ⦄

/-- [subtle::{impl core::ops::bit::BitOr<subtle::Choice, subtle::Choice>
    for subtle::Choice}::bitor]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 177:4-177:41
    Name pattern:
    [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor] -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
opaque subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor :
  subtle.Choice → subtle.Choice → Result subtle.Choice

/-- "The `Choice` struct implements operators for AND, OR, XOR, and NOT, to allow combining `Choice`
values. These operations do not short-circuit." (lib.rs:114-115). Body:
`(self.0 | rhs.0).into()`; the `.into()` asserts validity (debug semantics). -/
def subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor.Contract : Prop :=
  ∀ (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid),
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b ⦃ c =>
      c.IsValid ∧ c = a ||| b ⦄

/-- [subtle::{impl core::ops::bit::Not<subtle::Choice> for subtle::Choice}::not]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 207:4-207:26
    Name pattern: [subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not] -/
@[rust_fun
  "subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not"]
opaque subtle.Choice.Insts.CoreOpsBitNotChoice.not : subtle.Choice → Result subtle.Choice

/-- "The `Choice` struct implements operators for AND, OR, XOR, and NOT, to allow combining `Choice`
values." (lib.rs:114-115). Body: `(1u8 & (!self.0)).into()`; `1 & !x` is always 0 or 1, so the
`.into()` assertion always holds. -/
def subtle.Choice.Insts.CoreOpsBitNotChoice.not.Contract : Prop :=
  ∀ (c : subtle.Choice) (hc : c.IsValid),
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c ⦃ r => r.IsValid ∧ r = 1#u8 &&& ~~~c ⦄

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 238:4-238:32
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from] -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
opaque subtle.Choice.Insts.CoreConvertFromU8.from : Std.U8 → Result subtle.Choice

/-- "It is a wrapper around a `u8`, which should have the value either `1` (true) or `0` (false)."
(lib.rs:104-105). Body: `debug_assert!((input == 0u8) | (input == 1u8));
Choice(black_box(input))`. -/
def subtle.Choice.Insts.CoreConvertFromU8.from.Contract : Prop :=
  ∀ (input : Std.U8)
    (h : input = 0#u8 ∨ input = 1#u8),
    subtle.Choice.Insts.CoreConvertFromU8.from input ⦃ c => c.IsValid ∧ c = input ⦄

/-! ## `ConstantTimeEq` -/

/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 313:4-313:41
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
opaque Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) :
  Slice T → Slice T → Result subtle.Choice

/-- "Check whether two slices of `ConstantTimeEq` types are equal. [...] This function
short-circuits if the lengths of the input slices are different." (lib.rs:290-295).
The trait contract: "`Choice(1u8)` if `self == other`; `Choice(0u8)` if `self != other`"
(lib.rs:269-270). The body ANDs the element `ct_eq`s, so this spec assumes that contract
for the element instance. -/
@[nolint defsWithUnderscore]
def Slice.Insts.SubtleConstantTimeEq.ct_eq.Contract : Prop :=
  ∀ {T : Type}
    (inst : subtle.ConstantTimeEq T)
    (hinst : ∀ x y, inst.ct_eq x y ⦃ c => (x = y → c = 1#u8) ∧ (x ≠ y → c = 0#u8) ⦄)
    (a b : Slice T),
    Slice.Insts.SubtleConstantTimeEq.ct_eq inst a b ⦃ c =>
      c.IsValid ∧ (a = b → c = 1#u8) ∧ (a ≠ b → c = 0#u8) ⦄

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
opaque U8.Insts.SubtleConstantTimeEq.ct_eq : Std.U8 → Std.U8 → Result subtle.Choice

/-- "Determine if two items are equal. [...] Returns `Choice(1u8)` if `self == other`;
`Choice(0u8)` if `self != other`." (lib.rs:263-270) -/
@[nolint defsWithUnderscore]
def U8.Insts.SubtleConstantTimeEq.ct_eq.Contract : Prop :=
  ∀ (a b : Std.U8),
    U8.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄

/-- [subtle::{impl subtle::ConstantTimeEq for u16}::ct_eq]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u16>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u16>}::ct_eq"]
opaque U16.Insts.SubtleConstantTimeEq.ct_eq : Std.U16 → Std.U16 → Result subtle.Choice

/-- "Determine if two items are equal. [...] Returns `Choice(1u8)` if `self == other`;
`Choice(0u8)` if `self != other`." (lib.rs:263-270) -/
@[nolint defsWithUnderscore]
def U16.Insts.SubtleConstantTimeEq.ct_eq.Contract : Prop :=
  ∀ (a b : Std.U16),
    U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄

/-! ## `ConditionallySelectable`: provided methods (faithful bodies) -/

/-- [subtle::ConditionallySelectable::conditional_assign]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 442:4-442:66
    Name pattern: [subtle::ConditionallySelectable::conditional_assign]

Verbatim translation of `*self = Self::conditional_select(self, other, choice);`. -/
@[nolint defsWithUnderscore, trait_default,
  rust_fun "subtle::ConditionallySelectable::conditional_assign"]
def subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self) :
  Self → Self → subtle.Choice → Result Self :=
  fun self other choice => ConditionallySelectableInst.conditional_select self other choice

/-- [subtle::ConditionallySelectable::conditional_swap]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 469:4-469:67
    Name pattern: [subtle::ConditionallySelectable::conditional_swap]

Verbatim translation of
`let t: Self = *a; a.conditional_assign(&b, choice); b.conditional_assign(&t, choice);`. -/
@[nolint defsWithUnderscore, trait_default,
  rust_fun "subtle::ConditionallySelectable::conditional_swap"]
def subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self) :
  Self → Self → subtle.Choice → Result (Self × Self) :=
  fun a b choice => do
    let t := a
    let a1 ← ConditionallySelectableInst.conditional_assign a b choice
    let b1 ← ConditionallySelectableInst.conditional_assign b t choice
    ok (a1, b1)

/-! ## `ConditionallySelectable` for `u8`, `u32`, `u64` -/

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_select]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_select] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_select"]
opaque U8.Insts.SubtleConditionallySelectable.conditional_select :
  Std.U8 → Std.U8 → subtle.Choice → Result Std.U8

/-- "Select `a` or `b` according to `choice`. Returns `a` if `choice == Choice(0)`; `b` if
`choice == Choice(1)`." (lib.rs:394-399). `-(choice as i8)` overflows for `choice = 128`, so
the spec requires a valid choice. -/
@[nolint defsWithUnderscore]
def U8.Insts.SubtleConditionallySelectable.conditional_select.Contract : Prop :=
  ∀ (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid),
    U8.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_assign]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign"]
opaque U8.Insts.SubtleConditionallySelectable.conditional_assign :
  Std.U8 → Std.U8 → subtle.Choice → Result Std.U8

/-- "Conditionally assign `other` to `self`, according to `choice`." (lib.rs:422).
`-(choice as i8)` overflows for `choice = 128`, so the spec requires a valid choice. -/
@[nolint defsWithUnderscore]
def U8.Insts.SubtleConditionallySelectable.conditional_assign.Contract : Prop :=
  ∀ (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid),
    U8.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u8}::conditional_swap]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap"]
opaque U8.Insts.SubtleConditionallySelectable.conditional_swap :
  Std.U8 → Std.U8 → subtle.Choice → Result (Std.U8 × Std.U8)

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_select]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_select] -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u32>}::conditional_select"]
opaque U32.Insts.SubtleConditionallySelectable.conditional_select :
  Std.U32 → Std.U32 → subtle.Choice → Result Std.U32

/-- "Select `a` or `b` according to `choice`. Returns `a` if `choice == Choice(0)`; `b` if
`choice == Choice(1)`." (lib.rs:394-399) -/
@[nolint defsWithUnderscore]
def U32.Insts.SubtleConditionallySelectable.conditional_select.Contract : Prop :=
  ∀ (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid),
    U32.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_assign]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_assign] -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u32>}::conditional_assign"]
opaque U32.Insts.SubtleConditionallySelectable.conditional_assign :
  Std.U32 → Std.U32 → subtle.Choice → Result Std.U32

/-- "Conditionally assign `other` to `self`, according to `choice`." (lib.rs:422) -/
@[nolint defsWithUnderscore]
def U32.Insts.SubtleConditionallySelectable.conditional_assign.Contract : Prop :=
  ∀ (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid),
    U32.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u32}::conditional_swap]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u32>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u32>}::conditional_swap"]
opaque U32.Insts.SubtleConditionallySelectable.conditional_swap :
  Std.U32 → Std.U32 → subtle.Choice → Result (Std.U32 × Std.U32)

/-- "Conditionally swap `self` and `other` if `choice == 1`; otherwise, reassign both unto
themselves." (lib.rs:446-447) -/
@[nolint defsWithUnderscore]
def U32.Insts.SubtleConditionallySelectable.conditional_swap.Contract : Prop :=
  ∀ (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid),
    U32.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select] -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
opaque U64.Insts.SubtleConditionallySelectable.conditional_select :
  Std.U64 → Std.U64 → subtle.Choice → Result Std.U64

/-- "Select `a` or `b` according to `choice`. Returns `a` if `choice == Choice(0)`; `b` if
`choice == Choice(1)`." (lib.rs:394-399) -/
@[nolint defsWithUnderscore]
def U64.Insts.SubtleConditionallySelectable.conditional_select.Contract : Prop :=
  ∀ (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid),
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_assign]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign] -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
opaque U64.Insts.SubtleConditionallySelectable.conditional_assign :
  Std.U64 → Std.U64 → subtle.Choice → Result Std.U64

/-- "Conditionally assign `other` to `self`, according to `choice`." (lib.rs:422) -/
@[nolint defsWithUnderscore]
def U64.Insts.SubtleConditionallySelectable.conditional_assign.Contract : Prop :=
  ∀ (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid),
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_swap]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap] -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
opaque U64.Insts.SubtleConditionallySelectable.conditional_swap :
  Std.U64 → Std.U64 → subtle.Choice → Result (Std.U64 × Std.U64)

/-- "Conditionally swap `self` and `other` if `choice == 1`; otherwise, reassign both unto
themselves." (lib.rs:446-447) -/
@[nolint defsWithUnderscore]
def U64.Insts.SubtleConditionallySelectable.conditional_swap.Contract : Prop :=
  ∀ (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid),
    U64.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄

/-! ## `ConditionallySelectable` for `[T; N]` -/

/-- [subtle::{impl subtle::ConditionallySelectable for [T; N]}::conditional_select]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 581:4-581:69
    Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select] -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select"]
opaque Array.Insts.SubtleConditionallySelectable.conditional_select
  {T : Type} {N : Std.Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T) :
  Array T N → Array T N → subtle.Choice → Result (Array T N)

/-- "Select `a` or `b` according to `choice`. Returns `a` if `choice == Choice(0)`; `b` if
`choice == Choice(1)`." (lib.rs:394-399). Body (lib.rs:581-591): copy `a`, then
`a_i.conditional_assign(b_i, choice)` for each element. So the spec assumes a valid choice and
the `conditional_assign` contract for the element instance at that choice. -/
@[nolint defsWithUnderscore]
def Array.Insts.SubtleConditionallySelectable.conditional_select.Contract : Prop :=
  ∀ {T : Type} {N : Std.Usize} (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) (hc : choice.IsValid)
    (hinst : ∀ x y, inst.conditional_assign x y choice ⦃ r =>
      (choice = 0#u8 → r = x) ∧ (choice = 1#u8 → r = y) ⦄),
    Array.Insts.SubtleConditionallySelectable.conditional_select inst a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-! ## `ConditionallyNegatable` (faithful body) -/

/-- [subtle::{impl subtle::ConditionallyNegatable for T}::conditional_negate]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 620:4-620:52
    Name pattern: [subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate]

Verbatim translation of
`let self_neg: T = -(self as &T); self.conditional_assign(&self_neg, choice);`. -/
@[nolint defsWithUnderscore,
  rust_fun "subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate"]
def subtle.ConditionallyNegatable.Blanket.conditional_negate
  {T : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (coreopsarithNegShared0TTInst : core.ops.arith.Neg T T) :
  T → subtle.Choice → Result T :=
  fun self choice => do
    let self_neg ← coreopsarithNegShared0TTInst.neg self
    let self1 ← ConditionallySelectableInst.conditional_assign self self_neg choice
    ok self1

/-! ## `CtOption` -/

/-- [subtle::{subtle::CtOption<T>}::new]:
    Source: 'subtle-2.6.1/src/lib.rs', lines 678:4-678:56
    Name pattern: [subtle::{subtle::CtOption<@T>}::new] -/
@[rust_fun "subtle::{subtle::CtOption<@T>}::new"]
opaque subtle.CtOption.new {T : Type} : T → subtle.Choice → Result (subtle.CtOption T)

/-- "This method is used to construct a new `CtOption<T>` and takes a value of type `T`, and a
`Choice` that determines whether the optional value should be `Some` or not. If `is_some` is
false, the value will still be stored but its value is never exposed." (lib.rs:672-676) -/
def subtle.CtOption.new.Contract : Prop :=
  ∀ {T : Type} (value : T) (is_some : subtle.Choice)
    (his_some : is_some.IsValid),
    subtle.CtOption.new value is_some ⦃ opt => opt = { value, is_some } ⦄

/-! ## The specification of the crate -/

/-- The specification of `subtle`: one field per function, the predicates above. -/
structure subtle.Contract : Prop where
  unwrap_u8 : subtle.Choice.unwrap_u8.Contract
  bool_from_choice : Bool.Insts.CoreConvertFromChoice.from.Contract
  choice_bitand : subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand.Contract
  choice_bitor : subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor.Contract
  choice_not : subtle.Choice.Insts.CoreOpsBitNotChoice.not.Contract
  choice_from_u8 : subtle.Choice.Insts.CoreConvertFromU8.from.Contract
  slice_ct_eq : Slice.Insts.SubtleConstantTimeEq.ct_eq.Contract
  u8_ct_eq : U8.Insts.SubtleConstantTimeEq.ct_eq.Contract
  u16_ct_eq : U16.Insts.SubtleConstantTimeEq.ct_eq.Contract
  u8_conditional_select : U8.Insts.SubtleConditionallySelectable.conditional_select.Contract
  u8_conditional_assign : U8.Insts.SubtleConditionallySelectable.conditional_assign.Contract
  u32_conditional_select : U32.Insts.SubtleConditionallySelectable.conditional_select.Contract
  u32_conditional_assign : U32.Insts.SubtleConditionallySelectable.conditional_assign.Contract
  u32_conditional_swap : U32.Insts.SubtleConditionallySelectable.conditional_swap.Contract
  u64_conditional_select : U64.Insts.SubtleConditionallySelectable.conditional_select.Contract
  u64_conditional_assign : U64.Insts.SubtleConditionallySelectable.conditional_assign.Contract
  u64_conditional_swap : U64.Insts.SubtleConditionallySelectable.conditional_swap.Contract
  array_conditional_select : Array.Insts.SubtleConditionallySelectable.conditional_select.Contract
  ctOption_new : subtle.CtOption.new.Contract

/-- The single trusted assumption about `subtle`: its functions meet their contracts. -/
axiom RustAx.subtle : subtle.Contract

/-- `subtle.Choice.unwrap_u8` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.unwrap_u8_spec
    (c : subtle.Choice) (hc : c.IsValid) :
    subtle.Choice.unwrap_u8 c ⦃ r => r = c ⦄ :=
  RustAx.subtle.unwrap_u8 c hc

/-- `Bool.Insts.CoreConvertFromChoice.from` meets its contract (`RustAx.subtle`). -/
@[step]
theorem Bool.Insts.CoreConvertFromChoice.from_spec
    (c : subtle.Choice)
    (hc : c.IsValid) :
    Bool.Insts.CoreConvertFromChoice.from c ⦃ b => b = (c != 0#u8) ⦄ :=
  RustAx.subtle.bool_from_choice c hc

/-- `subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec
    (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃ c =>
      c.IsValid ∧ c = a &&& b ⦄ :=
  RustAx.subtle.choice_bitand a b ha hb

/-- `subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec
    (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b ⦃ c =>
      c.IsValid ∧ c = a ||| b ⦄ :=
  RustAx.subtle.choice_bitor a b ha hb

/-- `subtle.Choice.Insts.CoreOpsBitNotChoice.not` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec
    (c : subtle.Choice) (hc : c.IsValid) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c ⦃ r => r.IsValid ∧ r = 1#u8 &&& ~~~c ⦄ :=
  RustAx.subtle.choice_not c hc

/-- `subtle.Choice.Insts.CoreConvertFromU8.from` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreConvertFromU8.from_spec
    (input : Std.U8)
    (h : input = 0#u8 ∨ input = 1#u8) :
    subtle.Choice.Insts.CoreConvertFromU8.from input ⦃ c => c.IsValid ∧ c = input ⦄ :=
  RustAx.subtle.choice_from_u8 input h

/-- `Slice.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem Slice.Insts.SubtleConstantTimeEq.ct_eq_spec
    {T : Type}
    (inst : subtle.ConstantTimeEq T)
    (hinst : ∀ x y, inst.ct_eq x y ⦃ c => (x = y → c = 1#u8) ∧ (x ≠ y → c = 0#u8) ⦄)
    (a b : Slice T) :
    Slice.Insts.SubtleConstantTimeEq.ct_eq inst a b ⦃ c =>
      c.IsValid ∧ (a = b → c = 1#u8) ∧ (a ≠ b → c = 0#u8) ⦄ :=
  RustAx.subtle.slice_ct_eq inst hinst a b

/-- `U8.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConstantTimeEq.ct_eq_spec
    (a b : Std.U8) :
    U8.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄ :=
  RustAx.subtle.u8_ct_eq a b

/-- `U16.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem U16.Insts.SubtleConstantTimeEq.ct_eq_spec
    (a b : Std.U16) :
    U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄ :=
  RustAx.subtle.u16_ct_eq a b

/-- `U8.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid) :
    U8.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u8_conditional_select a b choice hc

/-- `U8.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid) :
    U8.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u8_conditional_assign a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u32_conditional_select a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u32_conditional_assign a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_swap`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  RustAx.subtle.u32_conditional_swap a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u64_conditional_select a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u64_conditional_assign a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_swap`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  RustAx.subtle.u64_conditional_swap a b choice hc

/-- `Array.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem Array.Insts.SubtleConditionallySelectable.conditional_select_spec
    {T : Type} {N : Std.Usize} (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) (hc : choice.IsValid)
    (hinst : ∀ x y, inst.conditional_assign x y choice ⦃ r =>
      (choice = 0#u8 → r = x) ∧ (choice = 1#u8 → r = y) ⦄) :
    Array.Insts.SubtleConditionallySelectable.conditional_select inst a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.array_conditional_select inst a b choice hc hinst

/-- `subtle.CtOption.new` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.CtOption.new_spec
    {T : Type} (value : T) (is_some : subtle.Choice)
    (his_some : is_some.IsValid) :
    subtle.CtOption.new value is_some ⦃ opt => opt = { value, is_some } ⦄ :=
  RustAx.subtle.ctOption_new value is_some his_some
