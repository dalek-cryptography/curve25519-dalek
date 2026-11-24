module
public import Aeneas
@[expose] public section

/-! # Functions of `core` that Aeneas does not model

Defined by their documented behaviour, as Aeneas's library defines the other functions of `core`.
-/

open Aeneas Aeneas.Std Result
set_option linter.style.whitespace false

/-- `bool::then_some`: `Some t` if `b`, otherwise `None`. -/
@[rust_fun "core::bool::{bool}::then_some", nolint defsWithUnderscore]
def core.bool.Bool.then_some {T : Type _} (b : Bool) (t : T) : Result (Option T) :=
  ok (if b then some t else none)

/-- `Option::filter`: `Some x` if `predicate(&x)` holds, otherwise `None`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::filter"]
def core.option.Option.filter {T : Type _} {P : Type _} (inst : core.ops.function.FnOnce P T Bool)
    (self : Option T) (predicate : P) : Result (Option T) :=
  match self with
  | none => ok none
  | some x => do
    let b ← inst.call_once predicate x
    ok (if b then some x else none)

/-- `?` on an `Option`: continue with `x` on `Some x`, return `None` on `None`. -/
@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch",
  nolint defsWithUnderscore]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type _} (self : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match self with
  | some x => ok (.Continue x)
  | none => ok (.Break none)

/-- The `None` that `?` returns from a function returning `Option`. -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, \
    core::option::Option<!>>}::from_residual", nolint defsWithUnderscore]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual (T : Type _)
    (_residual : Option Never) : Result (Option T) :=
  ok none
