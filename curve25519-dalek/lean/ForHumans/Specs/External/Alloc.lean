-- [curve25519_dalek]: external functions.
module -- shake: keep-all
public import Aeneas
public import Curve25519Dalek.Types
public import ForHumans.Specs.External.Subtle.Contract
public import ForHumans.Specs.External.Zeroize.Contract
public import ForHumans.Specs.External.Core
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open Curve25519Dalek

/-- [alloc::vec::{impl core::iter::traits::collect::IntoIterator<&'a T, core::slice::iter::Iter<'a,
    T>> for &'a alloc::vec::Vec<T>}::into_iter]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4088:4-4088:40
    Name pattern: [alloc::vec::{core::iter::traits::collect::IntoIterator<&'a
    alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, \
    core::slice::iter::Iter<'a, @T>>}::into_iter"]
opaque SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (core.slice.iter.Iter T)

/-! ## Contracts

The behaviour of the `opaque` function above, as stated in the Rust standard library
documentation: a predicate `….Contract : Prop`, and one axiom (`RustAx.alloc`) stating it. The
axiom is the only trusted addition of this file; the theorem `…_spec` used by the proofs is its
projection. -/

/-- `<&Vec<T> as IntoIterator>::into_iter` (alloc/src/vec/mod.rs,
`impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A>`): "Creates an iterator from a value."
Body: `self.iter()`, the slice iterator over the vector's elements, starting at index `0`; never
fails. `A` is the allocator type parameter. -/
@[nolint defsWithUnderscore]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter.Contract : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter A v ⦃
      (it : core.slice.iter.Iter T) => it = ⟨v.deref, 0⟩ ⦄

/-- The specification of the `alloc` functions used: one field per function, the predicates
above. -/
structure alloc.Contract : Prop where
  sharedVec_into_iter :
    SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter.Contract

/-- The single trusted assumption about `alloc`: its functions meet their contracts. -/
axiom RustAx.alloc : alloc.Contract
