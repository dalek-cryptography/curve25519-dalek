/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Alloc.Vec
public import Aeneas.Std.Alloc.Vec.IntoIter
import all Aeneas.Std.Alloc.Vec.IntoIter
public import Aeneas.Std.Core.CoreOption
public import ToAeneas.Iterator
import Aeneas.Tactic.Step.StepStar
import Proofs.Helpers.Vec
public section

/-! # Generic forms of the collecting loops

The translation patches replace `iter.map(f).collect()` by `while let Some(x) = it.next()`
loops pushing onto a `Vec` (aeneas#1057). They come in three shapes, defined here generically
(the translated loop bodies are definitionally equal to them) with their specs:

- `collectBody`: push each item;
- `collectMapBody`: push `f (borrow x)` for each item `x`;
- `collectOptBody`: for items `Option P`, push `f P`, and stop with `none` at the first `none`;
- `collectApplyBody`: push `g x` for each item `x` (the Ristretto wrappers: `g` is `borrow`, or
  `Option::map` with the identity closure).

The iterator is described by `Iterator.Yields`, `borrow` by its results on the items. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP ControlFlow

namespace Curve25519Dalek.collect

variable {It T Y Z : Type}

/-- The `Vec::from_iter` model accumulates the yielded items in reverse order. -/
private theorem iterToList_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (it : It) (xs : List T) (hit : iterInst.Yields it xs) (acc : List T) :
    alloc.vec.FromIteratorVec.iterToList iterInst it acc
      ⦃ r => r = acc.reverse ++ xs ⦄ := by
  induction hit generalizing acc with
  | nil hnext =>
    rw [alloc.vec.FromIteratorVec.iterToList.eq_def]
    step with hnext as ⟨o, it1, ho⟩
    subst ho
    simp
  | cons hnext _ ih =>
    rw [alloc.vec.FromIteratorVec.iterToList.eq_def]
    step with hnext as ⟨o, it1, ho, hit⟩
    subst ho hit
    apply spec_mono (ih (_ :: acc))
    intro r hr
    simpa [List.reverse_cons, List.append_assoc] using hr

/-- `Vec::from_iter` preserves the finite sequence yielded by an iterator. -/
theorem fromIter_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (it : It) (xs : List T) (hit : iterInst.Yields it xs) (hlen : xs.length ≤ Usize.max) :
    alloc.vec.FromIteratorVec.from_iter
      (core.iter.traits.collect.IntoIterator.Blanket iterInst) it
      ⦃ (r : alloc.vec.Vec T) => r.val = xs ⦄ := by
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
  step with iterToList_spec iterInst it xs hit [] as ⟨l, hl⟩
  simp only [List.reverse_nil, List.nil_append] at hl
  subst hl
  simp [hlen, WP.spec_ok, alloc.vec.Vec.from_val]

/-- Push each item of the iterator. -/
@[expose] def collectBody (iterInst : core.iter.traits.iterator.Iterator It T) (it : It)
    (out : alloc.vec.Vec T) : Result (ControlFlow (It × alloc.vec.Vec T) (alloc.vec.Vec T)) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done out)
  | some x =>
    let out1 ← alloc.vec.Vec.push out x
    ok (cont (it1, out1))

/-- Push `f (borrow x)` for each item `x` of the iterator. -/
@[expose] def collectMapBody (iterInst : core.iter.traits.iterator.Iterator It T)
    (borrow : T → Result Y) (f : Y → Result Z) (it : It) (out : alloc.vec.Vec Z) :
    Result (ControlFlow (It × alloc.vec.Vec Z) (alloc.vec.Vec Z)) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done out)
  | some x =>
    let y ← borrow x
    let z ← f y
    let out1 ← alloc.vec.Vec.push out z
    ok (cont (it1, out1))

/-- For items `Option P`: push `f P`; stop with `none` at the first `none`. -/
@[expose] def collectOptBody (iterInst : core.iter.traits.iterator.Iterator It (Option Y))
    (f : Y → Result Z) (it : It) (out : alloc.vec.Vec Z) :
    Result (ControlFlow (It × alloc.vec.Vec Z) (Option (alloc.vec.Vec Z))) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done (some out))
  | some P_opt =>
    match P_opt with
    | none => ok (done none)
    | some P =>
      let z ← f P
      let out1 ← alloc.vec.Vec.push out z
      ok (cont (it1, out1))

/-- Push `g x` for each item `x` of the iterator. -/
@[expose] def collectApplyBody (iterInst : core.iter.traits.iterator.Iterator It T)
    (g : T → Result Z) (it : It) (out : alloc.vec.Vec Z) :
    Result (ControlFlow (It × alloc.vec.Vec Z) (alloc.vec.Vec Z)) := do
  let (o, it1) ← iterInst.next it
  match o with
  | none => ok (done out)
  | some x =>
    let z ← g x
    let out1 ← alloc.vec.Vec.push out z
    ok (cont (it1, out1))

theorem collectLoop_spec (iterInst : core.iter.traits.iterator.Iterator It T) (it : It)
    (xs : List T) (hit : iterInst.Yields it xs) (out : alloc.vec.Vec T)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec T) => collectBody iterInst it1 out1) (it, out)
      ⦃ (r : alloc.vec.Vec T) => r.val = out.val ++ xs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold loop collectBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold loop collectBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

theorem collectMapLoop_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (borrow : T → Result Y) (f : Y → Result Z) (Pf : Y → Z → Prop) (it : It) (xs : List T)
    (hit : iterInst.Yields it xs) (ys : List Y)
    (hborrow : List.Forall₂ (fun x y => borrow x ⦃ (y' : Y) => y' = y ⦄) xs ys)
    (hf : ∀ y ∈ ys, f y ⦃ (z : Z) => Pf y z ⦄) (out : alloc.vec.Vec Z)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectMapBody iterInst borrow f it1 out1)
      (it, out) ⦃ (r : alloc.vec.Vec Z) =>
        ∃ zs, r.val = out.val ++ zs ∧ List.Forall₂ Pf ys zs ⦄ := by
  induction hit generalizing out ys with
  | nil hnext =>
    cases hborrow
    unfold loop collectMapBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold loop collectMapBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨y, hy⟩
    subst hy
    step with hf y List.mem_cons_self as ⟨z, hz⟩
    step with alloc.vec.Vec.push_spec out z
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (out := out1) _ hrest
      (fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')) (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hz hzs⟩

theorem collectApplyLoop_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (g : T → Result Z) (it : It) (xs : List T) (hit : iterInst.Yields it xs) (zs : List Z)
    (hg : List.Forall₂ (fun x z => g x ⦃ (z' : Z) => z' = z ⦄) xs zs) (out : alloc.vec.Vec Z)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectApplyBody iterInst g it1 out1)
      (it, out) ⦃ (r : alloc.vec.Vec Z) => r.val = out.val ++ zs ⦄ := by
  induction hit generalizing out zs with
  | nil hnext =>
    cases hg
    unfold loop collectApplyBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    obtain _ | ⟨hx, hrest⟩ := hg
    unfold loop collectApplyBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hx as ⟨z, hz⟩
    subst hz
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (out := out1) _ hrest (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

/-- `collectApplyLoop_spec` with a property `Pg` of each result instead of its value. -/
theorem collectApplyLoopP_spec (iterInst : core.iter.traits.iterator.Iterator It T)
    (g : T → Result Z) (Pg : T → Z → Prop) (it : It) (xs : List T) (hit : iterInst.Yields it xs)
    (hg : ∀ x ∈ xs, g x ⦃ (z : Z) => Pg x z ⦄) (out : alloc.vec.Vec Z)
    (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectApplyBody iterInst g it1 out1)
      (it, out) ⦃ (r : alloc.vec.Vec Z) =>
        ∃ zs, r.val = out.val ++ zs ∧ List.Forall₂ Pg xs zs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold loop collectApplyBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' x xs' hnext _ ih =>
    unfold loop collectApplyBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hg x List.mem_cons_self as ⟨z, hz⟩
    step with alloc.vec.Vec.push_spec out z
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    rintro r ⟨zs, hr, hzs⟩
    exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
      List.Forall₂.cons hz hzs⟩

theorem collectOptLoop_spec (iterInst : core.iter.traits.iterator.Iterator It (Option Y))
    (f : Y → Result Z) (Pf : Y → Z → Prop) (it : It) (xs : List (Option Y))
    (hit : iterInst.Yields it xs) (hf : ∀ y, some y ∈ xs → f y ⦃ (z : Z) => Pf y z ⦄)
    (out : alloc.vec.Vec Z) (hlen : out.length + xs.length ≤ Usize.max) :
    loop (fun ((it1, out1) : It × alloc.vec.Vec Z) => collectOptBody iterInst f it1 out1)
      (it, out) ⦃ (r : Option (alloc.vec.Vec Z)) =>
        (r = none ↔ none ∈ xs) ∧
        ∀ v, r = some v → ∃ zs, v.val = out.val ++ zs ∧
          List.Forall₂ Pf (xs.filterMap id) zs ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold loop collectOptBody
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | @cons it it' x xs' hnext _ ih =>
    unfold loop collectOptBody
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    rcases x with _ | y
    · simp
    · step with hf y List.mem_cons_self as ⟨z, hz⟩
      step with alloc.vec.Vec.push_spec out z
        (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
      apply WP.spec_mono (ih (fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')) out1 (by
        rw [alloc.vec.Vec.length_of_val_eq_append hout1]
        simp only [List.length_cons] at hlen; omega))
      rintro r ⟨hnone, hsome⟩
      refine ⟨by simp [hnone], fun v hv => ?_⟩
      obtain ⟨zs, hr, hzs⟩ := hsome v hv
      exact ⟨z :: zs, by rw [hr, hout1, List.append_assoc, List.singleton_append],
        by simpa using List.Forall₂.cons hz hzs⟩

/-- `Option::map` with a closure that returns its argument leaves the option unchanged (the
Ristretto wrappers' identity closures, for which `hf` holds by `rfl`). -/
theorem optionMap_id_spec {F T : Type} (inst : core.ops.function.FnOnce F T T) (f : F)
    (hf : ∀ x, inst.call_once f x = ok x) (o : Option T) :
    core.option.Option.map inst o f ⦃ (o' : Option T) => o' = o ⦄ := by
  rcases o with _ | x <;> simp [core.option.Option.map, hf]

end Curve25519Dalek.collect
