/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Scalar.Add
import Proofs.Scalar.Zero
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumSum

/-- The loop of `sum` adds the remaining items to the accumulator, modulo `L`. -/
private theorem sum_loop_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ss : List Scalar)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < L) (acc : Scalar) (hacc : acc.asNat < L) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : Scalar) =>
      r.asNat = (acc.asNat + (ss.map (·.asNat)).sum) % L ⦄ := by
  induction hiter generalizing acc ss with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨p, hp⟩
    obtain ⟨o, it1⟩ := p
    simp only at hp
    subst hp
    simp [Nat.mod_eq_of_lt hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨p, ho, hit⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho hit
    subst ho hit
    step with hb as ⟨s, hs⟩
    subst hs
    step with Scalar.Insts.CoreOpsArithAddSharedBScalarScalar.add_spec acc s hacc
      (hss s List.mem_cons_self) as ⟨acc1, hacc1⟩
    apply WP.spec_mono (ih _ hrest (fun t ht => hss t (List.mem_cons_of_mem _ ht)) acc1
      (hacc1 ▸ Nat.mod_lt _ L_pos))
    intro r hr
    rw [hr, hacc1, List.map_cons, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc]

@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T) (ss : List Scalar)
    (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < L) :
    sum borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).sum % L ⦄ := by
  unfold sum
  have hzero := ZERO_spec
  have := sum_loop_spec borrowInst iterInst iter xs hiter ss hborrow hss ZERO
    (by rw [hzero]; exact L_pos)
  apply WP.spec_mono this
  intro r hr
  rw [hr, hzero, Nat.zero_add]

end Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumSum
