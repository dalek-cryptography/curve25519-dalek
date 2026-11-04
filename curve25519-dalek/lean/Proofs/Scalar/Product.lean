/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Iterator
public import Defs.Scalar
import Proofs.Scalar.Mul
import Proofs.Scalar.One
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumProduct

/-- The loop of `product` multiplies the accumulator by the remaining items, modulo `L`. -/
private theorem product_loop_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ss : List Scalar)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (acc : Scalar) (hacc : acc.asNat < L) :
    product_loop borrowInst iterInst iter acc ⦃ (r : Scalar) =>
      r.asNat = acc.asNat * (ss.map (·.asNat)).prod % L ⦄ := by
  induction hiter generalizing acc ss with
  | nil hnext =>
    cases hborrow
    unfold product_loop loop product_loop.body
    step with hnext as ⟨p, hp⟩
    obtain ⟨o, it1⟩ := p
    simp only at hp
    subst hp
    simp [Nat.mod_eq_of_lt hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold product_loop loop product_loop.body
    step with hnext as ⟨p, ho, hit⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho hit
    subst ho hit
    step with hb as ⟨s, hs⟩
    subst hs
    step as ⟨acc1, hacc1⟩
    apply WP.spec_mono (ih _ hrest acc1 (hacc1 ▸ Nat.mod_lt _ L_pos))
    intro r hr
    rw [hr, hacc1, List.map_cons, List.prod_cons, Nat.mod_mul_mod, Nat.mul_assoc]

@[step]
theorem product_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T) (ss : List Scalar)
    (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss) :
    product borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).prod % L ⦄ := by
  unfold product
  have hone := ONE_spec
  have := product_loop_spec borrowInst iterInst iter xs hiter ss hborrow ONE
    (by rw [hone]; exact (Nat.one_lt_two_pow (by decide)).trans two_pow_252_lt_L)
  apply WP.spec_mono this
  intro r hr
  rw [hr, hone, Nat.one_mul]

end Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumProduct
