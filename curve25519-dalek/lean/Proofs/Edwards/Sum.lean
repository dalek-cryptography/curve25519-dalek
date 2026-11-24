module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
import Proofs.Edwards.Add
import Proofs.Edwards.Identity
public section

/-! # `Sum for EdwardsPoint`

The patched loop (`while let Some(item) = iter.next()`) adds the borrowed items to the identity.
The iterator is described by `Iterator.Yields` and `borrow` by its results on the yielded items,
as for `Sum for Scalar`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.EdwardsPoint.«64bit-tables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPoint64bit-tablesEdwardsPoint64bit-tables»
  (add_spec)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«64bit-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«64bit-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«64bit-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«64bit-tables») (hacc : acc.LimbsLt 52) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.LimbsLt 52 ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«64bit-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«64bit-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«64bit-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«32bit-tables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPoint32bit-tablesEdwardsPoint32bit-tables»
  (add_spec)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«32bit-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«32bit-tables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«32bit-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«32bit-tables») (hacc : acc.LimbsLt 26) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.LimbsLt 26 ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^26`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«32bit-tables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«32bit-tables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«32bit-tables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«64bit-notables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPoint64bit-notablesEdwardsPoint64bit-notables»
  (add_spec)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«64bit-notables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«64bit-notables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«64bit-notables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«64bit-notables») (hacc : acc.LimbsLt 52) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.LimbsLt 52 ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^52`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«64bit-notables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«64bit-notables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«64bit-notables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.LimbsLt 52 ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«64bit-notables».Insts

namespace Curve25519Dalek.edwards.EdwardsPoint.«32bit-notables».Insts
namespace CoreIterTraitsAccumSum

open «CoreOpsArithAddSharedBEdwardsPoint32bit-notablesEdwardsPoint32bit-notables»
  (add_spec)

/-- The loop of `sum` adds the remaining items to the accumulator. -/
private theorem sum_loop_spec {T I : Type}
    (borrowInst : core.borrow.Borrow T EdwardsPoint.«32bit-notables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (hiter : iterInst.Yields iter xs) (ps : List EdwardsPoint.«32bit-notables»)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«32bit-notables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hps_on : ∀ P ∈ ps, P.OnCurve)
    (acc : EdwardsPoint.«32bit-notables») (hacc : acc.LimbsLt 26) (hacc_on : acc.OnCurve) :
    sum_loop borrowInst iterInst iter acc ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = acc.toPoint + (ps.map (·.toPoint)).sum ∧ r.LimbsLt 26 ⦄ := by
  induction hiter generalizing acc ps with
  | nil hnext =>
    cases hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp [hacc_on, hacc]
  | cons hnext _ ih =>
    obtain _ | ⟨hb, hrest⟩ := hborrow
    unfold sum_loop loop sum_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with hb as ⟨P, hP⟩
    subst hP
    step with add_spec acc P hacc (hps P List.mem_cons_self) hacc_on
      (hps_on P List.mem_cons_self) as ⟨acc1, hacc1on, hacc1, hacc1b⟩
    apply WP.spec_mono (ih _ hrest (fun Q hQ => hps Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ => hps_on Q (List.mem_cons_of_mem _ hQ)) acc1 hacc1b hacc1on)
    rintro r ⟨hron, hr, hrb⟩
    refine ⟨hron, ?_, hrb⟩
    rw [hr, hacc1, List.map_cons, List.sum_cons, add_assoc]

/-- `Sum for EdwardsPoint`: the sum of the points yielded by the iterator (through `borrow`);
limbs `< 2^26`. -/
@[step]
theorem sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T EdwardsPoint.«32bit-notables»)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ps : List EdwardsPoint.«32bit-notables») (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂
      (fun x P => borrowInst.borrow x ⦃ (P' : EdwardsPoint.«32bit-notables») => P' = P ⦄) xs ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26) (hps_on : ∀ P ∈ ps, P.OnCurve) :
    sum borrowInst iterInst iter ⦃ (r : EdwardsPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = (ps.map (·.toPoint)).sum ∧ r.LimbsLt 26 ⦄ := by
  unfold sum
  step with Curve25519_dalekTraitsIdentity.identity_spec as ⟨acc, hacc_on, hacc, haccb⟩
  apply WP.spec_mono (sum_loop_spec borrowInst iterInst iter xs hiter ps hborrow hps hps_on acc
    haccb hacc_on)
  rintro r ⟨hron, hr, hrb⟩
  exact ⟨hron, by rw [hr, hacc, zero_add], hrb⟩

end CoreIterTraitsAccumSum
end Curve25519Dalek.edwards.EdwardsPoint.«32bit-notables».Insts


