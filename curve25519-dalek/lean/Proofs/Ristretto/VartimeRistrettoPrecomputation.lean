module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.VartimePrecomputedStrausNew
import Proofs.Backend.VartimePrecomputedStrausLen
import Proofs.Backend.VartimePrecomputedStrausIsEmpty
import Proofs.Backend.VartimePrecomputedStrausOptionalMixedMultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Vec
import Proofs.Helpers.Optional
public section

/-! # `VartimePrecomputedMultiscalarMul for VartimeRistrettoPrecomputation`

`VartimeRistrettoPrecomputation` is the backend `VartimePrecomputedStraus`. `new` and
`optional_mixed_multiscalar_mul` collect the (optional) points into a vector first, through
`borrow` or `Option::map` with the identity closure, and the result is mapped back with the
`RistrettoPoint` constructor (the identity). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint64bit-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54`
out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«64bit-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«64bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«64bit-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«64bit-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  have hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve := fun P hP => ⟨hps P hP, hps_on P hP⟩
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  have hpsys := hborrow.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowInst.borrow it ys hit ps hborrow
    (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with backend.«VartimePrecomputedStraus64bit-tables».new_spec
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) v v.val ps
      (core.iter.traits.collect.IntoIteratorVec_yields v)
      (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P)
      hps (by rw [hv, ← hpsys]; exact hys) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeRistrettoPrecomputation.«64bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus64bit-tables».len_spec self

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeRistrettoPrecomputation.«64bit-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus64bit-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimeRistrettoPrecomputation64bit-tablesRistrettoPoint64bit-tables»
set_option linter.style.longLine true

/-- The collecting loop of `optional_mixed_multiscalar_mul` pushes the optional points
unchanged. -/
private theorem extended_points_loop_spec {I J K S SI D DI It : Type}
    (staticInst : core.iter.traits.collect.IntoIterator I S SI)
    (borrowStatic : core.borrow.Borrow S scalar.Scalar)
    (dynamicInst : core.iter.traits.collect.IntoIterator J D DI)
    (borrowDynamic : core.borrow.Borrow D scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«64bit-tables») It)
    (it : It) (qops : List (Option ristretto.RistrettoPoint.«64bit-tables»))
    (hit : pointsInst.iteratorInst.Yields it qops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-tables»))
    (hlen : out.length + qops.length ≤ Usize.max) :
    optional_mixed_multiscalar_mul_loop staticInst borrowStatic dynamicInst borrowDynamic
      pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-tables»)) =>
        r.val = out.val ++ qops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with collect.optionMap_id_spec as ⟨z, hz⟩
    · intro x
      rfl
    subst hz
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«64bit-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«64bit-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«64bit-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option ristretto.RistrettoPoint.«64bit-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 52 ⦄ := by
  apply spec_some_of_filterMap
  have hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve := fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩
  unfold optional_mixed_multiscalar_mul
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h3 as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ _ _ it qops hit (alloc.vec.Vec.new _)
    (by simpa using hqops) as ⟨v, hv⟩
  replace hv : v.val = qops := by rw [hv]; rfl
  step with
    backend.«VartimePrecomputedStraus64bit-tables».optional_mixed_multiscalar_mul_spec _ _ _ _
      (core.iter.traits.collect.IntoIteratorVec _) self static_scalars dynamic_scalars v xs ss
      ys ds v.val hself hself_b hstatic_scalars hdynamic_scalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_static hborrow_dynamic hss hds
      (by rw [hv]; exact hqs) hxs hys (by rw [hv]; exact hqops) (by rw [hv]; exact hstatic)
      (by rw [hv]; exact hdynamic) as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint64bit-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«64bit-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint32bit-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`); limbs `< 2^26` in, `< 2^27`
out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«32bit-tables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«32bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«32bit-tables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«32bit-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  have hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve := fun P hP => ⟨hps P hP, hps_on P hP⟩
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  have hpsys := hborrow.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowInst.borrow it ys hit ps hborrow
    (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with backend.«VartimePrecomputedStraus32bit-tables».new_spec
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) v v.val ps
      (core.iter.traits.collect.IntoIteratorVec_yields v)
      (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P)
      hps (by rw [hv, ← hpsys]; exact hys) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeRistrettoPrecomputation.«32bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus32bit-tables».len_spec self

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeRistrettoPrecomputation.«32bit-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus32bit-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimeRistrettoPrecomputation32bit-tablesRistrettoPoint32bit-tables»
set_option linter.style.longLine true

/-- The collecting loop of `optional_mixed_multiscalar_mul` pushes the optional points
unchanged. -/
private theorem extended_points_loop_spec {I J K S SI D DI It : Type}
    (staticInst : core.iter.traits.collect.IntoIterator I S SI)
    (borrowStatic : core.borrow.Borrow S scalar.Scalar)
    (dynamicInst : core.iter.traits.collect.IntoIterator J D DI)
    (borrowDynamic : core.borrow.Borrow D scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«32bit-tables») It)
    (it : It) (qops : List (Option ristretto.RistrettoPoint.«32bit-tables»))
    (hit : pointsInst.iteratorInst.Yields it qops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-tables»))
    (hlen : out.length + qops.length ≤ Usize.max) :
    optional_mixed_multiscalar_mul_loop staticInst borrowStatic dynamicInst borrowDynamic
      pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-tables»)) =>
        r.val = out.val ++ qops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with collect.optionMap_id_spec as ⟨z, hz⟩
    · intro x
      rfl
    subst hz
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^26`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«32bit-tables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«32bit-tables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«32bit-tables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option ristretto.RistrettoPoint.«32bit-tables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 26 ⦄ := by
  apply spec_some_of_filterMap
  have hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26 ∧ Q.OnCurve := fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩
  unfold optional_mixed_multiscalar_mul
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h3 as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ _ _ it qops hit (alloc.vec.Vec.new _)
    (by simpa using hqops) as ⟨v, hv⟩
  replace hv : v.val = qops := by rw [hv]; rfl
  step with
    backend.«VartimePrecomputedStraus32bit-tables».optional_mixed_multiscalar_mul_spec _ _ _ _
      (core.iter.traits.collect.IntoIteratorVec _) self static_scalars dynamic_scalars v xs ss
      ys ds v.val hself hself_b hstatic_scalars hdynamic_scalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_static hborrow_dynamic hss hds
      (by rw [hv]; exact hqs) hxs hys (by rw [hv]; exact hqops) (by rw [hv]; exact hstatic)
      (by rw [hv]; exact hdynamic) as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint32bit-tables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«32bit-tables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint64bit-notables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54`
out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«64bit-notables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«64bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«64bit-notables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«64bit-notables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  have hps : ∀ P ∈ ps, P.LimbsLt 52 ∧ P.OnCurve := fun P hP => ⟨hps P hP, hps_on P hP⟩
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  have hpsys := hborrow.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowInst.borrow it ys hit ps hborrow
    (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with backend.«VartimePrecomputedStraus64bit-notables».new_spec
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) v v.val ps
      (core.iter.traits.collect.IntoIteratorVec_yields v)
      (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P)
      hps (by rw [hv, ← hpsys]; exact hys) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeRistrettoPrecomputation.«64bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus64bit-notables».len_spec self

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeRistrettoPrecomputation.«64bit-notables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus64bit-notables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimeRistrettoPrecomputation64bit-notablesRistrettoPoint64bit-notables»
set_option linter.style.longLine true

/-- The collecting loop of `optional_mixed_multiscalar_mul` pushes the optional points
unchanged. -/
private theorem extended_points_loop_spec {I J K S SI D DI It : Type}
    (staticInst : core.iter.traits.collect.IntoIterator I S SI)
    (borrowStatic : core.borrow.Borrow S scalar.Scalar)
    (dynamicInst : core.iter.traits.collect.IntoIterator J D DI)
    (borrowDynamic : core.borrow.Borrow D scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«64bit-notables») It)
    (it : It) (qops : List (Option ristretto.RistrettoPoint.«64bit-notables»))
    (hit : pointsInst.iteratorInst.Yields it qops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-notables»))
    (hlen : out.length + qops.length ≤ Usize.max) :
    optional_mixed_multiscalar_mul_loop staticInst borrowStatic dynamicInst borrowDynamic
      pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-notables»)) =>
        r.val = out.val ++ qops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with collect.optionMap_id_spec as ⟨z, hz⟩
    · intro x
      rfl
    subst hz
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^52`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«64bit-notables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«64bit-notables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«64bit-notables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 54)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option ristretto.RistrettoPoint.«64bit-notables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 52 ⦄ := by
  apply spec_some_of_filterMap
  have hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 52 ∧ Q.OnCurve := fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩
  unfold optional_mixed_multiscalar_mul
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h3 as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ _ _ it qops hit (alloc.vec.Vec.new _)
    (by simpa using hqops) as ⟨v, hv⟩
  replace hv : v.val = qops := by rw [hv]; rfl
  step with
    backend.«VartimePrecomputedStraus64bit-notables».optional_mixed_multiscalar_mul_spec _ _ _ _
      (core.iter.traits.collect.IntoIteratorVec _) self static_scalars dynamic_scalars v xs ss
      ys ds v.val hself hself_b hstatic_scalars hdynamic_scalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_static hborrow_dynamic hss hds
      (by rw [hv]; exact hqs) hxs hys (by rw [hv]; exact hqops) (by rw [hv]; exact hstatic)
      (by rw [hv]; exact hdynamic) as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint64bit-notables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«64bit-notables».Insts

namespace Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint32bit-notables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeRistrettoPrecomputation`: a
precomputation of the points the input yields (through `borrow`); limbs `< 2^26` in, `< 2^27`
out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item ristretto.RistrettoPoint.«32bit-notables»)
    (static_points : I) (ys : List Clause0_Item)
    (ps : List ristretto.RistrettoPoint.«32bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y
          ⦃ (P' : ristretto.RistrettoPoint.«32bit-notables») => P' = P ⦄)
      ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeRistrettoPrecomputation.«32bit-notables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  have hps : ∀ P ∈ ps, P.LimbsLt 26 ∧ P.OnCurve := fun P hP => ⟨hps P hP, hps_on P hP⟩
  unfold new
  have h : pointsInst.into_iter static_points
      ⦃ (it : Clause0_IntoIter) => pointsInst.iteratorInst.Yields it ys ⦄ := hstatic_points
  step with h as ⟨it, hit⟩
  have hpsys := hborrow.length_eq
  apply spec_bind (collect.collectApplyLoop_spec _ borrowInst.borrow it ys hit ps hborrow
    (alloc.vec.Vec.new _) (by simpa using hys))
  intro v hv
  replace hv : v.val = ps := by rw [hv]; rfl
  step with backend.«VartimePrecomputedStraus32bit-notables».new_spec
      (core.iter.traits.collect.IntoIteratorVec _) (core.borrow.Borrow.Blanket _) v v.val ps
      (core.iter.traits.collect.IntoIteratorVec_yields v)
      (by rw [hv]; exact List.forall₂_same.mpr fun P _ =>
        core.borrow.Borrow.Blanket.borrow_spec P)
      hps (by rw [hv, ← hpsys]; exact hys) as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeRistrettoPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeRistrettoPrecomputation.«32bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus32bit-notables».len_spec self

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeRistrettoPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeRistrettoPrecomputation.«32bit-notables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus32bit-notables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

set_option linter.style.longLine false
open «VartimePrecomputedMultiscalarMulVartimeRistrettoPrecomputation32bit-notablesRistrettoPoint32bit-notables»
set_option linter.style.longLine true

/-- The collecting loop of `optional_mixed_multiscalar_mul` pushes the optional points
unchanged. -/
private theorem extended_points_loop_spec {I J K S SI D DI It : Type}
    (staticInst : core.iter.traits.collect.IntoIterator I S SI)
    (borrowStatic : core.borrow.Borrow S scalar.Scalar)
    (dynamicInst : core.iter.traits.collect.IntoIterator J D DI)
    (borrowDynamic : core.borrow.Borrow D scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«32bit-notables») It)
    (it : It) (qops : List (Option ristretto.RistrettoPoint.«32bit-notables»))
    (hit : pointsInst.iteratorInst.Yields it qops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-notables»))
    (hlen : out.length + qops.length ≤ Usize.max) :
    optional_mixed_multiscalar_mul_loop staticInst borrowStatic dynamicInst borrowDynamic
      pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-notables»)) =>
        r.val = out.val ++ qops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_mixed_multiscalar_mul_loop loop
      optional_mixed_multiscalar_mul_loop.body
    step with hnext as ⟨q, ho, hit⟩
    obtain ⟨o, it1⟩ := q
    simp only at ho hit
    subst ho hit
    step with collect.optionMap_id_spec as ⟨z, hz⟩
    · intro x
      rfl
    subst hz
    step with alloc.vec.Vec.push_spec out _
      (by
        have h : out.length < Usize.max := by simp only [List.length_cons] at hlen; omega
        exact h) as ⟨out1, hout1⟩
    apply WP.spec_mono (ih out1 (by
      rw [alloc.vec.Vec.length_of_val_eq_append hout1]
      simp only [List.length_cons] at hlen; omega))
    intro r hr
    rw [hr, hout1, List.append_assoc, List.singleton_append]

/-- `VartimePrecomputedMultiscalarMul::optional_mixed_multiscalar_mul` for
`VartimeRistrettoPrecomputation` (static points `ps`): `none` iff some dynamic point is `none`;
otherwise `∑ s_i • ps_i + ∑ d_i • Q_i` (at most `|ps|` static scalars, the missing ones count
as `0`; as many dynamic scalars as dynamic points; unreduced scalars `< 2^255`); limbs
`< 2^26`. -/
@[step]
theorem optional_mixed_multiscalar_mul_spec
    {I J K Clause0_Item Clause0_IntoIter Clause2_Item Clause2_IntoIter Clause4_IntoIter : Type}
    (staticScalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowStaticInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (dynamicScalarsInst : core.iter.traits.collect.IntoIterator J Clause2_Item Clause2_IntoIter)
    (borrowDynamicInst : core.borrow.Borrow Clause2_Item scalar.Scalar)
    (dynamicPointsInst : core.iter.traits.collect.IntoIterator K
      (Option ristretto.RistrettoPoint.«32bit-notables») Clause4_IntoIter)
    (self : VartimeRistrettoPrecomputation.«32bit-notables») (static_scalars : I)
    (dynamic_scalars : J) (dynamic_points : K)
    (xs : List Clause0_Item) (ss : List scalar.Scalar) (ys : List Clause2_Item)
    (ds : List scalar.Scalar) (qops : List (Option ristretto.RistrettoPoint.«32bit-notables»))
    (hself : self.IsValid) (hself_b : self.LimbsLt 27)
    (hstatic_scalars : staticScalarsInst.Yields static_scalars xs)
    (hdynamic_scalars : dynamicScalarsInst.Yields dynamic_scalars ys)
    (hdynamic_points : dynamicPointsInst.Yields dynamic_points qops)
    (hborrow_static : List.Forall₂
      (fun x s => borrowStaticInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hborrow_dynamic : List.Forall₂
      (fun y s => borrowDynamicInst.borrow y ⦃ (s' : scalar.Scalar) => s' = s ⦄) ys ds)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hds : ∀ s ∈ ds, s.asNat < 2 ^ 255)
    (hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26)
    (hqs_on : ∀ Q, some Q ∈ qops → Q.OnCurve)
    (hxs : xs.length ≤ Usize.max) (hys : ys.length ≤ Usize.max)
    (hqops : qops.length ≤ Usize.max) (hstatic : none ∉ qops → ss.length ≤ self.points.length)
    (hdynamic : none ∉ qops → ds.length = qops.length) :
    optional_mixed_multiscalar_mul staticScalarsInst borrowStaticInst dynamicScalarsInst
      borrowDynamicInst dynamicPointsInst self static_scalars dynamic_scalars dynamic_points
      ⦃ (r : Option ristretto.RistrettoPoint.«32bit-notables») => (none ∈ qops → r = none) ∧
        ∀ qs, qops = qs.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P) ss self.points).sum +
            (List.zipWith (fun s Q => s.asNat • Q.toPoint) ds qs).sum ∧
          R.LimbsLt 26 ⦄ := by
  apply spec_some_of_filterMap
  have hqs : ∀ Q, some Q ∈ qops → Q.LimbsLt 26 ∧ Q.OnCurve := fun Q hQ => ⟨hqs Q hQ, hqs_on Q hQ⟩
  unfold optional_mixed_multiscalar_mul
  have h3 : dynamicPointsInst.into_iter dynamic_points
      ⦃ (it : Clause4_IntoIter) => dynamicPointsInst.iteratorInst.Yields it qops ⦄ :=
    hdynamic_points
  step with h3 as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ _ _ it qops hit (alloc.vec.Vec.new _)
    (by simpa using hqops) as ⟨v, hv⟩
  replace hv : v.val = qops := by rw [hv]; rfl
  step with
    backend.«VartimePrecomputedStraus32bit-notables».optional_mixed_multiscalar_mul_spec _ _ _ _
      (core.iter.traits.collect.IntoIteratorVec _) self static_scalars dynamic_scalars v xs ss
      ys ds v.val hself hself_b hstatic_scalars hdynamic_scalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_static hborrow_dynamic hss hds
      (by rw [hv]; exact hqs) hxs hys (by rw [hv]; exact hqops) (by rw [hv]; exact hstatic)
      (by rw [hv]; exact hdynamic) as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulRistrettoPoint32bit-notables»
end Curve25519Dalek.ristretto.VartimeRistrettoPrecomputation.«32bit-notables».Insts
