module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
import Proofs.Edwards.OptionalMultiscalarMul
import Proofs.Helpers.Collect
import Proofs.Helpers.Iterator
import Proofs.Helpers.Vec
public section

/-! # `VartimeMultiscalarMul for RistrettoPoint`

The patched wrapper collects the optional points into a vector (`Option::map` with the
identity closure), calls the Edwards `optional_multiscalar_mul` on it and maps the result back
with the `RistrettoPoint` constructor (the identity). -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.ristretto.RistrettoPoint.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint64bit-tables»

/-- The collecting loop pushes the optional points unchanged. -/
private theorem extended_points_loop_spec {I J Item SI It : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item SI)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option RistrettoPoint.«64bit-tables») It)
    (it : It) (ops : List (Option RistrettoPoint.«64bit-tables»))
    (hit : pointsInst.iteratorInst.Yields it ops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    optional_multiscalar_mul_loop scalarsInst borrowInst pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-tables»)) =>
        r.val = out.val ++ ops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
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

open edwards.EdwardsPoint.«64bit-tables».Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-tables» renaming
  optional_multiscalar_mul_spec → edwards_spec in
/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«64bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«64bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«64bit-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.LimbsLt 52 ⦄ := by
  have hops : ops.length ≤ Usize.max := hlen ▸ hxs
  unfold optional_multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ it ops hit (alloc.vec.Vec.new _) (by simpa using hops)
    as ⟨v, hv⟩
  replace hv : v.val = ops := by rw [hv]; rfl
  step with edwards_spec _ _ (core.iter.traits.collect.IntoIteratorVec _) scalars v xs v.val ss
      hscalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_scalars hss
      (by rw [hv]; exact hps) (by rw [hv]; exact hps_on) hxs
      (by rw [hv]; exact hlen)
    as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint64bit-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«64bit-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint32bit-tables»

/-- The collecting loop pushes the optional points unchanged. -/
private theorem extended_points_loop_spec {I J Item SI It : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item SI)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option RistrettoPoint.«32bit-tables») It)
    (it : It) (ops : List (Option RistrettoPoint.«32bit-tables»))
    (hit : pointsInst.iteratorInst.Yields it ops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-tables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    optional_multiscalar_mul_loop scalarsInst borrowInst pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-tables»)) =>
        r.val = out.val ++ ops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
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

open edwards.EdwardsPoint.«32bit-tables».Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-tables» renaming
  optional_multiscalar_mul_spec → edwards_spec in
/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«32bit-tables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«32bit-tables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«32bit-tables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.LimbsLt 26 ⦄ := by
  have hops : ops.length ≤ Usize.max := hlen ▸ hxs
  unfold optional_multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ it ops hit (alloc.vec.Vec.new _) (by simpa using hops)
    as ⟨v, hv⟩
  replace hv : v.val = ops := by rw [hv]; rfl
  step with edwards_spec _ _ (core.iter.traits.collect.IntoIteratorVec _) scalars v xs v.val ss
      hscalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_scalars hss
      (by rw [hv]; exact hps) (by rw [hv]; exact hps_on) hxs
      (by rw [hv]; exact hlen)
    as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint32bit-tables»
end Curve25519Dalek.ristretto.RistrettoPoint.«32bit-tables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint64bit-notables»

/-- The collecting loop pushes the optional points unchanged. -/
private theorem extended_points_loop_spec {I J Item SI It : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item SI)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option RistrettoPoint.«64bit-notables») It)
    (it : It) (ops : List (Option RistrettoPoint.«64bit-notables»))
    (hit : pointsInst.iteratorInst.Yields it ops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-notables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    optional_multiscalar_mul_loop scalarsInst borrowInst pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«64bit-notables»)) =>
        r.val = out.val ++ ops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
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

open edwards.EdwardsPoint.«64bit-notables».Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint64bit-notables» renaming
  optional_multiscalar_mul_spec → edwards_spec in
/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`); limbs `< 2^52`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«64bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«64bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 52)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«64bit-notables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.LimbsLt 52 ⦄ := by
  have hops : ops.length ≤ Usize.max := hlen ▸ hxs
  unfold optional_multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ it ops hit (alloc.vec.Vec.new _) (by simpa using hops)
    as ⟨v, hv⟩
  replace hv : v.val = ops := by rw [hv]; rfl
  step with edwards_spec _ _ (core.iter.traits.collect.IntoIteratorVec _) scalars v xs v.val ss
      hscalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_scalars hss
      (by rw [hv]; exact hps) (by rw [hv]; exact hps_on) hxs
      (by rw [hv]; exact hlen)
    as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint64bit-notables»
end Curve25519Dalek.ristretto.RistrettoPoint.«64bit-notables».Insts

namespace Curve25519Dalek.ristretto.RistrettoPoint.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint32bit-notables»

/-- The collecting loop pushes the optional points unchanged. -/
private theorem extended_points_loop_spec {I J Item SI It : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Item SI)
    (borrowInst : core.borrow.Borrow Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
      (Option RistrettoPoint.«32bit-notables») It)
    (it : It) (ops : List (Option RistrettoPoint.«32bit-notables»))
    (hit : pointsInst.iteratorInst.Yields it ops)
    (out : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-notables»))
    (hlen : out.length + ops.length ≤ Usize.max) :
    optional_multiscalar_mul_loop scalarsInst borrowInst pointsInst it out
      ⦃ (r : alloc.vec.Vec (Option edwards.EdwardsPoint.«32bit-notables»)) =>
        r.val = out.val ++ ops ⦄ := by
  induction hit generalizing out with
  | nil hnext =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
    step with hnext as ⟨q, hq⟩
    obtain ⟨o, it1⟩ := q
    simp only at hq
    subst hq
    simp
  | cons hnext _ ih =>
    unfold optional_multiscalar_mul_loop loop
      optional_multiscalar_mul_loop.body
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

open edwards.EdwardsPoint.«32bit-notables».Insts in
open «Curve25519_dalekTraitsVartimeMultiscalarMulEdwardsPoint32bit-notables» renaming
  optional_multiscalar_mul_spec → edwards_spec in
/-- `VartimeMultiscalarMul::optional_multiscalar_mul` for `RistrettoPoint`: `none` iff some point
is `none`; otherwise `∑ s_i • P_i` over the scalars and points, which must be equally many (the
patched `assert_eq!`; unreduced scalars `< 2^255`); limbs `< 2^26`. -/
@[step]
theorem optional_multiscalar_mul_spec {I J Clause0_Item Clause0_IntoIter Clause2_IntoIter : Type}
    (scalarsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowScalarInst : core.borrow.Borrow Clause0_Item scalar.Scalar)
    (pointsInst : core.iter.traits.collect.IntoIterator J
        (Option ristretto.RistrettoPoint.«32bit-notables»)
      Clause2_IntoIter)
    (scalars : I) (points : J) (xs : List Clause0_Item)
    (ops : List (Option ristretto.RistrettoPoint.«32bit-notables»)) (ss : List scalar.Scalar)
    (hscalars : scalarsInst.Yields scalars xs) (hpoints : pointsInst.Yields points ops)
    (hborrow_scalars : List.Forall₂
      (fun x s => borrowScalarInst.borrow x ⦃ (s' : scalar.Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < 2 ^ 255) (hps : ∀ P, some P ∈ ops → P.LimbsLt 26)
    (hps_on : ∀ P, some P ∈ ops → P.OnCurve)
    (hxs : xs.length ≤ Usize.max)
    (hlen : xs.length = ops.length) :
    optional_multiscalar_mul scalarsInst borrowScalarInst pointsInst scalars points
      ⦃ (r : Option ristretto.RistrettoPoint.«32bit-notables») => (none ∈ ops → r = none) ∧
        ∀ ps, ops = ps.map some → ∃ R, r = some R ∧ R.OnCurve ∧ R.toPoint =
          (List.zipWith (fun s P => s.asNat • P.toPoint) ss ps).sum ∧
          R.LimbsLt 26 ⦄ := by
  have hops : ops.length ≤ Usize.max := hlen ▸ hxs
  unfold optional_multiscalar_mul
  have hpoints' : pointsInst.into_iter points
      ⦃ (it : Clause2_IntoIter) => pointsInst.iteratorInst.Yields it ops ⦄ := hpoints
  step with hpoints' as ⟨it, hit⟩
  step with extended_points_loop_spec _ _ _ it ops hit (alloc.vec.Vec.new _) (by simpa using hops)
    as ⟨v, hv⟩
  replace hv : v.val = ops := by rw [hv]; rfl
  step with edwards_spec _ _ (core.iter.traits.collect.IntoIteratorVec _) scalars v xs v.val ss
      hscalars
      (core.iter.traits.collect.IntoIteratorVec_yields v) hborrow_scalars hss
      (by rw [hv]; exact hps) (by rw [hv]; exact hps_on) hxs
      (by rw [hv]; exact hlen)
    as ⟨o, hnone, hsome⟩
  rw [hv] at hnone hsome
  refine spec_mono (collect.optionMap_id_spec _ _ ?_ o) ?_
  · intro x
    rfl
  rintro r rfl
  exact ⟨hnone, hsome⟩

end «Curve25519_dalekTraitsVartimeMultiscalarMulRistrettoPoint32bit-notables»
end Curve25519Dalek.ristretto.RistrettoPoint.«32bit-notables».Insts
