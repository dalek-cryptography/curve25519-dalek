module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.VartimePrecomputedStrausNew
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«64bit-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«64bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«64bit-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«64bit-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStraus64bit-tables».new_spec _ _ _ ys ps hstatic_points
    hborrow (fun P hP => ⟨hps P hP, hps_on P hP⟩) hys as ⟨v, hv, hpts, hvb⟩
  exact ⟨hv, hpts, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«32bit-tables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«32bit-tables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«32bit-tables») => P' = P ⦄) ys
          ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«32bit-tables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStraus32bit-tables».new_spec _ _ _ ys ps hstatic_points
    hborrow (fun P hP => ⟨hps P hP, hps_on P hP⟩) hys as ⟨v, hv, hpts, hvb⟩
  exact ⟨hv, hpts, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«64bit-notables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«64bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«64bit-notables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 52)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«64bit-notables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 54 ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStraus64bit-notables».new_spec _ _ _ ys ps hstatic_points
    hborrow (fun P hP => ⟨hps P hP, hps_on P hP⟩) hys as ⟨v, hv, hpts, hvb⟩
  exact ⟨hv, hpts, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

/-- `VartimePrecomputedMultiscalarMul::new` for `VartimeEdwardsPrecomputation`: a precomputation
of the points the input yields (through `borrow`); limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem new_spec {I Clause0_Item Clause0_IntoIter : Type}
    (pointsInst : core.iter.traits.collect.IntoIterator I Clause0_Item Clause0_IntoIter)
    (borrowInst : core.borrow.Borrow Clause0_Item edwards.EdwardsPoint.«32bit-notables»)
    (static_points : I) (ys : List Clause0_Item) (ps : List edwards.EdwardsPoint.«32bit-notables»)
    (hstatic_points : pointsInst.Yields static_points ys)
    (hborrow : List.Forall₂
      (fun y P => borrowInst.borrow y ⦃ (P' : edwards.EdwardsPoint.«32bit-notables») => P' = P ⦄)
          ys ps)
    (hps : ∀ P ∈ ps, P.LimbsLt 26)
    (hps_on : ∀ P ∈ ps, P.OnCurve) (hys : ys.length ≤ Usize.max) :
    new pointsInst borrowInst static_points
      ⦃ (r : VartimeEdwardsPrecomputation.«32bit-notables») =>
        r.IsValid ∧ r.points = ps.map (·.toPoint) ∧ r.LimbsLt 27 ⦄ := by
  unfold new
  step with backend.«VartimePrecomputedStraus32bit-notables».new_spec _ _ _ ys ps hstatic_points
    hborrow (fun P hP => ⟨hps P hP, hps_on P hP⟩) hys as ⟨v, hv, hpts, hvb⟩
  exact ⟨hv, hpts, hvb⟩

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts


