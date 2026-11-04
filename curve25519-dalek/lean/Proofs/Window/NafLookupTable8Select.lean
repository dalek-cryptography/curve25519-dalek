/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Window
import Proofs.Helpers.StepSpecs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.window.NafLookupTable8

variable {T : Type} [Inhabited T] [PointRepr T] {n : ℕ}

open scoped Helpers.IndexStep in
/-- `NafLookupTable8::select`: the entry `x / 2`, a representative of `x • P`, for odd `x < 128`. -/
@[step]
theorem select_spec (copyInst : core.marker.Copy T) (self : NafLookupTable8 T) (x : Usize)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt n) (hP : self.Represents P)
    (hx : x.val % 2 = 1 ∧ x.val < 128) :
    select copyInst self x ⦃ (r : T) =>
      PointRepr.OnCurve r ∧ PointRepr.toPoint r = x.val • P ∧ PointRepr.LimbsLt n r ⦄ := by
  unfold select
  step as ⟨b, hb, _⟩
  have hb1 : b = 1#usize := by
    rw [UScalar.eq_equiv, hb, UScalar.val_and, show (1#usize).val = 1 from rfl,
      Nat.and_one_is_mod, hx.1]
  step
  step
  step as ⟨i, hi⟩
  have hi' : i.val < 64 := by scalar_tac
  step as ⟨r, hr⟩
  obtain ⟨hon, hpt⟩ := hP _ hi'
  refine ⟨hr ▸ hon, ?_, hr ▸ hself _ hi'⟩
  rw [hr, hpt, hi]
  congr 1
  omega

end Curve25519Dalek.window.NafLookupTable8
