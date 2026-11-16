/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Aeneas.Std.Scalar.EqOrd
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.WP
public section

/-! # `core::cmp::min` on `usize` -/

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- `core::cmp::min` through the `Ord` instance of `usize`. -/
@[step]
theorem Aeneas.Std.core.cmp.min_Usize_spec (a b : Usize) :
    core.cmp.min core.cmp.OrdUsize a b ⦃ (r : Usize) => r.val = Min.min a.val b.val ⦄ := by
  simp only [core.cmp.min, liftFun2, WP.spec_ok]
  exact core.cmp.impls.OrdUsize.min_val a b
