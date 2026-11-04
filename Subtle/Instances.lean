/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
@[expose] public section
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! # `subtle` for the trait instances generated in `Curve25519Dalek/Funs.lean` -/

namespace Curve25519Dalek

/-- `ct_eq` on byte slices: `Choice(1)` iff the slices are equal. -/
@[step]
theorem Slice.Insts.SubtleConstantTimeEq.ct_eq_U8_spec (a b : Slice Std.U8) :
    _root_.Slice.Insts.SubtleConstantTimeEq.ct_eq U8.Insts.SubtleConstantTimeEq a b ⦃ c =>
      c.IsValid ∧ (a = b → c = 1#u8) ∧ (a ≠ b → c = 0#u8) ⦄ :=
  _root_.Slice.Insts.SubtleConstantTimeEq.ct_eq_spec _
    (fun x y => spec_mono (U8.Insts.SubtleConstantTimeEq.ct_eq_spec x y) (by grind)) a b

end Curve25519Dalek
