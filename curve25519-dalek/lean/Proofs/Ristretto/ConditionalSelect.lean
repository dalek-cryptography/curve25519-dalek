/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Scalar
public import Curve25519.Edwards.Basepoint
public import Subtle
import Proofs.Edwards.ConditionalSelect
import Proofs.Edwards.Zeroize
public section

/-! # `ConditionallySelectable` and `Zeroize` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«x86_64-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    edwards.EdwardsPoint.«x86_64-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«i686-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«i686-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    edwards.EdwardsPoint.«i686-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«x86_64-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«x86_64-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«x86_64-tables».Insts.ZeroizeZeroize.zeroize_spec_point
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«i686-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«i686-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«i686-tables».Insts.ZeroizeZeroize.zeroize_spec_point
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

open edwards in
/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«x86_64-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    EdwardsPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.SubtleConditionallySelectable

open edwards in
/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«i686-no-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    EdwardsPoint.«i686-no-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«x86_64-no-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«x86_64-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«x86_64-no-tables».Insts.ZeroizeZeroize.zeroize_spec_point
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«x86_64-no-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«i686-no-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«i686-no-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«i686-no-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«i686-no-tables».Insts.ZeroizeZeroize.zeroize_spec_point
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«i686-no-tables».Insts.ZeroizeZeroize

end Curve25519Dalek
