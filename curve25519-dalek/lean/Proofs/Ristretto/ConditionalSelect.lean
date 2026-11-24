module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Representation.Scalar
public import Proofs.Curve25519.Edwards.Basepoint
public import Proofs.External.Subtle
import Proofs.Edwards.ConditionalSelect
import Proofs.Edwards.Zeroize
public section

/-! # `ConditionallySelectable` and `Zeroize` for `RistrettoPoint` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«64bit-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    edwards.EdwardsPoint.«64bit-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.SubtleConditionallySelectable

/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«32bit-tables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    edwards.EdwardsPoint.«32bit-tables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«64bit-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«64bit-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«64bit-tables».Insts.ZeroizeZeroize.zeroize_spec
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«32bit-tables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«32bit-tables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«32bit-tables».Insts.ZeroizeZeroize.zeroize_spec
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-tables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.SubtleConditionallySelectable

open edwards in
/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«64bit-notables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    EdwardsPoint.«64bit-notables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.SubtleConditionallySelectable

open edwards in
/-- `ConditionallySelectable for RistrettoPoint`: `a` if `choice = 0`, `b` if `choice = 1`. -/
@[step]
theorem conditional_select_spec (a b : ristretto.RistrettoPoint.«32bit-notables»)
    (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ := by
  unfold conditional_select
  step with
    EdwardsPoint.«32bit-notables».Insts.SubtleConditionallySelectable.conditional_select_spec
    a b choice hchoice as ⟨r, h1, h2⟩
  exact ⟨h1, h2⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.SubtleConditionallySelectable

namespace ristretto.RistrettoPoint.«64bit-notables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«64bit-notables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«64bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 52 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«64bit-notables».Insts.ZeroizeZeroize.zeroize_spec
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«64bit-notables».Insts.ZeroizeZeroize

namespace ristretto.RistrettoPoint.«32bit-notables».Insts.ZeroizeZeroize

/-- `Zeroize for RistrettoPoint` leaves the neutral element. -/
@[step]
theorem zeroize_spec (self : ristretto.RistrettoPoint.«32bit-notables») :
    zeroize self ⦃ (r : ristretto.RistrettoPoint.«32bit-notables») =>
      r.OnCurve ∧ r.toPoint = 0 ∧ r.LimbsLt 26 ⦄ := by
  unfold zeroize
  step with edwards.EdwardsPoint.«32bit-notables».Insts.ZeroizeZeroize.zeroize_spec
    self as ⟨r, h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

end ristretto.RistrettoPoint.«32bit-notables».Insts.ZeroizeZeroize

end Curve25519Dalek
