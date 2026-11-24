module
public import Proofs.Curve25519.Basic
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
public import Proofs.Representation.Scalar29
import Proofs.Helpers.Scalar
import Proofs.Helpers.Target
import Proofs.Scalar.Scalar52Invert
import Proofs.Scalar.Scalar52Pack
import Proofs.Scalar.Unpack
import Proofs.Scalar.Scalar29Invert
import Proofs.Scalar.Scalar29Pack
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)
open Curve25519Dalek.backend.serial.u64.scalar (montgomeryRadix)

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«64bit-tables_spec» (self : Scalar) :
    invert.«64bit-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ := by
  unfold invert.«64bit-tables»
  step as ⟨u, hu, hub⟩
  step as ⟨v, hv1, hv0, hvL, hvb⟩
  step with Scalar52.pack_spec v hvb (lt_two_pow_256_of_lt_L hvL) as ⟨r, hr⟩
  rw [hr, ← hu]
  exact ⟨hv1, hv0, hvL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«64bit-notables_spec» (self : Scalar) :
    invert.«64bit-notables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  invert.«64bit-tables_spec» self

end Curve25519Dalek.scalar.Scalar


namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«32bit-tables_spec» (self : Scalar) :
    invert.«32bit-tables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ := by
  unfold invert.«32bit-tables»
  step as ⟨u, hu, hub⟩
  step as ⟨v, hv1, hv0, hvL, hvb⟩
  step with Scalar29.pack_spec v hvb (lt_two_pow_256_of_lt_L hvL) as ⟨r, hr⟩
  rw [hr, ← hu]
  exact ⟨hv1, hv0, hvL⟩

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert.«32bit-notables_spec» (self : Scalar) :
    invert.«32bit-notables» self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ :=
  invert.«32bit-tables_spec» self

end Curve25519Dalek.scalar.Scalar
namespace Curve25519Dalek.scalar.Scalar

@[step]
theorem invert_spec (self : Scalar) :
    invert self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄ := by
  unfold invert
  exact dispatch_all_spec
    (invert.«64bit-tables_spec» self)
    (invert.«64bit-notables_spec» self)
    (invert.«32bit-tables_spec» self)
    (invert.«32bit-notables_spec» self)

end Curve25519Dalek.scalar.Scalar
