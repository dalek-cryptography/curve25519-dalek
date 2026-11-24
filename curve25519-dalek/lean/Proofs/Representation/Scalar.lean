module
public import ForHumans.Specs.Representation.Scalar
import all ForHumans.Specs.Representation.Scalar
public import Curve25519Dalek.Types
public import Proofs.Representation.Array
public section

/-! # The value of a `Scalar` (audited) -/

open Aeneas.Std

namespace Curve25519Dalek

theorem scalar.Scalar.asNat_def (self : scalar.Scalar) : self.asNat = self.bytes.asNat 8 := by
  unfold scalar.Scalar.asNat
  rfl

theorem scalar.HalfWidthScalar.asNat_def (self : scalar.HalfWidthScalar) :
    self.asNat = scalar.Scalar.asNat self := by
  unfold scalar.HalfWidthScalar.asNat
  rfl

theorem scalar.Scalar.isCanonical_of_eq {s : scalar.Scalar} {n : ℕ} (h : s.asNat = n)
    (hn : n < curve25519.L) : s.IsCanonical := by
  unfold scalar.Scalar.IsCanonical
  omega

end Curve25519Dalek
