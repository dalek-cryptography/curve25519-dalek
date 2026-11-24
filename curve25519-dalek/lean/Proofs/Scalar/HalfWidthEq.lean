module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
import Proofs.Scalar.Eq
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar

@[step]
theorem eq_spec (self other : HalfWidthScalar) :
    eq self other ⦃ (r : Bool) =>
      (r = true ↔ self = other) ⦄ := by
  unfold eq
  step*

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar
