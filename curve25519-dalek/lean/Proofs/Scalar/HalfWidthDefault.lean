module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Scalar
import Proofs.Scalar.Default
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault

@[step]
theorem default_spec :
    default ⦃ (r : HalfWidthScalar) =>
      r.asNat < 2 ^ 128 ∧ r.asNat = 0 ⦄ := by
  unfold default
  step as ⟨s, hs⟩
  have h : HalfWidthScalar.asNat s = 0 := by rw [scalar.HalfWidthScalar.asNat_def]; exact hs
  exact ⟨by rw [h]; norm_num, h⟩

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault
