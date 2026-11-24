module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.Helpers.ByteValues
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.CompressedEdwardsY

/-- `CompressedEdwardsY::to_bytes`: the bytes. -/
@[step]
theorem to_bytes_spec (self : CompressedEdwardsY) :
    to_bytes self ⦃ (r : Array U8 32#usize) => r = self ⦄ := by
  unfold to_bytes
  step*

end Curve25519Dalek.edwards.CompressedEdwardsY
