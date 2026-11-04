/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Curve25519.Edwards.Encoding
import Proofs.Edwards.CompressedIdentity
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault

/-- `Default for CompressedEdwardsY`: the identity `[1, 0, …, 0]`, value `1`. -/
@[step]
theorem default_spec :
    default ⦃ (r : CompressedEdwardsY) => r.asNat = 1 ⦄ := by
  unfold default
  step*

/-- `Default for CompressedEdwardsY` is the encoding of the neutral element. -/
theorem default_spec_point :
    default ⦃ (r : CompressedEdwardsY) => r.asNat = encode 0 ⦄ :=
  spec_mono default_spec fun r hr => by rw [hr, encode_zero]

end Curve25519Dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault
