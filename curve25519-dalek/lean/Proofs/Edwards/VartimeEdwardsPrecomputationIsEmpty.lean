module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.VartimePrecomputedStrausIsEmpty
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«64bit-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus64bit-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«32bit-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus32bit-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«64bit-notables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus64bit-notables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«32bit-notables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStraus32bit-notables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts
