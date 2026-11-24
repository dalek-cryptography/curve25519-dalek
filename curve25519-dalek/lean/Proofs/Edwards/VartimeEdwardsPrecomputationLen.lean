module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import Proofs.ToAeneas.Iterator
public import Proofs.Representation.Scalar
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
import Proofs.Backend.VartimePrecomputedStrausLen
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«64bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus64bit-tables».len_spec self

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«32bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus32bit-tables».len_spec self

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«64bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus64bit-notables».len_spec self

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«64bit-notables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«32bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.points.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStraus32bit-notables».len_spec self

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«32bit-notables».Insts


