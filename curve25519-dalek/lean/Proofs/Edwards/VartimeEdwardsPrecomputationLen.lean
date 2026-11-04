/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.VartimePrecomputedStrausLen
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«x86_64-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStrausx86_64-tables».len_spec self ps hself

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«i686-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStrausi686-tables».len_spec self ps hself

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStrausx86_64-no-tables».len_spec self ps hself

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::len` for `VartimeEdwardsPrecomputation`: the number of
static points. -/
@[step]
theorem len_spec (self : VartimeEdwardsPrecomputation.«i686-no-tables»)
    (ps : List curve25519.edwards.Point) (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  exact backend.«VartimePrecomputedStrausi686-no-tables».len_spec self ps hself

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts


