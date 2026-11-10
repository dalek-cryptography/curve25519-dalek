/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import ToAeneas.Iterator
public import Defs.Scalar
public import Defs.ScalarMul
import Proofs.Backend.VartimePrecomputedStrausIsEmpty
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«x86_64-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStrausx86_64-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«i686-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStrausi686-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«x86_64-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStrausx86_64-no-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«x86_64-no-tables».Insts

namespace Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedMultiscalarMul::is_empty` for `VartimeEdwardsPrecomputation`: whether
there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimeEdwardsPrecomputation.«i686-no-tables») :
    is_empty self ⦃ (r : Bool) => r = true ↔ self.points = [] ⦄ := by
  unfold is_empty
  refine spec_mono (backend.«VartimePrecomputedStrausi686-no-tables».is_empty_spec self) ?_
  intro r h
  rw [h, decide_eq_true_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end Curve25519Dalek.edwards.VartimeEdwardsPrecomputation.«i686-no-tables».Insts
