/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.ScalarMul
public section

/-! # `VartimePrecomputedStraus::len` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]
  exact hself.length_eq

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end VartimePrecomputedStraus.«x86_64-tables».Insts

namespace VartimePrecomputedStraus.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]
  exact hself.length_eq

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end VartimePrecomputedStraus.«i686-tables».Insts

namespace VartimePrecomputedStraus.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]
  exact hself.length_eq

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end VartimePrecomputedStraus.«x86_64-no-tables».Insts

namespace VartimePrecomputedStraus.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«i686-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    len self ⦃ (r : Usize) => r.val = ps.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]
  exact hself.length_eq

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end VartimePrecomputedStraus.«i686-no-tables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
