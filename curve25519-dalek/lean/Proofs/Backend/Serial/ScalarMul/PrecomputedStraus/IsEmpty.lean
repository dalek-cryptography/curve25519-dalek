/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
public import Defs.ScalarMul
public section

/-! # `VartimePrecomputedStraus::is_empty` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«x86_64-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  rw [hself.length_eq, List.length_eq_zero_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-tables»
end VartimePrecomputedStraus.«x86_64-tables».Insts

namespace VartimePrecomputedStraus.«i686-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«i686-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  rw [hself.length_eq, List.length_eq_zero_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-tables»
end VartimePrecomputedStraus.«i686-tables».Insts

namespace VartimePrecomputedStraus.«x86_64-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«x86_64-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  rw [hself.length_eq, List.length_eq_zero_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointx86_64-no-tables»
end VartimePrecomputedStraus.«x86_64-no-tables».Insts

namespace VartimePrecomputedStraus.«i686-no-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«i686-no-tables»)
    (ps : List curve25519.edwards.Point)
    (hself : self.Represents ps) :
    is_empty self ⦃ (r : Bool) => r = decide (ps = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  rw [hself.length_eq, List.length_eq_zero_iff]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPointi686-no-tables»
end VartimePrecomputedStraus.«i686-no-tables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
