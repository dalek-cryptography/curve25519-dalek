/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
public section

/-! # `VartimePrecomputedStraus::is_empty` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«64bit-tables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.static_lookup_tables.val = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  exact List.length_eq_zero_iff

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end VartimePrecomputedStraus.«64bit-tables».Insts

namespace VartimePrecomputedStraus.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«32bit-tables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.static_lookup_tables.val = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  exact List.length_eq_zero_iff

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end VartimePrecomputedStraus.«32bit-tables».Insts

namespace VartimePrecomputedStraus.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«64bit-notables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.static_lookup_tables.val = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  exact List.length_eq_zero_iff

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end VartimePrecomputedStraus.«64bit-notables».Insts

namespace VartimePrecomputedStraus.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

/-- `VartimePrecomputedStraus::is_empty`: whether there are no static points. -/
@[step]
theorem is_empty_spec (self : VartimePrecomputedStraus.«32bit-notables») :
    is_empty self ⦃ (r : Bool) => r = decide (self.static_lookup_tables.val = []) ⦄ := by
  unfold is_empty
  step as ⟨b, hb⟩
  rw [hb, decide_eq_decide]
  change self.static_lookup_tables.val.length = 0 ↔ _
  exact List.length_eq_zero_iff

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end VartimePrecomputedStraus.«32bit-notables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
