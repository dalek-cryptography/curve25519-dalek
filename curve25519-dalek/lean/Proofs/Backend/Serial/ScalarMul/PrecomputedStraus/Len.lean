module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
public import ForHumans.Specs.Representation
public import Proofs.Representation.Window
public section

/-! # `VartimePrecomputedStraus::len` -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus

namespace VartimePrecomputedStraus.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«64bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.static_lookup_tables.val.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-tables»
end VartimePrecomputedStraus.«64bit-tables».Insts

namespace VartimePrecomputedStraus.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«32bit-tables») :
    len self ⦃ (r : Usize) => r.val = self.static_lookup_tables.val.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-tables»
end VartimePrecomputedStraus.«32bit-tables».Insts

namespace VartimePrecomputedStraus.«64bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«64bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.static_lookup_tables.val.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint64bit-notables»
end VartimePrecomputedStraus.«64bit-notables».Insts

namespace VartimePrecomputedStraus.«32bit-notables».Insts
namespace «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»

/-- `VartimePrecomputedStraus::len`: the number of static points. -/
@[step]
theorem len_spec (self : VartimePrecomputedStraus.«32bit-notables») :
    len self ⦃ (r : Usize) => r.val = self.static_lookup_tables.val.length ⦄ := by
  unfold len
  rw [WP.spec_ok, alloc.vec.Vec.len_val]

end «Curve25519_dalekTraitsVartimePrecomputedMultiscalarMulEdwardsPoint32bit-notables»
end VartimePrecomputedStraus.«32bit-notables».Insts

end Curve25519Dalek.backend.serial.scalar_mul.precomputed_straus
