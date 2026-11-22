/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Constants.BasepointOrder
import Proofs.Edwards.IsIdentity
import Proofs.Edwards.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPoint64bit-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«64bit-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPoint64bit-tables»

namespace «EdwardsPoint32bit-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^26`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«32bit-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPoint32bit-tables»

namespace «EdwardsPoint64bit-notables»

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«64bit-notables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPoint64bit-notables»

namespace «EdwardsPoint32bit-notables»

/-- `EdwardsPoint::is_torsion_free`: `L • self = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^26`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«32bit-notables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (r : Bool) => r = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPoint32bit-notables»

end Curve25519Dalek.edwards
