/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
import Proofs.Constants.BasepointOrder
import Proofs.Edwards.IsIdentity
import Proofs.Edwards.Mul
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek.edwards

namespace «EdwardsPointx86_64-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«x86_64-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPointx86_64-tables»

namespace «EdwardsPointi686-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^26`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«i686-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPointi686-tables»

namespace «EdwardsPointx86_64-no-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^52`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«x86_64-no-tables») (hself : self.LimbsLt 52)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPointx86_64-no-tables»

namespace «EdwardsPointi686-no-tables»

/-- `EdwardsPoint::is_torsion_free`: `L • P = 0` (multiplication by the unreduced
`BASEPOINT_ORDER`); limbs `< 2^26`. -/
@[step]
theorem is_torsion_free_spec (self : EdwardsPoint.«i686-no-tables») (hself : self.LimbsLt 26)
    (hon : self.OnCurve) :
    is_torsion_free self ⦃ (b : Bool) => b = true ↔ L • self.toPoint = 0 ⦄ := by
  unfold is_torsion_free
  have hL : constants.BASEPOINT_ORDER.asNat < 2 ^ 255 := by
    rw [constants.BASEPOINT_ORDER_spec]; exact L_lt_two_pow_253.trans (by norm_num)
  step as ⟨ep, hepon, hep, hepb⟩
  step as ⟨b, hb⟩
  rw [hb, hep, constants.BASEPOINT_ORDER_spec]

end «EdwardsPointi686-no-tables»

end Curve25519Dalek.edwards
