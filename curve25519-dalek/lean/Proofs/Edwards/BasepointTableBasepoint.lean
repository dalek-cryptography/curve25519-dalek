module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.AddAffineNiels
import Proofs.Backend.Serial.CurveModels.CompletedAsExtended
import Proofs.Edwards.Identity
import Proofs.Helpers.StepSpecs
import Proofs.Window.LookupTableSelect
import Proofs.Window.LookupTableRadix32Select
import Proofs.Window.LookupTableRadix64Select
import Proofs.Window.LookupTableRadix128Select
import Proofs.Window.LookupTableRadix256Select
public section

/-! # `BasepointTable::basepoint` (the five basepoint tables)

`identity + select(row 0, 1)`: entry `0` of row `0`, i.e. `1 • 2^0 • P`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models
open Curve25519Dalek.«Shared0EdwardsPoint64bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint64bit-tablesCompletedPoint64bit-tables»
  (add_spec)

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^4`): the table's point `self.point`;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTable.«64bit-tables») (hself : self.LimbsLt 54)
    (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (8 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableAffineNielsPoint64bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^4`): the table's point `self.point`;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTable.«32bit-tables») (hself : self.LimbsLt 27)
    (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (8 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableAffineNielsPoint32bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^5`): the table's point `self.point`;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix32.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (10 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix32AffineNielsPoint64bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^5`): the table's point `self.point`;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix32.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (10 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix32AffineNielsPoint32bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^6`): the table's point `self.point`;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix64.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (12 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix64AffineNielsPoint64bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^6`): the table's point `self.point`;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix64.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (12 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix64AffineNielsPoint32bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^7`): the table's point `self.point`;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix128.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (14 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix128AffineNielsPoint64bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^7`): the table's point `self.point`;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix128.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (14 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix128AffineNielsPoint32bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^8`): the table's point `self.point`;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix256.«64bit-tables»)
    (hself : self.LimbsLt 54) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«64bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«64bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (16 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix256AffineNielsPoint64bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint64bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPoint32bit-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPoint32bit-tablesCompletedPoint32bit-tables»
  (add_spec)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^8`): the table's point `self.point`;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix256.«32bit-tables»)
    (hself : self.LimbsLt 27) (hP : self.IsTable) :
    basepoint self ⦃ (r : EdwardsPoint.«32bit-tables») =>
      r.OnCurve ∧ r.toPoint = self.point ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«32bit-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (16 * 0) • self.point = self.point by simp] at hP0
  step with window.«LookupTableRadix256AffineNielsPoint32bit-tables».select_spec lt 1#i8 self.point
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) as ⟨q, hqon, hq, hqb⟩
  step with add_spec e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPoint32bit-tables».as_extended_spec as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul self.point

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

