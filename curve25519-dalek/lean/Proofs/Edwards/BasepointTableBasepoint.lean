/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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
open Curve25519Dalek.«Shared0EdwardsPointx86_64-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointx86_64-tablesCompletedPointx86_64-tables»
  (add_spec_point)

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^4`): the point `P` the table represents;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTable.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (8 * 0) • P = P by simp] at hP0
  step with window.«LookupTableAffineNielsPointx86_64-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^4`): the point `P` the table represents;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTable.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (8 * 0) • P = P by simp] at hP0
  step with window.«LookupTableAffineNielsPointi686-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointi686-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^5`): the point `P` the table represents;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix32.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (10 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix32AffineNielsPointx86_64-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^5`): the point `P` the table represents;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix32.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (10 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix32AffineNielsPointi686-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointi686-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^6`): the point `P` the table represents;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix64.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (12 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix64AffineNielsPointx86_64-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^6`): the point `P` the table represents;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix64.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (12 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix64AffineNielsPointi686-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointi686-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^7`): the point `P` the table represents;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix128.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (14 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix128AffineNielsPointx86_64-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^7`): the point `P` the table represents;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix128.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (14 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix128AffineNielsPointi686-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) (by decide) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointi686-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^8`): the point `P` the table represents;
limbs `< 2^52`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix256.«x86_64-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 54) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«x86_64-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 52 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«x86_64-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (16 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix256AffineNielsPointx86_64-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointx86_64-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
open Curve25519Dalek.«Shared0EdwardsPointi686-tables».Insts
open «CoreOpsArithAddSharedAAffineNielsPointi686-tablesCompletedPointi686-tables»
  (add_spec_point)
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open scoped Helpers.IndexStep in
/-- `BasepointTable::basepoint` (radix `2^8`): the point `P` the table represents;
limbs `< 2^26`. -/
@[step]
theorem basepoint_spec (self : EdwardsBasepointTableRadix256.«i686-tables»)
    (P : curve25519.edwards.Point) (hself : self.LimbsLt 27) (hP : self.Represents P) :
    basepoint self ⦃ (r : EdwardsPoint.«i686-tables») =>
      r.OnCurve ∧ r.toPoint = P ∧ r.LimbsLt 26 ⦄ := by
  unfold basepoint
  step with EdwardsPoint.«i686-tables».Insts.Curve25519_dalekTraitsIdentity.identity_spec_point
    as ⟨e, heon, he, heb⟩
  step as ⟨lt, hlt⟩
  have hP0 := hP 0 (by decide)
  rw [show 2 ^ (16 * 0) • P = P by simp] at hP0
  step with window.«LookupTableRadix256AffineNielsPointi686-tables».select_spec lt 1#i8 P
    (hlt ▸ hself 0 (by decide)) (hlt ▸ hP0) as ⟨q, hqon, hq, hqb⟩
  step with add_spec_point e q heb hqb heon hqon as ⟨c, hcon, hc, hcb⟩
  step with «CompletedPointi686-tables».as_extended_spec_point as ⟨r, hron, hr, hrb⟩
  refine ⟨hron, ?_, hrb⟩
  rw [hr, hc, he, hq, zero_add]
  exact one_zsmul P

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

