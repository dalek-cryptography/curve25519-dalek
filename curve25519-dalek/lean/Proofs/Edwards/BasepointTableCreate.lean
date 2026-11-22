/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Proofs.Helpers.Represents
public import Curve25519Dalek.Funs
public import Proofs.Representation.Edwards
import Proofs.Backend.Serial.CurveModels.AffineNielsDefault
import Proofs.Helpers.BasepointTable
import Proofs.Window.LookupTableFrom
import Proofs.Window.LookupTableRadix32From
import Proofs.Window.LookupTableRadix64From
import Proofs.Window.LookupTableRadix128From
import Proofs.Window.LookupTableRadix256From
public section

/-! # `BasepointTable::create` (the five basepoint tables)

Row `i` is the lookup table (`From<&EdwardsPoint>`) of `P`, after which `P := 2^(2 w) • P`; the
generic loop is `basepointTable.createLoop_spec`. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek.backend.serial.curve_models

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open window.«LookupTableAffineNielsPoint64bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTable.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«64bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels
    as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec Q hQ hQon)
    4#u32 4 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 8#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 8 * i = 2 * 4 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open window.«LookupTableAffineNielsPoint32bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTable.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«32bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels as ⟨d,
      hd⟩
  have h := basepointTable.bits32.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec Q hQ hQon)
    4#u32 4 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 8#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 8 * i = 2 * 4 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open window.«LookupTableRadix32AffineNielsPoint64bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix32.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«64bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels
    as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec Q hQ hQon)
    5#u32 5 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 16#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 10 * i = 2 * 5 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open window.«LookupTableRadix32AffineNielsPoint32bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix32.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«32bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels as ⟨d,
      hd⟩
  have h := basepointTable.bits32.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec Q hQ hQon)
    5#u32 5 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 16#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 10 * i = 2 * 5 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open window.«LookupTableRadix64AffineNielsPoint64bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix64.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«64bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels
    as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec Q hQ hQon)
    6#u32 6 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 32#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 12 * i = 2 * 6 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open window.«LookupTableRadix64AffineNielsPoint32bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix64.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«32bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels as ⟨d,
      hd⟩
  have h := basepointTable.bits32.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec Q hQ hQon)
    6#u32 6 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 32#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 12 * i = 2 * 6 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open window.«LookupTableRadix128AffineNielsPoint64bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix128.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«64bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels
    as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec Q hQ hQon)
    7#u32 7 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 64#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 14 * i = 2 * 7 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open window.«LookupTableRadix128AffineNielsPoint32bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix128.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«32bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels as ⟨d,
      hd⟩
  have h := basepointTable.bits32.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec Q hQ hQon)
    7#u32 7 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 64#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 14 * i = 2 * 7 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«32bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»

open window.«LookupTableRadix256AffineNielsPoint64bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«64bit-tables»)
    (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«64bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix256.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«64bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels
    as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint64bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint64bit-tables».from_spec Q hQ hQon)
    8#u32 8 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 128#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 16 * i = 2 * 8 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint64bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«64bit-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»

open window.«LookupTableRadix256AffineNielsPoint32bit-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«32bit-tables»)
    (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«32bit-tables») =>
      r.IsTable ∧ r.point = basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix256.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«32bit-tables».Insts.CoreDefaultDefault.default_toAffineNiels as ⟨d,
      hd⟩
  have h := basepointTable.bits32.createLoop_spec
    «CoreConvertFromSharedAEdwardsPoint32bit-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPoint32bit-tables».from_spec Q hQ hQon)
    8#u32 8 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 128#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine isTable_and_of_rows (fun i hi => ?_) fun i hi => (ha i hi).2
  rw [show 16 * i = 2 * 8 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPoint32bit-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«32bit-tables».Insts

