/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public import Defs.Edwards
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

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableAffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTable.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec Q hQ hQon)
    4#u32 4 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 8#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 8 * i = 2 * 4 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableAffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^4`): row `i` is the lookup table of
`2^(8 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTable.«i686-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTable.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.i686.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec Q hQ hQon)
    4#u32 4 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 8#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 8 * i = 2 * 4 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTable.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix32AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix32.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec Q hQ hQon)
    5#u32 5 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 16#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 10 * i = 2 * 5 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix32AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^5`): row `i` is the lookup table of
`2^(10 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix32.«i686-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix32.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.i686.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec Q hQ hQon)
    5#u32 5 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 16#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 10 * i = 2 * 5 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix32.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix64AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix64.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec Q hQ hQon)
    6#u32 6 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 32#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 12 * i = 2 * 6 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix64AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^6`): row `i` is the lookup table of
`2^(12 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix64.«i686-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix64.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.i686.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec Q hQ hQon)
    6#u32 6 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 32#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 12 * i = 2 * 6 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix64.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix128AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix128.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec Q hQ hQon)
    7#u32 7 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 64#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 14 * i = 2 * 7 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix128AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^7`): row `i` is the lookup table of
`2^(14 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix128.«i686-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix128.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.i686.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec Q hQ hQon)
    7#u32 7 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 64#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 14 * i = 2 * 7 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix128.«i686-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»

open window.«LookupTableRadix256AffineNielsPointx86_64-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`; limbs `< 2^52` in, `< 2^54` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«x86_64-tables») (hbasepoint : basepoint.LimbsLt 52)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«x86_64-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 54 ⦄ := by
  unfold create
  unfold window.LookupTableRadix256.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«x86_64-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointx86_64-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 54)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointx86_64-tables».from_spec Q hQ hQon)
    8#u32 8 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 128#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 16 * i = 2 * 8 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointx86_64-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«x86_64-tables».Insts

namespace Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts
namespace «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»

open window.«LookupTableRadix256AffineNielsPointi686-tables».Insts in
/-- `BasepointTable::create` (radix `2^8`): row `i` is the lookup table of
`2^(16 i) • basepoint`; limbs `< 2^26` in, `< 2^27` out. -/
@[step]
theorem create_spec (basepoint : EdwardsPoint.«i686-tables») (hbasepoint : basepoint.LimbsLt 26)
    (hon : basepoint.OnCurve) :
    create basepoint ⦃ (r : EdwardsBasepointTableRadix256.«i686-tables») =>
      r.Represents basepoint.toPoint ∧ r.LimbsLt 27 ⦄ := by
  unfold create
  unfold window.LookupTableRadix256.Insts.CoreDefaultDefault.default
  step with AffineNielsPoint.«i686-tables».Insts.CoreDefaultDefault.default_spec as ⟨d, hd⟩
  have h := basepointTable.i686.createLoop_spec
    «CoreConvertFromSharedAEdwardsPointi686-tables».«from»
    (fun t P => t.Represents P) (fun t => t.LimbsLt 27)
    (fun Q hQ hQon => «CoreConvertFromSharedAEdwardsPointi686-tables».from_spec Q hQ hQon)
    8#u32 8 rfl (by decide) (by decide) (Array.repeat 32#usize (Array.repeat 128#usize d))
    basepoint hbasepoint hon
  apply spec_bind h
  intro a ha
  simp only [WP.spec_ok]
  refine ⟨fun i hi => ?_, fun i hi => (ha i hi).2⟩
  rw [show 16 * i = 2 * 8 * i by ring]
  exact (ha i hi).1

end «Curve25519_dalekTraitsBasepointTableEdwardsPointi686-tables»
end Curve25519Dalek.edwards.EdwardsBasepointTableRadix256.«i686-tables».Insts

