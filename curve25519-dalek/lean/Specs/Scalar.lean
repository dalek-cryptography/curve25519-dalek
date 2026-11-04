/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519Dalek.Funs
public import Defs.Iterator
public import Defs.Scalar
public import Subtle
import Proofs.Scalar.Add
import Proofs.Scalar.AddAssign
import Proofs.Scalar.AsBytes
import Proofs.Scalar.ClampInteger
import Proofs.Scalar.ConditionalSelect
import Proofs.Scalar.CtEq
import Proofs.Scalar.Default
import Proofs.Scalar.DivBy2
import Proofs.Scalar.Eq
import Proofs.Scalar.FromBytesModOrder
import Proofs.Scalar.FromBytesModOrderWide
import Proofs.Scalar.FromCanonicalBytes
import Proofs.Scalar.FromHalfWidth
import Proofs.Scalar.FromUnsigned
import Proofs.Scalar.HalfWidthAsScalar
import Proofs.Scalar.HalfWidthDefault
import Proofs.Scalar.HalfWidthEq
import Proofs.Scalar.HalfWidthFromBytes
import Proofs.Scalar.HalfWidthFromUnsigned
import Proofs.Scalar.HalfWidthOne
import Proofs.Scalar.HalfWidthToBytes
import Proofs.Scalar.HalfWidthTryFrom
import Proofs.Scalar.HalfWidthZero
import Proofs.Scalar.HalfWidthZeroize
import Proofs.Scalar.Index
import Proofs.Scalar.Invert
import Proofs.Scalar.InvertBatch
import Proofs.Scalar.InvertBatchAlloc
import Proofs.Scalar.Mul
import Proofs.Scalar.MulAssign
import Proofs.Scalar.Neg
import Proofs.Scalar.One
import Proofs.Scalar.Product
import Proofs.Scalar.Sub
import Proofs.Scalar.SubAssign
import Proofs.Scalar.Sum
import Proofs.Scalar.ToBytes
import Proofs.Scalar.Zero
import Zeroize.Instances
public section

/-! # Specs of `src/scalar.rs`

Spec summary: the items of `scalar.rs` in the crate's public API, with their spec statements, each
restated with `recall` from the theorem proved in `Proofs/Scalar/`, and the axioms that proof
depends on. Items appear in the order of `scalar.rs`. Items outside the public API (`reduce`,
`as_radix_16`, …) are proved in
`Proofs/` but not restated here.

Definitions used: `Scalar.asNat`, `HalfWidthScalar.asNat` (`Defs/Scalar.lean`), `Array.asNat`
(`Defs/Array.lean`), `Iterator.Yields` (`Defs/Iterator.lean`), `L` (`Curve25519/Basic.lean`),
`subtle.Choice.IsValid`, `subtle.CtOption` (`Subtle/`).

Not specified: derived `Clone`/`Copy` impls. Not translated: `Debug`, `Hash`, `from_bits`, `random`,
`hash_from_bytes`, `from_hash`, the `group` and `serde` impls. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar HalfWidthScalar)

namespace Curve25519Dalek.scalar.Scalar

/-- `from_bytes_mod_order`: the 256-bit little-endian value reduced modulo `L`. -/
recall from_bytes_mod_order_spec (bytes : Array U8 32#usize) :
    from_bytes_mod_order bytes ⦃ (r : Scalar) =>
      r.asNat = bytes.asNat 8 % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_mod_order_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `from_bytes_mod_order_wide`: the 512-bit little-endian value reduced modulo `L`. -/
recall from_bytes_mod_order_wide_spec (input : Array U8 64#usize) :
    from_bytes_mod_order_wide input ⦃ (r : Scalar) =>
      r.asNat = input.asNat 8 % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_mod_order_wide_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `from_canonical_bytes`: `Some` exactly for canonical encodings (value below `L`). -/
recall from_canonical_bytes_spec (bytes : Array U8 32#usize) :
    from_canonical_bytes bytes ⦃ (r : subtle.CtOption Scalar) =>
      r.is_some.IsValid ∧ r.value.bytes = bytes ∧
      (bytes.asNat 8 < L → r.is_some = 1#u8) ∧ (L ≤ bytes.asNat 8 → r.is_some = 0#u8) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_canonical_bytes_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

/-- `PartialEq::eq`: equality of the byte encodings. -/
recall eq_spec (self other : Scalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

/-- `ConstantTimeEq::ct_eq`: `1` iff the byte encodings are equal. -/
recall ct_eq_spec (self other : Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c.IsValid ∧ (self = other → c = 1#u8) ∧ (self ≠ other → c = 0#u8) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ct_eq_spec

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

/-- `Index::index`: byte `index`. -/
recall index_spec (self : Scalar) (index : Usize) (hindex : index.val < 32) :
    CoreOpsIndexIndexUsizeU8.index self index ⦃ (r : U8) =>
      r = self.bytes[index.val]! ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms index_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

/-- `MulAssign::mul_assign`: the product modulo `L`. -/
recall mul_assign_spec (self rhs : Scalar) :
    mul_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar

/-- `MulAssign<Scalar> for Scalar`: as for `&Scalar`. -/
recall mul_assign_spec (self rhs : Scalar) :
    mul_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar

namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

/-- `Mul::mul`: the product modulo `L`. -/
recall mul_spec (self rhs : Scalar) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

/-- `Mul<&Scalar> for Scalar`: as for `&Scalar`. -/
recall mul_spec (self rhs : Scalar) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

/-- `Mul<Scalar> for &Scalar`: as for `&Scalar`. -/
recall mul_spec (self rhs : Scalar) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar

/-- `Mul<Scalar> for Scalar`: as for `&Scalar`. -/
recall mul_spec (self rhs : Scalar) :
    mul self rhs ⦃ (r : Scalar) =>
      r.asNat = self.asNat * rhs.asNat % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms mul_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar

/-- `AddAssign::add_assign`: the sum modulo `L`, for reduced inputs. -/
recall add_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignScalar

/-- `AddAssign<Scalar> for Scalar`: as for `&Scalar`. -/
recall add_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add_assign self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignScalar

namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar

/-- `Add::add`: the sum modulo `L`, for reduced inputs. -/
recall add_spec (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar

/-- `Add<&Scalar> for Scalar`: as for `&Scalar`. -/
recall add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar

/-- `Add<Scalar> for &Scalar`: as for `&Scalar`. -/
recall add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar

/-- `Add<Scalar> for Scalar`: as for `&Scalar`. -/
recall add_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    add self rhs ⦃ (r : Scalar) =>
      r.asNat = (self.asNat + rhs.asNat) % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms add_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignSharedAScalar

/-- `SubAssign::sub_assign`: the difference modulo `L`, reduced, for reduced inputs. -/
recall sub_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub_assign self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignSharedAScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignScalar

/-- `SubAssign<Scalar> for Scalar`: as for `&Scalar`. -/
recall sub_assign_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub_assign self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_assign_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignScalar

namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

/-- `Sub::sub`: the difference modulo `L`, reduced, for reduced inputs. -/
recall sub_spec (self rhs : Scalar) (hself : self.asNat < L)
    (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

/-- `Sub<&Scalar> for Scalar`: as for `&Scalar`. -/
recall sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

namespace Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar

/-- `Sub<Scalar> for &Scalar`: as for `&Scalar`. -/
recall sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end Curve25519Dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar

/-- `Sub<Scalar> for Scalar`: as for `&Scalar`. -/
recall sub_spec (self rhs : Scalar) (hself : self.asNat < L) (hrhs : rhs.asNat < L) :
    sub self rhs ⦃ (r : Scalar) =>
      (r.asNat + rhs.asNat) % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sub_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar

namespace Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

/-- `Neg::neg` (for `&Scalar`): the negation modulo `L`, reduced. -/
recall neg_spec (self : Scalar) :
    neg self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end Curve25519Dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar

/-- `Neg::neg` (for `Scalar`): the negation modulo `L`, reduced. -/
recall neg_spec (self : Scalar) :
    neg self ⦃ (r : Scalar) =>
      (r.asNat + self.asNat) % L = 0 ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms neg_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

/-- `conditional_select`: `a` if `choice = 0`, `b` if `choice = 1`, for a valid `choice`. -/
recall conditional_select_spec (a b : Scalar) (choice : subtle.Choice)
    (hchoice : choice.IsValid) :
    conditional_select a b choice ⦃ (r : Scalar) =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms conditional_select_spec

end Curve25519Dalek.scalar.Scalar.Insts.SubtleConditionallySelectable

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumProduct

/-- `Product::product`: the product of the items modulo `L`. -/
recall product_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ss : List Scalar) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss) :
    product borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).prod % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms product_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumProduct

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumSum

/-- `Sum::sum`: the sum of the items modulo `L`, for reduced items. -/
recall sum_spec {T I : Type} (borrowInst : core.borrow.Borrow T Scalar)
    (iterInst : core.iter.traits.iterator.Iterator I T) (iter : I) (xs : List T)
    (ss : List Scalar) (hiter : iterInst.Yields iter xs)
    (hborrow : List.Forall₂ (fun x s => borrowInst.borrow x ⦃ (s' : Scalar) => s' = s ⦄) xs ss)
    (hss : ∀ s ∈ ss, s.asNat < L) :
    sum borrowInst iterInst iter ⦃ (r : Scalar) =>
      r.asNat = (ss.map (·.asNat)).sum % L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms sum_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreIterTraitsAccumSum

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault

/-- `Default::default`: the scalar `0`. -/
recall default_spec :
    default ⦃ (r : Scalar) =>
      r.asNat = 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreDefaultDefault

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

/-- `From<u8>`: the value of `x`. -/
recall from_spec (x : U8) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

/-- `From<u16>`: the value of `x`. -/
recall from_spec (x : U16) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

/-- `From<u32>`: the value of `x`. -/
recall from_spec (x : U32) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

/-- `From<u64>`: the value of `x`. -/
recall from_spec (x : U64) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128

/-- `From<u128>`: the value of `x`. -/
recall from_spec (x : U128) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromU128

namespace Curve25519Dalek.scalar.Scalar.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize`: all bytes `0`. -/
recall zeroize_spec (self : Scalar) :
    zeroize self ⦃ (r : Scalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.scalar.Scalar.Insts.ZeroizeZeroize

namespace Curve25519Dalek.scalar.Scalar

/-- `ZERO`: the scalar `0`. -/
recall ZERO_spec :
    ZERO.asNat = 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `ONE`: the scalar `1`. -/
recall ONE_spec :
    ONE.asNat = 1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ONE_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `to_bytes`: the byte encoding. -/
recall to_bytes_spec (self : Scalar) :
    to_bytes self ⦃ (r : Array U8 32#usize) =>
      r = self.bytes ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `as_bytes`: the byte encoding. -/
recall as_bytes_spec (self : Scalar) :
    as_bytes self ⦃ (r : Array U8 32#usize) =>
      r = self.bytes ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_bytes_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert`: the inverse modulo `L` (reduced), and `0` for `0`. -/
recall invert_spec (self : Scalar) :
    invert self ⦃ (r : Scalar) =>
      (self.asNat % L ≠ 0 → r.asNat * self.asNat % L = 1) ∧
      (self.asNat % L = 0 → r.asNat = 0) ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch`: inverts every (nonzero) input; returns the inverse of their product. -/
recall invert_batch_spec {N : Usize} (inputs : Array Scalar N)
    (hinputs : ∀ i < N.val, inputs[i]!.asNat % L ≠ 0) :
    invert_batch inputs ⦃ (ret : Scalar) (r : Array Scalar N) =>
      (∀ i < N.val, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range N.val, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_batch_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `invert_batch_alloc`: as `invert_batch`, on a slice. -/
recall invert_batch_alloc_spec (inputs : Slice Scalar)
    (hinputs : ∀ i < inputs.length, inputs[i]!.asNat % L ≠ 0) :
    invert_batch_alloc inputs ⦃ (ret : Scalar) (r : Slice Scalar) =>
      r.length = inputs.length ∧
      (∀ i < inputs.length, r[i]!.asNat * inputs[i]!.asNat % L = 1 ∧ r[i]!.asNat < L) ∧
      ret.asNat * (∏ i ∈ Finset.range inputs.length, inputs[i]!.asNat) % L = 1 ∧
      ret.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms invert_batch_alloc_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar.Scalar

/-- `div_by_2`: `b` with `b + b = self` modulo `L`, reduced. -/
recall div_by_2_spec (self : Scalar) (hself : self.asNat < L) :
    div_by_2 self ⦃ (r : Scalar) =>
      2 * r.asNat % L = self.asNat ∧ r.asNat < L ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms div_by_2_spec

end Curve25519Dalek.scalar.Scalar

namespace Curve25519Dalek.scalar

/-- `clamp_integer`: clears the low 3 bits and bit 255, sets bit 254. -/
recall clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (r : Array U8 32#usize) =>
      r.asNat 8 + bytes.asNat 8 % 8 = 2 ^ 254 + bytes.asNat 8 % 2 ^ 254 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms clamp_integer_spec

end Curve25519Dalek.scalar

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault

/-- `Default::default` (derived): the scalar `0`. -/
recall default_spec :
    default ⦃ (r : HalfWidthScalar) =>
      r.asNat = 0 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms default_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreDefaultDefault

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar

/-- `PartialEq::eq` (derived): equality. -/
recall eq_spec (self other : HalfWidthScalar) :
    eq self other ⦃ (b : Bool) =>
      (b = true ↔ self = other) ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreCmpPartialEqHalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

/-- `TryFrom<Scalar> for HalfWidthScalar`: succeeds iff the value is below `2^128`. -/
recall try_from_spec (value : Scalar) :
    try_from value ⦃ (r : core.result.Result HalfWidthScalar Unit) =>
      (value.asNat < 2 ^ 128 → r = .Ok value) ∧ (2 ^ 128 ≤ value.asNat → r = .Err ()) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms try_from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertTryFromScalarTuple

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::ZERO`: `0`. -/
recall ZERO_spec :
    ZERO.asNat = 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ZERO_spec

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::ONE`: `1`. -/
recall ONE_spec :
    ONE.asNat = 1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms ONE_spec

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::from_bytes`: the 128-bit little-endian value. -/
recall from_bytes_spec (bytes : Array U8 16#usize) :
    from_bytes bytes ⦃ (r : HalfWidthScalar) =>
      r.asNat = bytes.asNat 8 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_bytes_spec

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::as_scalar`: the same value. -/
recall as_scalar_spec (self : HalfWidthScalar) :
    as_scalar self ⦃ (r : Scalar) =>
      r.asNat = self.asNat ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms as_scalar_spec

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar

/-- `HalfWidthScalar::to_bytes`: the low 16 bytes. -/
recall to_bytes_spec (self : HalfWidthScalar) :
    to_bytes self ⦃ (r : Array U8 16#usize) =>
      r.asNat 8 = self.asNat % 2 ^ 128 ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms to_bytes_spec

end Curve25519Dalek.scalar.HalfWidthScalar

namespace Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromHalfWidthScalar

/-- `From<HalfWidthScalar> for Scalar`: the same value. -/
recall from_spec (x : HalfWidthScalar) :
    «from» x ⦃ (r : Scalar) =>
      r.asNat = x.asNat ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.Scalar.Insts.CoreConvertFromHalfWidthScalar

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

/-- `From<u8> for HalfWidthScalar`: the value of `x`. -/
recall from_spec (x : U8) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU8

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

/-- `From<u16> for HalfWidthScalar`: the value of `x`. -/
recall from_spec (x : U16) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU16

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

/-- `From<u32> for HalfWidthScalar`: the value of `x`. -/
recall from_spec (x : U32) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU32

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

/-- `From<u64> for HalfWidthScalar`: the value of `x`. -/
recall from_spec (x : U64) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU64

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

/-- `From<u128> for HalfWidthScalar`: the value of `x`. -/
recall from_spec (x : U128) :
    «from» x ⦃ (r : HalfWidthScalar) =>
      r.asNat = x.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms from_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.CoreConvertFromU128

namespace Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize

/-- `Zeroize::zeroize` for `HalfWidthScalar`: all bytes `0`. -/
recall zeroize_spec (self : HalfWidthScalar) :
    zeroize self ⦃ (r : HalfWidthScalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.zeroize] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms zeroize_spec

end Curve25519Dalek.scalar.HalfWidthScalar.Insts.ZeroizeZeroize
