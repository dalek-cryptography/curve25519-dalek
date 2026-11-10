/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Basic
public import Curve25519.Ristretto.Encoding.Defs
public import Defs.Array
public import Subtle.Contract
public import Aeneas
public section

/-! # Field backends, for proofs shared by all configurations

The point functions (`curve_models`, `edwards`, `ristretto`, …) are translated once per
configuration, but their bodies agree up to the field backend: `FieldElement51` with `u64` limbs
for `«x86_64-tables»` and `«x86_64-no-tables»`, `FieldElement2625` with `u32` limbs for
`«i686-tables»` and `«i686-no-tables»`. A `Backend` bundles what the point proofs use of a field
backend: the element type `F`, its value `toField`, the operations as `Result` functions
(the backend's and those of `field.rs`), and five abstract limb bounds; the operations' specs,
stated with `toField` and the bounds, are propositions (`AddSpec`, `MulSpec`, …) that the
instance files and the generic `field.rs` proofs establish.

| bound   | meaning                                    | `U64`         | `U32`          |
|---------|--------------------------------------------|---------------|----------------|
| `Red`   | output of `mul`, `sub`, `square`, …        | `LimbsLt 52`  | `LimbsLt 26`   |
| `Sum2`  | sum of two `Red`                           | `LimbsLt 53`  | `LimbsLt 27`   |
| `SqIn`  | `square`, `pow2k` input                    | `LimbsLt 54`  | `LimbsLt 27`   |
| `MulIn` | `mul`, `sub`, `neg` input                  | `LimbsLt 54`  | `MulBounded`   |
| `Niels` | coordinates of the Niels points            | `LimbsLt 54`  | `LimbsLt 27`   |

A point function then has a generic counterpart (same body, field calls through the backend,
the result built by a constructor argument `mk`) with a generic spec, proved once. The
translated function of each configuration is `rfl`-equal to the generic one at the instance
(`Proofs/Helpers/Backend/U64.lean`, `…/U32.lean`), whose bounds are by definition the concrete
predicates, so each configuration's statement follows in a few lines. A generic theorem takes
exactly the specs it uses, so that each configuration's theorem depends on the same axioms as
the field specs it uses. -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519

namespace Curve25519Dalek

/-- A field backend: element type, value in `ZMod p`, operations, and limb bounds. -/
structure Backend where
  /-- the field-element type -/
  F : Type
  /-- the represented natural number (unreduced) -/
  asNat : F → ℕ
  /-- the represented element of `ZMod p` -/
  toField : F → ZMod p
  toField_eq : ∀ a, toField a = (asNat a : ZMod p)
  /-- for `getElem!` on slices of field elements -/
  inhF : Inhabited F
  /-- output bound of `mul`, `sub`, `square`, `neg` -/
  Red : F → Prop
  /-- bound of the sum of two `Red` elements -/
  Sum2 : F → Prop
  /-- input bound of `square`, `square2`, `pow2k` -/
  SqIn : F → Prop
  /-- input bound of `mul`, `sub`, `neg` -/
  MulIn : F → Prop
  /-- bound of the coordinates of `ProjectiveNielsPoint` and `AffineNielsPoint` -/
  Niels : F → Prop
  /-- `Add<&FieldElement> for &FieldElement` -/
  add : F → F → Result F
  /-- `Sub<&FieldElement> for &FieldElement` -/
  sub : F → F → Result F
  /-- `Mul<&FieldElement> for &FieldElement` -/
  mul : F → F → Result F
  /-- `FieldElement::square` -/
  square : F → Result F
  /-- `FieldElement::square2`: twice the square -/
  square2 : F → Result F
  /-- `FieldElement::pow2k`: `2^k`-th power -/
  pow2k : F → U32 → Result F
  /-- `Neg for &FieldElement` -/
  neg : F → Result F
  /-- `PartialEq for FieldElement` -/
  eq : F → F → Result Bool
  /-- `ConstantTimeEq for FieldElement` -/
  ctEq : F → F → Result subtle.Choice
  /-- `ConditionallySelectable::conditional_assign` -/
  condAssign : F → F → subtle.Choice → Result F
  /-- `ConditionallyNegatable::conditional_negate` -/
  condNeg : F → subtle.Choice → Result F
  /-- `EDWARDS_D` -/
  constEdwardsD : Result F
  /-- `SQRT_M1` -/
  constSqrtM1 : Result F
  /-- `FieldElement::ONE` -/
  constOne : Result F
  /-- `MINUS_ONE` -/
  constMinusOne : Result F
  /-- `ONE_MINUS_EDWARDS_D_SQUARED` -/
  constOneMinusDSq : Result F
  /-- `EDWARDS_D_MINUS_ONE_SQUARED` -/
  constDMinusOneSq : Result F
  /-- `SQRT_AD_MINUS_ONE` -/
  constSqrtAdMinusOne : Result F
  /-- `INVSQRT_A_MINUS_D` -/
  constInvsqrtAMinusD : Result F
  /-- `APLUS2_OVER_FOUR` -/
  constAplus2OverFour : Result F
  /-- `FieldElement::to_bytes` -/
  toBytes : F → Result (Array U8 32#usize)
  /-- `FieldElement::is_negative` -/
  isNegative : F → Result subtle.Choice
  /-- `FieldElement::is_zero` -/
  isZero : F → Result subtle.Choice
  /-- `FieldElement::pow22501` -/
  pow22501 : F → Result (F × F)
  /-- `FieldElement::pow_p58` -/
  powP58 : F → Result F
  /-- `FieldElement::invert` -/
  invert : F → Result F
  /-- `FieldElement::sqrt_ratio_i` -/
  sqrtRatioI : F → F → Result (subtle.Choice × F)
  /-- `FieldElement::invsqrt` -/
  invsqrt : F → Result (subtle.Choice × F)
  /-- `FieldElement::invert_batch_alloc` -/
  invertBatchAlloc : Slice F → Result (Slice F)
  red_sum2 : ∀ {a}, Red a → Sum2 a
  sum2_sqIn : ∀ {a}, Sum2 a → SqIn a
  sqIn_mulIn : ∀ {a}, SqIn a → MulIn a
  red_niels : ∀ {a}, Red a → Niels a
  niels_mulIn : ∀ {a}, Niels a → MulIn a

namespace Backend

variable (B : Backend)

instance : Inhabited B.F := B.inhF

theorem red_sqIn {a : B.F} (h : B.Red a) : B.SqIn a := B.sum2_sqIn (B.red_sum2 h)

theorem sum2_mulIn {a : B.F} (h : B.Sum2 a) : B.MulIn a := B.sqIn_mulIn (B.sum2_sqIn h)

theorem red_mulIn {a : B.F} (h : B.Red a) : B.MulIn a := B.sum2_mulIn (B.red_sum2 h)

/-! ### Specs of the backend operations -/

/-- `add` of two `Red` elements. -/
abbrev AddSpec : Prop := ∀ a b, B.Red a → B.Red b →
  B.add a b ⦃ r => B.toField r = B.toField a + B.toField b ∧ B.Sum2 r ⦄

/-- `add` of a `Sum2` and a `Red` element. -/
abbrev AddSum2Spec : Prop := ∀ a b, B.Sum2 a → B.Red b →
  B.add a b ⦃ r => B.toField r = B.toField a + B.toField b ∧ B.MulIn r ⦄

/-- `sub` of two `MulIn` elements. -/
abbrev SubSpec : Prop := ∀ a b, B.MulIn a → B.MulIn b →
  B.sub a b ⦃ r => B.toField r = B.toField a - B.toField b ∧ B.Red r ⦄

/-- `mul` of two `MulIn` elements. -/
abbrev MulSpec : Prop := ∀ a b, B.MulIn a → B.MulIn b →
  B.mul a b ⦃ r => B.toField r = B.toField a * B.toField b ∧ B.Red r ⦄

/-- `square` of a `SqIn` element. -/
abbrev SquareSpec : Prop := ∀ a, B.SqIn a →
  B.square a ⦃ r => B.toField r = B.toField a ^ 2 ∧ B.Red r ⦄

/-- `square2` of a `SqIn` element. -/
abbrev Square2Spec : Prop := ∀ a, B.SqIn a →
  B.square2 a ⦃ r => B.toField r = 2 * B.toField a ^ 2 ∧ B.Sum2 r ⦄

/-- `pow2k` of a `SqIn` element, `k > 0`. -/
abbrev Pow2kSpec : Prop := ∀ a (k : U32), 0 < k.val → B.SqIn a →
  B.pow2k a k ⦃ r => B.toField r = B.toField a ^ 2 ^ k.val ∧ B.Red r ⦄

/-- `neg` of a `MulIn` element. -/
abbrev NegSpec : Prop := ∀ a, B.MulIn a →
  B.neg a ⦃ r => B.toField r = -B.toField a ∧ B.Red r ⦄

/-- `eq` decides equality in `ZMod p`. -/
abbrev EqSpec : Prop := ∀ a b, B.eq a b ⦃ c => (c = true ↔ B.toField a = B.toField b) ⦄

/-- `ctEq` decides equality in `ZMod p`, as a `Choice`. -/
abbrev CtEqSpec : Prop := ∀ a b, B.ctEq a b ⦃ c =>
  c.IsValid ∧ (B.toField a = B.toField b → c = 1#u8) ∧ (B.toField a ≠ B.toField b → c = 0#u8) ⦄

/-- `condAssign a b c` is `a` if `c = 0`, `b` if `c = 1`. -/
abbrev CondAssignSpec : Prop := ∀ a b (c : subtle.Choice), c.IsValid →
  B.condAssign a b c ⦃ r => (c = 0#u8 → r = a) ∧ (c = 1#u8 → r = b) ⦄

/-- `condNeg a c` is `a` if `c = 0`, `-a` if `c = 1`. -/
abbrev CondNegSpec : Prop := ∀ a (c : subtle.Choice), c.IsValid → B.MulIn a →
  B.condNeg a c ⦃ r => (c = 0#u8 → r = a) ∧ (c = 1#u8 → B.toField r = -B.toField a ∧ B.Red r) ⦄

/-- `EDWARDS_D` is `d`. -/
abbrev EdwardsDSpec : Prop := B.constEdwardsD ⦃ r => B.toField r = d ∧ B.Red r ⦄

/-- `SQRT_M1` is `sqrtM1`. -/
abbrev SqrtM1Spec : Prop :=
  B.constSqrtM1 ⦃ r => B.toField r = (curve25519.sqrtM1 : ZMod p) ∧ B.Red r ⦄

/-- `ONE` is `1`. -/
abbrev OneSpec : Prop := B.constOne ⦃ r => B.toField r = 1 ∧ B.Red r ⦄

/-- `MINUS_ONE` is `-1`. -/
abbrev MinusOneSpec : Prop := B.constMinusOne ⦃ r => B.toField r = -1 ∧ B.Red r ⦄

/-- `ONE_MINUS_EDWARDS_D_SQUARED` is `1 - d²`. -/
abbrev OneMinusDSqSpec : Prop :=
  B.constOneMinusDSq ⦃ r => B.toField r = 1 - d ^ 2 ∧ B.Red r ⦄

/-- `EDWARDS_D_MINUS_ONE_SQUARED` is `(d - 1)²`. -/
abbrev DMinusOneSqSpec : Prop :=
  B.constDMinusOneSq ⦃ r => B.toField r = (d - 1) ^ 2 ∧ B.Red r ⦄

/-- `SQRT_AD_MINUS_ONE` is `sqrtAdMinusOne`. -/
abbrev SqrtAdMinusOneSpec : Prop :=
  B.constSqrtAdMinusOne ⦃ r => B.toField r = (curve25519.sqrtAdMinusOne : ZMod p) ∧ B.Red r ⦄

/-- `INVSQRT_A_MINUS_D` is a square root of `1 / (a - d)` (the sign is not needed). -/
abbrev InvsqrtAMinusDSpec : Prop :=
  B.constInvsqrtAMinusD ⦃ r => B.toField r ^ 2 = (invsqrtAMinusD : ZMod p) ^ 2 ∧ B.Red r ⦄

/-- `APLUS2_OVER_FOUR` is `(A + 2) / 4`. -/
abbrev Aplus2OverFourSpec : Prop :=
  B.constAplus2OverFour ⦃ r => B.toField r * 4 = (A : ZMod p) + 2 ∧ B.Red r ⦄

/-- `toBytes a` encodes the canonical value. -/
abbrev ToBytesSpec : Prop := ∀ a, B.toBytes a ⦃ r => r.asNat 8 = (B.toField a).val ⦄

/-- `isNegative a` is the low bit of the canonical value. -/
abbrev IsNegativeSpec : Prop := ∀ a, B.isNegative a ⦃ c =>
  c.IsValid ∧ c.val = (B.toField a).val % 2 ⦄

/-- `isZero a` decides `a = 0` in `ZMod p`. -/
abbrev IsZeroSpec : Prop := ∀ a, B.isZero a ⦃ c =>
  c.IsValid ∧ (B.toField a = 0 → c = 1#u8) ∧ (B.toField a ≠ 0 → c = 0#u8) ⦄

/-! ### Specs of the `field.rs` functions -/

/-- `pow22501 a` is `(a ^ (2^250 - 1), a ^ 11)`. -/
abbrev Pow22501Spec : Prop := ∀ a, B.SqIn a → B.pow22501 a ⦃ (t19 t3 : B.F) =>
  B.toField t19 = B.toField a ^ (2 ^ 250 - 1) ∧ B.toField t3 = B.toField a ^ 11 ∧
    B.Red t19 ∧ B.Red t3 ⦄

/-- `powP58 a` is `a ^ ((p - 5) / 8)`. -/
abbrev PowP58Spec : Prop := ∀ a, B.SqIn a →
  B.powP58 a ⦃ r => B.toField r = B.toField a ^ (2 ^ 252 - 3) ∧ B.Red r ⦄

/-- `invert a` is `a ^ (p - 2)`, i.e. `a⁻¹` (`0` for `0`). -/
abbrev InvertSpec : Prop := ∀ a, B.SqIn a →
  B.invert a ⦃ r => B.toField r = (B.toField a)⁻¹ ∧ B.Red r ⦄

/-- `sqrtRatioI u v`: RFC 9496's `SQRT_RATIO_M1`, in `ZMod p`. -/
abbrev SqrtRatioISpec : Prop := ∀ u v, B.SqIn u → B.SqIn v →
  B.sqrtRatioI u v ⦃ (c : subtle.Choice) (r : B.F) =>
    c.IsValid ∧ (B.toField u = 0 → c = 1#u8 ∧ B.toField r = 0) ∧
    (B.toField u ≠ 0 → B.toField v = 0 → c = 0#u8 ∧ B.toField r = 0) ∧
    (B.toField v ≠ 0 → (∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
      c = 1#u8 ∧ B.toField r ^ 2 * B.toField v = B.toField u) ∧
    (B.toField v ≠ 0 → (¬∃ x : ZMod p, x ^ 2 * B.toField v = B.toField u) →
      c = 0#u8 ∧ B.toField r ^ 2 * B.toField v = curve25519.sqrtM1 * B.toField u) ∧
    (B.toField r).val % 2 = 0 ∧ B.Red r ⦄

/-- `invsqrt a` is RFC 9496's `SQRT_RATIO_M1(1, a)`. -/
abbrev InvsqrtSpec : Prop := ∀ a, B.SqIn a → B.invsqrt a ⦃ (c : subtle.Choice) (r : B.F) =>
  sqrtRatioM1 1 (B.toField a) = (decide (c = 1#u8), B.toField r) ∧ c.IsValid ∧ B.Red r ⦄

/-- `invertBatchAlloc` inverts every entry (`0` stays `0`). -/
abbrev InvertBatchAllocSpec : Prop := ∀ (s : Slice B.F), (∀ i < s.length, B.Red s[i]!) →
  B.invertBatchAlloc s ⦃ r => r.length = s.length ∧
    ∀ i < s.length, B.toField r[i]! = (B.toField s[i]!)⁻¹ ∧ B.Red r[i]! ⦄

/-! ### From `toField` back to the specs' `asNat % p` form -/

variable {B}

theorem toField_val (a : B.F) : (B.toField a).val = B.asNat a % p := by
  rw [B.toField_eq, ZMod.val_natCast]

theorem toField_eq_toField_iff {a b : B.F} :
    B.toField a = B.toField b ↔ B.asNat a % p = B.asNat b % p := by
  rw [B.toField_eq, B.toField_eq, ZMod.natCast_eq_natCast_iff']

theorem toField_eq_zero_iff {a : B.F} : B.toField a = 0 ↔ B.asNat a % p = 0 := by
  rw [B.toField_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem mod_eq_of_toField_eq_pow {a b : B.F} {n : ℕ}
    (h : B.toField a = B.toField b ^ n) : B.asNat a % p = B.asNat b ^ n % p := by
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, ← B.toField_eq, ← B.toField_eq, h]

end Backend

end Curve25519Dalek
