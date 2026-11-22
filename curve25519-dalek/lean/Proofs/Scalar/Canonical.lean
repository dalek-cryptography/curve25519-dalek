module
public import Curve25519Dalek.Funs
public import Proofs.Curve25519.Basic
public import Proofs.Representation.Scalar
public import Proofs.Scalar.FromCanonicalBytes
public import Proofs.External.Zeroize.Instances
public section

/-! # `Scalar.IsCanonical` of results -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519
open Curve25519Dalek.scalar (Scalar)

namespace Curve25519Dalek.scalar.Scalar

/-- A result with value `n < L` is canonical. -/
theorem canonical_of_eq {m : Result Scalar} {n : ℕ} (h : m ⦃ (r : Scalar) => r.asNat = n ⦄)
    (hn : n < L) : m ⦃ (r : Scalar) => r.asNat = n ∧ r.IsCanonical ⦄ :=
  spec_mono h fun _ h => ⟨h, isCanonical_of_eq h hn⟩

/-- A result with value `n % L` is canonical. -/
theorem canonical_of_mod {m : Result Scalar} {n : ℕ} (h : m ⦃ (r : Scalar) => r.asNat = n % L ⦄) :
    m ⦃ (r : Scalar) => r.asNat = n % L ∧ r.IsCanonical ⦄ :=
  canonical_of_eq h (Nat.mod_lt _ L_pos)

/-- An unsigned integer of at most 128 bits is below `L`. -/
theorem val_lt_L {ty : UScalarTy} (x : UScalar ty) (h : ty.numBits ≤ 128 := by decide) :
    x.val < L := by
  have : 2 ^ ty.numBits ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) h
  have : 2 ^ 128 < L := by rw [L_eq_numeral]; decide
  have := x.hmax
  omega

/-- `from_canonical_bytes`: as `from_canonical_bytes_spec`, and the value is canonical when
`Some`. -/
theorem from_canonical_bytes_canonical_spec (bytes : Array U8 32#usize) :
    from_canonical_bytes bytes ⦃ (r : subtle.CtOption Scalar) =>
      r.is_some.IsValid ∧ r.value.bytes = bytes ∧
      (bytes.asNat 8 < L → r.is_some = 1#u8) ∧ (L ≤ bytes.asNat 8 → r.is_some = 0#u8) ∧
      (r.is_some = 1#u8 → r.value.IsCanonical) ⦄ :=
  spec_mono (from_canonical_bytes_spec bytes) fun r ⟨hv, hb, hlt, hge⟩ =>
    ⟨hv, hb, hlt, hge, fun h1 => isCanonical_of_eq (by rw [asNat_def, hb]) (by
      by_contra hc
      have := hge (Nat.le_of_not_lt hc)
      rw [h1] at this
      exact absurd this (by decide))⟩

/-- `Zeroize::zeroize`: all bytes `0`, a canonical scalar. -/
theorem zeroize_canonical_spec (s : Scalar) :
    Insts.ZeroizeZeroize.zeroize s ⦃ (r : Scalar) =>
      r = { bytes := Array.repeat 32#usize 0#u8 } ∧ r.IsCanonical ⦄ :=
  spec_mono (Insts.ZeroizeZeroize.zeroize_spec s) fun _ h =>
    ⟨h, isCanonical_of_eq (n := 0)
      (by rw [h, asNat_def]; simp [Array.asNat_def, Nat.ofDigits]) L_pos⟩

end Curve25519Dalek.scalar.Scalar
