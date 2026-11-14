/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.Nat.Digits.Lemmas
public section

/-! # Little-endian byte strings

The RFCs (7748, 8032, 9496) state their functions on byte strings of a fixed length, read and
written as little-endian integers (RFC 7748 §5 `decodeLittleEndian`). `decodeLittleEndian b` is
the value of the bytes `b`, below `256 ^ n` (`decodeLittleEndian_lt`); `encodeLittleEndian n x`
is the `n` bytes of `x` modulo `256 ^ n` (`decodeLittleEndian_encodeLittleEndian`). The two are
inverse (`encodeLittleEndian_decodeLittleEndian`), so a byte string is determined by its value
(`decodeLittleEndian_injective`). -/

namespace curve25519

/-- RFC 7748 `decodeLittleEndian`: the value of the bytes, `b[0] + 256 · b[1] + …`. -/
@[expose] def decodeLittleEndian {n : ℕ} (b : Vector UInt8 n) : ℕ :=
  Nat.ofDigits 256 (b.toList.map UInt8.toNat)

/-- The `n` little-endian bytes of `x` modulo `256 ^ n`: byte `i` is `x / 256 ^ i % 256`. -/
@[expose] def encodeLittleEndian (n : ℕ) (x : ℕ) : Vector UInt8 n :=
  Vector.ofFn fun i => UInt8.ofNat (x / 256 ^ i.val)

private theorem ofDigits_lt {l : List ℕ} (h : ∀ d ∈ l, d < 256) :
    Nat.ofDigits 256 l < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ']
    have hd := h d List.mem_cons_self
    have hl := ih fun e he => h e (List.mem_cons_of_mem d he)
    omega

theorem decodeLittleEndian_lt {n : ℕ} (b : Vector UInt8 n) : decodeLittleEndian b < 256 ^ n := by
  have h := ofDigits_lt (l := b.toList.map UInt8.toNat) fun d hd => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    exact x.toNat_lt
  simpa [decodeLittleEndian] using h

private theorem toList_encodeLittleEndian_succ (n x : ℕ) :
    (encodeLittleEndian (n + 1) x).toList =
      UInt8.ofNat x :: (encodeLittleEndian n (x / 256)).toList := by
  simp only [encodeLittleEndian, Vector.toList_ofFn, List.ofFn_succ, Fin.val_zero, pow_zero,
    Nat.div_one, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]

/-- The value of the bytes of `x` is `x` modulo `256 ^ n`. -/
theorem decodeLittleEndian_encodeLittleEndian (n x : ℕ) :
    decodeLittleEndian (encodeLittleEndian n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [decodeLittleEndian, encodeLittleEndian, Vector.toList_ofFn, Nat.mod_one]
  | succ n ih =>
    simp only [decodeLittleEndian] at ih ⊢
    rw [toList_encodeLittleEndian_succ, List.map_cons, Nat.ofDigits_cons, ih, UInt8.toNat_ofNat',
      show (2 : ℕ) ^ 8 = 256 by norm_num, pow_succ', Nat.mod_mul]

/-- A byte string is determined by its value. -/
theorem decodeLittleEndian_injective {n : ℕ} :
    Function.Injective (decodeLittleEndian : Vector UInt8 n → ℕ) := fun a b h => by
  have hdig : ∀ (c : Vector UInt8 n), ∀ d ∈ c.toList.map UInt8.toNat, d < 256 := fun c d hd => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    exact x.toNat_lt
  have hl := Nat.ofDigits_inj_of_len_eq (by norm_num) (by simp) (hdig a) (hdig b) h
  apply Vector.toList_inj.mp
  exact List.map_injective_iff.mpr (fun x y hxy => UInt8.toNat_inj.mp hxy) hl

/-- The bytes of the value of `b` are `b`. -/
theorem encodeLittleEndian_decodeLittleEndian {n : ℕ} (b : Vector UInt8 n) :
    encodeLittleEndian n (decodeLittleEndian b) = b := by
  apply decodeLittleEndian_injective
  rw [decodeLittleEndian_encodeLittleEndian, Nat.mod_eq_of_lt (decodeLittleEndian_lt b)]

/-- `b` is the encoding of `x < 256 ^ n` iff its value is `x`. -/
theorem eq_encodeLittleEndian_iff {n x : ℕ} (b : Vector UInt8 n) (hx : x < 256 ^ n) :
    b = encodeLittleEndian n x ↔ decodeLittleEndian b = x := by
  constructor
  · rintro rfl
    rw [decodeLittleEndian_encodeLittleEndian, Nat.mod_eq_of_lt hx]
  · rintro rfl
    rw [encodeLittleEndian_decodeLittleEndian]

end curve25519
