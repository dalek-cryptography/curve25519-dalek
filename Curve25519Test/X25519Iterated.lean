/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.X25519
public import Curve25519Test.X25519Fast
meta import Curve25519Fast.X25519
public section

/-! # RFC 7748's iterated X25519 test (not audited)

RFC 7748 §5.2: starting from `k = u = 9`, each iteration sets `k, u ← X25519(k, u), k`; after
`1` iteration `k` is `422c8e7a…` (`curve25519.Proofs.X25519_one_iteration`, by the kernel), after
`1,000` it is `684cf59b…` and after `1,000,000` it is `7c3911e0…`.

The statements are about `X25519`; `iterateX25519_eq` reduces them to the fast version
`Fast.iterate` (`Fast.x25519_eq`, checked by the kernel), which `native_decide` runs as compiled
code (about `0.1 s` and `2 min`). Each depends on an axiom that `native_decide` adds for its
evaluation, so they trust the Lean compiler and its runtime; nothing outside `Curve25519Test`
imports them. -/

namespace curve25519.Test

/-- RFC 7748 §5.2's iterated test: `k, u ← X25519(k, u), k`, `n` times; the final `k`. -/
def iterateX25519 : ℕ → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32
  | 0, k, _ => k
  | n + 1, k, u => iterateX25519 n (X25519 k u) k

/-- The byte string of `9`. -/
def nine : Vector UInt8 32 :=
  #v[0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `iterateX25519` is the fast iteration on the values of the bytes. -/
theorem iterateX25519_eq (n : ℕ) (k u : Vector UInt8 32) :
    iterateX25519 n k u =
      encodeLittleEndian 32 (Fast.iterate n (decodeLittleEndian k) (decodeLittleEndian u)) := by
  induction n generalizing k u with
  | zero => rw [iterateX25519, Fast.iterate, encodeLittleEndian_decodeLittleEndian]
  | succ n ih =>
    rw [iterateX25519, ih, Fast.iterate, Fast.x25519_eq, X25519_eq_x25519Nat,
      decodeLittleEndian_encodeLittleEndian, Nat.mod_eq_of_lt]
    exact lt_trans (x25519Nat_lt _ _) (by rw [p_eq_numeral]; norm_num)

theorem decodeLittleEndian_nine : decodeLittleEndian nine = 9 := by
  decide +kernel

/-- RFC 7748 §5.2, the iterated test after `1,000` iterations: `684cf59b…`. -/
theorem iterateX25519_thousand :
    iterateX25519 1000 nine nine =
      #v[0x68, 0x4c, 0xf5, 0x9b, 0xa8, 0x33, 0x09, 0x55,
        0x28, 0x00, 0xef, 0x56, 0x6f, 0x2f, 0x4d, 0x3c,
        0x1c, 0x38, 0x87, 0xc4, 0x93, 0x60, 0xe3, 0x87,
        0x5f, 0x2e, 0xb9, 0x4d, 0x99, 0x53, 0x2c, 0x51] := by
  have h : Fast.iterate 1000 9 9 =
      36715658984098675622644846447287739160727487991947607163673193504554999958632 := by
    native_decide
  rw [iterateX25519_eq, decodeLittleEndian_nine, h]
  decide +kernel

/-- RFC 7748 §5.2, the iterated test after `1,000,000` iterations: `7c3911e0…`. -/
theorem iterateX25519_million :
    iterateX25519 1000000 nine nine =
      #v[0x7c, 0x39, 0x11, 0xe0, 0xab, 0x25, 0x86, 0xfd,
        0x86, 0x44, 0x97, 0x29, 0x7e, 0x57, 0x5e, 0x6f,
        0x3b, 0xc6, 0x01, 0xc0, 0x88, 0x3c, 0x30, 0xdf,
        0x5f, 0x4d, 0xd2, 0xd2, 0x4f, 0x66, 0x54, 0x24] := by
  have h : Fast.iterate 1000000 9 9 =
      16432383832604228183214538433420724309548692366517210566425561007471436315004 := by
    native_decide
  rw [iterateX25519_eq, decodeLittleEndian_nine, h]
  decide +kernel

end curve25519.Test
