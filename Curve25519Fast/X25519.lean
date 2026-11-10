/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public section

/-! # A fast X25519 on natural numbers (not audited)

RFC 7748's X25519 on the little-endian values of the bytes, written for speed in core Lean only,
so that it compiles to native code without Mathlib: field elements are ten `UInt64` limbs in
radix `2^25.5` (as ref10; limb `i` has `26` bits for even `i`, `25` for odd `i`), products are
carried after each multiplication, and the inversion is ref10's addition chain. Used by
`native_decide` for RFC 7748's iterated test; `Curve25519Test.X25519Fast` proves
`x25519 = curve25519.x25519Nat`. Divisions and remainders by powers of two compile to shifts and
masks. -/

namespace curve25519.Fast

/-- A field element: `f0 + f1 2^26 + f2 2^51 + … + f9 2^230`. -/
structure Fe where
  /-- Limb `0` (`26` bits). -/
  f0 : UInt64
  /-- Limb `1` (`25` bits). -/
  f1 : UInt64
  /-- Limb `2` (`26` bits). -/
  f2 : UInt64
  /-- Limb `3` (`25` bits). -/
  f3 : UInt64
  /-- Limb `4` (`26` bits). -/
  f4 : UInt64
  /-- Limb `5` (`25` bits). -/
  f5 : UInt64
  /-- Limb `6` (`26` bits). -/
  f6 : UInt64
  /-- Limb `7` (`25` bits). -/
  f7 : UInt64
  /-- Limb `8` (`26` bits). -/
  f8 : UInt64
  /-- Limb `9` (`25` bits). -/
  f9 : UInt64

/-- Carry limb `0` into limb `1`. -/
@[inline, expose] def carry0 (a : Fe) : Fe :=
  { a with f0 := a.f0 % 67108864, f1 := a.f1 + a.f0 / 67108864 }

/-- Carry limb `1` into limb `2`. -/
@[inline, expose] def carry1 (a : Fe) : Fe :=
  { a with f1 := a.f1 % 33554432, f2 := a.f2 + a.f1 / 33554432 }

/-- Carry limb `2` into limb `3`. -/
@[inline, expose] def carry2 (a : Fe) : Fe :=
  { a with f2 := a.f2 % 67108864, f3 := a.f3 + a.f2 / 67108864 }

/-- Carry limb `3` into limb `4`. -/
@[inline, expose] def carry3 (a : Fe) : Fe :=
  { a with f3 := a.f3 % 33554432, f4 := a.f4 + a.f3 / 33554432 }

/-- Carry limb `4` into limb `5`. -/
@[inline, expose] def carry4 (a : Fe) : Fe :=
  { a with f4 := a.f4 % 67108864, f5 := a.f5 + a.f4 / 67108864 }

/-- Carry limb `5` into limb `6`. -/
@[inline, expose] def carry5 (a : Fe) : Fe :=
  { a with f5 := a.f5 % 33554432, f6 := a.f6 + a.f5 / 33554432 }

/-- Carry limb `6` into limb `7`. -/
@[inline, expose] def carry6 (a : Fe) : Fe :=
  { a with f6 := a.f6 % 67108864, f7 := a.f7 + a.f6 / 67108864 }

/-- Carry limb `7` into limb `8`. -/
@[inline, expose] def carry7 (a : Fe) : Fe :=
  { a with f7 := a.f7 % 33554432, f8 := a.f8 + a.f7 / 33554432 }

/-- Carry limb `8` into limb `9`. -/
@[inline, expose] def carry8 (a : Fe) : Fe :=
  { a with f8 := a.f8 % 67108864, f9 := a.f9 + a.f8 / 67108864 }

/-- Carry limb `9` into limb `0` (times `19`, as `2^255 = 19`). -/
@[inline, expose] def carry9 (a : Fe) : Fe :=
  { a with f9 := a.f9 % 33554432, f0 := a.f0 + 19 * (a.f9 / 33554432) }

/-- ref10's carry chain: limbs below `2^63` become limbs below `2^26`. -/
@[inline, expose] def carry (a : Fe) : Fe :=
  carry0 <| carry9 <| carry8 <| carry4 <| carry7 <| carry3 <| carry6 <| carry2 <| carry5 <|
    carry1 <| carry4 <| carry0 a

/-- Addition, without carrying. -/
@[inline, expose] def add (a b : Fe) : Fe :=
  ⟨a.f0 + b.f0, a.f1 + b.f1, a.f2 + b.f2, a.f3 + b.f3, a.f4 + b.f4, a.f5 + b.f5, a.f6 + b.f6,
    a.f7 + b.f7, a.f8 + b.f8, a.f9 + b.f9⟩

/-- `a + 4 p - b` limb by limb (no limb underflows for `b` below `2^26`). -/
@[inline, expose] def subRaw (a b : Fe) : Fe :=
  ⟨a.f0 + 268435380 - b.f0, a.f1 + 134217724 - b.f1, a.f2 + 268435452 - b.f2,
    a.f3 + 134217724 - b.f3, a.f4 + 268435452 - b.f4, a.f5 + 134217724 - b.f5,
    a.f6 + 268435452 - b.f6, a.f7 + 134217724 - b.f7, a.f8 + 268435452 - b.f8,
    a.f9 + 134217724 - b.f9⟩

/-- Subtraction. -/
@[inline, expose] def sub (a b : Fe) : Fe :=
  carry (subRaw a b)

/-- The uncarried product: limb `k` collects the products of limbs `i + j = k`
(`i + j = k + 10` times `19`; times `2` when `i` and `j` are odd). -/
@[inline, expose] def mulRaw (a b : Fe) : Fe :=
  let h0 := a.f0 * b.f0 + 19 * (a.f2 * b.f8) + 19 * (a.f4 * b.f6) + 19 * (a.f6 * b.f4) +
    19 * (a.f8 * b.f2) + 38 * (a.f1 * b.f9) + 38 * (a.f3 * b.f7) + 38 * (a.f5 * b.f5) +
    38 * (a.f7 * b.f3) + 38 * (a.f9 * b.f1)
  let h1 := a.f0 * b.f1 + a.f1 * b.f0 + 19 * (a.f2 * b.f9) + 19 * (a.f3 * b.f8) +
    19 * (a.f4 * b.f7) + 19 * (a.f5 * b.f6) + 19 * (a.f6 * b.f5) + 19 * (a.f7 * b.f4) +
    19 * (a.f8 * b.f3) + 19 * (a.f9 * b.f2)
  let h2 := a.f0 * b.f2 + a.f2 * b.f0 + 2 * (a.f1 * b.f1) + 19 * (a.f4 * b.f8) +
    19 * (a.f6 * b.f6) + 19 * (a.f8 * b.f4) + 38 * (a.f3 * b.f9) + 38 * (a.f5 * b.f7) +
    38 * (a.f7 * b.f5) + 38 * (a.f9 * b.f3)
  let h3 := a.f0 * b.f3 + a.f1 * b.f2 + a.f2 * b.f1 + a.f3 * b.f0 + 19 * (a.f4 * b.f9) +
    19 * (a.f5 * b.f8) + 19 * (a.f6 * b.f7) + 19 * (a.f7 * b.f6) + 19 * (a.f8 * b.f5) +
    19 * (a.f9 * b.f4)
  let h4 := a.f0 * b.f4 + a.f2 * b.f2 + a.f4 * b.f0 + 2 * (a.f1 * b.f3) + 2 * (a.f3 * b.f1) +
    19 * (a.f6 * b.f8) + 19 * (a.f8 * b.f6) + 38 * (a.f5 * b.f9) + 38 * (a.f7 * b.f7) +
    38 * (a.f9 * b.f5)
  let h5 := a.f0 * b.f5 + a.f1 * b.f4 + a.f2 * b.f3 + a.f3 * b.f2 + a.f4 * b.f1 + a.f5 * b.f0 +
    19 * (a.f6 * b.f9) + 19 * (a.f7 * b.f8) + 19 * (a.f8 * b.f7) + 19 * (a.f9 * b.f6)
  let h6 := a.f0 * b.f6 + a.f2 * b.f4 + a.f4 * b.f2 + a.f6 * b.f0 + 2 * (a.f1 * b.f5) +
    2 * (a.f3 * b.f3) + 2 * (a.f5 * b.f1) + 19 * (a.f8 * b.f8) + 38 * (a.f7 * b.f9) +
    38 * (a.f9 * b.f7)
  let h7 := a.f0 * b.f7 + a.f1 * b.f6 + a.f2 * b.f5 + a.f3 * b.f4 + a.f4 * b.f3 + a.f5 * b.f2 +
    a.f6 * b.f1 + a.f7 * b.f0 + 19 * (a.f8 * b.f9) + 19 * (a.f9 * b.f8)
  let h8 := a.f0 * b.f8 + a.f2 * b.f6 + a.f4 * b.f4 + a.f6 * b.f2 + a.f8 * b.f0 +
    2 * (a.f1 * b.f7) + 2 * (a.f3 * b.f5) + 2 * (a.f5 * b.f3) + 2 * (a.f7 * b.f1) +
    38 * (a.f9 * b.f9)
  let h9 := a.f0 * b.f9 + a.f1 * b.f8 + a.f2 * b.f7 + a.f3 * b.f6 + a.f4 * b.f5 + a.f5 * b.f4 +
    a.f6 * b.f3 + a.f7 * b.f2 + a.f8 * b.f1 + a.f9 * b.f0
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The uncarried square: limb `k` collects the products of limbs `i + j = k`
(`i + j = k + 10` times `19`; times `2` when `i` and `j` are odd). -/
@[inline, expose] def sqRaw (a : Fe) : Fe :=
  let h0 := a.f0 * a.f0 + 38 * (a.f2 * a.f8) + 38 * (a.f4 * a.f6) + 38 * (a.f5 * a.f5) +
    76 * (a.f1 * a.f9) + 76 * (a.f3 * a.f7)
  let h1 := 2 * (a.f0 * a.f1) + 38 * (a.f2 * a.f9) + 38 * (a.f3 * a.f8) + 38 * (a.f4 * a.f7) +
    38 * (a.f5 * a.f6)
  let h2 := 2 * (a.f0 * a.f2) + 2 * (a.f1 * a.f1) + 19 * (a.f6 * a.f6) + 38 * (a.f4 * a.f8) +
    76 * (a.f3 * a.f9) + 76 * (a.f5 * a.f7)
  let h3 := 2 * (a.f0 * a.f3) + 2 * (a.f1 * a.f2) + 38 * (a.f4 * a.f9) + 38 * (a.f5 * a.f8) +
    38 * (a.f6 * a.f7)
  let h4 := a.f2 * a.f2 + 2 * (a.f0 * a.f4) + 4 * (a.f1 * a.f3) + 38 * (a.f6 * a.f8) +
    38 * (a.f7 * a.f7) + 76 * (a.f5 * a.f9)
  let h5 := 2 * (a.f0 * a.f5) + 2 * (a.f1 * a.f4) + 2 * (a.f2 * a.f3) + 38 * (a.f6 * a.f9) +
    38 * (a.f7 * a.f8)
  let h6 := 2 * (a.f0 * a.f6) + 2 * (a.f2 * a.f4) + 2 * (a.f3 * a.f3) + 4 * (a.f1 * a.f5) +
    19 * (a.f8 * a.f8) + 76 * (a.f7 * a.f9)
  let h7 := 2 * (a.f0 * a.f7) + 2 * (a.f1 * a.f6) + 2 * (a.f2 * a.f5) + 2 * (a.f3 * a.f4) +
    38 * (a.f8 * a.f9)
  let h8 := a.f4 * a.f4 + 2 * (a.f0 * a.f8) + 2 * (a.f2 * a.f6) + 4 * (a.f1 * a.f7) +
    4 * (a.f3 * a.f5) + 38 * (a.f9 * a.f9)
  let h9 := 2 * (a.f0 * a.f9) + 2 * (a.f1 * a.f8) + 2 * (a.f2 * a.f7) + 2 * (a.f3 * a.f6) +
    2 * (a.f4 * a.f5)
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Multiplication. -/
@[inline, expose] def mul (a b : Fe) : Fe :=
  carry (mulRaw a b)

/-- Squaring. -/
@[inline, expose] def sq (a : Fe) : Fe :=
  carry (sqRaw a)

/-- Multiplication by `121665 = (A - 2) / 4`, the ladder constant. -/
@[inline, expose] def mul121665 (a : Fe) : Fe :=
  carry ⟨a.f0 * 121665, a.f1 * 121665, a.f2 * 121665, a.f3 * 121665, a.f4 * 121665,
    a.f5 * 121665, a.f6 * 121665, a.f7 * 121665, a.f8 * 121665, a.f9 * 121665⟩

/-- The limbs of `x % 2^255`. -/
@[expose] def ofNat (x : Nat) : Fe :=
  ⟨(x / 2 ^ 0 % 2 ^ 26).toUInt64, (x / 2 ^ 26 % 2 ^ 25).toUInt64, (x / 2 ^ 51 % 2 ^ 26).toUInt64,
    (x / 2 ^ 77 % 2 ^ 25).toUInt64, (x / 2 ^ 102 % 2 ^ 26).toUInt64,
    (x / 2 ^ 128 % 2 ^ 25).toUInt64, (x / 2 ^ 153 % 2 ^ 26).toUInt64,
    (x / 2 ^ 179 % 2 ^ 25).toUInt64, (x / 2 ^ 204 % 2 ^ 26).toUInt64,
    (x / 2 ^ 230 % 2 ^ 25).toUInt64⟩

/-- The value of the limbs. -/
@[expose] def Fe.val (a : Fe) : Nat :=
  a.f0.toNat + a.f1.toNat * 2 ^ 26 + a.f2.toNat * 2 ^ 51 + a.f3.toNat * 2 ^ 77 +
    a.f4.toNat * 2 ^ 102 + a.f5.toNat * 2 ^ 128 + a.f6.toNat * 2 ^ 153 + a.f7.toNat * 2 ^ 179 +
    a.f8.toNat * 2 ^ 204 + a.f9.toNat * 2 ^ 230

/-- `a ^ (2 ^ n)`. -/
@[expose] def sqn (a : Fe) : Nat → Fe
  | 0 => a
  | n + 1 => sqn (sq a) n

/-- `z ^ (p - 2) = z ^ (2^255 - 21)`, ref10's addition chain: `254` squarings, `11`
multiplications. -/
@[expose] def invert (z : Fe) : Fe :=
  let z2 := sq z
  let z9 := mul (sqn z2 2) z
  let z11 := mul z9 z2
  let z2_5_0 := mul (sq z11) z9
  let z2_10_0 := mul (sqn z2_5_0 5) z2_5_0
  let z2_20_0 := mul (sqn z2_10_0 10) z2_10_0
  let z2_40_0 := mul (sqn z2_20_0 20) z2_20_0
  let z2_50_0 := mul (sqn z2_40_0 10) z2_10_0
  let z2_100_0 := mul (sqn z2_50_0 50) z2_50_0
  let z2_200_0 := mul (sqn z2_100_0 100) z2_100_0
  let z2_250_0 := mul (sqn z2_200_0 50) z2_50_0
  mul (sqn z2_250_0 5) z11

/-- The ladder state: `(x2 : z2)` and `(x3 : z3)`. -/
structure St where
  /-- `x2`. -/
  x2 : Fe
  /-- `z2`. -/
  z2 : Fe
  /-- `x3`. -/
  x3 : Fe
  /-- `z3`. -/
  z3 : Fe

/-- One ladder step after the conditional swap: `(x2 : z2) ← xDBL`, `(x3 : z3) ← xADD` with the
base coordinate `x1` (RFC 7748 §5). -/
@[inline, expose] def step (x1 x2 z2 x3 z3 : Fe) : St :=
  let A := add x2 z2
  let AA := sq A
  let B := sub x2 z2
  let BB := sq B
  let E := sub AA BB
  let C := add x3 z3
  let D := sub x3 z3
  let DA := mul D A
  let CB := mul C B
  ⟨mul AA BB, mul E (add AA (mul121665 E)), sq (add DA CB), mul x1 (sq (sub DA CB))⟩

/-- Bit `t < 256` of the scalar with the `64`-bit words `w0`, …, `w3`. -/
@[inline, expose] def bit (w0 w1 w2 w3 : UInt64) (t : Nat) : Bool :=
  let w := if t < 64 then w0 else if t < 128 then w1 else if t < 192 then w2 else w3
  (w >>> (t % 64).toUInt64) % 2 == 1

/-- The ladder loop over the bits `t - 1, …, 0` of the scalar; `sw` is the pending swap. -/
@[expose] def loop (x1 : Fe) (w0 w1 w2 w3 : UInt64) : Nat → St → Bool → St × Bool
  | 0, s, sw => (s, sw)
  | t + 1, s, sw =>
    let kt := bit w0 w1 w2 w3 t
    let s' := if sw ^^ kt then step x1 s.x3 s.z3 s.x2 s.z2 else step x1 s.x2 s.z2 s.x3 s.z3
    loop x1 w0 w1 w2 w3 t s' kt

/-- RFC 7748 `decodeScalar25519` on the value of the bytes (as `curve25519.clamp`). -/
@[expose] def clamp (k : Nat) : Nat :=
  2 ^ 254 + 8 * (k % 2 ^ 254 / 8)

/-- RFC 7748 `X25519(k, u)` on the values of the bytes, as a value below `p`. -/
@[expose] def x25519 (k u : Nat) : Nat :=
  let k := clamp k
  let x1 := ofNat u
  let r := loop x1 (k % 2 ^ 64).toUInt64 (k / 2 ^ 64 % 2 ^ 64).toUInt64
    (k / 2 ^ 128 % 2 ^ 64).toUInt64 (k / 2 ^ 192 % 2 ^ 64).toUInt64 255
    ⟨ofNat 1, ofNat 0, x1, ofNat 1⟩ false
  let x2 := if r.2 then r.1.x3 else r.1.x2
  let z2 := if r.2 then r.1.z3 else r.1.z2
  (mul x2 (invert z2)).val % (2 ^ 255 - 19)

/-- RFC 7748 §5.2's iterated test on values: `k, u ← x25519 k u, k`, `n` times; the final `k`. -/
@[expose] def iterate : Nat → Nat → Nat → Nat
  | 0, k, _ => k
  | n + 1, k, u => iterate n (x25519 k u) k

end curve25519.Fast
