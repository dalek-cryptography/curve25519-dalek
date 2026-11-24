module
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Attr
public section

namespace curve25519

/-- RFC 7748 `decodeLittleEndian`: the value of the bytes, `b[0] + 256 · b[1] + …`. -/
@[expose] def decodeLittleEndian {n : ℕ} (b : Vector UInt8 n) : ℕ :=
  Nat.ofDigits 256 (b.toList.map UInt8.toNat)

/-- The `n` little-endian bytes of `x` modulo `256 ^ n`: byte `i` is `x / 256 ^ i % 256`. -/
@[expose] def encodeLittleEndian (n : ℕ) (x : ℕ) : Vector UInt8 n :=
  Vector.ofFn fun i => UInt8.ofNat (x / 256 ^ i.val)

end curve25519
