module
public import ForHumans.Specs.Bytes
public import ForHumans.Specs.Curves
public import EllipticCurve.Montgomery.Ladder.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public section

namespace curve25519

/-- RFC 7748 `decodeScalar25519` on the little-endian value `k` of the 32 bytes: clear the bits `0`,
`1`, `2` and `255`, set the bit `254`. Matches dalek's `clamp_integer` (`clamp_add_mod_eight`). Its
properties are the lemmas of `Proofs/Curve25519/X25519.lean`: `clamp_lt`, `two_pow_254_le_clamp`,
`clamp_mod_eight`, `clamp_add_mod_eight`, `clamp_mod_two_pow`. -/
@[expose] def clamp (k : ℕ) : ℕ :=
  2 ^ 254 + 8 * (k % 2 ^ 254 / 8)

/-- RFC 7748 `encodeUCoordinate`: the canonical representative below `p`. -/
@[expose] def encodeU (u : ZMod p) : ℕ :=
  u.val

/-- RFC 7748 `decodeScalar25519`: the clamped little-endian value of the 32 bytes. -/
@[expose] def decodeScalar25519 (k : Vector UInt8 32) : ℕ :=
  clamp (decodeLittleEndian k)

/-- RFC 7748 `decodeUCoordinate`: the little-endian value of the 32 bytes with bit `255`
masked, as a field element (the RFC processes non-canonical values as reduced modulo `p`). -/
@[expose] def decodeUCoordinate (u : Vector UInt8 32) : ZMod p :=
  ((decodeLittleEndian u % 2 ^ 255 : ℕ) : ZMod p)

/-- RFC 7748 `encodeUCoordinate`: the 32 little-endian bytes of the canonical representative
(the RFC reduces its integer argument modulo `p`; here the argument is the field element). -/
@[expose] def encodeUCoordinate (u : ZMod p) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeU u)

/-- RFC 7748 §5 `X25519(k, u)` on 32-byte strings: the Montgomery ladder of `montgomery` over
`255` bits on the clamped scalar and the decoded coordinate, encoded. -/
@[expose] def X25519 (k u : Vector UInt8 32) : Vector UInt8 32 :=
  encodeUCoordinate (montgomery.ladder 255 (decodeScalar25519 k) (decodeUCoordinate u))

end curve25519
