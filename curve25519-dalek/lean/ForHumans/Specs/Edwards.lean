module
public import ForHumans.Specs.Bytes
public import ForHumans.Specs.Curves
public import ForHumans.Specs.Models
import Proofs.Curve25519.Certificates.Edwards
public section

namespace curve25519

/-- The basepoint of edwards25519: `y = 4/5`, `x` even (RFC 8032 §5.1). -/
noncomputable def basepoint : edwards.Point :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960,
    Proofs.basepoint_equation⟩

/-- The point of order `8` with `2 • T = (-√-1, 0)` and `x` non-negative (`eq_torsion8_iff`):
dalek's `EIGHT_TORSION[1]`. -/
noncomputable def torsion8 : edwards.Point :=
  ⟨14399317868200118260347934320527232580618823971194345261214217575416788799818,
    55188659117513257062467267217118295137698188065244968500265048394206261417927,
    Proofs.torsion8_equation⟩


/-- RFC 8032 §5.1.2: the encoding of a point of edwards25519, `y.val + 2 ^ 255 * sign(x)`. -/
noncomputable abbrev encodeNat : edwards.Point → ℕ :=
  TwistedEdwardsModel.encode edwards 255

open scoped Classical in
/-- Lenient decoding of the value `n` of the 32 bytes: `y := n % 2^255` reduced modulo `p`, sign `s
:= n / 2^255`; `none` if no point has this `y`, otherwise the point `(x, y)` with `x = 0` or `x` of
sign `s`. Unlike the strict `decodeNat`, it accepts `y ≥ p` (reduced) and `x = 0` with `s = 1`; on
canonical inputs the two agree (`decodeLenientNat_eq_decodeNat_of_canonical`). This is dalek's
`CompressedEdwardsY::decompress`. -/
noncomputable def decodeLenientNat (n : ℕ) : Option edwards.Point :=
  if h : ∃ x : ZMod p, edwards.Equation x ((n % 2 ^ 255 : ℕ) : ZMod p) ∧
      (x = 0 ∨ (x.IsNeg ↔ n / 2 ^ 255 = 1)) then
    some ⟨Classical.choose h, ((n % 2 ^ 255 : ℕ) : ZMod p), (Classical.choose_spec h).1⟩
  else none

/-- RFC 8032 §5.1.2: the 32-byte encoding of a point, the little-endian bytes of `encodeNat`. -/
@[expose] noncomputable def encode (P : edwards.Point) : Vector UInt8 32 :=
  encodeLittleEndian 32 (encodeNat P)

/-- The lenient decoding of 32 bytes, `decodeLenientNat` of their value. -/
@[expose] noncomputable def decodeLenient (b : Vector UInt8 32) : Option edwards.Point :=
  decodeLenientNat (decodeLittleEndian b)

end curve25519
