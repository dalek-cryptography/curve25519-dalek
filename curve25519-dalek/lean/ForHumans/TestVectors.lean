/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ForHumans.Specs
import Proofs.Curve25519.Edwards.Encoding
import Proofs.Curve25519.Ristretto.Encoding
import Proofs.Curve25519.Ristretto.Map
import Proofs.Curve25519.TestVectors.X25519
import Proofs.Curve25519.TestVectors.RistrettoEncoding
import Proofs.Curve25519.TestVectors.RistrettoInvalid
import Proofs.Curve25519.TestVectors.RistrettoMap
public section

set_option linter.style.longLine false

namespace TestVectors

open curve25519

/-- The bytes written in hexadecimal digits by `s`, two digits per byte, first byte first (the
RFCs' notation). -/
@[expose] def hex {n : ℕ} (s : String) : Vector UInt8 n :=
  Vector.ofFn fun i => UInt8.ofNat (16 * digit (s.toList.getD (2 * i) '0') +
    digit (s.toList.getD (2 * i + 1) '0'))
where
  /-- The value of a hexadecimal digit `0`–`9`, `a`–`f`. -/
  digit (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- RFC 8032 §5.1: the encoding of the basepoint `B`, `(x, 4/5)` with `x` positive. -/
theorem rfc8032_basepoint :
    encode basepoint = hex "5866666666666666666666666666666666666666666666666666666666666666" := by
  change encodeLittleEndian 32 (encodeNat basepoint) = _
  rw [encodeNat_basepoint]
  decide +kernel

/-- RFC 7748 §5.2, first vector. -/
theorem rfc7748_vector₁ :
    X25519 (hex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
      (hex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c") =
      hex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552" := by
  convert Proofs.X25519_vector₁ using 2 <;> decide +kernel

/-- RFC 7748 §5.2, second vector. -/
theorem rfc7748_vector₂ :
    X25519 (hex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
      (hex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493") =
      hex "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957" := by
  convert Proofs.X25519_vector₂ using 2 <;> decide +kernel

/-- RFC 7748 §5.2, the iterated test after one iteration: `X25519(9, 9)`. -/
theorem rfc7748_one_iteration :
    X25519 (hex "0900000000000000000000000000000000000000000000000000000000000000")
      (hex "0900000000000000000000000000000000000000000000000000000000000000") =
      hex "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079" := by
  convert Proofs.X25519_one_iteration using 2 <;> decide +kernel

/-- RFC 7748 §6.1: Alice's public key, `X25519(a, 9)`. -/
theorem rfc7748_alice_public :
    X25519 (hex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
      (hex "0900000000000000000000000000000000000000000000000000000000000000") =
      hex "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a" := by
  convert Proofs.X25519_alice_public using 2 <;> decide +kernel

/-- RFC 7748 §6.1: Bob's public key, `X25519(b, 9)`. -/
theorem rfc7748_bob_public :
    X25519 (hex "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
      (hex "0900000000000000000000000000000000000000000000000000000000000000") =
      hex "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f" := by
  convert Proofs.X25519_bob_public using 2 <;> decide +kernel

/-- RFC 7748 §6.1: the shared secret, `X25519(a, X25519(b, 9))`. -/
theorem rfc7748_shared_secret :
    X25519 (hex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")
      (hex "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f") =
      hex "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742" := by
  convert Proofs.X25519_shared_secret using 2 <;> decide +kernel

/-- RFC 9496 §A.1: the encoding of `0 B`, the identity. -/
theorem rfc9496_encode_0 :
    Ristretto.encodeRep 0 = hex "0000000000000000000000000000000000000000000000000000000000000000" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat 0) = _
  rw [Ristretto.encodeRepNat_zero]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `B`. -/
theorem rfc9496_encode_1 :
    Ristretto.encodeRep basepoint = hex "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat basepoint) = _
  rw [Ristretto.encodeRepNat_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `2 B`. -/
theorem rfc9496_encode_2 :
    Ristretto.encodeRep (2 • basepoint) = hex "6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_two_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `3 B`. -/
theorem rfc9496_encode_3 :
    Ristretto.encodeRep (3 • basepoint) = hex "94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_three_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `4 B`. -/
theorem rfc9496_encode_4 :
    Ristretto.encodeRep (4 • basepoint) = hex "da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_four_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `5 B`. -/
theorem rfc9496_encode_5 :
    Ristretto.encodeRep (5 • basepoint) = hex "e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_five_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `6 B`. -/
theorem rfc9496_encode_6 :
    Ristretto.encodeRep (6 • basepoint) = hex "f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_six_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `7 B`. -/
theorem rfc9496_encode_7 :
    Ristretto.encodeRep (7 • basepoint) = hex "44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_seven_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `8 B`. -/
theorem rfc9496_encode_8 :
    Ristretto.encodeRep (8 • basepoint) = hex "903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_eight_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `9 B`. -/
theorem rfc9496_encode_9 :
    Ristretto.encodeRep (9 • basepoint) = hex "02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_nine_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `10 B`. -/
theorem rfc9496_encode_10 :
    Ristretto.encodeRep (10 • basepoint) = hex "20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_ten_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `11 B`. -/
theorem rfc9496_encode_11 :
    Ristretto.encodeRep (11 • basepoint) = hex "bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_eleven_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `12 B`. -/
theorem rfc9496_encode_12 :
    Ristretto.encodeRep (12 • basepoint) = hex "e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_twelve_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `13 B`. -/
theorem rfc9496_encode_13 :
    Ristretto.encodeRep (13 • basepoint) = hex "aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_thirteen_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `14 B`. -/
theorem rfc9496_encode_14 :
    Ristretto.encodeRep (14 • basepoint) = hex "46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_fourteen_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.1: the encoding of `15 B`. -/
theorem rfc9496_encode_15 :
    Ristretto.encodeRep (15 • basepoint) = hex "e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Proofs.encodeRepNat_fifteen_nsmul_basepoint]
  decide +kernel

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`). -/
theorem rfc9496_invalid_noncanonical₁ :
    Ristretto.decodeRep (hex "00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_noncanonical_vector₁ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`). -/
theorem rfc9496_invalid_noncanonical₂ :
    Ristretto.decodeRep (hex "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_noncanonical_vector₂ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`). -/
theorem rfc9496_invalid_noncanonical₃ :
    Ristretto.decodeRep (hex "f3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_noncanonical_vector₃ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`). -/
theorem rfc9496_invalid_noncanonical₄ :
    Ristretto.decodeRep (hex "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_noncanonical_vector₄ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₁ :
    Ristretto.decodeRep (hex "0100000000000000000000000000000000000000000000000000000000000000") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₁ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₂ :
    Ristretto.decodeRep (hex "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₂ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₃ :
    Ristretto.decodeRep (hex "ed57ffd8c914fb201471d1c3d245ce3c746fcbe63a3679d51b6a516ebebe0e20") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₃ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₄ :
    Ristretto.decodeRep (hex "c34c4e1826e5d403b78e246e88aa051c36ccf0aafebffe137d148a2bf9104562") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₄ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₅ :
    Ristretto.decodeRep (hex "c940e5a4404157cfb1628b108db051a8d439e1a421394ec4ebccb9ec92a8ac78") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₅ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₆ :
    Ristretto.decodeRep (hex "47cfc5497c53dc8e61c91d17fd626ffb1c49e2bca94eed052281b510b1117a24") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₆ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₇ :
    Ristretto.decodeRep (hex "f1c6165d33367351b0da8f6e4511010c68174a03b6581212c71c0e1d026c3c72") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₇ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, a negative field element. -/
theorem rfc9496_invalid_negative₈ :
    Ristretto.decodeRep (hex "87260f7a2f12495118360f02c26a470f450dadf34a413d21042b43b9d93e1309") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_vector₈ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₁ :
    Ristretto.decodeRep (hex "26948d35ca62e643e26a83177332e6b6afeb9d08e4268b650f1f5bbd8d81d371") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₁ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₂ :
    Ristretto.decodeRep (hex "4eac077a713c57b4f4397629a4145982c661f48044dd3f96427d40b147d9742f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₂ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₃ :
    Ristretto.decodeRep (hex "de6a7b00deadc788eb6b6c8d20c0ae96c2f2019078fa604fee5b87d6e989ad7b") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₃ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₄ :
    Ristretto.decodeRep (hex "bcab477be20861e01e4a0e295284146a510150d9817763caf1a6f4b422d67042") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₄ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₅ :
    Ristretto.decodeRep (hex "2a292df7e32cababbd9de088d1d1abec9fc0440f637ed2fba145094dc14bea08") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₅ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₆ :
    Ristretto.decodeRep (hex "f4a9e534fc0d216c44b218fa0c42d99635a0127ee2e53c712f70609649fdff22") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₆ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₇ :
    Ristretto.decodeRep (hex "8268436f8c4126196cf64b3c7ddbda90746a378625f9813dd9b8457077256731") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₇ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x²` is not a square. -/
theorem rfc9496_invalid_nonsquare₈ :
    Ristretto.decodeRep (hex "2810e5cbc2cc4d4eece54f61c6f69758e289aa7ab440b3cbeaa21995c2f4232b") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_nonsquare_vector₈ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₁ :
    Ristretto.decodeRep (hex "3eb858e78f5a7254d8c9731174a94f76755fd3941c0ac93735c07ba14579630e") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₁ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₂ :
    Ristretto.decodeRep (hex "a45fdc55c76448c049a1ab33f17023edfb2be3581e9c7aade8a6125215e04220") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₂ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₃ :
    Ristretto.decodeRep (hex "d483fe813c6ba647ebbfd3ec41adca1c6130c2beeee9d9bf065c8d151c5f396e") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₃ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₄ :
    Ristretto.decodeRep (hex "8a2e1d30050198c65a54483123960ccc38aef6848e1ec8f5f780e8523769ba32") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₄ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₅ :
    Ristretto.decodeRep (hex "32888462f8b486c68ad7dd9610be5192bbeaf3b443951ac1a8118419d9fa097b") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₅ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₆ :
    Ristretto.decodeRep (hex "227142501b9d4355ccba290404bde41575b037693cef1f438c47f8fbf35d1165") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₆ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₇ :
    Ristretto.decodeRep (hex "5c37cc491da847cfeb9281d407efc41e15144c876e0170b499a96a22ed31e01e") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₇ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `x y` is negative. -/
theorem rfc9496_invalid_negative_xy₈ :
    Ristretto.decodeRep (hex "445425117cb8c90edcbc7c1cc0e74f747f2c1efa5630a967c64f287792a48a4b") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_negative_xy_vector₈ using 2
  decide +kernel

/-- RFC 9496 §A.2: rejected, `s = -1`, so `y = 0`. -/
theorem rfc9496_invalid_y_zero :
    Ristretto.decodeRep (hex "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f") = none := by
  change Ristretto.decodeRepNat (decodeLittleEndian _) = none
  convert Proofs.decodeRepNat_y_zero_vector using 2
  decide +kernel

/-- RFC 9496 §A.3, vector 1. -/
theorem rfc9496_map_1 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "5d1be09e3d0c82fc538112490e35701979d99e06ca3e2b5b54bffe8b4dc772c14d98b696a1bbfb5ca32c436cc61c16563790306c79eaca7705668b47dffe5bb6")) =
      hex "3066f82a1a747d45120d1740f14358531a8f04bbffe6a819f86dfe50f44a0a46" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₁ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 2. -/
theorem rfc9496_map_2 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "f116b34b8f17ceb56e8732a60d913dd10cce47a6d53bee9204be8b44f6678b270102a56902e2488c46120e9276cfe54638286b9e4b3cdb470b542d46c2068d38")) =
      hex "f26e5b6f7d362d2d2a94c5d0e7602cb4773c95a2e5c31a64f133189fa76ed61b" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₂ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 3. -/
theorem rfc9496_map_3 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "8422e1bbdaab52938b81fd602effb6f89110e1e57208ad12d9ad767e2e25510c27140775f9337088b982d83d7fcf0b2fa1edffe51952cbe7365e95c86eaf325c")) =
      hex "006ccd2a9e6867e6a2c5cea83d3302cc9de128dd2a9a57dd8ee7b9d7ffe02826" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₃ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 4. -/
theorem rfc9496_map_4 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "ac22415129b61427bf464e17baee8db65940c233b98afce8d17c57beeb7876c2150d15af1cb1fb824bbd14955f2b57d08d388aab431a391cfc33d5bafb5dbbaf")) =
      hex "f8f0c87cf237953c5890aec3998169005dae3eca1fbb04548c635953c817f92a" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₄ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 5. -/
theorem rfc9496_map_5 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "165d697a1ef3d5cf3c38565beefcf88c0f282b8e7dbd28544c483432f1cec7675debea8ebb4e5fe7d6f6e5db15f15587ac4d4d4a1de7191e0c1ca6664abcc413")) =
      hex "ae81e7dedf20a497e10c304a765c1767a42d6e06029758d2d7e8ef7cc4c41179" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₅ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 6. -/
theorem rfc9496_map_6 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "a836e6c9a9ca9f1e8d486273ad56a78c70cf18f0ce10abb1c7172ddd605d7fd2979854f47ae1ccf204a33102095b4200e5befc0465accc263175485f0e17ea5c")) =
      hex "e2705652ff9f5e44d3e841bf1c251cf7dddb77d140870d1ab2ed64f1a9ce8628" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₆ using 4
  · decide +kernel
  · decide +kernel

/-- RFC 9496 §A.3, vector 7. -/
theorem rfc9496_map_7 :
    Ristretto.encodeRep (Ristretto.fromUniformRep
      (hex "2cdc11eaeb95daf01189417cdddbf95952993aa9cb9c640eb5058d09702c74622c9965a697a3b345ec24ee56335b556e677b30e6f90ac77d781064f866a3c982")) =
      hex "80bd07262511cdde4863f8a7434cef696750681cb9510eea557088f76d9e5065" := by
  change encodeLittleEndian 32 (Ristretto.encodeRepNat _) = _
  rw [Ristretto.fromUniformRep_eq]
  convert congrArg (encodeLittleEndian 32) Proofs.fromUniformRepNat_vector₇ using 4
  · decide +kernel
  · decide +kernel

end TestVectors
