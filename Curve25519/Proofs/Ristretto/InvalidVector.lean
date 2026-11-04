/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding
import all Curve25519.Basic
public section

/-! # The RFC 9496 §A.2 and §A.4 test vectors (not audited)

**§A.2, invalid encodings**: `Ristretto.decodeRep` rejects each of the 29 byte strings, read as
little-endian numbers, for the reason the RFC lists. Non-canonical encodings (`s ≥ p`) and
negative field elements are rejected by the first two disjuncts of `decodeRep_eq_none_iff`,
decided by the kernel. For the others the output of `SQRT_RATIO_M1(1, w)` is not computable, so
each comes with a certificate (`DecodeNoneCert`): the flag `b` and the root `r` with
`w r² = 1` (square) or `w r² = √-1` (non-square), `r` non-negative, which fix
`sqrtRatioM1 1 w` by `sqrtRatioM1_eq_of_mul_sq_eq` or `sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`;
the rejection itself (`b = false`, `x y` negative, or `y = 0`) is then decided by the kernel.

**§A.4, `SQRT_RATIO_M1`**: the six input/output pairs of `sqrtRatioM1`, including the cases
`v = 0`.

`Curve25519.Basic` is imported with `import all` so that the kernel can unfold `p` and `sqrtM1`;
`d` is used as a numeral (`d_eq_numeral`), so that the kernel never meets a field inverse. -/

namespace curve25519.Proofs

open Ristretto

/-! ### The decoding certificate -/

/-- `d` as a numeral. -/
private noncomputable abbrev dNum : ZMod p :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `u1 = 1 - s²` of RFC 9496 §4.3.1. -/
private noncomputable abbrev decU1 (s : ℕ) : ZMod p := 1 - (s : ZMod p) ^ 2

/-- `u2 = 1 + s²` of RFC 9496 §4.3.1. -/
private noncomputable abbrev decU2 (s : ℕ) : ZMod p := 1 + (s : ZMod p) ^ 2

/-- `v = -(d u1²) - u2²` of RFC 9496 §4.3.1. -/
private noncomputable abbrev decV (s : ℕ) : ZMod p := -(dNum * decU1 s ^ 2) - decU2 s ^ 2

/-- `w = v u2²`, the argument of `SQRT_RATIO_M1(1, w)`. -/
private noncomputable abbrev decW (s : ℕ) : ZMod p := decV s * decU2 s ^ 2

/-- `x = |2 s r u2|` for the root `r`. -/
private noncomputable abbrev decX (s : ℕ) (r : ZMod p) : ZMod p :=
  (2 * (s : ZMod p) * (r * decU2 s)).abs

/-- `y = u1 r (r u2) v` for the root `r`. -/
private noncomputable abbrev decY (s : ℕ) (r : ZMod p) : ZMod p :=
  decU1 s * (r * (r * decU2 s) * decV s)

/-- The certificate that `s < p`, non-negative, is rejected: the output `(b, r)` of
`SQRT_RATIO_M1(1, w)`, and a rejection reason. -/
private abbrev DecodeNoneCert (s : ℕ) (b : Bool) (r : ZMod p) : Prop :=
  decW s ≠ 0 ∧ (if b then decW s * r ^ 2 = 1 else decW s * r ^ 2 = sqrtM1) ∧ ¬ r.IsNeg ∧
    (b = false ∨ (decX s r * decY s r).IsNeg ∨ decY s r = 0)

private theorem decodeRep_eq_none_of_cert {s : ℕ} {b : Bool} {r : ZMod p}
    (h : DecodeNoneCert s b r) : decodeRep s = none := by
  obtain ⟨hw, hr, hneg, hc⟩ := h
  have hsq : sqrtRatioM1 1 (decW s) = (b, r) := by
    cases b
    · simp only [Bool.false_eq_true, reduceIte] at hr
      exact sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul one_ne_zero hw (by rw [hr, mul_one]) hneg
    · simp only [reduceIte] at hr
      exact sqrtRatioM1_eq_of_mul_sq_eq hw hr hneg
  have hd : (d : ZMod p) = dNum := d_eq_numeral
  rw [decodeRep_eq_none_iff]
  refine Or.inr (Or.inr ?_)
  simp only [hd]
  rw [hsq]
  exact hc

/-! ### §A.2: invalid encodings -/

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`):
`00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff`. -/
theorem decodeRep_noncanonical_vector₁ :
    decodeRep
      115792089237316195423570985008687907853269984665640564039457584007913129639680 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inl (by decide +kernel))

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`):
`ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f`. -/
theorem decodeRep_noncanonical_vector₂ :
    decodeRep
      57896044618658097711785492504343953926634992332820282019728792003956564819967 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inl (by decide +kernel))

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`):
`f3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f`. -/
theorem decodeRep_noncanonical_vector₃ :
    decodeRep
      57896044618658097711785492504343953926634992332820282019728792003956564819955 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inl (by decide +kernel))

/-- RFC 9496 §A.2: rejected, a non-canonical field encoding (`s ≥ p`):
`edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f`. -/
theorem decodeRep_noncanonical_vector₄ :
    decodeRep
      57896044618658097711785492504343953926634992332820282019728792003956564819949 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inl (by decide +kernel))

/-- RFC 9496 §A.2: rejected, a negative field element:
`0100000000000000000000000000000000000000000000000000000000000000`. -/
theorem decodeRep_negative_vector₁ :
    decodeRep
      1 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f`. -/
theorem decodeRep_negative_vector₂ :
    decodeRep
      57896044618658097711785492504343953926634992332820282019728792003956564819713 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`ed57ffd8c914fb201471d1c3d245ce3c746fcbe63a3679d51b6a516ebebe0e20`. -/
theorem decodeRep_negative_vector₃ :
    decodeRep
      14500063479385022835277550739659379331097757728016956051479075437203123296237 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`c34c4e1826e5d403b78e246e88aa051c36ccf0aafebffe137d148a2bf9104562`. -/
theorem decodeRep_negative_vector₄ :
    decodeRep
      44448688754183314721721344638891431560531202985536057727689530136001747242179 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`c940e5a4404157cfb1628b108db051a8d439e1a421394ec4ebccb9ec92a8ac78`. -/
theorem decodeRep_negative_vector₅ :
    decodeRep
      54582602979602457643045862250683707780101699596462536220851499828713588342985 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`47cfc5497c53dc8e61c91d17fd626ffb1c49e2bca94eed052281b510b1117a24`. -/
theorem decodeRep_negative_vector₆ :
    decodeRep
      16498939994258671651386659247120748516844473226545390441333276669266350165831 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`f1c6165d33367351b0da8f6e4511010c68174a03b6581212c71c0e1d026c3c72`. -/
theorem decodeRep_negative_vector₇ :
    decodeRep
      51670421007964280017714657847731230710296330325571800364228970257034673309425 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, a negative field element:
`87260f7a2f12495118360f02c26a470f450dadf34a413d21042b43b9d93e1309`. -/
theorem decodeRep_negative_vector₈ :
    decodeRep
      4104819509572519868543201024037287795491268958940121123356327555578876339847 =
      none :=
  (decodeRep_eq_none_iff _).mpr (Or.inr (Or.inl (by decide +kernel)))

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`26948d35ca62e643e26a83177332e6b6afeb9d08e4268b650f1f5bbd8d81d371`. -/
theorem decodeRep_nonsquare_vector₁ :
    decodeRep
      51485050767150065296458600688377593423602953320526694477039286172342700315686 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 15495766577639823676134711900429752138655598233747952377110188658380030747772)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`4eac077a713c57b4f4397629a4145982c661f48044dd3f96427d40b147d9742f`. -/
theorem decodeRep_nonsquare_vector₂ :
    decodeRep
      21465157754708084739295311339221741375582979524553508060362804158963009432654 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 55838612514174573003936752383750239017642994889237308434742020730857099470918)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`de6a7b00deadc788eb6b6c8d20c0ae96c2f2019078fa604fee5b87d6e989ad7b`. -/
theorem decodeRep_nonsquare_vector₃ :
    decodeRep
      55941096761458023935414165186618277230102282874700631014809344935399702358750 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 21455641947020703919336828571051057529954001923034546029624271284347852572412)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`bcab477be20861e01e4a0e295284146a510150d9817763caf1a6f4b422d67042`. -/
theorem decodeRep_nonsquare_vector₄ :
    decodeRep
      30052012787164017089121292961038987026176433828842582417638094166262857313212 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 43182623907231055326405292051357624650723409329646767908243503637802092468120)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`2a292df7e32cababbd9de088d1d1abec9fc0440f637ed2fba145094dc14bea08`. -/
theorem decodeRep_nonsquare_vector₅ :
    decodeRep
      4032467844182849831712595614101993190077054406673099007880897604436963961130 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 19417097946183953915422276571006201303435397471303076285808717407144429418454)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`f4a9e534fc0d216c44b218fa0c42d99635a0127ee2e53c712f70609649fdff22`. -/
theorem decodeRep_nonsquare_vector₆ :
    decodeRep
      15830930979087906057892298639120223705645399539580142363297277837331191409140 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 44126555934488131141663378753040633090288561779528086278320459372021832543212)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`8268436f8c4126196cf64b3c7ddbda90746a378625f9813dd9b8457077256731`. -/
theorem decodeRep_nonsquare_vector₇ :
    decodeRep
      22345573412924369918757814700737317802150687057988310390209106077862634678402 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 2161296845656190544269730829318851360185308826748634120057465622558984990556)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x²` is not a square:
`2810e5cbc2cc4d4eece54f61c6f69758e289aa7ab440b3cbeaa21995c2f4232b`. -/
theorem decodeRep_nonsquare_vector₈ :
    decodeRep
      19512981408388046136274577458805827768748955170706921029493671264916986990632 =
      none :=
  decodeRep_eq_none_of_cert (b := false)
    (r := 4707050997096535242273165358078689409787319594492845846736053289527650113656)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`3eb858e78f5a7254d8c9731174a94f76755fd3941c0ac93735c07ba14579630e`. -/
theorem decodeRep_negative_xy_vector₁ :
    decodeRep
      6508134728129258267401785812917589461151538941415167511984634590058360911934 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 24148388594628047181851572655204867419785385960599161985958566482611523479780)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`a45fdc55c76448c049a1ab33f17023edfb2be3581e9c7aade8a6125215e04220`. -/
theorem decodeRep_negative_xy_vector₂ :
    decodeRep
      14592169626923739789736967519467918409703774004045942201217664573082009624484 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 51484793662681944968165430015316673272019968522942787237028922309671063146562)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`d483fe813c6ba647ebbfd3ec41adca1c6130c2beeee9d9bf065c8d151c5f396e`. -/
theorem decodeRep_negative_xy_vector₃ :
    decodeRep
      49855780049902832452981760172249188176338395096175585508694799137701665604564 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 1606618290398347102798879518107870479680653125700696713281086337080993463222)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`8a2e1d30050198c65a54483123960ccc38aef6848e1ec8f5f780e8523769ba32`. -/
theorem decodeRep_negative_xy_vector₄ :
    decodeRep
      22945002158106833032138233898718596321274213043547452357469392415654131084938 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 29045884123425497480035810802511001246792817798091718703020583454326802190376)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`32888462f8b486c68ad7dd9610be5192bbeaf3b443951ac1a8118419d9fa097b`. -/
theorem decodeRep_negative_xy_vector₅ :
    decodeRep
      55652113288907032960861081309163558628596127364745050326116993777802630432818 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 48181155973447355981745025818081239593550587834853788094782817580173923100674)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`227142501b9d4355ccba290404bde41575b037693cef1f438c47f8fbf35d1165`. -/
theorem decodeRep_negative_xy_vector₆ :
    decodeRep
      45714282547223950863749405690062915276549156721896521676733608024734313902370 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 23393596812611006528822879098408512404439863683158441138075012380956694869478)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`5c37cc491da847cfeb9281d407efc41e15144c876e0170b499a96a22ed31e01e`. -/
theorem decodeRep_negative_xy_vector₇ :
    decodeRep
      13965503778711198918203915838518728987371894683505563766721209605120984889180 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 31645637207086812072258243862922921190887717832972837648929532853183299955856)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `x y` is negative:
`445425117cb8c90edcbc7c1cc0e74f747f2c1efa5630a967c64f287792a48a4b`. -/
theorem decodeRep_negative_xy_vector₈ :
    decodeRep
      34168424373786229169581271456527090150392758157833924976893378783710571484228 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 33230949984783740297605643094641858841147837653084682937890737920185063201720)
    (by decide +kernel)

/-- RFC 9496 §A.2: rejected, `s = -1`, so `y = 0`:
`ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f`. -/
theorem decodeRep_y_zero_vector :
    decodeRep
      57896044618658097711785492504343953926634992332820282019728792003956564819948 =
      none :=
  decodeRep_eq_none_of_cert (b := true)
    (r := 4920290344176876489201769826247135503861516628980972540686005268280957446188)
    (by decide +kernel)

/-! ### §A.4: `SQRT_RATIO_M1` -/

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(0, 0) = (TRUE, 00000000…)`. -/
theorem sqrtRatioM1_vector₁ :
    sqrtRatioM1 (0 : ZMod p) 0 = (true, 0) :=
  sqrtRatioM1_zero_zero

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(0, 1) = (TRUE, 00000000…)`. -/
theorem sqrtRatioM1_vector₂ :
    sqrtRatioM1 (0 : ZMod p) 1 = (true, 0) :=
  sqrtRatioM1_zero_left 1

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(1, 0) = (FALSE, 00000000…)`. -/
theorem sqrtRatioM1_vector₃ :
    sqrtRatioM1 (1 : ZMod p) 0 = (false, 0) :=
  sqrtRatioM1_zero_right one_ne_zero

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(2, 1) = (FALSE, 3c5ff1b5…)`. -/
theorem sqrtRatioM1_vector₄ :
    sqrtRatioM1 (2 : ZMod p) 1 = (false,
      38214883241950591754978413199355411911188925816896391856984770930832735035196) :=
  sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(4, 1) = (TRUE, 02000000…)`. -/
theorem sqrtRatioM1_vector₅ :
    sqrtRatioM1 (4 : ZMod p) 1 = (true, 2) :=
  sqrtRatioM1_eq_of_mul_sq_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.4: `SQRT_RATIO_M1(1, 4) = (TRUE, f6ffffff…)`. -/
theorem sqrtRatioM1_vector₆ :
    sqrtRatioM1 (1 : ZMod p) 4 = (true,
      28948022309329048855892746252171976963317496166410141009864396001978282409974) :=
  sqrtRatioM1_eq_of_mul_sq_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)

end curve25519.Proofs
