/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Encoding
import all Curve25519.Basic
import Curve25519.Proofs.Edwards.Certs
import Curve25519.Proofs.Ristretto.Certs
public section

/-! # The RFC 9496 §A.1 test vectors for the ristretto255 encoding (not audited)

Kernel checks (`decide +kernel`) of the encodings of the multiples `2 B, …, 15 B` of the
basepoint against RFC 9496 §A.1 (the encoding of `B` itself is `encodeRepNat_basepoint` in
`Curve25519.Ristretto.Encoding`): a regression test of `Ristretto.encodeRepNat`. For each `k`, the
coordinates of `k • basepoint` are certified by a projective-equality check of `Extended.nsmul`
(as in `Curve25519.Proofs.Edwards.Certs`), the inverse square root of `(1 + y)(1 - y)(x y)²` is
exhibited as a numeral, and the rest of RFC 9496 §4.3.2 is evaluated by the kernel.
`Curve25519.Basic` is imported with `import all` so that the kernel can unfold `p`, `sqrtM1` and
`invsqrtAMinusD`. -/

namespace curve25519.Proofs

open TwistedEdwardsModel

/-- The basepoint `(x, y, 1, x y)` in extended coordinates of a model over `ZMod p`, as numerals
(generic in the model, so that `edwards_eq` rewrites through it). -/
private noncomputable abbrev basepointExt (E : TwistedEdwardsModel (ZMod p)) : E.Extended :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
    46316835694926478169428394003475163141307993866256225615783033603165251855960, 1,
    15112221349535400772501151409588531511454012693041857206046113283949847762202 *
      46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

/-- `encodeRepNat (k • B) = n` from the coordinates `(x', y')` of `k • B` (a projective-equality
check of `Extended.nsmul`), the inverse square root `r` of `(1 + y')(1 - y')(x' y')²` as a
numeral, and a kernel evaluation of the rest (`encodeRepOf`). -/
private theorem encodeRepNat_nsmul_basepoint {k : ℕ} {x' y' r : ZMod p} {n : ℕ}
    (h' : edwards.Equation x' y')
    (hc : (Extended.nsmul k (basepointExt edwards)).ProjEq ⟨x', y', 1, x' * y'⟩)
    (hr : (1 + y') * (1 - y') * (x' * y') ^ 2 * r ^ 2 = 1) (hneg : ¬ r.IsNeg)
    (he : encodeRepOf x' y' r = n) : Ristretto.encodeRepNat (k • basepoint) = n := by
  obtain ⟨hx, hy⟩ := nsmul_x_y_of_coords basepoint basepoint_x_eq basepoint_y_eq h' hc
  exact encodeRepNat_of_coords _ hx hy hr hneg he

/-! ### `2 B` -/

/-- RFC 9496 §A.1: the encoding of `2 B` is
`6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919`. -/
theorem encodeRepNat_two_nsmul_basepoint :
    Ristretto.encodeRepNat (2 • basepoint) =
      11635816016306827767395297108041383048417969937796188516319649271592942455146 :=
  encodeRepNat_nsmul_basepoint
    (x' := 24727413235106541002554574571675588834622768167397638456726423682521233608206)
    (y' := 15549675580280190176352668710449542251549572066445060580507079593062643049417)
    (r := 44983099649789203610693030478239648478500906748903471392021725998287843189168)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `3 B` -/

/-- RFC 9496 §A.1: the encoding of `3 B` is
`94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259`. -/
theorem encodeRepNat_three_nsmul_basepoint :
    Ristretto.encodeRepNat (3 • basepoint) =
      40260461926755251955718706939243089925229788613177830462037219643110335673492 :=
  encodeRepNat_nsmul_basepoint
    (x' := 46896733464454938657123544595386787789046198280132665686241321779790909858396)
    (y' := 8324843778533443976490377120369201138301417226297555316741202210403726505172)
    (r := 36497461975840538690775936217744539451560550655315987188433936599141694408376)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `4 B` -/

/-- RFC 9496 §A.1: the encoding of `4 B` is
`da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57`. -/
theorem encodeRepNat_four_nsmul_basepoint :
    Ristretto.encodeRepNat (4 • basepoint) =
      39539712639727764854030096366263363835037234367571502173881976170473752789210 :=
  encodeRepNat_nsmul_basepoint
    (x' := 14582954232372986451776170844943001818709880559417862259286374126315108956272)
    (y' := 32483318716863467900234833297694612235682047836132991208333042722294373421359)
    (r := 35035121287605745812010655531725244480097667362960576006075430377872208938292)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `5 B` -/

/-- RFC 9496 §A.1: the encoding of `5 B` is
`e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e`. -/
theorem encodeRepNat_five_nsmul_basepoint :
    Ristretto.encodeRepNat (5 • basepoint) =
      35711617013263642786200824652404949926957298723655034617396250384949589410536 :=
  encodeRepNat_nsmul_basepoint
    (x' := 33467004535436536005251147249499675200073690106659565782908757308821616914995)
    (y' := 43097193783671926753355113395909008640284023746042808659097434958891230611693)
    (r := 36864048792385267477785273181408709010075678839984391979759091284924269403108)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `6 B` -/

/-- RFC 9496 §A.1: the encoding of `6 B` is
`f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403`. -/
theorem encodeRepNat_six_nsmul_basepoint :
    Ristretto.encodeRepNat (6 • basepoint) =
      1788254424908918268483736458686471308637153583273756912236989785099523737590 :=
  encodeRepNat_nsmul_basepoint
    (x' := 34643617590234865996699167120328052565261792237873803846102513686264813449789)
    (y' := 2399184961499513294557607325187831088545696902880432827228757905043131825908)
    (r := 23597701923362501195997216484741126723870607845115886041667811608139015248572)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `7 B` -/

/-- RFC 9496 §A.1: the encoding of `7 B` is
`44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d`. -/
theorem encodeRepNat_seven_nsmul_basepoint :
    Ristretto.encodeRepNat (7 • basepoint) =
      49343031373861346077246395661435597073206147504694015916602945883209739924804 :=
  encodeRepNat_nsmul_basepoint
    (x' := 9199134265559022971505535402808359556995554859516252602543778295037484220679)
    (y' := 22512087849695599276028560866629687720820254811233262850576678203618951717560)
    (r := 42522262833952556978665942061542260250276734237943600715593307807815159555802)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `8 B` -/

/-- RFC 9496 §A.1: the encoding of `8 B` is
`903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c`. -/
theorem encodeRepNat_eight_nsmul_basepoint :
    Ristretto.encodeRepNat (8 • basepoint) =
      12834969691472587231593312321477678625073638764492513285296224875004126507664 :=
  encodeRepNat_nsmul_basepoint
    (x' := 46706390780465557264338673484185971070529246228527338942042475661633188627656)
    (y' := 15299170165656271974649334809062094114079726227711063015095704409550798436788)
    (r := 23000972404242694156955020320386166686775676779813540364560723985311582255938)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `9 B` -/

/-- RFC 9496 §A.1: the encoding of `9 B` is
`02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031`. -/
theorem encodeRepNat_nine_nsmul_basepoint :
    Ristretto.encodeRepNat (9 • basepoint) =
      22332999780978691439433262707127500106954015930284539402710831823977601196546 :=
  encodeRepNat_nsmul_basepoint
    (x' := 24193060302538010417230488029838514081720802923509845138863968807030823940444)
    (y' := 57551756252899625001155759838357770487605224608455116862194664796369308545472)
    (r := 25860964878592866729865149077466376028126010202715821634870612722983097663674)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `10 B` -/

/-- RFC 9496 §A.1: the encoding of `10 B` is
`20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f`. -/
theorem encodeRepNat_ten_nsmul_basepoint :
    Ristretto.encodeRepNat (10 • basepoint) =
      43296902171613338270316180077133270930173776004594811824122909877887271137312 :=
  encodeRepNat_nsmul_basepoint
    (x' := 43500613248243327786121022071801015118933854441360174117148262713429272820047)
    (y' := 45005105423099817237495816771148012388779685712352441364231470781391834741548)
    (r := 23775496168407050728476307448257940900434002109640482907012210020806968671574)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `11 B` -/

/-- RFC 9496 §A.1: the encoding of `11 B` is
`bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42`. -/
theorem encodeRepNat_eleven_nsmul_basepoint :
    Ristretto.encodeRepNat (11 • basepoint) =
      30156530449173838445290106302113728740453244852608503736534270739358022625468 :=
  encodeRepNat_nsmul_basepoint
    (x' := 9451145793506787353375160377761530931587019091193333050860601958827395183563)
    (y' := 20609402718286069808115703540855311742885093522056241285814584245966805874451)
    (r := 27054922186333675756409881331068898103917418403452157499747384521499367621034)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `12 B` -/

/-- RFC 9496 §A.1: the encoding of `12 B` is
`e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460`. -/
theorem encodeRepNat_twelve_nsmul_basepoint :
    Ristretto.encodeRepNat (12 • basepoint) =
      43543894574131407852979279332177882444676506611650446010128826931834072749284 :=
  encodeRepNat_nsmul_basepoint
    (x' := 32159939716063394567822525359727347405356413309540137282993608327129696604205)
    (y' := 29147333543209904737197244325450674102993621692520459538942544703173373584633)
    (r := 27446688300725529313969938649410417677737265657747148603308518262233791394068)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `13 B` -/

/-- RFC 9496 §A.1: the encoding of `13 B` is
`aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f`. -/
theorem encodeRepNat_thirteen_nsmul_basepoint :
    Ristretto.encodeRepNat (13 • basepoint) =
      14163545407837206310051546595701536016361346949044556924887299097062973395626 :=
  encodeRepNat_nsmul_basepoint
    (x' := 7442235066513780790779899786332475485840754593728627195931759107337804079085)
    (y' := 8529785864514984411577036536286432879603480171865651918962709025066066124672)
    (r := 22014132603565178048751708030024053989022926549154153870001412763372316620972)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `14 B` -/

/-- RFC 9496 §A.1: the encoding of `14 B` is
`46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e`. -/
theorem encodeRepNat_fourteen_nsmul_basepoint :
    Ristretto.encodeRepNat (14 • basepoint) =
      13654307986525245705541547241685942107063914559952375847980265621465556793158 :=
  encodeRepNat_nsmul_basepoint
    (x' := 14642270634066990240227516988620748386040643134865523775420225321890511918521)
    (y' := 35422008320351900419562335198749713095866812710345432231966142485751234570297)
    (r := 15742537566750925888039108908282020821405164932189482342643218283855661233478)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### `15 B` -/

/-- RFC 9496 §A.1: the encoding of `15 B` is
`e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e`. -/
theorem encodeRepNat_fifteen_nsmul_basepoint :
    Ristretto.encodeRepNat (15 • basepoint) =
      35687351115805770120198060148188801341203537996309241960823042583481424594144 :=
  encodeRepNat_nsmul_basepoint
    (x' := 35771902585589234259498423420223840099331465042459337605611172842168536632769)
    (y' := 8502034780705657720897159939055122322178084209392286764802307224484658961631)
    (r := 18172309307421360256977488612855814185825149084848020461244509251665279586370)
    (by rw [edwards_eq]; decide +kernel) (by rw [edwards_eq]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### The encodings on bytes

The same vectors as byte strings, as RFC 9496 writes them: `Ristretto.encodeRep` on
`Vector UInt8 32` is the encoding of `encodeRepNat`. -/

private theorem encodeRep_of_encodeRepNat {P : edwards.Point} {N : ℕ} {o : Vector UInt8 32}
    (h : Ristretto.encodeRepNat P = N) (ho : encodeLittleEndian 32 N = o) :
    Ristretto.encodeRep P = o := by
  rw [Ristretto.encodeRep, h, ho]

/-- RFC 9496 §A.1: the encoding of `2 B` is
`6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919`. -/
theorem encodeRep_two_nsmul_basepoint :
    Ristretto.encodeRep (2 • basepoint) =
      #v[0x6a, 0x49, 0x32, 0x10, 0xf7, 0x49, 0x9c, 0xd1,
         0x7f, 0xec, 0xb5, 0x10, 0xae, 0x0c, 0xea, 0x23,
         0xa1, 0x10, 0xe8, 0xd5, 0xb9, 0x01, 0xf8, 0xac,
         0xad, 0xd3, 0x09, 0x5c, 0x73, 0xa3, 0xb9, 0x19] :=
  encodeRep_of_encodeRepNat encodeRepNat_two_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `3 B` is
`94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259`. -/
theorem encodeRep_three_nsmul_basepoint :
    Ristretto.encodeRep (3 • basepoint) =
      #v[0x94, 0x74, 0x1f, 0x5d, 0x5d, 0x52, 0x75, 0x5e,
         0xce, 0x4f, 0x23, 0xf0, 0x44, 0xee, 0x27, 0xd5,
         0xd1, 0xea, 0x1e, 0x2b, 0xd1, 0x96, 0xb4, 0x62,
         0x16, 0x6b, 0x16, 0x15, 0x2a, 0x9d, 0x02, 0x59] :=
  encodeRep_of_encodeRepNat encodeRepNat_three_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `4 B` is
`da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57`. -/
theorem encodeRep_four_nsmul_basepoint :
    Ristretto.encodeRep (4 • basepoint) =
      #v[0xda, 0x80, 0x86, 0x27, 0x73, 0x35, 0x8b, 0x46,
         0x6f, 0xfa, 0xdf, 0xe0, 0xb3, 0x29, 0x3a, 0xb3,
         0xd9, 0xfd, 0x53, 0xc5, 0xea, 0x6c, 0x95, 0x53,
         0x58, 0xf5, 0x68, 0x32, 0x2d, 0xaf, 0x6a, 0x57] :=
  encodeRep_of_encodeRepNat encodeRepNat_four_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `5 B` is
`e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e`. -/
theorem encodeRep_five_nsmul_basepoint :
    Ristretto.encodeRep (5 • basepoint) =
      #v[0xe8, 0x82, 0xb1, 0x31, 0x01, 0x6b, 0x52, 0xc1,
         0xd3, 0x33, 0x70, 0x80, 0x18, 0x7c, 0xf7, 0x68,
         0x42, 0x3e, 0xfc, 0xcb, 0xb5, 0x17, 0xbb, 0x49,
         0x5a, 0xb8, 0x12, 0xc4, 0x16, 0x0f, 0xf4, 0x4e] :=
  encodeRep_of_encodeRepNat encodeRepNat_five_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `6 B` is
`f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403`. -/
theorem encodeRep_six_nsmul_basepoint :
    Ristretto.encodeRep (6 • basepoint) =
      #v[0xf6, 0x47, 0x46, 0xd3, 0xc9, 0x2b, 0x13, 0x05,
         0x0e, 0xd8, 0xd8, 0x02, 0x36, 0xa7, 0xf0, 0x00,
         0x7c, 0x3b, 0x3f, 0x96, 0x2f, 0x5b, 0xa7, 0x93,
         0xd1, 0x9a, 0x60, 0x1e, 0xbb, 0x1d, 0xf4, 0x03] :=
  encodeRep_of_encodeRepNat encodeRepNat_six_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `7 B` is
`44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d`. -/
theorem encodeRep_seven_nsmul_basepoint :
    Ristretto.encodeRep (7 • basepoint) =
      #v[0x44, 0xf5, 0x35, 0x20, 0x92, 0x6e, 0xc8, 0x1f,
         0xbd, 0x5a, 0x38, 0x78, 0x45, 0xbe, 0xb7, 0xdf,
         0x85, 0xa9, 0x6a, 0x24, 0xec, 0xe1, 0x87, 0x38,
         0xbd, 0xcf, 0xa6, 0xa7, 0x82, 0x2a, 0x17, 0x6d] :=
  encodeRep_of_encodeRepNat encodeRepNat_seven_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `8 B` is
`903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c`. -/
theorem encodeRep_eight_nsmul_basepoint :
    Ristretto.encodeRep (8 • basepoint) =
      #v[0x90, 0x32, 0x93, 0xd8, 0xf2, 0x28, 0x7e, 0xbe,
         0x10, 0xe2, 0x37, 0x4d, 0xc1, 0xa5, 0x3e, 0x0b,
         0xc8, 0x87, 0xe5, 0x92, 0x69, 0x9f, 0x02, 0xd0,
         0x77, 0xd5, 0x26, 0x3c, 0xdd, 0x55, 0x60, 0x1c] :=
  encodeRep_of_encodeRepNat encodeRepNat_eight_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `9 B` is
`02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031`. -/
theorem encodeRep_nine_nsmul_basepoint :
    Ristretto.encodeRep (9 • basepoint) =
      #v[0x02, 0x62, 0x2a, 0xce, 0x8f, 0x73, 0x03, 0xa3,
         0x1c, 0xaf, 0xc6, 0x3f, 0x8f, 0xc4, 0x8f, 0xdc,
         0x16, 0xe1, 0xc8, 0xc8, 0xd2, 0x34, 0xb2, 0xf0,
         0xd6, 0x68, 0x52, 0x82, 0xa9, 0x07, 0x60, 0x31] :=
  encodeRep_of_encodeRepNat encodeRepNat_nine_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `10 B` is
`20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f`. -/
theorem encodeRep_ten_nsmul_basepoint :
    Ristretto.encodeRep (10 • basepoint) =
      #v[0x20, 0x70, 0x6f, 0xd7, 0x88, 0xb2, 0x72, 0x0a,
         0x1e, 0xd2, 0xa5, 0xda, 0xd4, 0x95, 0x2b, 0x01,
         0xf4, 0x13, 0xbc, 0xf0, 0xe7, 0x56, 0x4d, 0xe8,
         0xcd, 0xc8, 0x16, 0x68, 0x9e, 0x2d, 0xb9, 0x5f] :=
  encodeRep_of_encodeRepNat encodeRepNat_ten_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `11 B` is
`bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42`. -/
theorem encodeRep_eleven_nsmul_basepoint :
    Ristretto.encodeRep (11 • basepoint) =
      #v[0xbc, 0xe8, 0x3f, 0x8b, 0xa5, 0xdd, 0x2f, 0xa5,
         0x72, 0x86, 0x4c, 0x24, 0xba, 0x18, 0x10, 0xf9,
         0x52, 0x2b, 0xc6, 0x00, 0x4a, 0xfe, 0x95, 0x87,
         0x7a, 0xc7, 0x32, 0x41, 0xca, 0xfd, 0xab, 0x42] :=
  encodeRep_of_encodeRepNat encodeRepNat_eleven_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `12 B` is
`e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460`. -/
theorem encodeRep_twelve_nsmul_basepoint :
    Ristretto.encodeRep (12 • basepoint) =
      #v[0xe4, 0x54, 0x9e, 0xe1, 0x6b, 0x9a, 0xa0, 0x30,
         0x99, 0xca, 0x20, 0x8c, 0x67, 0xad, 0xaf, 0xca,
         0xfa, 0x4c, 0x3f, 0x3e, 0x4e, 0x53, 0x03, 0xde,
         0x60, 0x26, 0xe3, 0xca, 0x8f, 0xf8, 0x44, 0x60] :=
  encodeRep_of_encodeRepNat encodeRepNat_twelve_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `13 B` is
`aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f`. -/
theorem encodeRep_thirteen_nsmul_basepoint :
    Ristretto.encodeRep (13 • basepoint) =
      #v[0xaa, 0x52, 0xe0, 0x00, 0xdf, 0x2e, 0x16, 0xf5,
         0x5f, 0xb1, 0x03, 0x2f, 0xc3, 0x3b, 0xc4, 0x27,
         0x42, 0xda, 0xd6, 0xbd, 0x5a, 0x8f, 0xc0, 0xbe,
         0x01, 0x67, 0x43, 0x6c, 0x59, 0x48, 0x50, 0x1f] :=
  encodeRep_of_encodeRepNat encodeRepNat_thirteen_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `14 B` is
`46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e`. -/
theorem encodeRep_fourteen_nsmul_basepoint :
    Ristretto.encodeRep (14 • basepoint) =
      #v[0x46, 0x37, 0x6b, 0x80, 0xf4, 0x09, 0xb2, 0x9d,
         0xc2, 0xb5, 0xf6, 0xf0, 0xc5, 0x25, 0x91, 0x99,
         0x08, 0x96, 0xe5, 0x71, 0x6f, 0x41, 0x47, 0x7c,
         0xd3, 0x00, 0x85, 0xab, 0x7f, 0x10, 0x30, 0x1e] :=
  encodeRep_of_encodeRepNat encodeRepNat_fourteen_nsmul_basepoint (by decide +kernel)

/-- RFC 9496 §A.1: the encoding of `15 B` is
`e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e`. -/
theorem encodeRep_fifteen_nsmul_basepoint :
    Ristretto.encodeRep (15 • basepoint) =
      #v[0xe0, 0xc4, 0x18, 0xf7, 0xc8, 0xd9, 0xc4, 0xcd,
         0xd7, 0x39, 0x5b, 0x93, 0xea, 0x12, 0x4f, 0x3a,
         0xd9, 0x90, 0x21, 0xbb, 0x68, 0x1d, 0xfc, 0x33,
         0x02, 0xa9, 0xd9, 0x9a, 0x2e, 0x53, 0xe6, 0x4e] :=
  encodeRep_of_encodeRepNat encodeRepNat_fifteen_nsmul_basepoint (by decide +kernel)

end curve25519.Proofs
