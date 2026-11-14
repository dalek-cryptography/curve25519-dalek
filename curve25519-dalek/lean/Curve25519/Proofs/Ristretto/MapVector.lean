/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519.Ristretto.Map
import all Curve25519.Basic
import Curve25519.Proofs.Ristretto.Certs
public section

/-! # The RFC 9496 §A.3 test vectors for the one-way map (not audited)

Kernel checks (`decide +kernel`) of `Ristretto.fromUniformRepNat` on the seven 64-byte inputs of RFC
9496 §A.3, as little-endian numbers `lo + 2^256 hi`: a regression test of `Ristretto.mapRepField`
(both branches of `sqrtRatioM1` occur) and of `Ristretto.encodeRepNat`.

Each vector is one certificate (`FromUniformCert`), checked by the kernel in a single
`decide +kernel`: the two halves `r₀`, `r₁` after `decodeU`; for each half the branch and the root
`ρ` of `SQRT_RATIO_M1(u, v)` (`MapCert`, with the conditions of `sqrtRatioM1_eq_of_mul_sq_eq` or
`sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul`) and the coordinates of `MAP(r)`; and the coordinates of
the sum (`AddCert`, the addition formula with its denominators). `fromUniformRepNat_xy_of_cert`
turns a certificate into the coordinates of `fromUniformRepNat n`, and the encoding is checked as in
`Curve25519.Proofs.Ristretto.TestVector` (`encodeRepNat_of_coords`). Every condition is a polynomial
identity or a non-vanishing: the kernel never meets a field inverse. `Curve25519.Basic` is imported
with `import all` so that the kernel can unfold `p`, `sqrtM1` and the ristretto255 constants. -/

namespace curve25519.Proofs

open TwistedEdwardsModel Ristretto

/-! ### The certificates -/

/-- `d` as a numeral. -/
private noncomputable abbrev dNum : ZMod p :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `u = (√-1 r₀² + 1)(1 - d²)` of RFC 9496 §4.3.4. -/
private noncomputable abbrev mapU (r₀ : ZMod p) : ZMod p :=
  (sqrtM1 * r₀ ^ 2 + 1) * oneMinusDSq

/-- `v = (-1 - √-1 r₀² d)(√-1 r₀² + d)` of RFC 9496 §4.3.4. -/
private noncomputable abbrev mapV (r₀ : ZMod p) : ZMod p :=
  (-1 - sqrtM1 * r₀ ^ 2 * dNum) * (sqrtM1 * r₀ ^ 2 + dNum)

/-- `s` of RFC 9496 §4.3.4, from the branch `b` and the root `ρ` of `SQRT_RATIO_M1(u, v)`. -/
private noncomputable abbrev mapS (b : Bool) (r₀ ρ : ZMod p) : ZMod p :=
  if b then ρ else -(ρ * r₀).abs

/-- The denominator `w1 = N √(a d - 1)` of the `x`-coordinate of `MAP(r₀)`. -/
private noncomputable abbrev mapDen (b : Bool) (r₀ : ZMod p) : ZMod p :=
  ((if b then -1 else sqrtM1 * r₀ ^ 2) * (sqrtM1 * r₀ ^ 2 - 1) * dMinusOneSq - mapV r₀) *
    sqrtAdMinusOne

/-- The certificate for `MAP(r₀) = (x, y)`: `ρ` is the output of `SQRT_RATIO_M1(u, v)` with
flag `b`, and `x`, `y` solve the two divisions. -/
private abbrev MapCert (b : Bool) (r₀ ρ x y : ZMod p) : Prop :=
  mapV r₀ ≠ 0 ∧
    (if b then mapV r₀ * ρ ^ 2 = mapU r₀
      else mapU r₀ ≠ 0 ∧ mapV r₀ * ρ ^ 2 = sqrtM1 * mapU r₀) ∧
    ¬ ρ.IsNeg ∧ mapDen b r₀ ≠ 0 ∧ 2 * mapS b r₀ ρ * mapV r₀ = x * mapDen b r₀ ∧
    1 + mapS b r₀ ρ ^ 2 ≠ 0 ∧ 1 - mapS b r₀ ρ ^ 2 = y * (1 + mapS b r₀ ρ ^ 2)

/-- The certificate for `(x₀, y₀) + (x₁, y₁) = (x, y)` on `edwards` (`a = -1`). -/
private abbrev AddCert (x₀ y₀ x₁ y₁ x y : ZMod p) : Prop :=
  1 + dNum * x₀ * x₁ * y₀ * y₁ ≠ 0 ∧ x₀ * y₁ + x₁ * y₀ = x * (1 + dNum * x₀ * x₁ * y₀ * y₁) ∧
    1 - dNum * x₀ * x₁ * y₀ * y₁ ≠ 0 ∧
    y₀ * y₁ - (-1) * x₀ * x₁ = y * (1 - dNum * x₀ * x₁ * y₀ * y₁)

/-- The certificate for the one-way map on `n`: the decoded halves, the two `MAP`s and the sum. -/
private abbrev FromUniformCert (n : ℕ) (r₀ r₁ : ZMod p) (b₀ b₁ : Bool)
    (ρ₀ ρ₁ x₀ y₀ x₁ y₁ x y : ZMod p) : Prop :=
  decodeU (n % 2 ^ 256) = r₀ ∧ decodeU (n / 2 ^ 256) = r₁ ∧ MapCert b₀ r₀ ρ₀ x₀ y₀ ∧
    MapCert b₁ r₁ ρ₁ x₁ y₁ ∧ AddCert x₀ y₀ x₁ y₁ x y

private theorem mapRepField_coords (b : Bool) (r₀ ρ : ZMod p)
    (h : sqrtRatioM1 (mapU r₀) (mapV r₀) = (b, ρ)) :
    (mapRepField r₀).x = 2 * mapS b r₀ ρ * mapV r₀ / mapDen b r₀ ∧
      (mapRepField r₀).y = (1 - mapS b r₀ ρ ^ 2) / (1 + mapS b r₀ ρ ^ 2) := by
  cases b <;>
    simp only [mapRepField_x, mapRepField_y, d_eq_numeral, mapV, mapS, mapDen, dNum, h,
      Bool.false_eq_true, reduceIte, and_self]

/-- A `MapCert` gives the coordinates of `MAP(r₀)`. -/
private theorem mapRepField_xy_of_cert {b : Bool} {r₀ ρ x y : ZMod p} (h : MapCert b r₀ ρ x y) :
    (mapRepField r₀).x = x ∧ (mapRepField r₀).y = y := by
  obtain ⟨hv, hρ, hneg, hden, hx, hs, hy⟩ := h
  have hsq : sqrtRatioM1 (mapU r₀) (mapV r₀) = (b, ρ) := by
    cases b
    · simp only [Bool.false_eq_true, reduceIte] at hρ
      exact sqrtRatioM1_eq_of_mul_sq_eq_sqrtM1_mul hρ.1 hv hρ.2 hneg
    · simp only [reduceIte] at hρ
      exact sqrtRatioM1_eq_of_mul_sq_eq hv hρ hneg
  obtain ⟨h1, h2⟩ := mapRepField_coords b r₀ ρ hsq
  exact ⟨by rw [h1, div_eq_iff hden, hx], by rw [h2, div_eq_iff hs, hy]⟩

/-- An `AddCert` gives the coordinates of the sum. -/
private theorem add_xy_of_cert {P Q : edwards.Point} {x₀ y₀ x₁ y₁ x y : ZMod p} (hx₀ : P.x = x₀)
    (hy₀ : P.y = y₀) (hx₁ : Q.x = x₁) (hy₁ : Q.y = y₁) (h : AddCert x₀ y₀ x₁ y₁ x y) :
    (P + Q).x = x ∧ (P + Q).y = y := by
  obtain ⟨hd₁, hn₁, hd₂, hn₂⟩ := h
  have hd : edwards.d = dNum := by rw [edwards_d, d_eq_numeral]
  refine ⟨?_, ?_⟩
  · rw [add_x]
    unfold addX addDen₁
    rw [hx₀, hy₀, hx₁, hy₁, hd, div_eq_iff hd₁, hn₁]
  · rw [add_y]
    unfold addY addDen₂
    rw [hx₀, hy₀, hx₁, hy₁, edwards_a_eq_neg_one, hd, div_eq_iff hd₂, hn₂]

/-- A `FromUniformCert` gives the coordinates of `fromUniformRepNat n`. -/
private theorem fromUniformRepNat_xy_of_cert {n : ℕ} {r₀ r₁ : ZMod p} {b₀ b₁ : Bool}
    {ρ₀ ρ₁ x₀ y₀ x₁ y₁ x y : ZMod p} (h : FromUniformCert n r₀ r₁ b₀ b₁ ρ₀ ρ₁ x₀ y₀ x₁ y₁ x y) :
    (fromUniformRepNat n).x = x ∧ (fromUniformRepNat n).y = y := by
  obtain ⟨hr₀, hr₁, h₀, h₁, hs⟩ := h
  obtain ⟨hx₀, hy₀⟩ := mapRepField_xy_of_cert h₀
  obtain ⟨hx₁, hy₁⟩ := mapRepField_xy_of_cert h₁
  rw [fromUniformRepNat_def, hr₀, hr₁]
  exact add_xy_of_cert hx₀ hy₀ hx₁ hy₁ hs

/-! ### The vectors -/

/-- RFC 9496 §A.3, vector 1: input `5d1be09e3d0c82fc538112490e357019…`, output
`3066f82a1a747d45120d1740f14358531a8f04bbffe6a819f86dfe50f44a0a46`. -/
theorem fromUniformRepNat_vector₁ :
    encodeRepNat (fromUniformRepNat
      (87499175880137258998414822893360750755424224056161319623553458875923924261725 +
        2 ^ 256 *
        82483480588224025169569562118639141110780197061465840709495365165001842530381)) =
      31680085187462729902376606230845618866830056053850568863738022364209707771440 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 87499175880137258998414822893360750755424224056161319623553458875923924261725 +
      2 ^ 256 * 82483480588224025169569562118639141110780197061465840709495365165001842530381)
    (r₀ := 29603131261479161286629330389016796828789231723341037603824666871967359441757)
    (r₁ := 24587435969565927457784069614295187184145204728645558689766573161045277710413)
    (b₀ := true) (b₁ := false)
    (ρ₀ := 5738693154815273386581053923140376477062362783040032659146152438030662370886)
    (ρ₁ := 56172310523647345001245038749211548215797032383961217528645554865994147003130)
    (x₀ := 1375898843017352179869513266311370995016259013097784518819713402492743318198)
    (y₀ := 28582059668729797487790533420072691553514771260852751446762350955346819215934)
    (x₁ := 46947262463147434479611189727160334922192720839836696052699892530297714699123)
    (y₁ := 16974209175909088623665234762134817843987599266528751024532516909474704987010)
    (x := 43123130933603720118456132319826212419290038918687748397341757543086113937161)
    (y := 7807687545033837880223306372164802830037177291922390193675188163361710429134)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 29239299646152913398821779146647893351014742973850178649900625749722781627822) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 2: input `f116b34b8f17ceb56e8732a60d913dd1…`, output
`f26e5b6f7d362d2d2a94c5d0e7602cb4773c95a2e5c31a64f133189fa76ed61b`. -/
theorem fromUniformRepNat_vector₂ :
    encodeRepNat (fromUniformRepNat
      (17886510355990906579267560464485446403587976405970313434132635039714212255473 +
        2 ^ 256 *
        25578691604894911506658859699777905190263993550452968031351916343058162319873)) =
      12591315894774617980504893345159544623752570257311593035175980067567372562162 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 17886510355990906579267560464485446403587976405970313434132635039714212255473 +
      2 ^ 256 * 25578691604894911506658859699777905190263993550452968031351916343058162319873)
    (r₀ := 17886510355990906579267560464485446403587976405970313434132635039714212255473)
    (r₁ := 25578691604894911506658859699777905190263993550452968031351916343058162319873)
    (b₀ := true) (b₁ := false)
    (ρ₀ := 12720224983524676574568642325333913464211186070675454624371206767796865194494)
    (ρ₁ := 6093785242532077448870216104487898446220813987187055805487387864305411124722)
    (x₀ := 29234706227224010166763570026919887456611759949115055153216290052502263235446)
    (y₀ := 5014022871039269790738673313623830190663332514233697614984370654765901959636)
    (x₁ := 5525474276526524389982137176180960276792006929579090284358903943097853653033)
    (y₁ := 50770024048446131940325200843468872002520793272377582567072793151496879971879)
    (x := 52273580312577175737457209046160270220124467087124535546283536665682142235660)
    (y := 34874070204349079360043913306468422929150503655068655784988654951203758701709)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 29923396084785416307379371165574158378494368212689144511817816258695584780408) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 3: input `8422e1bbdaab52938b81fd602effb6f8…`, output
`006ccd2a9e6867e6a2c5cea83d3302cc9de128dd2a9a57dd8ee7b9d7ffe02826`. -/
theorem fromUniformRepNat_vector₃ :
    encodeRepNat (fromUniformRepNat
      (5571125413336794228515549131784564245641762771506154721169345934743809630852 +
        2 ^ 256 *
        41702335215228153457353050202710500438501035198908535261838564090875841287207)) =
      17260115017441958735051049041714646060274741218065493258847689150981160659968 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 5571125413336794228515549131784564245641762771506154721169345934743809630852 +
      2 ^ 256 * 41702335215228153457353050202710500438501035198908535261838564090875841287207)
    (r₀ := 5571125413336794228515549131784564245641762771506154721169345934743809630852)
    (r₁ := 41702335215228153457353050202710500438501035198908535261838564090875841287207)
    (b₀ := true) (b₁ := false)
    (ρ₀ := 21057623087470365232532787474946983458915711189663207177235697060857298786958)
    (ρ₁ := 17319615779753840977787233686303937194174330925207656210973944028643488826596)
    (x₀ := 50080696748727571738924592025494798740166496883432553084401993600212297395278)
    (y₀ := 12912228233790001127753714021870457301726230090768667966645421577213358598863)
    (x₁ := 6866795488305977985251732273332586432933811778109399022571767107594680637606)
    (y₁ := 8794144795777436695128886571844507434124423797520713017367024575498013423916)
    (x := 52339150320946288243065591346430106830768638747707544219675242294881744497576)
    (y := 52177649068252566057104519507065908996464071505282691939354472800854691280677)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 22543647343768848339892380032568337541767055412989416494300821856030944313822) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 4: input `ac22415129b61427bf464e17baee8db6…`, output
`f8f0c87cf237953c5890aec3998169005dae3eca1fbb04548c635953c817f92a`. -/
theorem fromUniformRepNat_vector₄ :
    encodeRepNat (fromUniformRepNat
      (87958015143991936062462724769133685135884029854916830060098924001334476743340 +
        2 ^ 256 *
        79485797552217833716597537377469844826100710372681224592285845197016987405589)) =
      19437248700560008275452320805274944452627882662443898453973705475946061558008 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 87958015143991936062462724769133685135884029854916830060098924001334476743340 +
      2 ^ 256 * 79485797552217833716597537377469844826100710372681224592285845197016987405589)
    (r₀ := 30061970525333838350677232264789731209249037522096548040370131997377911923372)
    (r₁ := 21589752933559736004812044873125890899465718039860942572557053193060422585621)
    (b₀ := false) (b₁ := false)
    (ρ₀ := 17983207047208929142159127072588174324108797293696267507791033738948119164376)
    (ρ₁ := 29409323826437563464543380330289266040270295162633980709491169984820673109754)
    (x₀ := 16341349142048757385442499004014158783889608163473197978517149365909831112138)
    (y₀ := 32107847450287062662903864548861182042793907124955814227171665697131127035767)
    (x₁ := 15951623571851837728587183168050215254938355862142738434119838015028278445826)
    (y₁ := 37593633349291621881018707748066278988946494367405653553686811121785045431969)
    (x := 42974799176289028225852631770594409465225725550690902062199697462217028403171)
    (y := 44212667807268941103987837418470793548535614963508001847537784123604845055642)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 50570876586495568680150866721332906941273544960135035317759358182592759469866) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 5: input `165d697a1ef3d5cf3c38565beefcf88c…`, output
`ae81e7dedf20a497e10c304a765c1767a42d6e06029758d2d7e8ef7cc4c41179`. -/
theorem fromUniformRepNat_vector₅ :
    encodeRepNat (fromUniformRepNat
      (46941254232349044444819396469397358049143126820442373211518371485869643750678 +
        2 ^ 256 *
        8941545681938061962481069917592138123103445813802295163960510132887321504605)) =
      54761249118267400467364721054401277608653602435298448423981548629218235482542 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 46941254232349044444819396469397358049143126820442373211518371485869643750678 +
      2 ^ 256 * 8941545681938061962481069917592138123103445813802295163960510132887321504605)
    (r₀ := 46941254232349044444819396469397358049143126820442373211518371485869643750678)
    (r₁ := 8941545681938061962481069917592138123103445813802295163960510132887321504605)
    (b₀ := false) (b₁ := false)
    (ρ₀ := 11879958695761835177416680061510627558671855016665297388698235393305013326066)
    (ρ₁ := 27896356410502328532770960352412005037861626599181497527011237351918988512988)
    (x₀ := 45577141585438095792806849592665447686149240651953408185180651514052918057002)
    (y₀ := 23760965906011354440229438538116513713549036149978469514000505825641657942594)
    (x₁ := 9746988911670099724976054966805264587698124098221669586597159683490298069310)
    (y₁ := 21602187217045385669661873130298925137383075963002090583691589857418203302013)
    (x := 45300682549104187980243240736529939337005885140088369383222005460098475331582)
    (y := 55249401592368152403860022212426180484253482102670690039190850750166676619813)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 14818382800204178201871218693803810451690074344213252556911398314459539676438) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 6: input `a836e6c9a9ca9f1e8d486273ad56a78c…`, output
`e2705652ff9f5e44d3e841bf1c251cf7dddb77d140870d1ab2ed64f1a9ce8628`. -/
theorem fromUniformRepNat_vector₆ :
    encodeRepNat (fromUniformRepNat
      (95210732253570494535244481476378183474505559882255783073909106206650992572072 +
        2 ^ 256 *
        42026383410458354297369621365737434533783068482897044100133690355266069239959)) =
      18330697791411166508030189457772520023729440463668422267029398889313655484642 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 95210732253570494535244481476378183474505559882255783073909106206650992572072 +
      2 ^ 256 * 42026383410458354297369621365737434533783068482897044100133690355266069239959)
    (r₀ := 37314687634912396823458988972034229547870567549435501054180314202694427752104)
    (r₁ := 42026383410458354297369621365737434533783068482897044100133690355266069239959)
    (b₀ := false) (b₁ := false)
    (ρ₀ := 49578549964099966380666512393953189659898227621156092753932956144343933655548)
    (ρ₁ := 55565491350018825115901528401685240789769968555591559419161867774106916963630)
    (x₀ := 39626731448900409332898821297389494775852618129840825515523968783359034541423)
    (y₀ := 38431965916100737945270696150109742403265004051544224729574170359709147318557)
    (x₁ := 6779856106754889860481754799739148049124362607970479598477435149336636450616)
    (y₁ := 9502637105943406914712504040127704388451311815546943223682046483330877708780)
    (x := 41066466250762021531823292840049961150238310936003197806195662482168212642322)
    (y := 37339002982191838980626041959225931149088796533694428670464177061683131814968)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 37328188772940969056905895561721630198107783347456614843588824055537931963066) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- RFC 9496 §A.3, vector 7: input `2cdc11eaeb95daf01189417cdddbf959…`, output
`80bd07262511cdde4863f8a7434cef696750681cb9510eea557088f76d9e5065`. -/
theorem fromUniformRepNat_vector₇ :
    encodeRepNat (fromUniformRepNat
      (44531920118033507980356872696360687059603462351796757847160156717238503726124 +
        2 ^ 256 *
        59156934336572785065121178987691935821338223278264997104560224432572328155436)) =
      45826038912717419314006741738835044459053993966913575321465019055886937079168 := by
  obtain ⟨hx, hy⟩ := fromUniformRepNat_xy_of_cert
    (n := 44531920118033507980356872696360687059603462351796757847160156717238503726124 +
      2 ^ 256 * 59156934336572785065121178987691935821338223278264997104560224432572328155436)
    (r₀ := 44531920118033507980356872696360687059603462351796757847160156717238503726124)
    (r₁ := 1260889717914687353335686483347981894703230945444715084831432428615763335468)
    (b₀ := false) (b₁ := true)
    (ρ₀ := 32186483099323074805801665054741163442034957412250611406271557616019433166854)
    (ρ₁ := 57329786285211412793126882179454482719441104730443957293694040876686638190246)
    (x₀ := 40742634313549636094100962098594789261729644302158795854062725632958914492647)
    (y₀ := 45335856672362511125320215445452967042873260262233597052548892070269758195105)
    (x₁ := 19365183218862213362984076758753280466903659074214497182728182351889130901739)
    (y₁ := 29324742037872667685776261406404227570966992208826909431387712488366765268199)
    (x := 33362194118192094025501732080357478163528764107113422320396025087238194043520)
    (y := 1481775127003541630722482109530043655253888446865222646791923987437201995291)
    (by decide +kernel)
  exact encodeRepNat_of_coords
    (r := 38859598079419181375699844779637875629277005664033100587208366682595124454624) _ hx hy
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### The vectors on bytes

The same vectors as byte strings, as RFC 9496 writes them: `Ristretto.fromUniformRep` on
`Vector UInt8 64` is `fromUniformRepNat` of the value of the bytes (`fromUniformRep_eq`). -/

private theorem encodeRep_fromUniformRep_of_value {b : Vector UInt8 64} {n N : ℕ}
    {o : Vector UInt8 32} (hb : decodeLittleEndian b = n)
    (h : encodeRepNat (fromUniformRepNat n) = N) (ho : encodeLittleEndian 32 N = o) :
    encodeRep (fromUniformRep b) = o := by
  rw [encodeRep, fromUniformRep_eq, hb, h, ho]

/-- RFC 9496 §A.3, vector 1: input `5d1be09e3d0c82fc538112490e357019…`, output
`3066f82a1a747d45120d1740f14358531a8f04bbffe6a819f86dfe50f44a0a46`. -/
theorem fromUniformRep_vector₁ :
    encodeRep (fromUniformRep
      #v[0x5d, 0x1b, 0xe0, 0x9e, 0x3d, 0x0c, 0x82, 0xfc,
         0x53, 0x81, 0x12, 0x49, 0x0e, 0x35, 0x70, 0x19,
         0x79, 0xd9, 0x9e, 0x06, 0xca, 0x3e, 0x2b, 0x5b,
         0x54, 0xbf, 0xfe, 0x8b, 0x4d, 0xc7, 0x72, 0xc1,
         0x4d, 0x98, 0xb6, 0x96, 0xa1, 0xbb, 0xfb, 0x5c,
         0xa3, 0x2c, 0x43, 0x6c, 0xc6, 0x1c, 0x16, 0x56,
         0x37, 0x90, 0x30, 0x6c, 0x79, 0xea, 0xca, 0x77,
         0x05, 0x66, 0x8b, 0x47, 0xdf, 0xfe, 0x5b, 0xb6]) =
      #v[0x30, 0x66, 0xf8, 0x2a, 0x1a, 0x74, 0x7d, 0x45,
         0x12, 0x0d, 0x17, 0x40, 0xf1, 0x43, 0x58, 0x53,
         0x1a, 0x8f, 0x04, 0xbb, 0xff, 0xe6, 0xa8, 0x19,
         0xf8, 0x6d, 0xfe, 0x50, 0xf4, 0x4a, 0x0a, 0x46] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₁
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 2: input `f116b34b8f17ceb56e8732a60d913dd1…`, output
`f26e5b6f7d362d2d2a94c5d0e7602cb4773c95a2e5c31a64f133189fa76ed61b`. -/
theorem fromUniformRep_vector₂ :
    encodeRep (fromUniformRep
      #v[0xf1, 0x16, 0xb3, 0x4b, 0x8f, 0x17, 0xce, 0xb5,
         0x6e, 0x87, 0x32, 0xa6, 0x0d, 0x91, 0x3d, 0xd1,
         0x0c, 0xce, 0x47, 0xa6, 0xd5, 0x3b, 0xee, 0x92,
         0x04, 0xbe, 0x8b, 0x44, 0xf6, 0x67, 0x8b, 0x27,
         0x01, 0x02, 0xa5, 0x69, 0x02, 0xe2, 0x48, 0x8c,
         0x46, 0x12, 0x0e, 0x92, 0x76, 0xcf, 0xe5, 0x46,
         0x38, 0x28, 0x6b, 0x9e, 0x4b, 0x3c, 0xdb, 0x47,
         0x0b, 0x54, 0x2d, 0x46, 0xc2, 0x06, 0x8d, 0x38]) =
      #v[0xf2, 0x6e, 0x5b, 0x6f, 0x7d, 0x36, 0x2d, 0x2d,
         0x2a, 0x94, 0xc5, 0xd0, 0xe7, 0x60, 0x2c, 0xb4,
         0x77, 0x3c, 0x95, 0xa2, 0xe5, 0xc3, 0x1a, 0x64,
         0xf1, 0x33, 0x18, 0x9f, 0xa7, 0x6e, 0xd6, 0x1b] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₂
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 3: input `8422e1bbdaab52938b81fd602effb6f8…`, output
`006ccd2a9e6867e6a2c5cea83d3302cc9de128dd2a9a57dd8ee7b9d7ffe02826`. -/
theorem fromUniformRep_vector₃ :
    encodeRep (fromUniformRep
      #v[0x84, 0x22, 0xe1, 0xbb, 0xda, 0xab, 0x52, 0x93,
         0x8b, 0x81, 0xfd, 0x60, 0x2e, 0xff, 0xb6, 0xf8,
         0x91, 0x10, 0xe1, 0xe5, 0x72, 0x08, 0xad, 0x12,
         0xd9, 0xad, 0x76, 0x7e, 0x2e, 0x25, 0x51, 0x0c,
         0x27, 0x14, 0x07, 0x75, 0xf9, 0x33, 0x70, 0x88,
         0xb9, 0x82, 0xd8, 0x3d, 0x7f, 0xcf, 0x0b, 0x2f,
         0xa1, 0xed, 0xff, 0xe5, 0x19, 0x52, 0xcb, 0xe7,
         0x36, 0x5e, 0x95, 0xc8, 0x6e, 0xaf, 0x32, 0x5c]) =
      #v[0x00, 0x6c, 0xcd, 0x2a, 0x9e, 0x68, 0x67, 0xe6,
         0xa2, 0xc5, 0xce, 0xa8, 0x3d, 0x33, 0x02, 0xcc,
         0x9d, 0xe1, 0x28, 0xdd, 0x2a, 0x9a, 0x57, 0xdd,
         0x8e, 0xe7, 0xb9, 0xd7, 0xff, 0xe0, 0x28, 0x26] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₃
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 4: input `ac22415129b61427bf464e17baee8db6…`, output
`f8f0c87cf237953c5890aec3998169005dae3eca1fbb04548c635953c817f92a`. -/
theorem fromUniformRep_vector₄ :
    encodeRep (fromUniformRep
      #v[0xac, 0x22, 0x41, 0x51, 0x29, 0xb6, 0x14, 0x27,
         0xbf, 0x46, 0x4e, 0x17, 0xba, 0xee, 0x8d, 0xb6,
         0x59, 0x40, 0xc2, 0x33, 0xb9, 0x8a, 0xfc, 0xe8,
         0xd1, 0x7c, 0x57, 0xbe, 0xeb, 0x78, 0x76, 0xc2,
         0x15, 0x0d, 0x15, 0xaf, 0x1c, 0xb1, 0xfb, 0x82,
         0x4b, 0xbd, 0x14, 0x95, 0x5f, 0x2b, 0x57, 0xd0,
         0x8d, 0x38, 0x8a, 0xab, 0x43, 0x1a, 0x39, 0x1c,
         0xfc, 0x33, 0xd5, 0xba, 0xfb, 0x5d, 0xbb, 0xaf]) =
      #v[0xf8, 0xf0, 0xc8, 0x7c, 0xf2, 0x37, 0x95, 0x3c,
         0x58, 0x90, 0xae, 0xc3, 0x99, 0x81, 0x69, 0x00,
         0x5d, 0xae, 0x3e, 0xca, 0x1f, 0xbb, 0x04, 0x54,
         0x8c, 0x63, 0x59, 0x53, 0xc8, 0x17, 0xf9, 0x2a] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₄
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 5: input `165d697a1ef3d5cf3c38565beefcf88c…`, output
`ae81e7dedf20a497e10c304a765c1767a42d6e06029758d2d7e8ef7cc4c41179`. -/
theorem fromUniformRep_vector₅ :
    encodeRep (fromUniformRep
      #v[0x16, 0x5d, 0x69, 0x7a, 0x1e, 0xf3, 0xd5, 0xcf,
         0x3c, 0x38, 0x56, 0x5b, 0xee, 0xfc, 0xf8, 0x8c,
         0x0f, 0x28, 0x2b, 0x8e, 0x7d, 0xbd, 0x28, 0x54,
         0x4c, 0x48, 0x34, 0x32, 0xf1, 0xce, 0xc7, 0x67,
         0x5d, 0xeb, 0xea, 0x8e, 0xbb, 0x4e, 0x5f, 0xe7,
         0xd6, 0xf6, 0xe5, 0xdb, 0x15, 0xf1, 0x55, 0x87,
         0xac, 0x4d, 0x4d, 0x4a, 0x1d, 0xe7, 0x19, 0x1e,
         0x0c, 0x1c, 0xa6, 0x66, 0x4a, 0xbc, 0xc4, 0x13]) =
      #v[0xae, 0x81, 0xe7, 0xde, 0xdf, 0x20, 0xa4, 0x97,
         0xe1, 0x0c, 0x30, 0x4a, 0x76, 0x5c, 0x17, 0x67,
         0xa4, 0x2d, 0x6e, 0x06, 0x02, 0x97, 0x58, 0xd2,
         0xd7, 0xe8, 0xef, 0x7c, 0xc4, 0xc4, 0x11, 0x79] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₅
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 6: input `a836e6c9a9ca9f1e8d486273ad56a78c…`, output
`e2705652ff9f5e44d3e841bf1c251cf7dddb77d140870d1ab2ed64f1a9ce8628`. -/
theorem fromUniformRep_vector₆ :
    encodeRep (fromUniformRep
      #v[0xa8, 0x36, 0xe6, 0xc9, 0xa9, 0xca, 0x9f, 0x1e,
         0x8d, 0x48, 0x62, 0x73, 0xad, 0x56, 0xa7, 0x8c,
         0x70, 0xcf, 0x18, 0xf0, 0xce, 0x10, 0xab, 0xb1,
         0xc7, 0x17, 0x2d, 0xdd, 0x60, 0x5d, 0x7f, 0xd2,
         0x97, 0x98, 0x54, 0xf4, 0x7a, 0xe1, 0xcc, 0xf2,
         0x04, 0xa3, 0x31, 0x02, 0x09, 0x5b, 0x42, 0x00,
         0xe5, 0xbe, 0xfc, 0x04, 0x65, 0xac, 0xcc, 0x26,
         0x31, 0x75, 0x48, 0x5f, 0x0e, 0x17, 0xea, 0x5c]) =
      #v[0xe2, 0x70, 0x56, 0x52, 0xff, 0x9f, 0x5e, 0x44,
         0xd3, 0xe8, 0x41, 0xbf, 0x1c, 0x25, 0x1c, 0xf7,
         0xdd, 0xdb, 0x77, 0xd1, 0x40, 0x87, 0x0d, 0x1a,
         0xb2, 0xed, 0x64, 0xf1, 0xa9, 0xce, 0x86, 0x28] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₆
      (by decide +kernel)

/-- RFC 9496 §A.3, vector 7: input `2cdc11eaeb95daf01189417cdddbf959…`, output
`80bd07262511cdde4863f8a7434cef696750681cb9510eea557088f76d9e5065`. -/
theorem fromUniformRep_vector₇ :
    encodeRep (fromUniformRep
      #v[0x2c, 0xdc, 0x11, 0xea, 0xeb, 0x95, 0xda, 0xf0,
         0x11, 0x89, 0x41, 0x7c, 0xdd, 0xdb, 0xf9, 0x59,
         0x52, 0x99, 0x3a, 0xa9, 0xcb, 0x9c, 0x64, 0x0e,
         0xb5, 0x05, 0x8d, 0x09, 0x70, 0x2c, 0x74, 0x62,
         0x2c, 0x99, 0x65, 0xa6, 0x97, 0xa3, 0xb3, 0x45,
         0xec, 0x24, 0xee, 0x56, 0x33, 0x5b, 0x55, 0x6e,
         0x67, 0x7b, 0x30, 0xe6, 0xf9, 0x0a, 0xc7, 0x7d,
         0x78, 0x10, 0x64, 0xf8, 0x66, 0xa3, 0xc9, 0x82]) =
      #v[0x80, 0xbd, 0x07, 0x26, 0x25, 0x11, 0xcd, 0xde,
         0x48, 0x63, 0xf8, 0xa7, 0x43, 0x4c, 0xef, 0x69,
         0x67, 0x50, 0x68, 0x1c, 0xb9, 0x51, 0x0e, 0xea,
         0x55, 0x70, 0x88, 0xf7, 0x6d, 0x9e, 0x50, 0x65] :=
  encodeRep_fromUniformRep_of_value (by decide +kernel) fromUniformRepNat_vector₇
      (by decide +kernel)

end curve25519.Proofs
