// -*- mode: rust; -*-

//! Functions mapping curve points to representative values
//! (indistinguishable from random), and back again.
use crate::constants::{MONTGOMERY_A, MONTGOMERY_A_NEG};
use crate::field::FieldElement;
use crate::montgomery::MontgomeryPoint;
use crate::EdwardsPoint;

use subtle::{
    Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
    CtOption,
};

/// bitmask for a single byte when clearing the high order two bits of a representative
pub(crate) const MASK_UNSET_BYTE: u8 = 0x3f;
/// bitmask for a single byte when setting the high order two bits of a representative
pub(crate) const MASK_SET_BYTE: u8 = 0xc0;

/// (p - 1) / 2 = 2^254 - 10
pub(crate) const DIVIDE_MINUS_P_1_2_BYTES: [u8; 32] = [
    0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
];

/// Gets a public representative for a key pair using the private key.
///
/// The `tweak` parameter is used to adjust the computed representative making
/// it computationally indistinguishable from uniform random. If this property
/// is not required then the provided tweak value does not matter.
///
/// The tweak allows us to overcome three limitations:
/// - Representatives are not always canonical.
/// - Bit 255 (the most significant bit) was always zero.
/// - Only points from the large prime-order subgroup are represented.
///
/// In order for the returned representative to be canonical a tweak to the
/// high order two bits must be applied.
/// ```txt
/// [An adversary could] observe a representative, interpret it as a field
/// element, square it, then take the square root using the same
/// non-canonical square root algorithm. With representatives produced by
/// an affected version of [the elligator2 implementation], the output of
/// the square-then-root operation would always match the input. With
/// random strings, the output would match only half the time.
/// ```
///
/// For a more in-depth explanation see:
/// https://github.com/agl/ed25519/issues/27
/// https://www.bamsoftware.com/papers/fep-flaws/
pub fn representative_from_privkey(privkey: &[u8; 32], tweak: u8) -> Option<[u8; 32]> {
    let pubkey = EdwardsPoint::mul_base_clamped(*privkey).to_montgomery();
    let v_in_sqrt = v_in_sqrt(privkey);
    let p: Option<[u8; 32]> = point_to_representative(&pubkey, v_in_sqrt.into()).into();
    match p {
        None => None,
        Some(mut a) => {
            a[31] |= MASK_SET_BYTE & tweak;
            Some(a)
        }
    }
}

/// This function is used to map a curve point (i.e. an x25519 public key)
/// to a point that is effectively indistinguishable from random noise.
///
/// This operation may fail because not all curve points are capable of being
/// hidden. On failure, this function will return None.
///
/// This implementation is adapted from both:
/// - [kleshni C implementation](https://github.com/Kleshni/Elligator-2)
/// - [agl/ed25519 golang forks](https://gitlab.com/yawning/edwards25519-extra)
///
///
/// Note: the output field elements of this function are uniformly
/// distributed among the nonnegative field elements, but only if the
/// input points are also uniformly distributed among all points of
/// the curve. In particular, if the inputs are only selected from
/// members of the prime order group, then the outputs are
/// distinguishable from random.
///
/// # Inputs
///
/// * `point`: the \\(u\\)-coordinate of a point on the curve. Not all
/// points map to field elements.
///
/// * `v_in_sqrt`: true if the \\(v\\)-coordinate of the point is negative.
///
/// # Returns
///
/// Either `None`, if the point couldn't be mapped, or `Some(fe)` such
/// that `fe` is nonnegative and `map_to_point(&fe) == point`.
///
/// [elligator paper](https://elligator.cr.yp.to/elligator-20130828.pdf)
/// [elligator site](https://elligator.org/)
///
pub fn point_to_representative(point: &MontgomeryPoint, v_in_sqrt: bool) -> CtOption<[u8; 32]> {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // a := point
    let a = &FieldElement::from_bytes(&point.0);
    let mut a_neg = *a;
    a_neg.negate();

    let is_encodable = is_encodable(a);

    // Calculate r1 = sqrt(-a/(2*(a+A)))
    let (_r1_sqrt, r1) = FieldElement::sqrt_ratio_i(
        &a_neg,
        &(&(a + &MONTGOMERY_A) * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // Calculate  r0 = sqrt(-(a+A)/(2a))
    let (_r0_sqrt, r0) = FieldElement::sqrt_ratio_i(
        &(&a_neg - &MONTGOMERY_A),
        &(a * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // if v_in_sqrt root=r0 otherwise r1
    let mut b = FieldElement::conditional_select(&r1, &r0, Choice::from(v_in_sqrt as u8));

    // If root > (p - 1) / 2, root := -root
    let negate = divide_minus_p_1_2.ct_gt(&b);
    FieldElement::conditional_negate(&mut b, negate);

    CtOption::new(b.as_bytes(), is_encodable)
}

/// Determines whether a point is encodable as a representative. Approximately
/// 50% of points are not encodable.
#[inline]
fn is_encodable(u: &FieldElement) -> Choice {
    let b0 = u + &MONTGOMERY_A;
    let b1 = &(&(&b0.square().square() * &b0.square()) * &b0) * u; // b1 = u * (u + A)^7
    let c = b1.pow_p58();

    let b2 = &(&b0.square().square().square() * &b0.square().square()) * &b0.square(); // (u + A)^14
    let mut chi = &(&c.square().square() * &u.square()) * &b2; // chi = -c^4 * u^2 * (u + A)^14
    chi.negate();

    let chi_bytes = chi.as_bytes();

    // chi[1] is either 0 or 0xff
    chi_bytes[1].ct_eq(&0_u8)
}

///  `high_y` - Montgomery points can have have two different values for a
///  single X coordinate (based on sign). The Kleshni implementation determines
///  which sign value to use with this function.
///
///  If the point is 0, this should be ignored.
#[inline]
pub(crate) fn high_y(d: &FieldElement) -> Choice {
    let d_sq = &d.square();
    let au = &MONTGOMERY_A * d;

    let inner = &(d_sq + &au) + &FieldElement::ONE;
    let eps = d * &inner; /* eps = d^3 + Ad^2 + d */

    let (eps_is_sq, _) = FieldElement::sqrt_ratio_i(&eps, &FieldElement::ONE);

    eps_is_sq
}

/// Determines if `V <= (p - 1)/2` for a Scalar (e.g an x25519 private key) and
/// returns a [`Choice`] indicating the result.
///
/// Note: When using the elligator2 transformations on x25519 keypairs this
/// requires the use of the clamped scalar_base_mult of the private key to
/// get the edwards representation of the public key, otherwise we need to know
/// the correct sign value for the edwards conversion or the derivation of
/// the `V` value will be broken. As noted in [`EdwardsPoint::to_montgomery`],
/// the sign information about the X coordinate is lost on conversion so we
/// have to use the edwards point derived from the private key to guarantee the
/// correct value here.
///
/// Alternatively you can keep track of the public key and sign bit manually
/// and construct an EdwardsPoint for which [`v_in_sqrt_pubkey_edwards`] will
/// give you the same result.
///
// As an interface, using the private key should work just fine. This allows
// us to match the existing [`PublicKey`] generation interface for the
// [`PublicRepresentative`] in the [`x25519_dalek`] crate. AFAIK there is no
// need for anyone with only the public key to be able to generate the
// representative.
pub fn v_in_sqrt(key_input: &[u8; 32]) -> Choice {
    let mut masked_pk = *key_input;
    masked_pk[0] &= 0xf8;
    masked_pk[31] &= 0x7f;
    masked_pk[31] |= 0x40;

    let pubkey = EdwardsPoint::mul_base_clamped(masked_pk);
    v_in_sqrt_pubkey_edwards(&pubkey)
}

/// Determines if `V <= (p - 1)/2` for an EdwardsPoint (e.g an x25519 public key)
/// and returns a [`Choice`] indicating the result.
pub fn v_in_sqrt_pubkey_edwards(pubkey: &EdwardsPoint) -> Choice {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // sqrtMinusAPlus2 is sqrt(-(486662+2))
    let (_, sqrt_minus_a_plus_2) = FieldElement::sqrt_ratio_i(
        &(&MONTGOMERY_A_NEG - &(&FieldElement::ONE + &FieldElement::ONE)),
        &FieldElement::ONE,
    );

    // inv1 = 1/((A.Z - A.y) * A.X)
    let inv1 = (&(&pubkey.Z - &pubkey.Y) * &pubkey.X).invert();

    // t0 = A.Y + A.Z
    let t0 = &pubkey.Y + &pubkey.Z;

    // v = t0 * inv1 * A.Z * sqrtMinusAPlus2
    let v = &(&t0 * &inv1) * &(&pubkey.Z * &sqrt_minus_a_plus_2);

    // is   v <= (q-1)/2  ?
    divide_minus_p_1_2.ct_gt(&v)
}

// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

fn map_to_curve_parts(
    r: &FieldElement,
) -> (FieldElement, FieldElement, FieldElement, FieldElement) {
    let zero = FieldElement::ZERO;
    let one = FieldElement::ONE;
    let mut minus_one = FieldElement::ONE;
    minus_one.negate();

    // Exceptional case 2u^2 == -1
    let mut tv1 = r.square2();
    tv1.conditional_assign(&zero, tv1.ct_eq(&minus_one));

    let d_1 = &one + &tv1; /* 1 + 2u^2 */
    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* d = -A/(1+2u^2) */

    let inner = &(&d.square() + &(&d * &MONTGOMERY_A)) + &one;
    let gx1 = &d * &inner; /* gx1 = d^3 + Ad^2 + d */
    let gx2 = &gx1 * &tv1;

    let eps_is_sq = high_y(&d);

    // complete X
    /* A_temp = 0, or A if nonsquare*/
    let a_temp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq);
    let mut x = &d + &a_temp; /* d, or d+A if nonsquare */
    x.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    // complete Y
    let y2 = FieldElement::conditional_select(&gx2, &gx1, eps_is_sq);
    let (_, mut y) = FieldElement::sqrt_ratio_i(&y2, &one);
    y.conditional_negate(eps_is_sq ^ y.is_negative());

    (&x * &d_1, d_1, y, one)
}

pub(crate) fn map_fe_to_montgomery(r: &FieldElement) -> (FieldElement, FieldElement) {
    let (xmn, xmd, y, _) = map_to_curve_parts(r);
    (&xmn * &(xmd.invert()), y)
}

pub(crate) fn map_fe_to_edwards(r: &FieldElement) -> (FieldElement, FieldElement) {
    // 1.  (xMn, xMd, yMn, yMd) = map_to_curve_elligator2_curve25519(u)
    let (xmn, xmd, ymn, ymd) = map_to_curve_parts(r);
    // c1 = sqrt(-486664)
    // this cannot fail as it computes a constant
    let c1 = &(&MONTGOMERY_A_NEG - &FieldElement::ONE) - &FieldElement::ONE;
    let (_, c1) = FieldElement::sqrt_ratio_i(&c1, &FieldElement::ONE);

    // 2.  xn = xMn * yMd
    // 3.  xn = xn * c1
    let mut xn = &(&xmn * &ymd) * &c1;

    // 4.  xd = xMd * yMn    # xn / xd = c1 * xM / yM
    let mut xd = &xmd * &ymn;

    // 5.  yn = xMn - xMd
    let mut yn = &xmn - &xmd;
    // 6.  yd = xMn + xMd    # (n / d - 1) / (n / d + 1) = (n - d) / (n + d)
    let mut yd = &xmn + &xmd;

    // 7. tv1 = xd * yd
    // 8.   e = tv1 == 0
    let cond = (&xd * &yd).is_zero();

    // 9.  xn = CMOV(xn, 0, e)
    // 10. xd = CMOV(xd, 1, e)
    // 11. yn = CMOV(yn, 1, e)
    // 12. yd = CMOV(yd, 1, e)
    xn = FieldElement::conditional_select(&xn, &FieldElement::ZERO, cond);
    xd = FieldElement::conditional_select(&xd, &FieldElement::ONE, cond);
    yn = FieldElement::conditional_select(&yn, &FieldElement::ONE, cond);
    yd = FieldElement::conditional_select(&yd, &FieldElement::ONE, cond);

    // 13. return (xn, xd, yn, yd)
    (&xn * &(xd.invert()), &yn * &(yd.invert()))
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
#[cfg(feature = "elligator2")]
#[cfg(feature = "alloc")]
mod test {
    use super::*;

    use hex::FromHex;

    ////////////////////////////////////////////////////////////
    // Ntor tests                                             //
    ////////////////////////////////////////////////////////////

    #[test]
    #[cfg(feature = "elligator2")]
    fn repres_from_pubkey_kleshni() {
        // testcases from kleshni
        for (i, testcase) in encoding_testcases().iter().enumerate() {
            let point = <[u8; 32]>::from_hex(testcase.point).expect("failed to decode hex point");

            let edw_point = MontgomeryPoint(point)
                .to_edwards(testcase.high_y as u8)
                .expect("failed to convert point to edwards");
            let v_in_sqrt = v_in_sqrt_pubkey_edwards(&edw_point);

            let repres: Option<[u8; 32]> =
                point_to_representative(&MontgomeryPoint(point), v_in_sqrt.into()).into();
            if testcase.representative.is_some() {
                assert_eq!(
                    testcase.representative.expect("checked, is some"),
                    hex::encode(repres.expect("failed to get representative from point")),
                    "[good case] kleshni ({i}) bad pubkey from true representative"
                );
            } else {
                assert!(
                    repres.is_none(),
                    "[good case] kleshni ({i}) expected none got repres {}",
                    hex::encode(repres.expect("this should not fail"))
                );
            }
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    /// Ensure private keys generate the expected representatives. These tests
    /// are generated from agl/ed25519 to ensure compatibility.
    fn repres_from_privkey_agl() {
        for (i, vector) in ntor_valid_test_vectors().iter().enumerate() {
            let privkey = <[u8; 32]>::from_hex(vector[0]).expect("failed to decode hex privatekey");
            let true_repres = vector[2];

            let repres_res = representative_from_privkey(&privkey, 0u8);
            assert!(
                Into::<bool>::into(repres_res.is_some()),
                "failed to get representative when we should have gotten one :("
            );
            let repres = repres_res.expect("failed to get representative from pubkey");

            assert_eq!(
                true_repres,
                hex::encode(repres),
                "[good case] agl/ed25519 ({i}) bad representative from privkey"
            );
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    fn pubkey_from_repres() {
        // testcases from kleshni
        for (i, testcase) in decoding_testcases().iter().enumerate() {
            let repres = <[u8; 32]>::from_hex(testcase.representative)
                .expect("failed to decode hex representative");

            let point = MontgomeryPoint::map_to_point(&repres);
            assert_eq!(
                testcase.point,
                hex::encode(point.to_bytes()),
                "[good case] kleshni ({i}) bad representative from point"
            );

            let point_from_unbounded = MontgomeryPoint::map_to_point_unbounded(&repres);
            assert_eq!(
                testcase.non_lsr_point,
                hex::encode(point_from_unbounded.to_bytes()),
                "[good case] kleshni ({i}) bad representative from point"
            );
        }

        // testcases from golang agl/ed25519
        for (i, vector) in ntor_valid_test_vectors().iter().enumerate() {
            let true_pubkey = vector[1];
            let repres =
                <[u8; 32]>::from_hex(vector[2]).expect("failed to decode hex representative");

            // ensure that the representative can be reversed to recover the
            // original public key.
            let pubkey = MontgomeryPoint::map_to_point(&repres);
            assert_eq!(
                true_pubkey,
                hex::encode(pubkey.to_bytes()),
                "[good case] agl/ed25519 ({i}) bad pubkey from true representative"
            );
        }
    }

    #[test]
    #[cfg(feature = "elligator2")]
    fn non_representable_points() {
        for (i, key) in ntor_invalid_keys().iter().enumerate() {
            let privkey = <[u8; 32]>::from_hex(key).expect("failed to decode hex privkey");

            // ensure that the representative can be reversed to recover the
            // original public key.
            let res: Option<[u8; 32]> = representative_from_privkey(&privkey, 0u8);
            assert!(
                res.is_none(),
                "[bad case] agl/ed25519 ({i}) expected None, got Some({})",
                hex::encode(res.expect("this shouldn't happen"))
            );
        }
    }

    /// returns a set of keypair encodings generated by (a fork of) the golang
    /// implementation agl/ed25519 which is used by the mainstream obfs4
    /// library. Each set of three strings is
    ///
    ///   1) the generated private key scalar
    ///   2) the associated public key point
    ///   3) the successfully created representative
    ///
    /// All of these are valid keypairs and our public key to
    /// representative implementation (and repres-to-pubkey) should match and
    /// handle these cases.
    ///
    fn ntor_valid_test_vectors() -> [[&'static str; 3]; 20] {
        [
            [
                "eec0c0e43a2f693557dac4938c9a0f44be8bf7999399f26a24e5eab3267517c8",
                "309d1f477c62df666f47b87930d1883c072d007a169c03d1c231efe2e51cae1f",
                "bfd7e6dc33b735403cf6c7235513463843db8e1d2c16e62f0d5cacc8a3817515",
            ],
            [
                "d27f87a4850f85ef5211094eb417bc8fb9441dd8eedba8def6fd040da93fdf94",
                "bb6fe9e93c929e104a6b9f956c5de1fdc977899a781d50e76dd8f8852f19e635",
                "420c98e6ac9cabaccf54e02034916df64a45ad1e7799b5d2ab0403073c6f6a21",
            ],
            [
                "54b0d4e7110fb3a6ca5424fa7ffdc7cc599f9280df9759d1eb5d04186a4e82dd",
                "f305e32fbd38dd1e6b04ba32620c6b8db121ed3216f7118875580bd454eb077d",
                "a2b1a54463ad048ea9780fe2f92e0517636d2cd537d77a18cb6be03f1f991c04",
            ],
            [
                "9ce200c8a0c3e617c7c5605dc60d1ce67e30a608c492143d643880f91594a6dd",
                "56a2e451811eb62c78090c3d076f4b179b2e9baa4d80188a3db319301031191b",
                "c16f22f4899aae477d37c250164d10c9c898a820bf790b1532c3bc379b8d733e",
            ],
            [
                "98f09f9dedc813654e4ba28c9cd545587b20c6133603f13d8d4da2b67b4eab8c",
                "210d599d6b8d1659e4a6eb98fdebd1a7024b22ba148af2a603ab807735af6a57",
                "fc4ad471aff8243195ab6778054b0b243f93b4d31d5ac3a5bda9354dc3def735",
            ],
            [
                "fa850ae6663a8c7b84c71c6391e0b02df2d6adbc30a03b961c4b496b9979cf9d",
                "7fc7a4a8ae33cd045b064d1618689a7e16c87ce611f8f519433b10134dc57b04",
                "062d292892515a6a9e71e1430cc593e5cf90e4c18d7c0c0eaae7a07768e6f713",
            ],
            [
                "c19e91e47db473ff36714a8490665eaf6e57d228ef116e7771febce437c9e4ef",
                "5ca47c5affeaeac3d67ef6564f0faa0bd575857eb4e315b57458959b0034f75c",
                "f22ceea9e0e3826a308fe60df0edf4b82177e3704750f7af6e41aa5c5d806f16",
            ],
            [
                "012fb2f110c7da5d56bb86e28e23dff1d860bb6ed11e145be9344ba756dd4e6e",
                "badb58d30c1a8b6bbc0ee97f627272aa1c5625a1cadb7bf75fa274f76c081964",
                "62cf0d3d7c67715a7cc982c9186ccd4d151b64b2cef862433a963b7b2c13f033",
            ],
            [
                "fc9fec244ec6064f1060aabad079d04d1bb180239b07d4d02383ecbb05a7095e",
                "54fe5cc959be48e5a0251026ac4cd0f5a424b8f5c157a7c59857d2ab11521e4c",
                "0326b2e14412ef42fdd0144f96f6b47a5e0954aa110ca7ba124d1aca82269e1f",
            ],
            [
                "1cb297f54fd1b320995f885591abdd5b84ff35f55ed22f85475a00c0c97b648a",
                "2b0472ba2ffd8af768c2b6dab2b6db21c0ca153537d4b3c638a7cf7708c99e2d",
                "08bba17691f09c899bba92f8950dec551065249f77e59d46bf113c56fc54a20f",
            ],
            [
                "4871c2e7ada1911544713cbf15e0553d4972cc9867a4e67a667643b8e7a77d30",
                "d73258438f51a0f603180aa349e3276fd623bcce61ff9d2dbb9fd9a9aaf53e40",
                "a5ad91e362963312d95659b2e97bfcfddca573841f864cf8a8e0e075a72e4d1c",
            ],
            [
                "52959827c6c7d3e3b6b50089db8a9524243ae7cee3f9ad7eff477587683af118",
                "031d982caf72aa660a68d79439cedd0e0c47d09f9b6c90d1a0c322291591616e",
                "8dd9423dcc8d08c951330954c99eb508395ac26a3e6d864df907ad1b23fd6a37",
            ],
            [
                "12c77ad0259120089f5bfb841999e9e17acf71a00ef7891366e3f286c0122790",
                "ce7cb3c1789b119987d36ed73dd40db07099ae9eca8b8ee53f63f610728d7600",
                "8cdcc4d90a94f8148619bc7a32d230e8bbd4416051f53da3ebda320a40904128",
            ],
            [
                "db46139a816b40cc15be3b82cd799f025cfa0817552bf959386e0a264184a419",
                "03778d7eee1973fbe8a45670bc2172a8fbc8e0627cf81ad932f7bbedc1aca177",
                "f3382b89603501ac8a5038aeda9422af88a2557f6a831b20062518733d59382d",
            ],
            // The following key sets have a v_in_sqrt value of 0
            [
                "51a8b03750f4b34922d3588b73a556a09594b7b014d2b7cefa26bb8c5eee6d2e",
                "e8db45df5146d3745eae81e722af5e030a9a999a3e0d588f84514b125029b81b",
                "f859efb4704b0b4c71959b02976de3ea9746f01e5adacddddba10ee08178cd1d",
            ],
            [
                "d5a46dfdf2c66a76c312e83954fc0cf54f75ff14c2d6febfeb08153e34f54cfd",
                "08a6adca98cbee754c3cdb103b5d9f69e61b87c64339947cbbaa1a956df5b745",
                "139b06604063d7942540fbd33de329a2f733c65a89fd68151743896744397c2b",
            ],
            [
                "a06917dc2988e4b51559ab26e25fd920e8fec2f8f2fe0f4c3c725dce06de7867",
                "868603c764dff5f6db6f963237731452c469dfa2c8c5b682cfec85fc38661415",
                "2bdd5f3dcaeefa352f200306be3471ad90a0a0ac4b6abba44230e284a852b813",
            ],
            [
                "7acad18a021a568d2abaf079d046f5eb55e081a32b00d4f6c77f8b8c9afed866",
                "8e0f52904421469a46b2d636b9d17595573071d16ebff280fc88829b5ef8bd4f",
                "abc0de8594713993eab06144fe9b6d7bd04227c62bda19ef984008a93161fb33",
            ],
            [
                "c547b93c519a1c0b40b71fe7b08e13b38639564e9317f6b58c5f99d5ad82471a",
                "687fe9c6fe84e94ef0f7344abdac92dfd60dabc6156c1a3eea19d0d06705b461",
                "8b0ea3b2215bf829aedd250c629557ca646515861aa0b7fc881c50d622f9ac38",
            ],
            [
                "77e48dfa107bbfdda73f50ec2c38347e4fcc9c38866adb75488a2143993a058f",
                "7d124e12af90216f26ce3198f6b02e76faf990dd248cdb246dd80d4e1fef3d4d",
                "128481624af3015c6226428a247514370800f212a7a06c90dfe4f1aa672d3b3e",
            ],
        ]
    }

    /// returns a set of private keys generated by (a fork of) the golang
    /// implementation agl/ed25519 which is used by the mainstream obfs4
    /// library.
    ///
    /// All of these fail to generate a keypair capable of using elligator2
    /// to encode of the public key.
    ///
    #[cfg(feature = "elligator2")]
    fn ntor_invalid_keys() -> [&'static str; 16] {
        [
            "fd0d592d67038a6253331547949d70eb7a6b6c4c4831a1bc235554765b20f845",
            "9576aa473a2b73b174e753ada7d55bc34ae8c05c1b1d6077f9a098984df9cf52",
            "5b26538e0663a453994cf49d5614926786a0549c0123fa9afc7be99e04afc9ea",
            "d4e58db7420267ad43e72e1fe0dee1acb9ca547e258e22370d76c0945f4b1a1e",
            "01b047693c6b5212607387df88d1a427d2f24bd24157058705fc090e22778a64",
            "d2d363fad3ea3aceb8262adc1184f32c6f63911e6bc008c87f366f9c2b60753c",
            "75f703e3095343cf5d3ccd05a3fea06f82509a26c391a0365a1f1ca5e1d5f82f",
            "1f6986c9146f2d4b1907a812e7e7254c82e121776d58fd9c4a5f6741a326e2ef",
            "fe8465f11b40d52dc845df0a1639398b1726409d3b52526082c3e67c52f06842",
            "4546f8e010e0d3be7ab3e97480cecc411b054013960ff4032b3d3e5afe1565e0",
            "fc0f99f041118fd44c685b87b143b48d6d8c820d9f07235eeb7f7a9468dc0ca0",
            "847c1d842a2e91521d1a63e191d3d2389e54c73378130f376d013781730ace3e",
            "7d8a740b09f477588bc9a9020b2444ee384718f889403c02f3a61e69f55e6f7f",
            "0549080985424df8f9401be8802e8c6a4c02737c474ac76c9d3f7968a3fca40a",
            "53cd411b966503129365517e5c1b04e9f52a248cc57599af9ed58c9ff5b774d4",
            "015aebbe87a5e94c5d8d3179583cf46d02af06c8f99a6d4ce8a3a4b1de097cd2",
        ]
    }

    const ENCODING_TESTS_COUNT: usize = 10;
    struct EncodingTestCase {
        high_y: bool,
        point: &'static str,
        representative: Option<&'static str>,
    }

    fn encoding_testcases() -> [EncodingTestCase; ENCODING_TESTS_COUNT] {
        [
            // A not encodable point with both "high_y" values
            EncodingTestCase {
                point: "e6f66fdf6e230c603c5e6e59a254ea1476a13eb9511b9549846781e12e52230a",
                high_y: false,
                representative: None,
            },
            EncodingTestCase {
                point: "e6f66fdf6e230c603c5e6e59a254ea1476a13eb9511b9549846781e12e52230a",
                high_y: true,
                representative: None,
            },
            // An encodable point with both "high_y" values
            EncodingTestCase {
                point: "33951964003c940878063ccfd0348af42150ca16d2646f2c5856e8338377d800",
                high_y: false,
                representative: Some(
                    "999b591b6697d074f266192277d554dec3c24c2ef6108101f63d94f7fff3a013",
                ),
            },
            EncodingTestCase {
                point: "33951964003c940878063ccfd0348af42150ca16d2646f2c5856e8338377d800",
                high_y: true,
                representative: Some(
                    "bd3d2a7ed1c8a100a977f8d992e33aaa6f630d55089770ea469101d7fd73d13d",
                    // "999b591b6697d074f266192277d554dec3c24c2ef6108101f63d94f7fff3a013",
                ),
            },
            // 0 with both "high_y" values
            EncodingTestCase {
                point: "0000000000000000000000000000000000000000000000000000000000000000",
                high_y: false,
                representative: Some(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                ),
            },
            EncodingTestCase {
                point: "0000000000000000000000000000000000000000000000000000000000000000",
                high_y: true,
                representative: Some(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                ),
            },
            // A not encodable point with both "high_y" values
            EncodingTestCase {
                point: "10745497d35c6ede6ea6b330546a6fcbf15c903a7be28ae69b1ca14e0bf09b60",
                high_y: false,
                representative: Some(
                    "d660db8cf212d31ce8c6f7139e69b9ac47fd81c7c0bfcb93e364b2d424e24813",
                ),
            },
            EncodingTestCase {
                point: "10745497d35c6ede6ea6b330546a6fcbf15c903a7be28ae69b1ca14e0bf09b60",
                high_y: true,
                representative: Some(
                    "489a2e0f6955e08f1ae6eb8dcdbc0f867a87a96a02d2dfd2aca21d8b536f0f1b",
                ),
            },
            // A not encodable point with both "high_y" values
            EncodingTestCase {
                point: "6d3187192afc3bcc05a497928816e3e2336dc539aa7fc296a9ee013f560db843",
                high_y: false,
                representative: Some(
                    "63d0d79e7f3c279cf4a0a5c3833fd85aa1f2c004c4e466f3a3844b3c2e06e410",
                ),
            },
            EncodingTestCase {
                point: "6d3187192afc3bcc05a497928816e3e2336dc539aa7fc296a9ee013f560db843",
                high_y: true,
                representative: Some(
                    "0f03b41c86aeb49acf2f76b39cc90a55a0b140b7290f1c9e032591ddcb074537",
                ),
            },
        ]
    }

    const DECODING_TESTS_COUNT: usize = 7;
    struct DecodingTestCase {
        representative: &'static str,
        /// if we only allow least-square-root values as the representative and
        /// clear the high order two bits (effectively) ensuring that the
        /// representative value is less than `2^254 - 10`, this is the point
        /// that we should receive.
        point: &'static str,
        /// if we allow unbounded values to be used directly as representatives,
        /// not only least-square-root values, this is the point we should receive.
        non_lsr_point: &'static str,
    }

    fn decoding_testcases() -> [DecodingTestCase; DECODING_TESTS_COUNT] {
        [
            // A small representative with false "high_y" property
            DecodingTestCase {
                representative: "e73507d38bae63992b3f57aac48c0abc14509589288457995a2b4ca3490aa207",
                point: "1e8afffed6bf53fe271ad572473262ded8faec68e5e67ef45ebb82eeba52604f",
                non_lsr_point: "1e8afffed6bf53fe271ad572473262ded8faec68e5e67ef45ebb82eeba52604f",
            },
            // A small representative with true "high_y" property
            DecodingTestCase {
                representative: "95a16019041dbefed9832048ede11928d90365f24a38aa7aef1b97e23954101b",
                point: "794f05ba3e3a72958022468c88981e0be5782be1e1145ce2c3c6fde16ded5363",
                non_lsr_point: "794f05ba3e3a72958022468c88981e0be5782be1e1145ce2c3c6fde16ded5363",
            },
            // The last representative returning true: (p - 1) / 2
            DecodingTestCase {
                representative: "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
                point: "9cdb525555555555555555555555555555555555555555555555555555555555",
                non_lsr_point: "9cdb525555555555555555555555555555555555555555555555555555555555",
            },
            // The first representative returning false: (p + 1) / 2
            DecodingTestCase {
                representative: "f7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
                point: "9cdb525555555555555555555555555555555555555555555555555555555555",
                non_lsr_point: "9cdb525555555555555555555555555555555555555555555555555555555555",
            },
            // 0
            DecodingTestCase {
                representative: "0000000000000000000000000000000000000000000000000000000000000000",
                point: "0000000000000000000000000000000000000000000000000000000000000000",
                non_lsr_point: "0000000000000000000000000000000000000000000000000000000000000000",
            },
            // These two tests are not least-square-root representations.

            // A large representative with false "high_y" property
            DecodingTestCase {
                representative: "179f24730ded2ce3173908ec61964653b8027e383f40346c1c9b4d2bdb1db76c",
                point: "e6e5355e0482e952cc951f13db26316ab111ae9edb58c45428a984ce7042d349",
                non_lsr_point: "10745497d35c6ede6ea6b330546a6fcbf15c903a7be28ae69b1ca14e0bf09b60",
            },
            // A large representative with true "high_y" property
            DecodingTestCase {
                representative: "8a2f286180c3d8630b5f5a3c7cc027a55e0d3ffb3b1b990c5c7bb4c3d1f91b6f",
                point: "27e222fec324b0293842a59a63b8201b0f97b1dd599ebcd478a896b7261aff3e",
                non_lsr_point: "6d3187192afc3bcc05a497928816e3e2336dc539aa7fc296a9ee013f560db843",
            },
        ]
    }
}

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod rfc9380 {
    use super::*;

    use hex::FromHex;
    use std::string::String;

    #[test]
    fn map_to_curve_test_go_ed25519_extra() {
        for (i, testcase) in CURVE25519_ELL2.iter().enumerate() {
            let u = testcase[0].must_from_be();
            let mut clamped = u;
            clamped[31] &= 63;

            // map point to curve
            let (q_x, _) = map_fe_to_montgomery(&FieldElement::from_bytes(&clamped));

            // check resulting point
            assert_eq!(
                q_x.encode_be(),
                testcase[1],
                "({i}) incorrect x curve25519 ELL2\n"
            );
        }
    }

    #[test]
    fn map_to_curve_test_curve25519() {
        for (i, testcase) in curve25519_XMD_SHA512_ELL2_NU.iter().enumerate() {
            let u = FieldElement::from_bytes(&testcase.u_0.must_from_le());

            // map point to curve
            let (q_x, q_y) = map_fe_to_montgomery(&u);

            // check resulting point
            assert_eq!(
                q_x.encode_le(),
                testcase.Q_x,
                "({i}) incorrect Q0_x curve25519 NU\n{:?}",
                testcase
            );
            assert_eq!(
                q_y.encode_le(),
                testcase.Q_y,
                "({i}) incorrect Q0_y curve25519 NU\n{:?}",
                testcase
            );
        }
        for (i, testcase) in curve25519_XMD_SHA512_ELL2_RO.iter().enumerate() {
            let u0 = FieldElement::from_bytes(&testcase.u_0.must_from_le());
            let u1 = FieldElement::from_bytes(&testcase.u_1.must_from_le());

            // map points to curve
            let (q0_x, q0_y) = map_fe_to_montgomery(&u0);
            let (q1_x, q1_y) = map_fe_to_montgomery(&u1);

            // check resulting points
            assert_eq!(
                q0_x.encode_le(),
                testcase.Q0_x,
                "({i}) incorrect Q0_x curve25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q0_y.encode_le(),
                testcase.Q0_y,
                "({i}) incorrect Q0_y curve25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q1_x.encode_le(),
                testcase.Q1_x,
                "({i}) incorrect Q1_x curve25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q1_y.encode_le(),
                testcase.Q1_y,
                "({i}) incorrect Q1_y curve25519 RO\n{:?}",
                testcase
            );
        }
    }

    #[test]
    fn map_to_curve_test_edwards25519() {
        for (i, testcase) in edwards25519_XMD_SHA512_ELL2_NU.iter().enumerate() {
            let u = FieldElement::from_bytes(&testcase.u_0.must_from_le());
            let (q_x, q_y) = map_fe_to_edwards(&u);

            // check resulting point
            assert_eq!(
                q_x.encode_le(),
                testcase.Q_x,
                "({i}) incorrect Q0_x edwards25519 NU\n{:?}",
                testcase
            );
            assert_eq!(
                q_y.encode_le(),
                testcase.Q_y,
                "({i}) incorrect Q0_y edwards25519 NU\n{:?}",
                testcase
            );
        }
        for (i, testcase) in edwards25519_XMD_SHA512_ELL2_RO.iter().enumerate() {
            let u0 = FieldElement::from_bytes(&testcase.u_0.must_from_le());
            let u1 = FieldElement::from_bytes(&testcase.u_1.must_from_le());

            // map points to curve
            let (q0_x, q0_y) = map_fe_to_edwards(&u0);
            let (q1_x, q1_y) = map_fe_to_edwards(&u1);

            // check resulting points
            assert_eq!(
                q0_x.encode_le(),
                testcase.Q0_x,
                "({i}) incorrect Q0_x edwards25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q0_y.encode_le(),
                testcase.Q0_y,
                "({i}) incorrect Q0_y edwards25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q1_x.encode_le(),
                testcase.Q1_x,
                "({i}) incorrect Q1_x edwards25519 RO\n{:?}",
                testcase
            );
            assert_eq!(
                q1_y.encode_le(),
                testcase.Q1_y,
                "({i}) incorrect Q1_y edwards25519 RO\n{:?}",
                testcase
            );
        }
    }

    /// Example test cases found in gitlab.com/yawning/edwards25519-extra
    ///
    /// 1. representative
    /// 2. associated point
    ///
    /// These test cases need the upper two bits cleared to be properly mapped.
    const CURVE25519_ELL2: [[&str; 2]; 14] = [
        [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "0000000000000000000000000000000000000000000000000000000000000040",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "0000000000000000000000000000000000000000000000000000000000000080",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "00000000000000000000000000000000000000000000000000000000000000c0",
            "0000000000000000000000000000000000000000000000000000000000000000",
        ],
        [
            "673a505e107189ee54ca93310ac42e4545e9e59050aaac6f8b5f64295c8ec02f",
            "242ae39ef158ed60f20b89396d7d7eef5374aba15dc312a6aea6d1e57cacf85e",
        ],
        [
            "922688fa428d42bc1fa8806998fbc5959ae801817e85a42a45e8ec25a0d7545a",
            "696f341266c64bcfa7afa834f8c34b2730be11c932e08474d1a22f26ed82410b",
        ],
        [
            "0d3b0eb88b74ed13d5f6a130e03c4ad607817057dc227152827c0506a538bbba",
            "0b00df174d9fb0b6ee584d2cf05613130bad18875268c38b377e86dfefef177f",
        ],
        [
            "01a3ea5658f4e00622eeacf724e0bd82068992fae66ed2b04a8599be16662ef5",
            "7ae4c58bc647b5646c9f5ae4c2554ccbf7c6e428e7b242a574a5a9c293c21f7e",
        ],
        [
            "69599ab5a829c3e9515128d368da7354a8b69fcee4e34d0a668b783b6cae550f",
            "09024abaaef243e3b69366397e8dfc1fdc14a0ecc7cf497cbe4f328839acce69",
        ],
        [
            "9172922f96d2fa41ea0daf961857056f1656ab8406db80eaeae76af58f8c9f50",
            "beab745a2a4b4e7f1a7335c3ffcdbd85139f3a72b667a01ee3e3ae0e530b3372",
        ],
        [
            "6850a20ac5b6d2fa7af7042ad5be234d3311b9fb303753dd2b610bd566983281",
            "1287388eb2beeff706edb9cf4fcfdd35757f22541b61528570b86e8915be1530",
        ],
        [
            "84417826c0e80af7cb25a73af1ba87594ff7048a26248b5757e52f2824e068f1",
            "51acd2e8910e7d28b4993db7e97e2b995005f26736f60dcdde94bdf8cb542251",
        ],
        [
            "b0fbe152849f49034d2fa00ccc7b960fad7b30b6c4f9f2713eb01c147146ad31",
            "98508bb3590886af3be523b61c3d0ce6490bb8b27029878caec57e4c750f993d",
        ],
        [
            "a0ca9ff75afae65598630b3b93560834c7f4dd29a557aa29c7becd49aeef3753",
            "3c5fad0516bb8ec53da1c16e910c23f792b971c7e2a0ee57d57c32e3655a646b",
        ],
    ];

    // J.4.1.  curve25519_XMD:SHA-512_ELL2_RO_
    //
    // Random Oracle Curve25519 SHA512 Elligator2
    //
    // suite   = curve25519_XMD:SHA-512_ELL2_RO_
    // dst     = QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_RO_
    //
    #[allow(non_upper_case_globals)]
    const curve25519_XMD_SHA512_ELL2_RO: [xmd_sha512_25519_ro_testcase; 5] = [
        xmd_sha512_25519_ro_testcase {
            u_0: "49bed021c7a3748f09fa8cdfcac044089f7829d3531066ac9e74e0994e05bc7d",
            u_1: "5c36525b663e63389d886105cee7ed712325d5a97e60e140aba7e2ce5ae851b6",
            Q0_x: "16b3d86e056b7970fa00165f6f48d90b619ad618791661b7b5e1ec78be10eac1",
            Q0_y: "4ab256422d84c5120b278cbdfc4e1facc5baadffeccecf8ee9bf3946106d50ca",
            Q1_x: "7ec29ddbf34539c40adfa98fcb39ec36368f47f30e8f888cc7e86f4d46e0c264",
            Q1_y: "10d1abc1cae2d34c06e247f2141ba897657fb39f1080d54f09ce0af128067c74",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "6412b7485ba26d3d1b6c290a8e1435b2959f03721874939b21782df17323d160",
            u_1: "24c7b46c1c6d9a21d32f5707be1380ab82db1054fde82865d5c9e3d968f287b2",
            Q0_x: "71de3dadfe268872326c35ac512164850860567aea0e7325e6b91a98f86533ad",
            Q0_y: "26a08b6e9a18084c56f2147bf515414b9b63f1522e1b6c5649f7d4b0324296ec",
            Q1_x: "5704069021f61e41779e2ba6b932268316d6d2a6f064f997a22fef16d1eaeaca",
            Q1_y: "50483c7540f64fb4497619c050f2c7fe55454ec0f0e79870bb44302e34232210",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "5e123990f11bbb5586613ffabdb58d47f64bb5f2fa115f8ea8df0188e0c9e1b5",
            u_1: "5e8553eb00438a0bb1e7faa59dec6d8087f9c8011e5fb8ed9df31cb6c0d4ac19",
            Q0_x: "7a94d45a198fb5daa381f45f2619ab279744efdd8bd8ed587fc5b65d6cea1df0",
            Q0_y: "67d44f85d376e64bb7d713585230cdbfafc8e2676f7568e0b6ee59361116a6e1",
            Q1_x: "30506fb7a32136694abd61b6113770270debe593027a968a01f271e146e60c18",
            Q1_y: "7eeee0e706b40c6b5174e551426a67f975ad5a977ee2f01e8e20a6d612458c3b",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "20f481e85da7a3bf60ac0fb11ed1d0558fc6f941b3ac5469aa8b56ec883d6d7d",
            u_1: "017d57fd257e9a78913999a23b52ca988157a81b09c5442501d07fed20869465",
            Q0_x: "02d606e2699b918ee36f2818f2bc5013e437e673c9f9b9cdc15fd0c5ee913970",
            Q0_y: "29e9dc92297231ef211245db9e31767996c5625dfbf92e1c8107ef887365de1e",
            Q1_x: "38920e9b988d1ab7449c0fa9a6058192c0c797bb3d42ac345724341a1aa98745",
            Q1_y: "24dcc1be7c4d591d307e89049fd2ed30aae8911245a9d8554bf6032e5aa40d3d",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "005fe8a7b8fef0a16c105e6cadf5a6740b3365e18692a9c05bfbb4d97f645a6a",
            u_1: "1347edbec6a2b5d8c02e058819819bee177077c9d10a4ce165aab0fd0252261a",
            Q0_x: "36b4df0c864c64707cbf6cf36e9ee2c09a6cb93b28313c169be29561bb904f98",
            Q0_y: "6cd59d664fb58c66c892883cd0eb792e52055284dac3907dd756b45d15c3983d",
            Q1_x: "3fa114783a505c0b2b2fbeef0102853c0b494e7757f2a089d0daae7ed9a0db2b",
            Q1_y: "76c0fe7fec932aaafb8eefb42d9cbb32eb931158f469ff3050af15cfdbbeff94",
        },
    ];

    // J.4.2.  curve25519_XMD:SHA-512_ELL2_NU_
    //
    // Nonuniform Encoding Curve25519 SHA512 Elligator2
    //
    //    suite: curve25519_XMD:SHA-512_ELL2_NU_
    //    dst: QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_NU_
    //
    #[allow(non_upper_case_globals)]
    const curve25519_XMD_SHA512_ELL2_NU: [xmd_sha512_25519_nu_testcase; 5] = [
        xmd_sha512_25519_nu_testcase {
            u_0: "608d892b641f0328523802a6603427c26e55e6f27e71a91a478148d45b5093cd",
            Q_x: "51125222da5e763d97f3c10fcc92ea6860b9ccbbd2eb1285728f566721c1e65b",
            Q_y: "343d2204f812d3dfc5304a5808c6c0d81a903a5d228b342442aa3c9ba5520a3d",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "46f5b22494bfeaa7f232cc8d054be68561af50230234d7d1d63d1d9abeca8da5",
            Q_x: "7d56d1e08cb0ccb92baf069c18c49bb5a0dcd927eff8dcf75ca921ef7f3e6eeb",
            Q_y: "404d9a7dc25c9c05c44ab9a94590e7c3fe2dcec74533a0b24b188a5d5dacf429",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "235fe40c443766ce7e18111c33862d66c3b33267efa50d50f9e8e5d252a40aaa",
            Q_x: "3fbe66b9c9883d79e8407150e7c2a1c8680bee496c62fabe4619a72b3cabe90f",
            Q_y: "08ec476147c9a0a3ff312d303dbbd076abb7551e5fce82b48ab14b433f8d0a7b",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "001e92a544463bda9bd04ddbe3d6eed248f82de32f522669efc5ddce95f46f5b",
            Q_x: "227e0bb89de700385d19ec40e857db6e6a3e634b1c32962f370d26f84ff19683",
            Q_y: "5f86ff3851d262727326a32c1bf7655a03665830fa7f1b8b1e5a09d85bc66e4a",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "1a68a1af9f663592291af987203393f707305c7bac9c8d63d6a729bdc553dc19",
            Q_x: "3bcd651ee54d5f7b6013898aab251ee8ecc0688166fce6e9548d38472f6bd196",
            Q_y: "1bb36ad9197299f111b4ef21271c41f4b7ecf5543db8bb5931307ebdb2eaa465",
        },
    ];

    // J.5.1.  edwards25519_XMD:SHA-512_ELL2_RO_
    //
    // Random Oracle Edwards 25519 SHA512 Elligator2
    //
    //    suite: edwards25519_XMD:SHA-512_ELL2_RO_
    //    dst: QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_RO_
    //
    #[allow(non_upper_case_globals)]
    const edwards25519_XMD_SHA512_ELL2_RO: [xmd_sha512_25519_ro_testcase; 5] = [
        xmd_sha512_25519_ro_testcase {
            u_0: "03fef4813c8cb5f98c6eef88fae174e6e7d5380de2b007799ac7ee712d203f3a",
            u_1: "780bdddd137290c8f589dc687795aafae35f6b674668d92bf92ae793e6a60c75",
            Q0_x: "6549118f65bb617b9e8b438decedc73c496eaed496806d3b2eb9ee60b88e09a7",
            Q0_y: "7315bcc8cf47ed68048d22bad602c6680b3382a08c7c5d3f439a973fb4cf9feb",
            Q1_x: "31dcfc5c58aa1bee6e760bf78cbe71c2bead8cebb2e397ece0f37a3da19c9ed2",
            Q1_y: "7876d81474828d8a5928b50c82420b2bd0898d819e9550c5c82c39fc9bafa196",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "5081955c4141e4e7d02ec0e36becffaa1934df4d7a270f70679c78f9bd57c227",
            u_1: "005bdc17a9b378b6272573a31b04361f21c371b256252ae5463119aa0b925b76",
            Q0_x: "5c1525bd5d4b4e034512949d187c39d48e8cd84242aa4758956e4adc7d445573",
            Q0_y: "2bf426cf7122d1a90abc7f2d108befc2ef415ce8c2d09695a7407240faa01f29",
            Q1_x: "37b03bba828860c6b459ddad476c83e0f9285787a269df2156219b7e5c86210c",
            Q1_y: "285ebf5412f84d0ad7bb4e136729a9ffd2195d5b8e73c0dc85110ce06958f432",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "285ebaa3be701b79871bcb6e225ecc9b0b32dff2d60424b4c50642636a78d5b3",
            u_1: "2e253e6a0ef658fedb8e4bd6a62d1544fd6547922acb3598ec6b369760b81b31",
            Q0_x: "3ac463dd7fddb773b069c5b2b01c0f6b340638f54ee3bd92d452fcec3015b52d",
            Q0_y: "7b03ba1e8db9ec0b390d5c90168a6a0b7107156c994c674b61fe696cbeb46baf",
            Q1_x: "0757e7e904f5e86d2d2f4acf7e01c63827fde2d363985aa7432106f1b3a444ec",
            Q1_y: "50026c96930a24961e9d86aa91ea1465398ff8e42015e2ec1fa397d416f6a1c0",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "4fedd25431c41f2a606952e2945ef5e3ac905a42cf64b8b4d4a83c533bf321af",
            u_1: "02f20716a5801b843987097a8276b6d869295b2e11253751ca72c109d37485a9",
            Q0_x: "703e69787ea7524541933edf41f94010a201cc841c1cce60205ec38513458872",
            Q0_y: "32bb192c4f89106466f0874f5fd56a0d6b6f101cb714777983336c159a9bec75",
            Q1_x: "0c9077c5c31720ed9413abe59bf49ce768506128d810cb882435aa90f713ef6b",
            Q1_y: "7d5aec5210db638c53f050597964b74d6dda4be5b54fa73041bf909ccb3826cb",
        },
        xmd_sha512_25519_ro_testcase {
            u_0: "6e34e04a5106e9bd59f64aba49601bf09d23b27f7b594e56d5de06df4a4ea33b",
            u_1: "1c1c2cb59fc053f44b86c5d5eb8c1954b64976d0302d3729ff66e84068f5fd96",
            Q0_x: "21091b2e3f9258c7dfa075e7ae513325a94a3d8a28e1b1cb3b5b6f5d65675592",
            Q0_y: "41a33d324c89f570e0682cdf7bdb78852295daf8084c669f2cc9692896ab5026",
            Q1_x: "4c07ec48c373e39a23bd7954f9e9b66eeab9e5ee1279b867b3d5315aa815454f",
            Q1_y: "67ccac7c3cb8d1381242d8d6585c57eabaddbb5dca5243a68a8aeb5477d94b3a",
        },
    ];

    // J.5.2.  edwards25519_XMD:SHA-512_ELL2_NU_
    //
    // Nonuniform Encoding Edwards 25519 SHA512 Elligator2
    //
    //    suite: edwards25519_XMD:SHA-512_ELL2_NU_
    //    dst: QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_
    //
    #[allow(non_upper_case_globals)]
    const edwards25519_XMD_SHA512_ELL2_NU: [xmd_sha512_25519_nu_testcase; 5] = [
        xmd_sha512_25519_nu_testcase {
            u_0: "7f3e7fb9428103ad7f52db32f9df32505d7b427d894c5093f7a0f0374a30641d",
            Q_x: "42836f691d05211ebc65ef8fcf01e0fb6328ec9c4737c26050471e50803022eb",
            Q_y: "22cb4aaa555e23bd460262d2130d6a3c9207aa8bbb85060928beb263d6d42a95",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "09cfa30ad79bd59456594a0f5d3a76f6b71c6787b04de98be5cd201a556e253b",
            Q_x: "333e41b61c6dd43af220c1ac34a3663e1cf537f996bab50ab66e33c4bd8e4e19",
            Q_y: "51b6f178eb08c4a782c820e306b82c6e273ab22e258d972cd0c511787b2a3443",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "475ccff99225ef90d78cc9338e9f6a6bb7b17607c0c4428937de75d33edba941",
            Q_x: "55186c242c78e7d0ec5b6c9553f04c6aeef64e69ec2e824472394da32647cfc6",
            Q_y: "5b9ea3c265ee42256a8f724f616307ef38496ef7eba391c08f99f3bea6fa88f0",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "049a1c8bd51bcb2aec339f387d1ff51428b88d0763a91bcdf6929814ac95d03d",
            Q_x: "024b6e1621606dca8071aa97b43dce4040ca78284f2a527dcf5d0fbfac2b07e7",
            Q_y: "5102353883d739bdc9f8a3af650342b171217167dcce34f8db57208ec1dfdbf2",
        },
        xmd_sha512_25519_nu_testcase {
            u_0: "3cb0178a8137cefa5b79a3a57c858d7eeeaa787b2781be4a362a2f0750d24fa0",
            Q_x: "3e6368cff6e88a58e250c54bd27d2c989ae9b3acb6067f2651ad282ab8c21cd9",
            Q_y: "38fb39f1566ca118ae6c7af42810c0bb9767ae5960abb5a8ca792530bfb9447d",
        },
    ];

    #[allow(non_camel_case_types, non_snake_case)]
    #[derive(Debug)]
    struct xmd_sha512_25519_ro_testcase {
        u_0: &'static str,
        u_1: &'static str,
        // Output
        Q0_x: &'static str,
        Q0_y: &'static str,
        Q1_x: &'static str,
        Q1_y: &'static str,
    }

    #[allow(non_camel_case_types, non_snake_case)]
    #[derive(Debug)]
    struct xmd_sha512_25519_nu_testcase {
        u_0: &'static str,
        // output
        Q_x: &'static str,
        Q_y: &'static str,
    }

    trait FromByteString {
        fn must_from_le(&self) -> [u8; 32];
        fn must_from_be(&self) -> [u8; 32];
    }

    impl<'a> FromByteString for &'a str {
        fn must_from_le(&self) -> [u8; 32] {
            let mut u = <[u8; 32]>::from_hex(self).expect("failed to unhex");
            u.reverse();
            u
        }
        fn must_from_be(&self) -> [u8; 32] {
            <[u8; 32]>::from_hex(self).expect("failed to unhex from be")
        }
    }

    trait ToByteString {
        fn encode_le(&self) -> String;
        fn encode_be(&self) -> String;
    }

    impl ToByteString for FieldElement {
        fn encode_le(&self) -> String {
            let mut b = self.as_bytes();
            b.reverse();
            hex::encode(b)
        }

        fn encode_be(&self) -> String {
            hex::encode(self.as_bytes())
        }
    }

    impl ToByteString for [u8; 32] {
        fn encode_le(&self) -> String {
            let mut b = *self;
            b.reverse();
            hex::encode(b)
        }

        fn encode_be(&self) -> String {
            hex::encode(self)
        }
    }
}

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod randomness {
    use super::*;

    use kolmogorov_smirnov as ks;
    use rand::{thread_rng, RngCore};
    use rand_distr::{Binomial, Distribution};
    use std::vec::Vec;

    struct BitCounts {
        counts: [[u64; 100]; 32 * 8],
        entries: usize,
    }

    impl BitCounts {
        fn new() -> Self {
            BitCounts {
                counts: [[0u64; 100]; 256],
                entries: 0,
            }
        }
        fn entry(&mut self, arr: &[u8; 32]) {
            for (i, arr_byte) in arr.iter().enumerate() {
                for j in 0..8 {
                    self.counts[i * 8 + j][self.entries % 100] += ((arr_byte >> j) & 0x01) as u64;
                }
            }
            self.entries += 1;
        }
        fn outliers(&self) -> Vec<usize> {
            let mut rng = thread_rng();
            let binomial_100 =
                Binomial::new(100, 0.5).expect("failed to build binomial distribution");
            let expected_dist: [u64; 100] = binomial_100
                .sample_iter(&mut rng)
                .take(100)
                .collect::<Vec<u64>>()
                .try_into()
                .expect("failed to build example binomial expected distribution");
            // this is a high confidence, but we want to avoid this test failing
            // due to statistical variability on repeat runs.
            let confidence = 0.95;
            let mut outlier_indices = vec![];

            for (n, bit_trial) in self.counts.iter().enumerate() {
                let result = ks::test(bit_trial, &expected_dist, confidence);
                // require reject_probability == 1.0 to avoid statistical variability on re-runs
                if result.is_rejected && result.reject_probability == 1.0 {
                    // samples definitely not from same distribution
                    outlier_indices.push(n);
                    println!(
                        "{n}, {} {} {} {}",
                        result.statistic,
                        result.reject_probability,
                        result.critical_value,
                        result.confidence
                    );
                    if n == 255 {
                        println!("{:?}\n{:?}", bit_trial, expected_dist);
                    }
                }
            }
            outlier_indices
        }
    }

    #[test]
    /// If we use a "random" value for the tweak the high order bits will be
    /// set such that the representative is:
    /// 1) unchanged w.r.t. the public key value derived from the representative
    ///    i.e) it still derives the same public key value from the (clamped)
    ///         representative that we get from the private key.
    /// 2) statistically indistinguishable from uniform random.
    /// 4) computationally indistinguishable from random strings for the `a ?= sqrt(a^2)` test.
    ///
    /// (To see this test fail change `rng.next_u32() as u8` to `0u8`)
    fn bitwise_entropy() {
        const ITERATIONS: usize = 10000;
        // number of iterations
        let mut i = 0usize;
        let mut rng = thread_rng();
        let mut privkey = [0u8; 32];

        // count of occurences of a 1 per bit in the representative
        let mut bitcounts = BitCounts::new();

        while i < ITERATIONS {
            rng.fill_bytes(&mut privkey);
            let alice_representative =
                match representative_from_privkey(&privkey, rng.next_u32() as u8) {
                    None => continue,
                    Some(r) => r,
                };

            bitcounts.entry(&alice_representative);

            let pub_from_repr = MontgomeryPoint::map_to_point(&alice_representative);
            let pub_from_priv = EdwardsPoint::mul_base_clamped(privkey).to_montgomery();
            assert_eq!(
                hex::encode(pub_from_priv.as_bytes()),
                hex::encode(pub_from_repr.as_bytes()),
                "failed pubkey match at iteration {i}"
            );

            i += 1;
        }

        let outliers = bitcounts.outliers();
        assert!(outliers.is_empty(), "bad bits: {:?}", outliers);
    }

    /// TLDR: The sqrt_ratio_i function is canonical so this library does not
    /// suffer from the describbed computational distinguisher.
    ///
    /// The specific issue that this is testing for can be described as:
    /// ```txt
    /// An instantiation of Elligator is parameterized by what might be called
    /// a “canonical” square root function, one with the property that
    /// `√a2 = √(−a)2` for all field elements `a`. That is, we designate just
    /// over half the field elements as “non-negative,” and the image of the
    /// square root function consists of exactly those elements. A convenient
    /// definition of “non-negative” for Curve25519, suggested by its authors,
    /// is the lower half of the field, the elements `{0, 1, …, (q − 1) / 2}`.
    /// When there are two options for a square root, take the smaller of the two.
    /// ```
    ///
    /// Any Elligator implementation that does not do this canonicalization of
    /// the final square root, and instead it maps a given input systematically
    /// to either its negative or non-negative root is vulnerable to the
    /// following computational distinguisher.
    ///
    /// ```txt
    /// [An adversary could] observe a representative, interpret it as a field
    /// element, square it, then take the square root using the same
    /// non-canonical square root algorithm. With representatives produced by
    /// an affected version of [the elligator2 implementation], the output of
    /// the square-then-root operation would always match the input. With
    /// random strings, the output would match only half the time.
    /// ```
    ///
    /// For a more in-depth explanation see:
    /// https://github.com/agl/ed25519/issues/27
    /// https://www.bamsoftware.com/papers/fep-flaws/
    #[test]
    fn test_canonical() {
        const ITERATIONS: usize = 10000;
        // number of iterations
        let mut i = 0usize;
        let mut rng = thread_rng();
        let mut privkey = [0u8; 32];

        // number of times the representative (interpreted as a point) squared, then square_rooted,
        // equals the original representative. Should happen w/ 50% probability.
        let mut squares_equal = 0usize;

        while i < ITERATIONS {
            rng.fill_bytes(&mut privkey);
            let alice_representative = match representative_from_privkey(&privkey, 0u8) {
                None => continue,
                Some(r) => r,
            };

            if is_canonical(&alice_representative) {
                squares_equal += 1;
            }
            i += 1;
        }

        let expected_range = 4500..5500; // if truly binomial n=10000, p=0.5 then this should "always" pass (> 10x std dev)
        assert!(
            expected_range.contains(&squares_equal),
            "squares_equal: {squares_equal} is not in [4500:5500]"
        );
    }

    fn is_canonical(repres: &[u8; 32]) -> bool {
        let r_fe = FieldElement::from_bytes(repres);
        let (ok, r_fe_prime) = FieldElement::sqrt_ratio_i(&r_fe.square(), &FieldElement::ONE);
        (r_fe.ct_eq(&r_fe_prime) & ok).into()
    }
}
