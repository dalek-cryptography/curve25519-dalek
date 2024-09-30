use crate::{elligator2::*, MontgomeryPoint};

use hex::{self, FromHex};

#[test]
#[cfg(feature = "elligator2")]
fn repres_from_pubkey_kleshni() {
    // testcases from kleshni
    for (i, testcase) in encoding_testcases().iter().enumerate() {
        // the testcases for kleshni have public key values encoded as montgomery
        // points with high_y as the sign bit
        let pubkey = <[u8; 32]>::from_hex(testcase.point).expect("failed to decode hex point");

        let edw_point = MontgomeryPoint(pubkey)
            .to_edwards(testcase.high_y as u8)
            .expect("failed to convert point to edwards");
        let v_in_sqrt = v_in_sqrt_pubkey_edwards(&edw_point);
        let repres = point_to_representative(&MontgomeryPoint(pubkey), v_in_sqrt.into());

        if testcase.representative.is_some() {
            let r = repres.expect("failed to get representative from point");

            // make sure that we did in fact get a representative
            assert_eq!(
                testcase
                    .representative
                    .expect("checked, is some - this should never fail"),
                hex::encode(r),
                "[good case] kleshni ({i}) bad representative from privkey",
            );

            // make sure that the representative we got is the correct representative
            let p = Legacy::from_representative(&r)
                .expect("failed to get pubkey from valid representative");

            // make sure that the public key derived from the representative matches
            // the public key derived from the privatekey.
            assert_eq!(
                hex::encode(pubkey),
                hex::encode(p.to_montgomery().to_bytes()),
                "[good case] kleshni ({i}) pubkey from repres doesn't match pubkey from privkey"
            );
        } else {
            // We expect the provided private key NOT to map to a representative
            assert!(
                <Choice as Into<bool>>::into(repres.is_none()),
                "[good case] kleshni ({i}) expected none got repres {}",
                hex::encode(repres.expect("this should not fail"))
            );
        }
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

        let point_from_unbounded = MontgomeryPoint::from_representative::<Legacy>(&repres)
            .expect("expected point, failed");
        assert_eq!(
            testcase.non_lsr_point,
            hex::encode(point_from_unbounded.to_bytes()),
            "[good case] kleshni ({i}) bad representative from point"
        );
    }
}

const ENCODING_TESTS_COUNT: usize = 10;
struct EncodingTestCase {
    /// sign value of the Montgomery point representation of the public key point
    high_y: bool,
    /// publkic key value, byte encoding of a Montgomery point
    point: &'static str,
    /// representative value associated with the provided point, if one exists.
    representative: Option<&'static str>,
}

/// In these testcases the `point` is the montgomery representation of the public
/// key value. We do not need the private key value to check these tests as we can
/// convert from public key to representative, and for some of the examples we may
/// not know what the associated private key would be as we manually swap the sign
/// ('high_y`) value for the public key point.
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
