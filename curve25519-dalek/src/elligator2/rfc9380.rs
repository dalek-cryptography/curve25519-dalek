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
