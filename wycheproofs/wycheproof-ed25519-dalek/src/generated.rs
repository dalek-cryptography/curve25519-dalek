/// wycheproofs TC[1]
#[test]
fn wycheproof_tc_1() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "d4fbdb52bfa726b44d1786a8c0d171c3e62ca83c9e5bbe63de0bb2483f8fd6cc1429ab72cafc41ab56af02ff8fcc43b99bfe4c7ae940f60f38ebaa9d311c4007", "")
}

/// wycheproofs TC[2]
#[test]
fn wycheproof_tc_2() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "d80737358ede548acb173ef7e0399f83392fe8125b2ce877de7975d8b726ef5b1e76632280ee38afad12125ea44b961bf92f1178c9fa819d020869975bcbe109", "78")
}

/// wycheproofs TC[3]
#[test]
fn wycheproof_tc_3() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d", "54657374")
}

/// wycheproofs TC[4]
#[test]
fn wycheproof_tc_4() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "1c1ad976cbaae3b31dee07971cf92c928ce2091a85f5899f5e11ecec90fc9f8e93df18c5037ec9b29c07195ad284e63d548cd0a6fe358cc775bd6c1608d2c905", "48656c6c6f")
}

/// wycheproofs TC[5]
#[test]
fn wycheproof_tc_5() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bf0cf5b3a289976458a1be6277a5055545253b45b07dcc1abd96c8b989c00f301", "313233343030")
}

/// wycheproofs TC[6]
#[test]
fn wycheproof_tc_6() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "d46543bfb892f84ec124dcdfc847034c19363bf3fc2fa89b1267833a14856e52e60736918783f950b6f1dd8d40dc343247cd43ce054c2d68ef974f7ed0f3c60f", "000000000000000000000000")
}

/// wycheproofs TC[7]
#[test]
fn wycheproof_tc_7() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "879350045543bc14ed2c08939b68c30d22251d83e018cacbaf0c9d7a48db577e80bdf76ce99e5926762bc13b7b3483260a5ef63d07e34b58eb9c14621ac92f00", "6161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161")
}

/// wycheproofs TC[8]
#[test]
fn wycheproof_tc_8() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7bdc3f9919a05f1d5db4a3ada896094f6871c1f37afc75db82ec3147d84d6f237b7e5ecc26b59cfea0c7eaf1052dc427b0f724615be9c3d3e01356c65b9b5109", "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60")
}

/// wycheproofs TC[9]
#[test]
fn wycheproof_tc_9() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "5dbd7360e55aa38e855d6ad48c34bd35b7871628508906861a7c4776765ed7d1e13d910faabd689ec8618b78295c8ab8f0e19c8b4b43eb8685778499e943ae04", "ffffffffffffffffffffffffffffffff")
}

/// wycheproofs TC[10] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_10() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[11] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_11() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "00000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[12] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_12() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0000000000000000000000000000000000000000000000000000000000000000ecd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[13] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_13() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0000000000000000000000000000000000000000000000000000000000000000edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[14] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_14() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0000000000000000000000000000000000000000000000000000000000000000edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "3f")
}

/// wycheproofs TC[15] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_15() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[16] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_16() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "01000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[17] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_17() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0100000000000000000000000000000000000000000000000000000000000000ecd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[18] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_18() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0100000000000000000000000000000000000000000000000000000000000000edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[19] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_19() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0100000000000000000000000000000000000000000000000000000000000000edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "3f")
}

/// wycheproofs TC[20] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_20() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edd3f55c1a631258d69cf7a2def9de14000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[21] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_21() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edd3f55c1a631258d69cf7a2def9de14000000000000000000000000000000100100000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[22] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_22() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010ecd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[23] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_23() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[24] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_24() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "3f")
}

/// wycheproofs TC[25] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_25() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f0000000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[26] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_26() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f0100000000000000000000000000000000000000000000000000000000000000", "3f")
}

/// wycheproofs TC[27] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_27() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fecd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[28] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_28() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fedd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010", "3f")
}

/// wycheproofs TC[29] special values for r and s
#[test]
#[should_panic]
fn wycheproof_tc_29() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fedffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "3f")
}

/// wycheproofs TC[30] empty signature
#[test]
#[should_panic]
fn wycheproof_tc_30() {
    super::ed25519_dalek_wycheproof(
        "7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa",
        "",
        "54657374",
    )
}

/// wycheproofs TC[31] s missing
#[test]
#[should_panic]
fn wycheproof_tc_31() {
    super::ed25519_dalek_wycheproof(
        "7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa",
        "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab0",
        "54657374",
    )
}

/// wycheproofs TC[32] signature too short
#[test]
#[should_panic]
fn wycheproof_tc_32() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946", "54657374")
}

/// wycheproofs TC[33] signature too long
#[test]
#[should_panic]
fn wycheproof_tc_33() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d2020", "54657374")
}

/// wycheproofs TC[34] include pk in signature
#[test]
#[should_panic]
fn wycheproof_tc_34() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "54657374")
}

/// wycheproofs TC[35] prepending 0 byte to signature
#[test]
#[should_panic]
fn wycheproof_tc_35() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "007c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d", "54657374")
}

/// wycheproofs TC[36] prepending 0 byte to s
#[test]
#[should_panic]
fn wycheproof_tc_36() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab0007a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d", "54657374")
}

/// wycheproofs TC[37] appending 0 byte to signature
#[test]
#[should_panic]
fn wycheproof_tc_37() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d00", "54657374")
}

/// wycheproofs TC[38] removing 0 byte from signature
#[test]
#[should_panic]
fn wycheproof_tc_38() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "93de3ca252426c95f735cb9edd92e83321ac62372d5aa5b379786bae111ab6b17251330e8f9a7c30d6993137c596007d7b001409287535ac4804e662bc58a3", "546573743137")
}

/// wycheproofs TC[39] removing 0 byte from signature
#[test]
#[should_panic]
fn wycheproof_tc_39() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "dffed33a7f420b62bb1731cfd03be805affd18a281ec02b1067ba6e9d20826569e742347df59c88ae96db1f1969fb189b0ec34381d85633e1889da48d95e0e", "54657374313236")
}

/// wycheproofs TC[40] removing leading 0 byte from signature
#[test]
#[should_panic]
fn wycheproof_tc_40() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "6e170c719577c25e0e1e8b8aa7a6346f8b109f37385cc2e85dc3b4c0f46a9c6bcafd67f52324c5dbaf40a1b673fb29c4a56052d2d6999d0838a8337bccb502", "546573743530")
}

/// wycheproofs TC[41] dropping byte from signature
#[test]
#[should_panic]
fn wycheproof_tc_41() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "b0928b46e99fbbad3f5cb502d2cd309d94a7e86cfd4d84b1fcf4cea18075a9c36993c0582dba1e9e519fae5a8654f454201ae0c3cb397c37b8f4f8eef18400", "54657374333437")
}

/// wycheproofs TC[42] modified bit 0 in R
#[test]
#[should_panic]
fn wycheproof_tc_42() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "647c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b1d125e5538f38afbcc1c84e489521083041d24bc6240767029da063271a1ff0c", "313233343030")
}

/// wycheproofs TC[43] modified bit 1 in R
#[test]
#[should_panic]
fn wycheproof_tc_43() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "677c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bc108ca4b87a49c9ed2cf383aecad8f54a962b2899da891e12004d7993a627e01", "313233343030")
}

/// wycheproofs TC[44] modified bit 2 in R
#[test]
#[should_panic]
fn wycheproof_tc_44() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "617c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b9ce23fc6213ed5b87912e9bbf92f5e2c780eae26d15c50a112d1e97d2ea33c06", "313233343030")
}

/// wycheproofs TC[45] modified bit 7 in R
#[test]
#[should_panic]
fn wycheproof_tc_45() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "e57c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bbb3eb51cd98dddb235a5f46f2bded6af184a58d09cce928bda43f41d69118a03", "313233343030")
}

/// wycheproofs TC[46] modified bit 8 in R
#[test]
#[should_panic]
fn wycheproof_tc_46() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657d1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bcd237dda9a116501f67a5705a854b9adc304f34720803a91b324f2c13e0f5a09", "313233343030")
}

/// wycheproofs TC[47] modified bit 16 in R
#[test]
#[should_panic]
fn wycheproof_tc_47() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1592402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b6b167bbdc0d881cc04d28905552c1876f3709851abc5007376940cc8a435c300", "313233343030")
}

/// wycheproofs TC[48] modified bit 31 in R
#[test]
#[should_panic]
fn wycheproof_tc_48() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1412402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b7fd2ac7da14afffcceeb13f2a0d6b887941cb1a5eb57a52f3cb131a16cce7b0e", "313233343030")
}

/// wycheproofs TC[49] modified bit 32 in R
#[test]
#[should_panic]
fn wycheproof_tc_49() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492412ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b7373ba13ebbef99cd2a8ead55ce735c987d85a35320925a8e871702dc7c5c40d", "313233343030")
}

/// wycheproofs TC[50] modified bit 63 in R
#[test]
#[should_panic]
fn wycheproof_tc_50() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab54e03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bd35bd331c03f0855504ca1cab87b83c36a028425a3cf007ede4f4254c261cb00", "313233343030")
}

/// wycheproofs TC[51] modified bit 64 in R
#[test]
#[should_panic]
fn wycheproof_tc_51() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce02e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2bcb35101f73cf467deac8c1a03b6c3dc35af544132734b7e57ab20c89b2e4750d", "313233343030")
}

/// wycheproofs TC[52] modified bit 97 in R
#[test]
#[should_panic]
fn wycheproof_tc_52() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f2384d051b9cf3570f1207fc78c1bcc98c281c2bb58d2e8878290bff8d3355fdd4ea381924ee578752354eb6dee678ab4011c301", "313233343030")
}

/// wycheproofs TC[53] modified bit 127 in R
#[test]
#[should_panic]
fn wycheproof_tc_53() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d851b9cf3570f1207fc78c1bcc98c281c2bb978c866187ffb1cc7b29a0b4045aefc08768df65717194ff0c6e63f4dea0d02", "313233343030")
}

/// wycheproofs TC[54] modified bit 240 in R
#[test]
#[should_panic]
fn wycheproof_tc_54() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281d2b0576ecf8eaf675f00f3dfbe19f75b83b7607a6c96414f6821af920a2498d0305", "313233343030")
}

/// wycheproofs TC[55] modified bit 247 in R
#[test]
#[should_panic]
fn wycheproof_tc_55() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c289c2be5241a345c7b5428054c74b7c382fa10d4a5f1e8f8b79a71d3fdea2254f1ff0e", "313233343030")
}

/// wycheproofs TC[56] modified bit 248 in R
#[test]
#[should_panic]
fn wycheproof_tc_56() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2a63950c85cd6dc96364e768de50ff7732b538f8a0b1615d799190ab600849230e", "313233343030")
}

/// wycheproofs TC[57] modified bit 253 in R
#[test]
#[should_panic]
fn wycheproof_tc_57() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c0b543bd3da0a56a8c9c152f59c9fec12f31fa66434d48b817b30d90cb4efa8b501", "313233343030")
}

/// wycheproofs TC[58] modified bit 254 in R
#[test]
#[should_panic]
fn wycheproof_tc_58() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c6b8da07efd07a6dafb015ed6a32fe136319a972ffbc341f3a0beae97ccf8136505", "313233343030")
}

/// wycheproofs TC[59] modified bit 255 in R
#[test]
#[should_panic]
fn wycheproof_tc_59() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "657c1492402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281cab227aedf259f910f0f3a759a335062665217925d019173b88917eae294f75d40f", "313233343030")
}

/// wycheproofs TC[60] R==0
#[test]
#[should_panic]
fn wycheproof_tc_60() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "0000000000000000000000000000000000000000000000000000000000000000e0b8e7770d51c7a36375d006c5bffd6af43ff54aaf47e4330dc118c71d61ec02", "313233343030")
}

/// wycheproofs TC[61] invalid R
#[test]
#[should_panic]
fn wycheproof_tc_61() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff463a1908382e7eb7693acef9884f7cf931a215e0791876be22c631a59881fd0e", "313233343030")
}

/// wycheproofs TC[62] all bits flipped in R
#[test]
#[should_panic]
fn wycheproof_tc_62() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "9a83eb6dbfd54a31fc1d3c580fc7b2fae4630ca8f0edf803873e433673d7e3d40e94254586cb6188c5386c3febed477cb9a6cb29e3979adc4cb27cf5278fb70a", "313233343030")
}

/// wycheproofs TC[63] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_63() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab067654bce3832c2d76f8f6f5dafc08d9339d4eef676573336a5c51eb6f946b31d", "54657374")
}

/// wycheproofs TC[64] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_64() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab05439412b5395d42f462c67008eba6ca839d4eef676573336a5c51eb6f946b32d", "54657374")
}

/// wycheproofs TC[65] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_65() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab02ee12ce5875bf9dff26556464bae2ad239d4eef676573336a5c51eb6f946b34d", "54657374")
}

/// wycheproofs TC[66] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_66() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab0e2300459f1e742404cd934d2c595a6253ad4eef676573336a5c51eb6f946b38d", "54657374")
}

/// wycheproofs TC[67] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_67() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b32d", "54657374")
}

/// wycheproofs TC[68] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_68() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b34d", "54657374")
}

/// wycheproofs TC[69] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_69() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b38d", "54657374")
}

/// wycheproofs TC[70] checking malleability
#[test]
#[should_panic]
fn wycheproof_tc_70() {
    super::ed25519_dalek_wycheproof("7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa", "7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab0679155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b38d", "54657374")
}

/// wycheproofs TC[71]
#[test]
fn wycheproof_tc_71() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "5056325d2ab440bf30bbf0f7173199aa8b4e6fbc091cf3eb6bc6cf87cd73d992ffc216c85e4ab5b8a0bbc7e9a6e9f8d33b7f6e5ac0ffdc22d9fcaf784af84302", "")
}

/// wycheproofs TC[72]
#[test]
fn wycheproof_tc_72() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "481fafbf4364d7b682475282f517a3ac0538c9a6b6a562e99a3d8e5afb4f90a559b056b9f07af023905753b02d95eb329a35c77f154b79abbcd291615ce42f02", "78")
}

/// wycheproofs TC[73]
#[test]
fn wycheproof_tc_73() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "8a9bb4c465a3863abc9fd0dd35d80bb28f7d33d37d74679802d63f82b20da114b8d765a1206b3e9ad7cf2b2d8d778bb8651f1fa992db293c0039eacb6161480f", "54657374")
}

/// wycheproofs TC[74]
#[test]
fn wycheproof_tc_74() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "d839c20abfda1fd429531831c64f813f84b913e9928540310cf060b44c3dbf9457d44a7721fdc0d67724ff81cb450dd39b10cfb65db15dda4b8bf09d26bd3801", "48656c6c6f")
}

/// wycheproofs TC[75]
#[test]
fn wycheproof_tc_75() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "9bbb1052dcfa8ad2715c2eb716ae4f1902dea353d42ee09fd4c0b4fcb8b52b5219e2200016e1199d0061891c263e31b0bc3b55673c19610c4e0fa5408004160b", "313233343030")
}

/// wycheproofs TC[76]
#[test]
fn wycheproof_tc_76() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "f63b5c0667c7897fc283296416f7f60e84bbde9cbd832e56be463ed9f568069702b17a2f7c341ebf590706a6388ac76ac613c1675ec0f2c7118f2573422a500b", "000000000000000000000000")
}

/// wycheproofs TC[77]
#[test]
fn wycheproof_tc_77() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "1bc44d7001e6b5b9090fef34b2ca480f9786bbefa7d279353e5881e8dfb91b803ccd46500e270ef0109bfd741037558832120bc2a4f20fbe7b5fb3c3aaf23e08", "6161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161")
}

/// wycheproofs TC[78]
#[test]
fn wycheproof_tc_78() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "ea8e22143b02372e76e99aece3ed36aec529768a27e2bb49bdc135d44378061e1f62d1ac518f33ebf37b2ee8cc6dde68a4bd7d4a2f4d6cb77f015f71ca9fc30d", "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60")
}

/// wycheproofs TC[79]
#[test]
fn wycheproof_tc_79() {
    super::ed25519_dalek_wycheproof("a12c2beb77265f2aac953b5009349d94155a03ada416aad451319480e983ca4c", "8acd679e1a914fc45d5fa83d3021f0509c805c8d271df54e52f43cfbd00cb6222bf81d58fe1de2de378df67ee9f453786626961fe50a9b05f12b6f0899ebdd0a", "ffffffffffffffffffffffffffffffff")
}

/// wycheproofs TC[80] draft-josefsson-eddsa-ed25519-02: Test 1
#[test]
fn wycheproof_tc_80() {
    super::ed25519_dalek_wycheproof("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a", "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b", "")
}

/// wycheproofs TC[81] draft-josefsson-eddsa-ed25519-02: Test 2
#[test]
fn wycheproof_tc_81() {
    super::ed25519_dalek_wycheproof("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c", "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00", "72")
}

/// wycheproofs TC[82] draft-josefsson-eddsa-ed25519-02: Test 3
#[test]
fn wycheproof_tc_82() {
    super::ed25519_dalek_wycheproof("fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025", "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a", "af82")
}

/// wycheproofs TC[83] draft-josefsson-eddsa-ed25519-02: Test 1024
#[test]
fn wycheproof_tc_83() {
    super::ed25519_dalek_wycheproof("278117fc144c72340f67d0f2316e8386ceffbf2b2428c9c51fef7c597f1d426e", "0aab4c900501b3e24d7cdf4663326a3a87df5e4843b2cbdb67cbf6e460fec350aa5371b1508f9f4528ecea23c436d94b5e8fcd4f681e30a6ac00a9704a188a03", "08b8b2b733424243760fe426a4b54908632110a66c2f6591eabd3345e3e4eb98fa6e264bf09efe12ee50f8f54e9f77b1e355f6c50544e23fb1433ddf73be84d879de7c0046dc4996d9e773f4bc9efe5738829adb26c81b37c93a1b270b20329d658675fc6ea534e0810a4432826bf58c941efb65d57a338bbd2e26640f89ffbc1a858efcb8550ee3a5e1998bd177e93a7363c344fe6b199ee5d02e82d522c4feba15452f80288a821a579116ec6dad2b3b310da903401aa62100ab5d1a36553e06203b33890cc9b832f79ef80560ccb9a39ce767967ed628c6ad573cb116dbefefd75499da96bd68a8a97b928a8bbc103b6621fcde2beca1231d206be6cd9ec7aff6f6c94fcd7204ed3455c68c83f4a41da4af2b74ef5c53f1d8ac70bdcb7ed185ce81bd84359d44254d95629e9855a94a7c1958d1f8ada5d0532ed8a5aa3fb2d17ba70eb6248e594e1a2297acbbb39d502f1a8c6eb6f1ce22b3de1a1f40cc24554119a831a9aad6079cad88425de6bde1a9187ebb6092cf67bf2b13fd65f27088d78b7e883c8759d2c4f5c65adb7553878ad575f9fad878e80a0c9ba63bcbcc2732e69485bbc9c90bfbd62481d9089beccf80cfe2df16a2cf65bd92dd597b0707e0917af48bbb75fed413d238f5555a7a569d80c3414a8d0859dc65a46128bab27af87a71314f318c782b23ebfe808b82b0ce26401d2e22f04d83d1255dc51addd3b75a2b1ae0784504df543af8969be3ea7082ff7fc9888c144da2af58429ec96031dbcad3dad9af0dcbaaaf268cb8fcffead94f3c7ca495e056a9b47acdb751fb73e666c6c655ade8297297d07ad1ba5e43f1bca32301651339e22904cc8c42f58c30c04aafdb038dda0847dd988dcda6f3bfd15c4b4c4525004aa06eeff8ca61783aacec57fb3d1f92b0fe2fd1a85f6724517b65e614ad6808d6f6ee34dff7310fdc82aebfd904b01e1dc54b2927094b2db68d6f903b68401adebf5a7e08d78ff4ef5d63653a65040cf9bfd4aca7984a74d37145986780fc0b16ac451649de6188a7dbdf191f64b5fc5e2ab47b57f7f7276cd419c17a3ca8e1b939ae49e488acba6b965610b5480109c8b17b80e1b7b750dfc7598d5d5011fd2dcc5600a32ef5b52a1ecc820e308aa342721aac0943bf6686b64b2579376504ccc493d97e6aed3fb0f9cd71a43dd497f01f17c0e2cb3797aa2a2f256656168e6c496afc5fb93246f6b1116398a346f1a641f3b041e989f7914f90cc2c7fff357876e506b50d334ba77c225bc307ba537152f3f1610e4eafe595f6d9d90d11faa933a15ef1369546868a7f3a45a96768d40fd9d03412c091c6315cf4fde7cb68606937380db2eaaa707b4c4185c32eddcdd306705e4dc1ffc872eeee475a64dfac86aba41c0618983f8741c5ef68d3a101e8a3b8cac60c905c15fc910840b94c00a0b9d0")
}

/// wycheproofs TC[84] Signature with S just under the bound. [David Benjamin]
#[test]
fn wycheproof_tc_84() {
    super::ed25519_dalek_wycheproof("100fdf47fb94f1536a4f7c3fda27383fa03375a8f527c537e6f1703c47f94f86", "dac119d6ca87fc59ae611c157048f4d4fc932a149dbe20ec6effd1436abf83ea05c7df0fef06147241259113909bc71bd3c53ba4464ffcad3c0968f2ffffff0f", "124e583f8b8eca58bb29c271b41d36986bbc45541f8e51f9cb0133eca447601e")
}

/// wycheproofs TC[85] Signature with S just above the bound. [David Benjamin]
#[test]
#[should_panic]
fn wycheproof_tc_85() {
    super::ed25519_dalek_wycheproof("100fdf47fb94f1536a4f7c3fda27383fa03375a8f527c537e6f1703c47f94f86", "0971f86d2c9c78582524a103cb9cf949522ae528f8054dc20107d999be673ff4e25ebf2f2928766b1248bec6e91697775f8446639ede46ad4df4053000000010", "6a0bc2b0057cedfc0fa2e3f7f7d39279b30f454a69dfd1117c758d86b19d85e0")
}

/// wycheproofs TC[86] Random test failure 1
#[test]
fn wycheproof_tc_86() {
    super::ed25519_dalek_wycheproof("8fd659b77b558ed93882c1157438450ac86ec62d421d568e98ee236f3810295a", "7db17557ac470c0eda4eedaabce99197ab62565653cf911f632ee8be0e5ffcfc88fb94276b42e0798fd3aa2f0318be7fc6a29fae75f70c3dcdc414a0ad866601", "b0729a713593a92e46b56eaa66b9e435f7a09a8e7de03b078f6f282285276635f301e7aaafe42187c45d6f5b13f9f16b11195cc125c05b90d24dfe4c")
}

/// wycheproofs TC[87] Random test failure 2
#[test]
fn wycheproof_tc_87() {
    super::ed25519_dalek_wycheproof("2a606bf67ac770c607038b004101b325edb569efd3413d2d1f2c3e6b4e6e3082", "67d84d4c3945aaf06e06d524be63acbfb5dbb1988c4aea96a5ee9f7a9b9eecc29df4f66b8aa1d9e8607a58fb1ef0c2ad69aac005b4f58e34103344a9c8871a09", "a8546e50ba31cae3234310d32672447be213fad91a227a19669c53d309b959782b0e6b71f8791fdb470043b58122003157d2d96a43a6cbd7d3a8d86bf4c97391883e268d50af80e1e6e12939c2bd50ca746cdadfad4edf1bda875299740724148efb1ebe73fb60088cda890317658627a5f7ab5a0c075d9d8f3f97b6492b35519e50ff6b38377432a7081f9176bb1c29a862deac1336ca20b097a47829cec10a6a7cec178eda2d12f6dc6c87f910454af0123555ba184e68804d9cced60fd5c8c90943e56599c8f0ba59a38491ba5e5a53460682474c07e40ca142983314fd762856bb1093f359da6eb0a756bd93a3160c10dd8feea6b97e7c6a17cb54bd5d7649c05c66d7bdee056671dfdaf689fa3945bb8e29a429f4bd5d355dce9687b06f01d5e33e3999f0e8")
}

/// wycheproofs TC[88] Random test failure 3
#[test]
fn wycheproof_tc_88() {
    super::ed25519_dalek_wycheproof("c9c946cbc5544ac74eef491f07c5881c16faf7ec31ce4aa91bb60ae7b4539051", "24087d47f3e20af51b9668ae0a88ce76586802d0ec75d8c0f28fc30962b5e1d1a1d509571a1624ed125a8df92a6e963728d6b5de99200b8e285f70feb6f05207", "cd2212eddb0706f62c995cef958634f0cb7793444cbf4d30e81c27c41ebea6cb02607510131f9c015692dfd521b148841e9a2d3564d20ac401f6cb8e40f520fe0cafbeaa88840b83013369d879f013463fe52a13267aa0c8c59c45cde9399cd1e6be8cc64cf48315ac2eb31a1c567a4fb7d601746d1f63b5ac020712adbbe07519bded6f")
}

/// wycheproofs TC[89] Random test failure 4
#[test]
fn wycheproof_tc_89() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "d920d421a5956b69bfe1ba834c025e2babb6c7a6d78c97de1d9bb1116dfdd1185147b2887e34e15578172e150774275ea2aad9e02106f7e8ca1caa669a066f0c", "ec5c7cb078")
}

/// wycheproofs TC[90] Random test failure 5
#[test]
fn wycheproof_tc_90() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "4f62daf7f7c162038552ad7d306e195baa37ecf6ca7604142679d7d1128e1f8af52e4cb3545748c44ef1ff1c64e877e4f4d248259b7f6eb56e3ef72097dc8e0c", "4668c6a76f0e482190a7175b9f3806a5fe4314a004fa69f988373f7a")
}

/// wycheproofs TC[91] Random test failure 6
#[test]
fn wycheproof_tc_91() {
    super::ed25519_dalek_wycheproof("c29ec1894e06d27b4e40486b4fa5063d66a746c7f9c323b12203c03b72b8b78a", "6669acf94667c5b541afe5307bde9476b13ae7e0e6058a772101ac8eb0a94331428eb4db0a2c68a9b6c1763b8624dab259b0876cdcfaeacc17b21a18e3fc010a", "0f325ffd87e58131ffa23c05ea4579513b287fdba87b44")
}

/// wycheproofs TC[92] Random test failure 7
#[test]
fn wycheproof_tc_92() {
    super::ed25519_dalek_wycheproof("cfda5b899e35764c5229e59295fe1222b7ddce176643697c29e46ecbba10cf10", "30490c28f806298225df62103521dcee047153912c33ab8ab8bbdd1ffabd70fd4fdb360f05be535b067d1cf4e78c2cb432206bf280aab3bd21aaa1cb894c5b06", "ec5c7cb078")
}

/// wycheproofs TC[93] Random test failure 8
#[test]
fn wycheproof_tc_93() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "deecafb6f2ede73fec91a6f10e45b9c1c61c4b9bfbe6b6147e2de0b1df6938971f7896c3ab83851fb5d9e537037bff0fca0ccb4a3cc38f056f91f7d7a0557e08", "5dc9bb87eb11621a93f92abe53515697d2611b2eef73")
}

/// wycheproofs TC[94] Random test failure 9
#[test]
fn wycheproof_tc_94() {
    super::ed25519_dalek_wycheproof("cfda5b899e35764c5229e59295fe1222b7ddce176643697c29e46ecbba10cf10", "4cd4f77ed473a6647387f3163541c67a1708a3c3bd1673247cb87f0cb68b3c56f04bfa72970c8a483efe659c87009ab4020b590b6641316b3deddb5450544e02", "67484059b2490b1a0a4f8dee77979e26")
}

/// wycheproofs TC[95] Random test failure 10
#[test]
fn wycheproof_tc_95() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "7f8663cf98cbd39d5ff553f00bcf3d0d520605794f8866ce75714d77cc51e66c91818b657d7b0dae430a68353506edc4a714c345f5ddb5c8b958ba3d035f7a01", "7dcfe60f881e1285676f35b68a1b2dbcdd7be6f719a288ababc28d36e3a42ac3010a1ca54b32760e74")
}

/// wycheproofs TC[96] Random test failure 11
#[test]
fn wycheproof_tc_96() {
    super::ed25519_dalek_wycheproof("cfda5b899e35764c5229e59295fe1222b7ddce176643697c29e46ecbba10cf10", "1e41a24fe732bd7cab14c2a2f5134ee8c87fcbd2e987e60957ed9239e5c32404d56977e1b4282871896cb10625a1937468e4dc266e16a9c1b8e9891177eca802", "a020a4381dc9141f47ee508871ab7a8b5a3648727c4281ae9932376f23a8e1bcda0626b7129197d864178631ec89c4332dbb18")
}

/// wycheproofs TC[97] Random test failure 12
#[test]
fn wycheproof_tc_97() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "6aab49e5c0bc309b783378ee03ffda282f0185cdf94c847701ff307a6ee8d0865411c44e0a8206f6a5f606107451940c2593af790ce1860f4c14ab25b2deae08", "58e456064dff471109def4ca27fa8310a1df32739655b624f27e6418d34b7f007173f3faa5")
}

/// wycheproofs TC[98] Random test failure 13
#[test]
fn wycheproof_tc_98() {
    super::ed25519_dalek_wycheproof("529919c9c780985a841c42ba6c180ff2d67a276ccfbe281080e47ab71a758f56", "01abfa4d6bbc726b196928ec84fd03f0c953a4fa2b228249562ff1442a4f63a7150b064f3712b51c2af768d2c2711a71aabf8d186833e941a0301b82f0502905", "e1cbf2d86827825613fb7a85811d")
}

/// wycheproofs TC[99] Random test failure 14
#[test]
fn wycheproof_tc_99() {
    super::ed25519_dalek_wycheproof("cfda5b899e35764c5229e59295fe1222b7ddce176643697c29e46ecbba10cf10", "2a833aadecd9f28235cb5896bf3781521dc71f28af2e91dbe1735a61dce3e31ac15ca24b3fc47817a59d386bbbb2ce60a6adc0a2703bb2bdea8f70f91051f706", "a25176b3afea318b2ec11ddacb10caf7179c0b3f8eabbfa2895581138d3c1e0e")
}

/// wycheproofs TC[100] Random test failure 15
#[test]
fn wycheproof_tc_100() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "1a74ed2cbdc7d8f3827014e8e6ecf8fd2698ac8f86833acccdd400df710fe0d6b0543c9cfa00d52bf024ab7ce0d91981944097233ec134d5c7abbd44bfd32d0d", "a1")
}

/// wycheproofs TC[101] Random test failure 16
#[test]
fn wycheproof_tc_101() {
    super::ed25519_dalek_wycheproof("2252b3d57c74cbf8bc460dc2e082847926bc022f09ab6ae95756362bfd1167c1", "af0fd9dda7e03e12313410d8d8844ebb6fe6b7f65141f22d7bcba5695a25414a9e54326fb44d59fb14707899a8aae70857b23d4080d7ab2c396ef3a36d45ce02", "975ef941710071a9e1e6325a0c860becd7c695b5117c3107b686e330e5")
}

/// wycheproofs TC[102] Random test failure 17
#[test]
fn wycheproof_tc_102() {
    super::ed25519_dalek_wycheproof("c0a773110f975de3732355bb7ec7f0c41c091c0252966070205516693b992a4a", "0280427e713378f49d478df6373c6cac847b622b567daa2376c839e7ac10e22c380ab0fa8617c9dcfe76c4d9db5459b21dc1413726e46cc8f387d359e344f407", "")
}

/// wycheproofs TC[103] Random test failure 18
#[test]
fn wycheproof_tc_103() {
    super::ed25519_dalek_wycheproof("cfda5b899e35764c5229e59295fe1222b7ddce176643697c29e46ecbba10cf10", "c97e3190f83bae7729ba473ad46b420b8aad735f0808ea42c0f898ccfe6addd4fd9d9fa3355d5e67ee21ab7e1f805cd07f1fce980e307f4d7ad36cc924eef00c", "a9e6d94870a67a9fe1cf13b1e6f9150cdd407bf6480ec841ea586ae3935e9787163cf419c1")
}

/// wycheproofs TC[104] Random test failure 19
#[test]
fn wycheproof_tc_104() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "14ceb2eaf4688d995d482f44852d71ad878cd7c77b41e60b0065fd01a59b054ee74759224187dbde9e59a763a70277c960892ef89fba997aba2576b2c54ba608", "11cb1eafa4c42a8402c4193c4696f7b2e6d4585e4b42dcf1a8b67a80b2da80bc9d4b649fb2f35eaf1f56c426fd0b")
}

/// wycheproofs TC[105] Random test failure 20
#[test]
fn wycheproof_tc_105() {
    super::ed25519_dalek_wycheproof("c9c946cbc5544ac74eef491f07c5881c16faf7ec31ce4aa91bb60ae7b4539051", "c2656951e2a0285585a51ff0eda7e9a23c2dfd2ffa273aee7808f4604e8f9a8c8ea49e9fce4eb2d8d75d36b7238fe6fc13b6c5d9427dd58f8c6615d033c0bd0f", "27d465bc632743522aefa23c")
}

/// wycheproofs TC[106] Random test failure 21
#[test]
fn wycheproof_tc_106() {
    super::ed25519_dalek_wycheproof("c29ec1894e06d27b4e40486b4fa5063d66a746c7f9c323b12203c03b72b8b78a", "931e5152fcef078c22cc5d6a3a65f06e396289f6f5f2d1efa6340254a53526ef5dc6874eeddf35c3f50991c53cd02bf06313e37d93ee1f7022128ffa3b8f300b", "5ffa")
}

/// wycheproofs TC[107] Random test failure 22
#[test]
fn wycheproof_tc_107() {
    super::ed25519_dalek_wycheproof("529919c9c780985a841c42ba6c180ff2d67a276ccfbe281080e47ab71a758f56", "e4ae21f7a8f4b3b325c161a8c6e53e2edd7005b9c2f8a2e3b0ac4ba94aa80be6f2ee22ac8d4a96b9a3eb73a825e7bb5aff4a3393bf5b4a38119e9c9b1b041106", "25")
}

/// wycheproofs TC[108] Random test failure 23
#[test]
fn wycheproof_tc_108() {
    super::ed25519_dalek_wycheproof("2252b3d57c74cbf8bc460dc2e082847926bc022f09ab6ae95756362bfd1167c1", "e097e0bd0370bff5bde359175a11b728ee9639095d5df8eda496395565616edfe079977f7d4dc8c75d6113a83d6a55e6e1676408c0967a2906339b43337dcb01", "80fdd6218f29c8c8f6bd820945f9b0854e3a8824")
}

/// wycheproofs TC[109] Random test failure 24
#[test]
fn wycheproof_tc_109() {
    super::ed25519_dalek_wycheproof("2a606bf67ac770c607038b004101b325edb569efd3413d2d1f2c3e6b4e6e3082", "28fafbb62b4d688fa79e1ac92851f46e319b161f801d4dc09acc21fdd6780a2c4292b8c1003c61c2bcebe7f3f88ccc4bb26d407387c5f27cb8c94cf6ce810405", "b477b0480bb84642608b908d29a51cf2fce63f24ee95")
}

/// wycheproofs TC[110] Random test failure 25
#[test]
fn wycheproof_tc_110() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "83c40ce13d483cc58ff65844875862d93df4bd367af77efa469ec06a8ed9e6d7905a04879535708ddf225567a815c9b941d405c98e918fd0c151165cea7fb101", "aa365b442d12b7f3c925")
}

/// wycheproofs TC[111] Random test failure 26
#[test]
fn wycheproof_tc_111() {
    super::ed25519_dalek_wycheproof("54cda623245759ad6d43e620a606908befc633d60792bc7798447a0ef38e7311", "14d9b497c19b91d43481c55bb6f5056de252d9ecb637575c807e58e9b4c5eac8b284089d97e2192dc242014363208e2c9a3435edf8928fb1d893553e9be4c703", "27e792b28b2f1702")
}

/// wycheproofs TC[112] Random test failure 27
#[test]
fn wycheproof_tc_112() {
    super::ed25519_dalek_wycheproof("2362bac514d5fad33802642e979a1e82de6eb6f1bcbf6a5b304f2bb02b9e57fe", "242ddb3a5d938d07af690b1b0ef0fa75842c5f9549bf39c8750f75614c712e7cbaf2e37cc0799db38b858d41aec5b9dd2fca6a3c8e082c10408e2cf3932b9d08", "eef3bb0f617c17d0420c115c21c28e3762edc7b7fb048529b84a9c2bc6")
}

/// wycheproofs TC[113] Random test failure 28
#[test]
fn wycheproof_tc_113() {
    super::ed25519_dalek_wycheproof("32ad026f693d0d2afe7f4388d91c4c964426fcb9e3665c3ebd8650009b815c8e", "71a4a06a34075f2fd47bc3abf4714d46db7e97b08cb6180d3f1539ac50b18ce51f8af8ae95ed21d4fa0daab7235925631ecea1fd9d0d8a2ba7a7583fd04b900c", "475f")
}

/// wycheproofs TC[114] Test case for overflow in signature generation
#[test]
fn wycheproof_tc_114() {
    super::ed25519_dalek_wycheproof("037b55b427dc8daa0f80fcebaf0846902309f8a6cf18b465c0ce9b6539629ac8", "c964e100033ce8888b23466677da4f4aea29923f642ae508f9d0888d788150636ab9b2c3765e91bbb05153801114d9e52dc700df377212222bb766be4b8c020d", "01234567")
}

/// wycheproofs TC[115] Test case for overflow in signature generation
#[test]
fn wycheproof_tc_115() {
    super::ed25519_dalek_wycheproof("9c0007698f177998a7666c7cf7973e2b88e9c4946e33804a7bbe8968d2394b2e", "176065c6d64a136a2227687d77f61f3fca3b16122c966276fd9a8b14a1a2cea4c33b3533d11101717016684e3810efbea63bb23773f7cc480174199abd734f08", "9399a6db9433d2a28d2b0c11c8794ab7d108c95b")
}

/// wycheproofs TC[116] Test case for overflow in signature generation
#[test]
fn wycheproof_tc_116() {
    super::ed25519_dalek_wycheproof("ed3a6f9721dc9729c1f76635bcf080d7036e1c2f0228654ccbbe1e738c17b963", "7ca69331eec8610d38f00e2cdbd46966cb359dcde98a257ac6f362cc00c8f4fe85c02285fe4d66e31a44cadb2bf474e1a7957609eb4fe95a71473fe6699aa70d", "7af783afbbd44c1833ab7237ecaf63b94ffdd003")
}

/// wycheproofs TC[117] Test case for overflow in signature generation
#[test]
fn wycheproof_tc_117() {
    super::ed25519_dalek_wycheproof("4abfb535313705a6570018440cdec1a3ae33e51f352112fa6acbd0c6bc3ea859", "f296715e855d8aecccba782b670163dedc4458fe4eb509a856bcac450920fd2e95a3a3eb212d2d9ccaf948c39ae46a2548af125f8e2ad9b77bd18f92d59f9200", "321b5f663c19e30ee7bbb85e48ecf44db9d3f512")
}

/// wycheproofs TC[118] Test case for overflow in signature generation
#[test]
fn wycheproof_tc_118() {
    super::ed25519_dalek_wycheproof("4f2162e6bf03a712db0efa418b7e7006e23871d9d7ec555a313885c4afd96385", "367d07253a9d5a77d054b9c1a82d3c0a448a51905343320b3559325ef41839608aa45564978da1b2968c556cfb23b0c98a9be83e594d5e769d69d1156e1b1506", "c48890e92aeeb3af04858a8dc1d34f16a4347b91")
}

/// wycheproofs TC[119] regression test for arithmetic error
#[test]
fn wycheproof_tc_119() {
    super::ed25519_dalek_wycheproof("4abfb535313705a6570018440cdec1a3ae33e51f352112fa6acbd0c6bc3ea859", "f296715e855d8aecccba782b670163dedc4458fe4eb509a856bcac450920fd2e95a3a3eb212d2d9ccaf948c39ae46a2548af125f8e2ad9b77bd18f92d59f9200", "321b5f663c19e30ee7bbb85e48ecf44db9d3f512")
}

/// wycheproofs TC[120] regression test for arithmetic error
#[test]
fn wycheproof_tc_120() {
    super::ed25519_dalek_wycheproof("4f2162e6bf03a712db0efa418b7e7006e23871d9d7ec555a313885c4afd96385", "367d07253a9d5a77d054b9c1a82d3c0a448a51905343320b3559325ef41839608aa45564978da1b2968c556cfb23b0c98a9be83e594d5e769d69d1156e1b1506", "c48890e92aeeb3af04858a8dc1d34f16a4347b91")
}

/// wycheproofs TC[121] regression test for arithmetic error
#[test]
fn wycheproof_tc_121() {
    super::ed25519_dalek_wycheproof("0717d75ce27ea181ed5a30e6456c649b5cf453a6b4c12cd3f9fd16b31e0c25cd", "9588e02bc815649d359ce710cdc69814556dd8c8bab1c468f40a49ebefb7f0de7ed49725edfd1b708fa1bad277c35d6c1b9c5ec25990997645780f9203d7dd08", "26d5f0631f49106db58c4cfc903691134811b33c")
}

/// wycheproofs TC[122] regression test for arithmetic error
#[test]
fn wycheproof_tc_122() {
    super::ed25519_dalek_wycheproof("db5b9eab7e84e5a13505865fa711c9c896c898609fc11fc9bc1e55028f9496df", "2217a0be57dd0d6c0090641496bcb65e37213f02a0df50aff0368ee2808e1376504f37b37494132dfc4d4887f58b9e86eff924040db3925ee4f8e1428c4c500e", "2a71f064af982a3a1103a75cef898732d7881981")
}

/// wycheproofs TC[123] regression test for arithmetic error
#[test]
fn wycheproof_tc_123() {
    super::ed25519_dalek_wycheproof("7bac18f6d2625d3915f233434cda38a577247a7332a5170b37142a34644145e0", "1fda6dd4519fdbefb515bfa39e8e5911f4a0a8aa65f40ef0c542b8b34b87f9c249dc57f320718ff457ed5915c4d0fc352affc1287724d3f3a9de1ff777a02e01", "bf26796cef4ddafcf5033c8d105057db0210b6ad")
}

/// wycheproofs TC[124] regression test for arithmetic error
#[test]
fn wycheproof_tc_124() {
    super::ed25519_dalek_wycheproof("7bac18f6d2625d3915f233434cda38a577247a7332a5170b37142a34644145e0", "1fda6dd4519fdbefb515bfa39e8e5911f4a0a8aa65f40ef0c542b8b34b87f9c249dc57f320718ff457ed5915c4d0fc352affc1287724d3f3a9de1ff777a02e01", "bf26796cef4ddafcf5033c8d105057db0210b6ad")
}

/// wycheproofs TC[125] regression test for arithmetic error
#[test]
fn wycheproof_tc_125() {
    super::ed25519_dalek_wycheproof("38ead304624abebf3e2b31e20e5629531e3fc659008887c9106f5e55adbbc62a", "068eafdc2f36b97f9bae7fbda88b530d16b0e35054d3a351e3a4c914b22854c711505e49682e1a447e10a69e3b04d0759c859897b64f71137acf355b63faf100", "ae03da6997e40cea67935020152d3a9a365cc055")
}

/// wycheproofs TC[126] regression test for arithmetic error
#[test]
fn wycheproof_tc_126() {
    super::ed25519_dalek_wycheproof("e9bc95049af7e4817b17c402269ba5e767b7348757ac8002fec9e08390c0a9cf", "43670abc9f09a8a415e76f4a21c6a46156f066b5a37b3c1e867cf67248c7b927e8d13a763e37abf936f5f27f7a8aa290539d21f740efd26b65fd5ad27085f400", "489d473f7fb83c7f6823baf65482517bccd8f4ea")
}

/// wycheproofs TC[127] regression test for arithmetic error
#[test]
fn wycheproof_tc_127() {
    super::ed25519_dalek_wycheproof("ee8155ca4e8fe7bc5bca5992044eab7f8c3c6a13db1176f42f46c29da5b064f4", "56388f2228893b14ce4f2a5e0cc626591061de3a57c50a5ecab7b9d5bb2caeea191560a1cf2344c75fdb4a085444aa68d727b39f498169eaa82cf64a31f59803", "1b704d6692d60a07ad1e1d047b65e105a80d3459")
}

/// wycheproofs TC[128] regression test for arithmetic error
#[test]
fn wycheproof_tc_128() {
    super::ed25519_dalek_wycheproof("db507bfcc9576393f7157bb360532b05c5fcf2e764b690cc6698a4a30d349095", "553e5845fc480a577da6544e602caadaa00ae3e5aa3dce9ef332b1541b6d5f21bdf1d01e98baf80b8435f9932f89b3eb70f02da24787aac8e77279e797d0bd0b", "dc87030862c4c32f56261e93a367caf458c6be27")
}

/// wycheproofs TC[129] regression test for arithmetic error
#[test]
fn wycheproof_tc_129() {
    super::ed25519_dalek_wycheproof("994eaf03309d6ad9d95a656bc1744e2886f029023a3750b34f35086b3c7227f8", "bc10f88081b7be1f2505b6e76c5c82e358cf21ec11b7df1f334fb587bada465b53d9f7b4d4fec964432ee91ead1bc32ed3c82f2167da1c834a37515df7fe130e", "7f41ef68508343ef18813cb2fb332445ec6480cd")
}

/// wycheproofs TC[130] regression test for arithmetic error
#[test]
fn wycheproof_tc_130() {
    super::ed25519_dalek_wycheproof("127d37e406e0d83e4b55a09e21e8f50fb88af47e4a43f018cdebffc1948757f0", "00c11e76b5866b7c37528b0670188c1a0473fb93c33b72ae604a8865a7d6e094ff722e8ede3cb18389685ff3c4086c29006047466f81e71a329711e0b9294709", "e1ce107971534bc46a42ac609a1a37b4ca65791d")
}

/// wycheproofs TC[131] regression test for arithmetic error
#[test]
fn wycheproof_tc_131() {
    super::ed25519_dalek_wycheproof("d83ba84edfb4bec49f29be31d80a64b7c0b5a502438cdb1d0dd1e0e3e55786de", "0a6f0ac47ea136cb3ff00f7a96638e4984048999ee2da0af6e5c86bffb0e70bb97406b6ad5a4b764f7c99ebb6ec0fd434b8efe253b0423ef876c037998e8ab07", "869a827397c585cf35acf88a8728833ab1c8c81e")
}

/// wycheproofs TC[132] regression test for arithmetic error
#[test]
fn wycheproof_tc_132() {
    super::ed25519_dalek_wycheproof("d3c9aa2f3d6ef217a166e8ae403ed436c37facbbe3beceb78df6eb439f8fa04a", "b7cbb942a6661e2312f79548224f3e44f5841c6e880c68340756a00ce94a914e8404858265985e6bb97ef01d2d7e5e41340309606bfc43c8c6a8f925126b3d09", "619d8c4f2c93104be01cd574a385ceca08c33a9e")
}

/// wycheproofs TC[133] regression test for arithmetic error
#[test]
fn wycheproof_tc_133() {
    super::ed25519_dalek_wycheproof("d53280367c1c0b95ac4112218b92c6a71c51fb6312ce668de196c7d52a136155", "27a4f24009e579173ff3064a6eff2a4d20224f8f85fdec982a9cf2e6a3b51537348a1d7851a3a932128a923a393ea84e6b35eb3473c32dceb9d7e9cab03a0f0d", "5257a0bae8326d259a6ce97420c65e6c2794afe2")
}

/// wycheproofs TC[134] regression test for arithmetic error
#[test]
fn wycheproof_tc_134() {
    super::ed25519_dalek_wycheproof("94ac2336ba97a476fb4c9f2b5563e4167ca292c6e99e422350a911ae3172c315", "985b605fe3f449f68081197a68c714da0bfbf6ac2ab9abb0508b6384ea4999cb8d79af98e86f589409e8d2609a8f8bd7e80aaa8d92a84e7737fbe8dcef41920a", "5acb6afc9b368f7acac0e71f6a4831c72d628405")
}

/// wycheproofs TC[135] regression test for arithmetic error
#[test]
fn wycheproof_tc_135() {
    super::ed25519_dalek_wycheproof("e1e7316d231f7f275bdf403360304da1509fdf1af1fd25ca214eaac0a289398f", "1c8fbda3d39e2b441f06da6071c13115cb4115c7c3341704cf6513324d4cf1ef4a1dd7678a048b0dde84e48994d080befcd70854079d44b6a0b0f9fa002d130c", "3c87b3453277b353941591fc7eaa7dd37604b42a")
}

/// wycheproofs TC[136] regression test for arithmetic error
#[test]
fn wycheproof_tc_136() {
    super::ed25519_dalek_wycheproof("fffbeea71215efaf9888fec2cc68edb3703ff11a66fd629b53cbda5eabc18750", "59097233eb141ed948b4f3c28a9496b9a7eca77454ecfe7e46737d1449a0b76b15aacf77cf48af27a668aa4434cfa26c504d75a2bcc4feac46465446234c0508", "0a68e27ef6847bfd9e398b328a0ded3679d4649d")
}

/// wycheproofs TC[137] regression test for arithmetic error
#[test]
fn wycheproof_tc_137() {
    super::ed25519_dalek_wycheproof("19ccc0527599cb032e0b4c4d74e60f13901768a99df041c3bc1bf6c0ef271169", "519105608508fe2f1b6da4cc8b23e39798b1d18d25972beed0404cec722e01ba1b6a0f85e99e092cca8076b101b60d4ac5035684357f4d0daacdc642da742a06", "4e9bef60737c7d4dd10bd52567e1473a36d3573d")
}

/// wycheproofs TC[138] regression test for arithmetic error
#[test]
fn wycheproof_tc_138() {
    super::ed25519_dalek_wycheproof("0e726e27047563aa0a1a9c2e085d8d26af2acba129d0869c65031e3e6cac329a", "d8b03ee579e73f16477527fc9dc37a72eaac0748a733772c483ba013944f01ef64fb4ec5e3a95021dc22f4ae282baff6e9b9cc8433c6b6710d82e7397d72ef04", "cc82b3163efda3ba7e9240e765112caa69113694")
}

/// wycheproofs TC[139] regression test for arithmetic error
#[test]
fn wycheproof_tc_139() {
    super::ed25519_dalek_wycheproof("e77717b54a2b5e5bce5bccb8f0c5fdb5fd7df77ac254020fc9120dc0d4df4178", "26da61fdfd38e6d01792813f27840c8b4766b0faaed39d0ee898cb450d94a5d5f57e58b6a003d7f9b56b20561954c6edcf66492d116b8b5e91f205a3a6449d0b", "923a5c9e7b5635bb6c32c5a408a4a15b652450eb")
}

/// wycheproofs TC[140] regression test for arithmetic error
#[test]
fn wycheproof_tc_140() {
    super::ed25519_dalek_wycheproof("6220972d3f7d150b36790d7d522384876d64d640cd9913186815e1629582ed36", "4adeaff7a58c5010a5a067feea0ae504d37b0c6a76c6c153e222f13409dff2df0fab69bc5059b97d925dc1b89e9851d7c627cb82d65585f9fd976124553f8902", "6f2f0245de4587062979d0422d349f93ccdc3af2")
}

/// wycheproofs TC[141] regression test for arithmetic error
#[test]
fn wycheproof_tc_141() {
    super::ed25519_dalek_wycheproof("7b64a28c50ec7678a90e3e1a21522e30ac9db7b5215aea2bfb33bea037eab987", "4204d620cde0c3008c0b2901f5d6b44f88f0e3cb4f4d62252bf6f3cb37c1fb150a9ccb296afe5e7c75f65b5c8edd13dc4910ffe1e1265b3707c59042cf9a5902", "6e911edb27a170b983d4dee1110554f804330f41")
}

/// wycheproofs TC[142] regression test for arithmetic error
#[test]
fn wycheproof_tc_142() {
    super::ed25519_dalek_wycheproof("724452210a9e4c994819229bf12bf84e95768a3a97c08d8d8f5f939a4cad34c5", "f8a69d3fd8c2ff0a9dec41e4c6b43675ce08366a35e220b1185ffc246c339e22c20ac661e866f52054015efd04f42eca2adcee6834c4df923b4a62576e4dff0e", "b8cf807eea809aaf739aa091f3b7a3f2fd39fb51")
}

/// wycheproofs TC[143] regression test for arithmetic error
#[test]
fn wycheproof_tc_143() {
    super::ed25519_dalek_wycheproof("bad265b294ed2f422cb6a141694086238fbfe987571aa765d8b4f3a24105aa01", "61792c9442bc6338ac41fd42a40bee9b02ec1836503d60ff725128c63d72808880c36e6190b7da525cbee5d12900aa043547dd14a2709ef9e49d628f37f6b70c", "01a2b5f7fee813b4e9bd7fc25137648004795010")
}

/// wycheproofs TC[144] regression test for arithmetic error
#[test]
fn wycheproof_tc_144() {
    super::ed25519_dalek_wycheproof("0aaee4b723db9b51ba7d22eb23eb8a76a5ac02f4fc9dd06f77bea42e1d37ec5a", "fa3cd41e3a8c00b19eecd404a63c3cb787cd30de0dfc936966cff2117f5aff18db6bef80fcfd8856f3fb2e9c3dc47593e9471103032af918feee638a33d40505", "0fbf5d47cb5d498feace8f98f1896208da38a885")
}

/// wycheproofs TC[145] regression test for arithmetic error
#[test]
fn wycheproof_tc_145() {
    super::ed25519_dalek_wycheproof("812344af15a91ba83c2c91e96f1727ac0f3c4c41385b9fa84efa399ada5168be", "97fbbcd7a1d0eb42d2f8c42448ef35a2c2472740556b645547865330d6c57068af377fced08aaf810c08cd3c43d296f1975710312e9334c98b485f831efa4103", "36e67c1939750bffb3e4ba6cb85562612275e862")
}

/// wycheproofs TC[146] regression test for arithmetic error
#[test]
fn wycheproof_tc_146() {
    super::ed25519_dalek_wycheproof("0ee5cb5597fbdf8dccc48b01485e39b33aa133b52d30d23740277267cfec3e3e", "d7dbaa337ffd2a5fd8d5fd8ad5aeccc0c0f83795c2c59fe62a40b87903b1ae62ed748a8df5af4d32f9f822a65d0e498b6f40eaf369a9342a1164ee7d08b58103", "13945c894c1d3fe8562e8b20e5f0efaa26ade8e3")
}

/// wycheproofs TC[147] regression test for arithmetic error
#[test]
fn wycheproof_tc_147() {
    super::ed25519_dalek_wycheproof("9fba1de92b60b5b4703089763d0d6f9125e4dd7efae41f08a22882aef96892c4", "09a2ed303a2fa7027a1dd7c3b0d25121eeed2b644a2fbc17aa0c8aea4524071ede7e7dd7a536d5497f8165d29e4e1b63200f74bbae39fbbbccb29889c62c1f09", "4de142af4b8402f80a47fa812df84f42e283cee7")
}

/// wycheproofs TC[148] regression test for arithmetic error
#[test]
fn wycheproof_tc_148() {
    super::ed25519_dalek_wycheproof("7582ab1b52e1316e5c13671f43b39ca36b28133cd0832831bcddd0b0f23398cb", "e6884a6e6b2e60a0b5862251c001e7c79d581d777d6fc11d218d0aecd79f26a30e2ca22cc7c4674f8b72655bc4ee5cb5494ca07c05177656142ac55cc9d33e02", "563357f41b8b23b1d83f19f5667177a67da20b18")
}

/// wycheproofs TC[149] regression test for arithmetic error
#[test]
fn wycheproof_tc_149() {
    super::ed25519_dalek_wycheproof("dd2d678bae222f3fb6e8278f08cc9e1a66339c926c29ac0a16f9717f5ee18cd8", "6124c206d864507ea5d984b363b4cf583314db6856a45ded5e61eebff4d5e337e0b4c82b445ae2e52d549d2d961eace2ea01f81158e09a9686baa040db65ad08", "931bbf9c877a6571cf7d4609fc3eb867edd43f51")
}

/// wycheproofs TC[150] regression test for arithmetic error
#[test]
fn wycheproof_tc_150() {
    super::ed25519_dalek_wycheproof("ccbe7cb2e4bc215cee2f885e1d22f7e0d582b2bbbd782c104e548b152d26fc69", "cfbd450a2c83cb8436c348822fe3ee347d4ee937b7f2ea11ed755cc52852407c9eec2c1fa30d2f9aef90e89b2cc3bcef2b1b9ca59f712110d19894a9cf6a2802", "44530b0b34f598767a7b875b0caee3c7b9c502d1")
}
