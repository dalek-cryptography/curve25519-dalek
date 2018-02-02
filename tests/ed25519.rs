// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2017 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Integration test for ed25519-dalek.

extern crate ed25519_dalek;
extern crate rand;
extern crate sha2;

#[test]
pub fn integration_ed25519() {
    use ed25519_dalek::Keypair;
    use ed25519_dalek::Signature;
    use rand::OsRng;
    use sha2::Sha512;

    let mut cspring: OsRng;
    let keypair: Keypair;
    let good_sig: Signature;
    let bad_sig:  Signature;

    let good: &[u8] = "test message".as_bytes();
    let bad:  &[u8] = "wrong message".as_bytes();

    cspring  = OsRng::new().unwrap();
    keypair  = Keypair::generate::<Sha512>(&mut cspring);
    good_sig = keypair.sign::<Sha512>(&good);
    bad_sig  = keypair.sign::<Sha512>(&bad);

    assert!(keypair.verify::<Sha512>(&good, &good_sig) == true,
            "Verification of a valid signature failed!");
    assert!(keypair.verify::<Sha512>(&good, &bad_sig)  == false,
            "Verification of a signature on a different message passed!");
    assert!(keypair.verify::<Sha512>(&bad,  &good_sig) == false,
            "Verification of a signature on a different message passed!");
}
