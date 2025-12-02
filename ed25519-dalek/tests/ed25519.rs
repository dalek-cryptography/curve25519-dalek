// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2017-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

//! Integration tests for ed25519-dalek.

#![allow(clippy::items_after_test_module)]

use ed25519_dalek::*;

use hex::FromHex;
#[cfg(feature = "digest")]
use hex_literal::hex;

#[cfg(test)]
mod vectors {
    use super::*;

    use curve25519_dalek::{
        constants::ED25519_BASEPOINT_POINT,
        edwards::{CompressedEdwardsY, EdwardsPoint},
        scalar::Scalar,
        traits::IsIdentity,
    };
    use rand::TryRngCore;

    #[cfg(not(feature = "digest"))]
    use sha2::{Sha512, digest::Digest};

    use std::{
        fs::File,
        io::{BufRead, BufReader},
        ops::Neg,
    };

    // TESTVECTORS is taken from sign.input.gz in agl's ed25519 Golang
    // package. It is a selection of test cases from
    // http://ed25519.cr.yp.to/python/sign.input
    #[test]
    fn against_reference_implementation() {
        // TestGolden
        let mut line: String;
        let mut lineno: usize = 0;

        let f = File::open("TESTVECTORS");
        if f.is_err() {
            println!(
                "This test is only available when the code has been cloned \
                 from the git repository, since the TESTVECTORS file is large \
                 and is therefore not included within the distributed crate."
            );
            panic!();
        }
        let file = BufReader::new(f.unwrap());

        for l in file.lines() {
            lineno += 1;
            line = l.unwrap();

            let parts: Vec<&str> = line.split(':').collect();
            assert_eq!(parts.len(), 5, "wrong number of fields in line {}", lineno);

            let sec_bytes: Vec<u8> = FromHex::from_hex(parts[0]).unwrap();
            let pub_bytes: Vec<u8> = FromHex::from_hex(parts[1]).unwrap();
            let msg_bytes: Vec<u8> = FromHex::from_hex(parts[2]).unwrap();
            let sig_bytes: Vec<u8> = FromHex::from_hex(parts[3]).unwrap();

            let sec_bytes = &sec_bytes[..SECRET_KEY_LENGTH].try_into().unwrap();
            let pub_bytes = &pub_bytes[..PUBLIC_KEY_LENGTH].try_into().unwrap();

            let signing_key = SigningKey::from_bytes(sec_bytes);
            let expected_verifying_key = VerifyingKey::from_bytes(pub_bytes).unwrap();
            assert_eq!(expected_verifying_key, signing_key.verifying_key());

            // The signatures in the test vectors also include the message
            // at the end, but we just want R and S.
            let sig1: Signature = Signature::try_from(&sig_bytes[..64]).unwrap();
            let sig2: Signature = signing_key.sign(&msg_bytes);

            assert!(sig1 == sig2, "Signature bytes not equal on line {}", lineno);
            assert!(
                signing_key.verify(&msg_bytes, &sig2).is_ok(),
                "Signature verification failed on line {}",
                lineno
            );
            assert!(
                expected_verifying_key
                    .verify_strict(&msg_bytes, &sig2)
                    .is_ok(),
                "Signature strict verification failed on line {}",
                lineno
            );
            assert!(
                expected_verifying_key
                    .verify_heea(&msg_bytes, &sig2)
                    .is_ok(),
                "Signature strict verification failed on line {}",
                lineno
            );
        }
    }

    // From https://tools.ietf.org/html/rfc8032#section-7.3
    #[cfg(feature = "digest")]
    #[test]
    fn ed25519ph_rf8032_test_vector_prehash() {
        let sec_bytes = hex!("833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42");
        let pub_bytes = hex!("ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf");
        let msg_bytes = hex!("616263");
        let sig_bytes = hex!(
            "98a70222f0b8121aa9d30f813d683f809e462b469c7ff87639499bb94e6dae4131f85042463c2a355a2003d062adf5aaa10b8c61e636062aaad11c2a26083406"
        );

        let signing_key = SigningKey::from_bytes(&sec_bytes);
        let expected_verifying_key = VerifyingKey::from_bytes(&pub_bytes).unwrap();
        assert_eq!(expected_verifying_key, signing_key.verifying_key());
        let sig1 = Signature::try_from(&sig_bytes[..]).unwrap();

        let mut prehash_for_signing = Sha512::default();
        let mut prehash_for_verifying = Sha512::default();

        prehash_for_signing.update(&msg_bytes[..]);
        prehash_for_verifying.update(&msg_bytes[..]);

        let sig2: Signature = signing_key
            .sign_prehashed(prehash_for_signing, None)
            .unwrap();

        assert!(
            sig1 == sig2,
            "Original signature from test vectors doesn't equal signature produced:\
             \noriginal:\n{:?}\nproduced:\n{:?}",
            sig1,
            sig2
        );
        assert!(
            signing_key
                .verify_prehashed(prehash_for_verifying.clone(), None, &sig2)
                .is_ok(),
            "Could not verify ed25519ph signature!"
        );
        assert!(
            expected_verifying_key
                .verify_prehashed_strict(prehash_for_verifying, None, &sig2)
                .is_ok(),
            "Could not strict-verify ed25519ph signature!"
        );
    }

    //
    // The remaining items in this mod are for the repudiation tests
    //

    // Taken from curve25519_dalek::constants::EIGHT_TORSION[4]
    const EIGHT_TORSION_4: [u8; 32] = [
        236, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127,
    ];

    // Computes the prehashed or non-prehashed challenge, depending on whether context is given
    fn compute_challenge(
        message: &[u8],
        pub_key: &EdwardsPoint,
        signature_r: &EdwardsPoint,
        context: Option<&[u8]>,
    ) -> Scalar {
        let mut h = Sha512::default();
        if let Some(c) = context {
            h.update(b"SigEd25519 no Ed25519 collisions");
            h.update([1]);
            h.update([c.len() as u8]);
            h.update(c);
        }
        h.update(signature_r.compress().as_bytes());
        h.update(&pub_key.compress().as_bytes()[..]);
        h.update(message);
        Scalar::from_hash(h)
    }

    fn serialize_signature(r: &EdwardsPoint, s: &Scalar) -> Vec<u8> {
        [&r.compress().as_bytes()[..], &s.as_bytes()[..]].concat()
    }

    const WEAK_PUBKEY: CompressedEdwardsY = CompressedEdwardsY(EIGHT_TORSION_4);

    // Pick a random Scalar
    fn non_null_scalar() -> Scalar {
        let mut rng = rand::rngs::OsRng.unwrap_err();
        let mut s_candidate = Scalar::random(&mut rng);
        while s_candidate == Scalar::ZERO {
            s_candidate = Scalar::random(&mut rng);
        }
        s_candidate
    }

    fn pick_r(s: Scalar) -> EdwardsPoint {
        let r0 = s * ED25519_BASEPOINT_POINT;
        // Pick a torsion point of order 2
        r0 + WEAK_PUBKEY.decompress().unwrap().neg()
    }

    // Tests that verify_strict() rejects small-order pubkeys. We test this by explicitly
    // constructing a pubkey-signature pair that verifies with respect to two distinct messages.
    // This should be accepted by verify(), but rejected by verify_strict().
    #[test]
    fn repudiation() {
        let message1 = b"Send 100 USD to Alice";
        let message2 = b"Send 100000 USD to Alice";

        let mut s: Scalar = non_null_scalar();
        let pubkey = WEAK_PUBKEY.decompress().unwrap();
        let mut r = pick_r(s);

        // Find an R such that
        //     H(R || A || M₁) · A == A == H(R || A || M₂) · A
        // This happens with high probability when A is low order.
        while !(pubkey.neg() + compute_challenge(message1, &pubkey, &r, None) * pubkey)
            .is_identity()
            || !(pubkey.neg() + compute_challenge(message2, &pubkey, &r, None) * pubkey)
                .is_identity()
        {
            // We pick an s and let R = sB - A where B is the basepoint
            s = non_null_scalar();
            r = pick_r(s);
        }

        // At this point, both verification equations hold:
        //     sB = R + H(R || A || M₁) · A
        //        = R + H(R || A || M₂) · A
        // Check that this is true
        let signature = serialize_signature(&r, &s);
        let vk = VerifyingKey::from_bytes(pubkey.compress().as_bytes()).unwrap();
        let sig = Signature::try_from(&signature[..]).unwrap();
        assert!(vk.verify(message1, &sig).is_ok());
        assert!(vk.verify(message2, &sig).is_ok());

        // Check that this public key appears as weak
        assert!(vk.is_weak());

        // Now check that the sigs fail under verify_strict. This is because verify_strict rejects
        // small order pubkeys.
        assert!(vk.verify_strict(message1, &sig).is_err());
        assert!(vk.verify_strict(message2, &sig).is_err());
        assert!(vk.verify_heea(message1, &sig).is_err());
        assert!(vk.verify_heea(message2, &sig).is_err());
    }

    // Identical to repudiation() above, but testing verify_prehashed against
    // verify_prehashed_strict. See comments above for a description of what's happening.
    #[cfg(feature = "digest")]
    #[test]
    fn repudiation_prehash() {
        let message1 = Sha512::new().chain_update(b"Send 100 USD to Alice");
        let message2 = Sha512::new().chain_update(b"Send 100000 USD to Alice");
        let message1_bytes = message1.clone().finalize();
        let message2_bytes = message2.clone().finalize();

        let mut s: Scalar = non_null_scalar();
        let pubkey = WEAK_PUBKEY.decompress().unwrap();
        let mut r = pick_r(s);
        let context_str = Some(&b"edtest"[..]);

        while !(pubkey.neg()
            + compute_challenge(&message1_bytes, &pubkey, &r, context_str) * pubkey)
            .is_identity()
            || !(pubkey.neg()
                + compute_challenge(&message2_bytes, &pubkey, &r, context_str) * pubkey)
                .is_identity()
        {
            s = non_null_scalar();
            r = pick_r(s);
        }

        // Check that verify_prehashed succeeds on both sigs
        let signature = serialize_signature(&r, &s);
        let vk = VerifyingKey::from_bytes(pubkey.compress().as_bytes()).unwrap();
        let sig = Signature::try_from(&signature[..]).unwrap();
        assert!(
            vk.verify_prehashed(message1.clone(), context_str, &sig)
                .is_ok()
        );
        assert!(
            vk.verify_prehashed(message2.clone(), context_str, &sig)
                .is_ok()
        );

        // Check that verify_prehashed_strict fails on both sigs
        assert!(
            vk.verify_prehashed_strict(message1.clone(), context_str, &sig)
                .is_err()
        );
        assert!(
            vk.verify_prehashed_strict(message2.clone(), context_str, &sig)
                .is_err()
        );
    }
}

#[cfg(feature = "rand_core")]
mod integrations {
    use super::*;
    use rand::{TryRngCore, rngs::OsRng};
    use std::collections::HashMap;

    #[test]
    fn sign_verify() {
        // TestSignVerify

        let good: &[u8] = "test message".as_bytes();
        let bad: &[u8] = "wrong message".as_bytes();

        let mut csprng = OsRng.unwrap_err();

        let signing_key: SigningKey = SigningKey::generate(&mut csprng);
        let verifying_key = signing_key.verifying_key();
        let good_sig: Signature = signing_key.sign(good);
        let bad_sig: Signature = signing_key.sign(bad);

        // Check that an honestly generated public key is not weak
        assert!(!verifying_key.is_weak());

        assert!(
            signing_key.verify(good, &good_sig).is_ok(),
            "Verification of a valid signature failed!"
        );
        assert!(
            verifying_key.verify_strict(good, &good_sig).is_ok(),
            "Strict verification of a valid signature failed!"
        );
        assert!(
            verifying_key.verify_heea(good, &good_sig).is_ok(),
            "HEEA verification of a valid signature failed!"
        );
        assert!(
            signing_key.verify(good, &bad_sig).is_err(),
            "Verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key.verify_strict(good, &bad_sig).is_err(),
            "Strict verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key.verify_heea(good, &bad_sig).is_err(),
            "HEEA verification of a signature on a different message passed!"
        );
        assert!(
            signing_key.verify(bad, &good_sig).is_err(),
            "Verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key.verify_strict(bad, &good_sig).is_err(),
            "Strict verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key.verify_heea(bad, &good_sig).is_err(),
            "HEEA verification of a signature on a different message passed!"
        );
    }

    #[cfg(feature = "digest")]
    #[test]
    fn sign_verify_digest_equivalence() {
        // TestSignVerify

        let mut csprng = OsRng.unwrap_err();

        let good: &[u8] = "test message".as_bytes();
        let bad: &[u8] = "wrong message".as_bytes();

        let keypair: SigningKey = SigningKey::generate(&mut csprng);
        let good_sig: Signature = keypair.sign(good);
        let bad_sig: Signature = keypair.sign(bad);

        let mut verifier = keypair.verify_stream(&good_sig).unwrap();
        verifier.update(good);
        assert!(
            verifier.finalize_and_verify().is_ok(),
            "Verification of a valid signature failed!"
        );

        let mut verifier = keypair.verify_stream(&bad_sig).unwrap();
        verifier.update(good);
        assert!(
            verifier.finalize_and_verify().is_err(),
            "Verification of a signature on a different message passed!"
        );

        let mut verifier = keypair.verify_stream(&good_sig).unwrap();
        verifier.update("test ");
        verifier.update("message");
        assert!(
            verifier.finalize_and_verify().is_ok(),
            "Verification of a valid signature failed!"
        );

        let mut verifier = keypair.verify_stream(&good_sig).unwrap();
        verifier.update(bad);
        assert!(
            verifier.finalize_and_verify().is_err(),
            "Verification of a signature on a different message passed!"
        );
    }

    #[cfg(feature = "digest")]
    #[test]
    fn ed25519ph_sign_verify() {
        let good: &[u8] = b"test message";
        let bad: &[u8] = b"wrong message";

        let mut csprng = OsRng.unwrap_err();

        // ugh… there's no `impl Copy for Sha512`… i hope we can all agree these are the same hashes
        let mut prehashed_good1: Sha512 = Sha512::default();
        prehashed_good1.update(good);
        let mut prehashed_good2: Sha512 = Sha512::default();
        prehashed_good2.update(good);
        let mut prehashed_good3: Sha512 = Sha512::default();
        prehashed_good3.update(good);

        let mut prehashed_bad1: Sha512 = Sha512::default();
        prehashed_bad1.update(bad);
        let mut prehashed_bad2: Sha512 = Sha512::default();
        prehashed_bad2.update(bad);

        let context: &[u8] = b"testing testing 1 2 3";

        let signing_key: SigningKey = SigningKey::generate(&mut csprng);
        let verifying_key = signing_key.verifying_key();
        let good_sig: Signature = signing_key
            .sign_prehashed(prehashed_good1, Some(context))
            .unwrap();
        let bad_sig: Signature = signing_key
            .sign_prehashed(prehashed_bad1, Some(context))
            .unwrap();

        assert!(
            signing_key
                .verify_prehashed(prehashed_good2.clone(), Some(context), &good_sig)
                .is_ok(),
            "Verification of a valid signature failed!"
        );
        assert!(
            verifying_key
                .verify_prehashed_strict(prehashed_good2, Some(context), &good_sig)
                .is_ok(),
            "Strict verification of a valid signature failed!"
        );
        assert!(
            signing_key
                .verify_prehashed(prehashed_good3.clone(), Some(context), &bad_sig)
                .is_err(),
            "Verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key
                .verify_prehashed_strict(prehashed_good3, Some(context), &bad_sig)
                .is_err(),
            "Strict verification of a signature on a different message passed!"
        );
        assert!(
            signing_key
                .verify_prehashed(prehashed_bad2.clone(), Some(context), &good_sig)
                .is_err(),
            "Verification of a signature on a different message passed!"
        );
        assert!(
            verifying_key
                .verify_prehashed_strict(prehashed_bad2, Some(context), &good_sig)
                .is_err(),
            "Strict verification of a signature on a different message passed!"
        );
    }

    #[cfg(feature = "batch")]
    #[test]
    fn verify_batch_seven_signatures() {
        let messages: [&[u8]; 7] = [
            b"Watch closely everyone, I'm going to show you how to kill a god.",
            b"I'm not a cryptographer I just encrypt a lot.",
            b"Still not a cryptographer.",
            b"This is a test of the tsunami alert system. This is only a test.",
            b"Fuck dumbin' it down, spit ice, skip jewellery: Molotov cocktails on me like accessories.",
            b"Hey, I never cared about your bucks, so if I run up with a mask on, probably got a gas can too.",
            b"And I'm not here to fill 'er up. Nope, we came to riot, here to incite, we don't want any of your stuff.", ];
        let mut csprng = OsRng.unwrap_err();
        let mut signing_keys: Vec<SigningKey> = Vec::new();
        let mut signatures: Vec<Signature> = Vec::new();

        for msg in messages {
            let signing_key: SigningKey = SigningKey::generate(&mut csprng);
            signatures.push(signing_key.sign(msg));
            signing_keys.push(signing_key);
        }
        let verifying_keys: Vec<VerifyingKey> =
            signing_keys.iter().map(|key| key.verifying_key()).collect();

        let result = verify_batch(&messages, &signatures, &verifying_keys);

        assert!(result.is_ok());
    }

    #[test]
    fn public_key_hash_trait_check() {
        let mut csprng = OsRng.unwrap_err();
        let secret: SigningKey = SigningKey::generate(&mut csprng);
        let public_from_secret: VerifyingKey = (&secret).into();

        let mut m = HashMap::new();
        m.insert(public_from_secret, "Example_Public_Key");

        m.insert(public_from_secret, "Updated Value");

        let (k, &v) = m.get_key_value(&public_from_secret).unwrap();
        assert_eq!(k, &public_from_secret);
        assert_eq!(v, "Updated Value");
        assert_eq!(m.len(), 1usize);

        let second_secret: SigningKey = SigningKey::generate(&mut csprng);
        let public_from_second_secret: VerifyingKey = (&second_secret).into();
        assert_ne!(public_from_secret, public_from_second_secret);
        m.insert(public_from_second_secret, "Second public key");

        let (k, &v) = m.get_key_value(&public_from_second_secret).unwrap();
        assert_eq!(k, &public_from_second_secret);
        assert_eq!(v, "Second public key");
        assert_eq!(m.len(), 2usize);
    }

    #[test]
    fn montgomery_and_edwards_conversion() {
        let mut rng = rand::rngs::OsRng.unwrap_err();
        let signing_key = SigningKey::generate(&mut rng);
        let verifying_key = signing_key.verifying_key();

        let ed = verifying_key.to_edwards();

        // Check that to_edwards and From return same result:
        assert_eq!(ed, curve25519_dalek::EdwardsPoint::from(verifying_key));

        // The verifying key serialization is simply the compressed Edwards point
        assert_eq!(verifying_key.to_bytes(), ed.compress().0);

        // Check that modulo sign, to_montgomery().to_edwards() returns the original point
        let monty = verifying_key.to_montgomery();
        let via_monty0 = monty.to_edwards(0).unwrap();
        let via_monty1 = monty.to_edwards(1).unwrap();

        assert!(via_monty0 != via_monty1);
        assert!(ed == via_monty0 || ed == via_monty1);
    }
}

#[cfg(all(test, feature = "serde"))]
#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(crate = "serde")]
struct Demo {
    signing_key: SigningKey,
}

#[cfg(all(test, feature = "serde"))]
mod serialisation {
    #![allow(clippy::zero_prefixed_literal)]

    use super::*;

    // The size for bincode to serialize the length of a byte array.
    static BINCODE_INT_LENGTH: usize = 8;

    static PUBLIC_KEY_BYTES: [u8; PUBLIC_KEY_LENGTH] = [
        130, 039, 155, 015, 062, 076, 188, 063, 124, 122, 026, 251, 233, 253, 225, 220, 014, 041,
        166, 120, 108, 035, 254, 077, 160, 083, 172, 058, 219, 042, 086, 120,
    ];

    static SECRET_KEY_BYTES: [u8; SECRET_KEY_LENGTH] = [
        062, 070, 027, 163, 092, 182, 011, 003, 077, 234, 098, 004, 011, 127, 079, 228, 243, 187,
        150, 073, 201, 137, 076, 022, 085, 251, 152, 002, 241, 042, 072, 054,
    ];

    /// Signature with the above signing_key of a blank message.
    static SIGNATURE_BYTES: [u8; SIGNATURE_LENGTH] = [
        010, 126, 151, 143, 157, 064, 047, 001, 196, 140, 179, 058, 226, 152, 018, 102, 160, 123,
        080, 016, 210, 086, 196, 028, 053, 231, 012, 157, 169, 019, 158, 063, 045, 154, 238, 007,
        053, 185, 227, 229, 079, 108, 213, 080, 124, 252, 084, 167, 216, 085, 134, 144, 129, 149,
        041, 081, 063, 120, 126, 100, 092, 059, 050, 011,
    ];

    #[test]
    fn serialize_deserialize_signature_bincode() {
        let signature: Signature = Signature::from_bytes(&SIGNATURE_BYTES);
        let encoded_signature: Vec<u8> = bincode::serialize(&signature).unwrap();
        let decoded_signature: Signature = bincode::deserialize(&encoded_signature).unwrap();

        assert_eq!(signature, decoded_signature);
    }

    #[test]
    fn serialize_deserialize_signature_json() {
        let signature: Signature = Signature::from_bytes(&SIGNATURE_BYTES);
        let encoded_signature = serde_json::to_string(&signature).unwrap();
        let decoded_signature: Signature = serde_json::from_str(&encoded_signature).unwrap();

        assert_eq!(signature, decoded_signature);
    }

    #[test]
    fn serialize_deserialize_verifying_key_bincode() {
        let verifying_key: VerifyingKey = VerifyingKey::from_bytes(&PUBLIC_KEY_BYTES).unwrap();
        let encoded_verifying_key: Vec<u8> = bincode::serialize(&verifying_key).unwrap();
        let decoded_verifying_key: VerifyingKey =
            bincode::deserialize(&encoded_verifying_key).unwrap();

        assert_eq!(
            &PUBLIC_KEY_BYTES[..],
            &encoded_verifying_key[encoded_verifying_key.len() - PUBLIC_KEY_LENGTH..]
        );
        assert_eq!(verifying_key, decoded_verifying_key);
    }

    #[test]
    fn serialize_deserialize_verifying_key_json() {
        let verifying_key: VerifyingKey = VerifyingKey::from_bytes(&PUBLIC_KEY_BYTES).unwrap();
        let encoded_verifying_key = serde_json::to_string(&verifying_key).unwrap();
        let decoded_verifying_key: VerifyingKey =
            serde_json::from_str(&encoded_verifying_key).unwrap();

        assert_eq!(verifying_key, decoded_verifying_key);
    }

    #[test]
    fn serialize_deserialize_verifying_key_json_too_long() {
        // derived from `serialize_deserialize_verifying_key_json` test
        // trailing zero elements makes key too long (34 bytes)
        let encoded_verifying_key_too_long = "[130,39,155,15,62,76,188,63,124,122,26,251,233,253,225,220,14,41,166,120,108,35,254,77,160,83,172,58,219,42,86,120,0,0]";
        let de_err = serde_json::from_str::<VerifyingKey>(encoded_verifying_key_too_long)
            .unwrap_err()
            .to_string();
        assert!(
            de_err.contains("invalid length 34"),
            "expected invalid length error, got: {de_err}",
        );
    }

    #[test]
    fn serialize_deserialize_verifying_key_json_too_short() {
        // derived from `serialize_deserialize_verifying_key_json` test
        let encoded_verifying_key_too_long = "[130,39,155,15]";
        let de_err = serde_json::from_str::<VerifyingKey>(encoded_verifying_key_too_long)
            .unwrap_err()
            .to_string();
        assert!(
            de_err.contains("invalid length 4"),
            "expected invalid length error, got: {de_err}"
        );
    }

    #[test]
    fn serialize_deserialize_signing_key_bincode() {
        let signing_key = SigningKey::from_bytes(&SECRET_KEY_BYTES);
        let encoded_signing_key: Vec<u8> = bincode::serialize(&signing_key).unwrap();
        let decoded_signing_key: SigningKey = bincode::deserialize(&encoded_signing_key).unwrap();

        #[allow(clippy::needless_range_loop)]
        for i in 0..SECRET_KEY_LENGTH {
            assert_eq!(SECRET_KEY_BYTES[i], decoded_signing_key.to_bytes()[i]);
        }
    }

    #[test]
    fn serialize_deserialize_signing_key_json() {
        let signing_key = SigningKey::from_bytes(&SECRET_KEY_BYTES);
        let encoded_signing_key = serde_json::to_string(&signing_key).unwrap();
        let decoded_signing_key: SigningKey = serde_json::from_str(&encoded_signing_key).unwrap();

        #[allow(clippy::needless_range_loop)]
        for i in 0..SECRET_KEY_LENGTH {
            assert_eq!(SECRET_KEY_BYTES[i], decoded_signing_key.to_bytes()[i]);
        }
    }

    #[test]
    fn serialize_deserialize_signing_key_json_too_long() {
        // derived from `serialize_deserialize_signing_key_json` test
        // trailing zero elements makes key too long (34 bytes)
        let encoded_signing_key_too_long = "[62,70,27,163,92,182,11,3,77,234,98,4,11,127,79,228,243,187,150,73,201,137,76,22,85,251,152,2,241,42,72,54,0,0]";
        let de_err = serde_json::from_str::<SigningKey>(encoded_signing_key_too_long)
            .unwrap_err()
            .to_string();
        assert!(
            de_err.contains("invalid length 34"),
            "expected invalid length error, got: {de_err}",
        );
    }

    #[test]
    fn serialize_deserialize_signing_key_json_too_short() {
        // derived from `serialize_deserialize_signing_key_json` test
        let encoded_signing_key_too_long = "[62,70,27,163]";
        let de_err = serde_json::from_str::<SigningKey>(encoded_signing_key_too_long)
            .unwrap_err()
            .to_string();
        assert!(
            de_err.contains("invalid length 4"),
            "expected invalid length error, got: {de_err}"
        );
    }

    #[test]
    fn serialize_deserialize_signing_key_toml() {
        let demo = Demo {
            signing_key: SigningKey::from_bytes(&SECRET_KEY_BYTES),
        };

        println!("\n\nWrite to toml");
        let demo_toml = toml::to_string(&demo).unwrap();
        println!("{}", demo_toml);
        let demo_toml_rebuild: Result<Demo, _> = toml::from_str(&demo_toml);
        println!("{:?}", demo_toml_rebuild);
    }

    #[test]
    fn serialize_verifying_key_size() {
        let verifying_key: VerifyingKey = VerifyingKey::from_bytes(&PUBLIC_KEY_BYTES).unwrap();
        assert_eq!(
            bincode::serialized_size(&verifying_key).unwrap() as usize,
            BINCODE_INT_LENGTH + PUBLIC_KEY_LENGTH
        );
    }

    #[test]
    fn serialize_signature_size() {
        let signature: Signature = Signature::from_bytes(&SIGNATURE_BYTES);
        assert_eq!(
            bincode::serialized_size(&signature).unwrap() as usize,
            SIGNATURE_LENGTH
        );
    }

    #[test]
    fn serialize_signing_key_size() {
        let signing_key = SigningKey::from_bytes(&SECRET_KEY_BYTES);
        assert_eq!(
            bincode::serialized_size(&signing_key).unwrap() as usize,
            BINCODE_INT_LENGTH + SECRET_KEY_LENGTH
        );
    }

    // Test verify_heea against standard verification
    // verify_heea should accept the same signatures as verify_strict
    #[test]
    fn verify_heea_basic() {
        let sec_bytes =
            hex::decode("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
                .unwrap();
        let pub_bytes =
            hex::decode("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
                .unwrap();
        let msg_bytes = b"";
        let sig_bytes = hex::decode("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b").unwrap();

        let sec_bytes: &[u8; 32] = sec_bytes.as_slice().try_into().unwrap();
        let pub_bytes: &[u8; 32] = pub_bytes.as_slice().try_into().unwrap();

        let signing_key = SigningKey::from_bytes(sec_bytes);
        let verifying_key = VerifyingKey::from_bytes(pub_bytes).unwrap();
        assert_eq!(verifying_key, signing_key.verifying_key());

        let sig = Signature::try_from(&sig_bytes[..]).unwrap();

        // Test that verify_heea accepts the same signatures as verify_strict
        assert!(
            verifying_key.verify_heea(msg_bytes, &sig).is_ok(),
            "verify_heea failed for valid signature"
        );
        assert!(
            verifying_key.verify_strict(msg_bytes, &sig).is_ok(),
            "verify_strict failed for valid signature"
        );
    }

    // Test verify_heea with multiple test vectors
    #[test]
    fn verify_heea_test_vectors() {
        let test_cases = vec![
            (
                "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
                "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
                "af82",
                "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a",
            ),
            (
                "f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5",
                "278117fc144c72340f67d0f2316e8386ceffbf2b2428c9c51fef7c597f1d426e",
                "08b8b2b733424243760fe426a4b54908632110a66c2f6591eabd3345e3e4eb98fa6e264bf09efe12ee50f8f54e9f77b1e355f6c50544e23fb1433ddf73be84d879de7c0046dc4996d9e773f4bc9efe5738829adb26c81b37c93a1b270b20329d658675fc6ea534e0810a4432826bf58c941efb65d57a338bbd2e26640f89ffbc1a858efcb8550ee3a5e1998bd177e93a7363c344fe6b199ee5d02e82d522c4feba15452f80288a821a579116ec6dad2b3b310da903401aa62100ab5d1a36553e06203b33890cc9b832f79ef80560ccb9a39ce767967ed628c6ad573cb116dbefefd75499da96bd68a8a97b928a8bbc103b6621fcde2beca1231d206be6cd9ec7aff6f6c94fcd7204ed3455c68c83f4a41da4af2b74ef5c53f1d8ac70bdcb7ed185ce81bd84359d44254d95629e9855a94a7c1958d1f8ada5d0532ed8a5aa3fb2d17ba70eb6248e594e1a2297acbbb39d502f1a8c6eb6f1ce22b3de1a1f40cc24554119a831a9aad6079cad88425de6bde1a9187ebb6092cf67bf2b13fd65f27088d78b7e883c8759d2c4f5c65adb7553878ad575f9fad878e80a0c9ba63bcbcc2732e69485bbc9c90bfbd62481d9089beccf80cfe2df16a2cf65bd92dd597b0707e0917af48bbb75fed413d238f5555a7a569d80c3414a8d0859dc65a46128bab27af87a71314f318c782b23ebfe808b82b0ce26401d2e22f04d83d1255dc51addd3b75a2b1ae0784504df543af8969be3ea7082ff7fc9888c144da2af58429ec96031dbcad3dad9af0dcbaaaf268cb8fcffead94f3c7ca495e056a9b47acdb751fb73e666c6c655ade8297297d07ad1ba5e43f1bca32301651339e22904cc8c42f58c30c04aafdb038dda0847dd988dcda6f3bfd15c4b4c4525004aa06eeff8ca61783aacec57fb3d1f92b0fe2fd1a85f6724517b65e614ad6808d6f6ee34dff7310fdc82aebfd904b01e1dc54b2927094b2db68d6f903b68401adebf5a7e08d78ff4ef5d63653a65040cf9bfd4aca7984a74d37145986780fc0b16ac451649de6188a7dbdf191f64b5fc5e2ab47b57f7f7276cd419c17a3ca8e1b939ae49e488acba6b965610b5480109c8b17b80e1b7b750dfc7598d5d5011fd2dcc5600a32ef5b52a1ecc820e308aa342721aac0943bf6686b64b2579376504ccc493d97e6aed3fb0f9cd71a43dd497f01f17c0e2cb3797aa2a2f256656168e6c496afc5fb93246f6b1116398a346f1a641f3b041e989f7914f90cc2c7fff357876e506b50d334ba77c225bc307ba537152f3f1610e4eafe595f6d9d90d11faa933a15ef1369546868a7f3a45a96768d40fd9d03412c091c6315cf4fde7cb68606937380db2eaaa707b4c4185c32eddcdd306705e4dc1ffc872eeee475a64dfac86aba41c0618983f8741c5ef68d3a101e8a3b8cac60c905c15fc910840b94c00a0b9d0",
                "0aab4c900501b3e24d7cdf4663326a3a87df5e4843b2cbdb67cbf6e460fec350aa5371b1508f9f4528ecea23c436d94b5e8fcd4f681e30a6ac00a9704a188a03",
            ),
        ];

        for (_secret, public, message, signature) in test_cases {
            let pub_bytes = hex::decode(public).unwrap();
            let msg_bytes = hex::decode(message).unwrap();
            let sig_bytes = hex::decode(signature).unwrap();

            let pub_bytes: &[u8; 32] = pub_bytes.as_slice().try_into().unwrap();
            let verifying_key = VerifyingKey::from_bytes(pub_bytes).unwrap();
            let sig = Signature::try_from(&sig_bytes[..]).unwrap();

            // Test that verify_heea accepts valid signatures
            assert!(
                verifying_key.verify_heea(&msg_bytes, &sig).is_ok(),
                "verify_heea failed for test vector with public key: {}",
                public
            );

            // Also verify with standard verification
            assert!(
                verifying_key.verify_strict(&msg_bytes, &sig).is_ok(),
                "verify_strict failed for test vector with public key: {}",
                public
            );
        }
    }

    // Test that verify_heea rejects invalid signatures
    #[test]
    fn verify_heea_rejects_invalid() {
        let pub_bytes =
            hex::decode("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
                .unwrap();
        let msg_bytes = b"test message";
        let sig_bytes = hex::decode("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b").unwrap();

        let pub_bytes: &[u8; 32] = pub_bytes.as_slice().try_into().unwrap();
        let verifying_key = VerifyingKey::from_bytes(pub_bytes).unwrap();
        let sig = Signature::try_from(&sig_bytes[..]).unwrap();

        // This signature is valid for an empty message, but we're verifying with a different message
        assert!(
            verifying_key.verify_heea(msg_bytes, &sig).is_err(),
            "verify_heea should reject invalid signature"
        );
    }
}
