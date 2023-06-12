//! Tests for converting Ed25519 keys into X25519 (Montgomery form) keys.

use ed25519_dalek::SigningKey;
use hex_literal::hex;

/// Tests that X25519 Diffie-Hellman works when using keys converted from Ed25519.
// TODO: generate test vectors using another implementation of Ed25519->X25519
#[test]
fn ed25519_to_x25519_dh() {
    // Keys from RFC8032 test vectors (from section 7.1)
    let ed25519_secret_key_a =
        hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
    let ed25519_secret_key_b =
        hex!("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb");

    let ed25519_signing_key_a = SigningKey::from_bytes(&ed25519_secret_key_a);
    let ed25519_signing_key_b = SigningKey::from_bytes(&ed25519_secret_key_b);

    let scalar_a_bytes = ed25519_signing_key_a.to_scalar_bytes();
    let scalar_b_bytes = ed25519_signing_key_b.to_scalar_bytes();

    assert_eq!(
        scalar_a_bytes,
        hex!("357c83864f2833cb427a2ef1c00a013cfdff2768d980c0a3a520f006904de90f")
    );
    assert_eq!(
        scalar_b_bytes,
        hex!("6ebd9ed75882d52815a97585caf4790a7f6c6b3b7f821c5e259a24b02e502e11")
    );

    let x25519_public_key_a = ed25519_signing_key_a.verifying_key().to_montgomery();
    let x25519_public_key_b = ed25519_signing_key_b.verifying_key().to_montgomery();

    assert_eq!(
        x25519_public_key_a.to_bytes(),
        hex!("d85e07ec22b0ad881537c2f44d662d1a143cf830c57aca4305d85c7a90f6b62e")
    );
    assert_eq!(
        x25519_public_key_b.to_bytes(),
        hex!("25c704c594b88afc00a76b69d1ed2b984d7e22550f3ed0802d04fbcd07d38d47")
    );

    let expected_shared_secret =
        hex!("5166f24a6918368e2af831a4affadd97af0ac326bdf143596c045967cc00230e");

    assert_eq!(
        x25519_public_key_a.mul_clamped(scalar_b_bytes).to_bytes(),
        expected_shared_secret
    );
    assert_eq!(
        x25519_public_key_b.mul_clamped(scalar_a_bytes).to_bytes(),
        expected_shared_secret
    );
}
