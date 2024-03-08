#[cfg(test)]
use ed25519_dalek::{Signature, Verifier, VerifyingKey};

// hex strings (due to generated source files being ascii
#[cfg(test)]
fn ed25519_dalek_wycheproof(public_key: &str, sig: &str, msg: &str) {
    let pk_bytes = hex::decode(public_key).unwrap();
    let sig_bytes = hex::decode(sig).unwrap();

    // panic if size wrong
    let pk: &[u8; 32] = pk_bytes
        .as_slice()
        .try_into()
        .expect("input pk incorrect length");

    // panic if size wrong
    let sig: &[u8; 64] = sig_bytes
        .as_slice()
        .try_into()
        .expect("input sig incorrect length");

    let typed_sig = Signature::from_bytes(sig);
    let verifying_key = VerifyingKey::from_bytes(pk).unwrap();

    assert!(verifying_key
        .verify(hex::decode(msg).unwrap().as_slice(), &typed_sig)
        .is_ok())
}

#[cfg(test)]
mod generated;
