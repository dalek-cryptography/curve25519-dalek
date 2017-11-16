#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate curve25519_dalek;

use curve25519_dalek::curve::ValidityCheck;
use curve25519_dalek::decaf::DecafPoint;
use curve25519_dalek::field::FieldElement;

fuzz_target!(|data: &[u8]| {
    if data.len() != 32 {
        return;
    }
    let mut field_bytes = [0u8; 32];
    for (by, data) in field_bytes.iter_mut().zip(data.iter()) {
        *by = *data;
    }
    let fe = FieldElement::from_bytes(&field_bytes);
    let p = DecafPoint::elligator_decaf_flavour(&fe);
    assert!(p.0.is_valid());
    p.compress();
});
