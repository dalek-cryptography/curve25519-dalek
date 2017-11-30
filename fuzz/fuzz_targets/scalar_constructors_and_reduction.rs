#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate curve25519_dalek;

use curve25519_dalek::scalar::Scalar;

/// Check that the Scalar constructor accepts 255-bit input values and
/// behaves correctly on them.
///
/// Specifically, we take 255-bit values `a` and `b` from the fuzzer
/// input data and check that `(a mod l) * (b mod l) == (a * b) mod l`.
fuzz_target!(|data: &[u8]| {
    if data.len() != 64 {
        return;
    }
    let mut a_bytes = [0u8; 32];
    let mut b_bytes = [0u8; 32];

    // Set a, b to be random 256-bit integers
    a_bytes.copy_from_slice(&data[ 0..32]);
    b_bytes.copy_from_slice(&data[32..64]);

    // Compute c = a*b (mod l)
    let c1 = (&Scalar::from_bits(a_bytes) * &Scalar::from_bits(b_bytes)).reduce();

    // Compute c = (a mod l) * (b mod l)
    let a_mod_l = Scalar::from_bytes_mod_order(a_bytes);
    let b_mod_l = Scalar::from_bytes_mod_order(b_bytes);
    let c2 = &a_mod_l * &b_mod_l;

    assert_eq!(c1, c2);
});
