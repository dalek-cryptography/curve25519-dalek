//! Implementation of the paper "Accelerating EdDSA Signature Verification
//! with Faster Scalar Size Halving" (TCHES 2025).
//!
//! This module implements Algorithm 4 (hEEA_approx_q) from the paper, which generates
//! half-size scalars for faster EdDSA verification.
//!
//! For verification sB = R + hA, we find rho, tau such that rho = tau*h (mod ell)
use ethnum::I256;

use crate::constants;

pub(crate) const HEEA_MAX_INDEX: usize = 129;

/// Implement curve25519_hEEA_vartime algorithm
/// Returns (rho, tau) such that rho ≡ tau * v (mod L)
/// where L is the Ed25519 group order (2^252 + 27742317777372353535851937790883648493)
pub(crate) fn curve25519_heea_vartime(v: I256) -> (I256, i128) {
    // Get L from the existing BASEPOINT_ORDER constant
    let mut r0: I256 = (&constants::BASEPOINT_ORDER).into();
    let mut r1 = v;

    debug_assert!(r1 < r0, "Input v must be less than the group order L");

    let mut t0: i128 = 0;
    let mut t1: i128 = 1;

    let mut bl_r0 = 253u32; // bit_length(L) = 253
    let mut bl_r1 = bit_length_i256(r1);

    // Main loop - continue until r1 is approximately half-size (~127 bits)
    while bl_r1 > 127 {
        // Compute shift amount
        // the initial s is less than 253 - 128 = 125
        // for consecutive iterations we are decreasing the gap between bl_r0 and bl_r1
        // so s will be in the range [0, 125]
        let s = bl_r0 - bl_r1;

        // Handle shift carefully - if s >= 128, result would overflow
        debug_assert!(s < 128, "s should be less than 128, got {}", s);

        // Check if signs are the same
        let sign_r0 = r0 < I256::ZERO;
        let sign_r1 = r1 < I256::ZERO;

        let (r, t) = if sign_r0 == sign_r1 {
            (r0.wrapping_sub(r1 << s), t0.wrapping_sub(t1 << s))
        } else {
            (r0.wrapping_add(r1 << s), t0.wrapping_add(t1 << s))
        };

        let bl_r = bit_length_i256(r);

        if bl_r > bl_r1 {
            // r grew, so keep it in r0
            r0 = r;
            t0 = t;
            bl_r0 = bl_r;
        } else {
            // r shrunk, swap
            r0 = r1;
            r1 = r;
            t0 = t1;
            t1 = t;
            bl_r0 = bl_r1;
            bl_r1 = bl_r;
        }
    }

    (r1, t1)
}

/// Compute bit length of I256 (magnitude, not including sign)
#[inline]
fn bit_length_i256(val: I256) -> u32 {
    let abs = val.unsigned_abs();
    256 - abs.leading_zeros()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Scalar, digest::Update, traits::HEEADecomposition};

    #[cfg(feature = "rand_core")]
    use rand::RngCore;

    #[test]
    #[cfg(feature = "rand_core")]
    fn test_generate_half_size_scalars() {
        use rand::rng;
        use sha2::{Digest, Sha512};

        let mut rng = rng();

        // Test with multiple random scalars
        for _ in 0..1000 {
            // Generate a random scalar by hashing random bytes
            let mut random_bytes = [0u8; 64];
            for byte in &mut random_bytes {
                *byte = (rng.next_u32() & 0xff) as u8;
            }
            let h = Scalar::from_hash(Sha512::new().chain(random_bytes));

            // Convert h to I256 to see the actual output
            let h_i256 = (&h).into();
            let (rho_i256, tau_i128) = curve25519_heea_vartime(h_i256);

            // Check the magnitude of rho and tau in their signed representation
            let rho_magnitude_bits = bit_length_i256(rho_i256);

            // For tau (i128), compute bit length
            let tau_magnitude_bits = if tau_i128 < 0 {
                let abs_val = tau_i128.wrapping_neg();
                128 - abs_val.leading_zeros()
            } else {
                128 - tau_i128.leading_zeros()
            };

            // Now convert to Scalars and verify the equation
            let (rho, tau, flip) = h.heea_decompose();

            // Verify that rho = tau * h (mod ell)
            let computed_rho = tau * h;
            let computed_rho = if flip { -computed_rho } else { computed_rho };
            assert_eq!(rho, computed_rho, "rho should equal tau * h");

            // Check that they are non-zero
            assert_ne!(rho, Scalar::ZERO, "rho should be non-zero");
            assert_ne!(tau, Scalar::ZERO, "tau should be non-zero");

            // Both magnitudes should be approximately half-size (~127 bits)
            assert!(
                rho_magnitude_bits <= 127,
                "rho magnitude should be approximately half-size, got {} bits",
                rho_magnitude_bits
            );
            assert!(
                tau_magnitude_bits <= 128,
                "tau magnitude should be approximately half-size, got {} bits",
                tau_magnitude_bits
            );
        }
    }

    #[test]
    fn test_heea_edge_cases() {
        // Test Zero: v = 0
        let v_zero = I256::ZERO;
        let (rho, tau) = curve25519_heea_vartime(v_zero);
        // When v = 0, the algorithm should return (0, 1) since we start with r1=0, t1=1
        // and the loop never executes (bl_r1 would be small)
        assert_eq!(rho, I256::ZERO, "rho should be zero when v is zero");
        assert_eq!(tau, 1, "tau should be 1 when v is zero");

        // Test One: v = 1
        let v_one = I256::ONE;
        let (rho, tau) = curve25519_heea_vartime(v_one);
        assert_eq!(rho, I256::ONE, "rho should be 1 when v is 1");
        assert_eq!(tau, 1, "tau should be 1 when v is 1");

        // Test Minus One: v = -1
        let v_minus_one = -I256::ONE;
        let (rho, tau) = curve25519_heea_vartime(v_minus_one);
        assert_eq!(rho, -I256::ONE, "rho should be -1 when v is -1");
        assert_eq!(tau, 1, "tau should be 1 when v is -1");

        // Test Max i128 Boundary: v = 2^127 - 1
        // This tests whether we handle values near the i128 boundary correctly
        // i128::MAX = 2^127 - 1
        let v_max_i128 = I256::new(i128::MAX);
        let (rho, tau) = curve25519_heea_vartime(v_max_i128);
        let rho_bits = bit_length_i256(rho);
        assert!(
            rho_bits <= 128,
            "rho should be half-size for 2^127-1, got {} bits",
            rho_bits
        );

        // Verify tau doesn't overflow i128
        let tau_magnitude = if tau < 0 {
            tau.wrapping_neg() as u128
        } else {
            tau as u128
        };
        assert!(
            tau_magnitude <= (1u128 << 127),
            "tau should fit in i128, got magnitude {}",
            tau_magnitude
        );

        // test v = 2^252
        let v_252 = I256::ONE << 252;
        let (rho, tau) = curve25519_heea_vartime(v_252);
        let rho_bits = bit_length_i256(rho);
        assert!(
            rho_bits <= 128,
            "rho should be half-size for 2^252, got {} bits",
            rho_bits
        );
        assert_eq!(tau, -1, "tau should be 1 for 2^252");
    }

    #[test]
    fn test_heea_large_shift() {
        // Create a test case where r0 and r1 differ by approximately 128 bits
        // This will trigger the s >= 128 case if it can happen
        // Create a value around 125 bits: 2^125
        let v_small = I256::ONE << 125;

        let (rho, _tau) = curve25519_heea_vartime(v_small);

        // Verify the result is still half-size
        let rho_bits = bit_length_i256(rho);
        assert!(
            rho_bits <= 128,
            "rho should be half-size even with large shifts, got {} bits",
            rho_bits
        );

        // Also test with a value that's exactly at the boundary
        let v_boundary = I256::ONE << 127;
        let (rho2, _tau2) = curve25519_heea_vartime(v_boundary);
        let rho2_bits = bit_length_i256(rho2);
        assert!(
            rho2_bits <= 128,
            "rho should be half-size for 2^127, got {} bits",
            rho2_bits
        );
    }

    #[test]
    fn test_heea_instrumented_shift_check() {
        // Instrumented version to check if s >= 128 ever occurs
        fn curve25519_heea_instrumented(v: I256) -> (I256, i128, u32) {
            let mut r0: I256 = (&constants::BASEPOINT_ORDER).into();
            let mut r1 = v;
            let mut t0: i128 = 0;
            let mut t1: i128 = 1;

            let mut bl_r0 = 253u32;
            let mut bl_r1 = bit_length_i256(r1);
            let mut max_s = 0u32;

            while bl_r1 > 127 {
                let s = bl_r0 - bl_r1;
                max_s = max_s.max(s);

                let mut r = r0;
                let mut t = t0;

                let sign_r0 = r0 < I256::ZERO;
                let sign_r1 = r1 < I256::ZERO;

                if sign_r0 == sign_r1 {
                    r = r.wrapping_sub(r1 << s);
                    if s < 128 {
                        t = t.wrapping_sub(t1.wrapping_shl(s));
                    }
                } else {
                    r = r.wrapping_add(r1 << s);
                    if s < 128 {
                        t = t.wrapping_add(t1.wrapping_shl(s));
                    }
                }

                let bl_r = bit_length_i256(r);

                if bl_r > bl_r1 {
                    r0 = r;
                    t0 = t;
                    bl_r0 = bl_r;
                } else {
                    r0 = r1;
                    r1 = r;
                    t0 = t1;
                    t1 = t;
                    bl_r0 = bl_r1;
                    bl_r1 = bl_r;
                }
            }

            (r1, t1, max_s)
        }

        // Test several edge cases to see max shift value
        let test_values = vec![
            I256::ZERO,
            I256::ONE,
            I256::ONE << 125,
            I256::ONE << 127,
            I256::ONE << 128,
            I256::ONE << 200,
            (&constants::BASEPOINT_ORDER).into(),
        ];

        for v in test_values {
            let (_rho, _tau, max_s) = curve25519_heea_instrumented(v);
            // Print or verify max_s is always < 128
            assert!(
                max_s < 128,
                "Found s >= 128! max_s = {} for input bit_length = {}",
                max_s,
                bit_length_i256(v)
            );
        }
    }
}
