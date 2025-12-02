//! Implementation of the paper "Accelerating EdDSA Signature Verification
//! with Faster Scalar Size Halving" (TCHES 2025).
//!
//! This module implements Algorithm 4 (hEEA_approx_q) from the paper, which generates
//! half-size scalars for faster EdDSA verification.
//!
//! For verification sB = R + hA, we find rho, tau such that rho = tau*h (mod ell)
use ethnum::I256;

/// Ed25519 group order L = 2^252 + 27742317777372353535851937790883648493
/// = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
/// High 128 bits: 0x10000000000000000000000000000000
/// Low 128 bits:  0x14def9dea2f79cd65812631a5cf5d3ed
const L: I256 = I256::from_words(
    0x10000000000000000000000000000000,
    0x14def9dea2f79cd65812631a5cf5d3ed,
);

/// Implement curve25519_hEEA_vartime algorithm
/// Returns (rho, tau) such that rho ≡ tau * v (mod L)
pub(crate) fn curve25519_heea_vartime(v: I256) -> (I256, i128) {
    let mut r0 = L;
    let mut r1 = v;
    let mut t0: i128 = 0;
    let mut t1: i128 = 1;

    let mut bl_r0 = 253u32; // bit_length(L) = 253
    let mut bl_r1 = bit_length_i256(r1);

    // Main loop - continue until r1 is approximately half-size (~127 bits)
    loop {
        // Stop when r1 is small enough (half-size)
        if bl_r1 <= 127 {
            return (r1, t1);
        }

        // Compute shift amount
        let s = bl_r0 - bl_r1;

        // Perform the shift-and-add/sub operation
        let mut r = r0;
        let mut t = t0;

        // Check if signs are the same
        let sign_r0 = r0 < I256::ZERO;
        let sign_r1 = r1 < I256::ZERO;

        if sign_r0 == sign_r1 {
            // Same sign: subtract
            r = r.wrapping_sub(r1 << s);
            // For t, handle shift carefully - if s >= 128, result would overflow
            if s < 128 {
                t = t.wrapping_sub(t1.wrapping_shl(s));
            }
        } else {
            // Different sign: add
            r = r.wrapping_add(r1 << s);
            // For t, handle shift carefully - if s >= 128, result would overflow
            if s < 128 {
                t = t.wrapping_add(t1.wrapping_shl(s));
            }
        }

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
}

/// Compute bit length of I256 (magnitude, not including sign)
#[inline]
fn bit_length_i256(val: I256) -> u32 {
    if val == I256::ZERO {
        return 1;
    }

    if val < I256::ZERO {
        // For negative, compute bit length of absolute value
        let abs_val = val.wrapping_neg();
        256 - abs_val.leading_zeros()
    } else {
        256 - val.leading_zeros()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Scalar, digest::Update, traits::HEEADecomposition};
    use rand::RngCore;

    #[test]
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
                rho_magnitude_bits <= 128,
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
}
