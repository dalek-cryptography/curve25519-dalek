#![allow(non_snake_case)]

#[curve25519_dalek_derive::unsafe_target_feature_specialize(
    "avx2",
    conditional(
        "avx512ifma,avx512vl",
        all(curve25519_dalek_backend = "unstable_avx512", nightly)
    )
)]
pub mod spec {

    use core::cmp::Ordering;

    #[for_target_feature("avx2")]
    use crate::backend::vector::avx2::{CachedPoint, ExtendedPoint};

    #[for_target_feature("avx512ifma")]
    use crate::backend::vector::ifma::{CachedPoint, ExtendedPoint};

    use crate::edwards::EdwardsPoint;
    use crate::scalar::Scalar;
    use crate::traits::Identity;
    use crate::window::{LookupTable, NafLookupTable5};

    /// Perform constant-time, variable-base scalar multiplication.
    pub fn mul(point: &EdwardsPoint, scalar: &Scalar) -> EdwardsPoint {
        // Construct a lookup table of [P,2P,3P,4P,5P,6P,7P,8P]
        let lookup_table = LookupTable::<CachedPoint>::from(point);
        // Setting s = scalar, compute
        //
        //    s = s_0 + s_1*16^1 + ... + s_63*16^63,
        //
        // with `-8 ≤ s_i < 8` for `0 ≤ i < 63` and `-8 ≤ s_63 ≤ 8`.
        let scalar_digits = scalar.as_radix_16();
        // Compute s*P as
        //
        //    s*P = P*(s_0 +   s_1*16^1 +   s_2*16^2 + ... +   s_63*16^63)
        //    s*P =  P*s_0 + P*s_1*16^1 + P*s_2*16^2 + ... + P*s_63*16^63
        //    s*P = P*s_0 + 16*(P*s_1 + 16*(P*s_2 + 16*( ... + P*s_63)...))
        //
        // We sum right-to-left.
        let mut Q = ExtendedPoint::identity();
        for i in (0..64).rev() {
            Q = Q.mul_by_pow_2(4);
            Q = &Q + &lookup_table.select(scalar_digits[i]);
        }
        Q.into()
    }

    /// Perform variable-time, variable-base scalar multiplication.
    pub fn vartime_mul(point: &EdwardsPoint, scalar: &Scalar) -> EdwardsPoint {
        let naf = scalar.non_adjacent_form(5);
        let table = NafLookupTable5::<CachedPoint>::from(point);

        // Find starting index
        let mut i: usize = 255;
        for j in (0..256).rev() {
            i = j;
            if naf[i] != 0 {
                break;
            }
        }

        let mut Q = ExtendedPoint::identity();

        loop {
            Q = Q.double();

            match naf[i].cmp(&0) {
                Ordering::Greater => {
                    Q = &Q + &table.select(naf[i] as usize);
                }
                Ordering::Less => {
                    Q = &Q - &table.select(-naf[i] as usize);
                }
                Ordering::Equal => {}
            }

            if i == 0 {
                break;
            }
            i -= 1;
        }

        Q.into()
    }
}
