//! Defines additional methods on RistrettoPoint for Lizard

use digest::Digest;
use digest::HashMarker;
use digest::consts::U32;

use crate::constants;
use crate::field::FieldElement;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use super::jacobi_quartic::JacobiPoint;
use super::lizard_constants;

use crate::ristretto::RistrettoPoint;

impl RistrettoPoint {
    /// Encode 16 bytes of data to a RistrettoPoint, using the Lizard method. The secure hash
    /// function `D` is used internally to produce a unique encoding for `data. Use SHA-256 if
    /// otherwise unsure.
    pub fn lizard_encode<D>(data: &[u8; 16]) -> RistrettoPoint
    where
        D: Digest<OutputSize = U32> + HashMarker,
    {
        let mut fe_bytes: [u8; 32] = Default::default();

        let digest = D::digest(data);
        fe_bytes[0..32].copy_from_slice(digest.as_slice());
        fe_bytes[8..24].copy_from_slice(data);
        fe_bytes[0] &= 0b11111110;
        fe_bytes[31] &= 0b00111111;
        let fe = FieldElement::from_bytes(&fe_bytes);
        RistrettoPoint::elligator_ristretto_flavor(&fe)
    }

    /// Decode 16 bytes of data from a RistrettoPoint, using the Lizard method. Returns `None` if
    /// this point was not generated using Lizard.
    pub fn lizard_decode<D>(&self) -> Option<[u8; 16]>
    where
        D: Digest<OutputSize = U32> + HashMarker,
    {
        let mut result: [u8; 16] = Default::default();
        let mut h: [u8; 32] = Default::default();
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();
        let mut n_found = 0;
        for (j, fe_j) in fes.iter().enumerate() {
            let mut ok = Choice::from((mask >> j) & 1);
            let buf2 = fe_j.to_bytes();
            h.copy_from_slice(&D::digest(&buf2[8..24]));
            h[8..24].copy_from_slice(&buf2[8..24]);
            h[0] &= 0b11111110;
            h[31] &= 0b00111111;
            ok &= h.ct_eq(&buf2);
            for i in 0..16 {
                result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok);
            }
            n_found += ok.unwrap_u8();
        }
        // Per the README, the likelihood that n_found == 2 is something like 2^-122
        if n_found == 1 { Some(result) } else { None }
    }

    /// Computes the at most 8 positive FieldElements f such that
    /// `self == RistrettoPoint::elligator_ristretto_flavor(f)`.
    /// Assumes self is even.
    ///
    /// First return value is a bitmask of which elements are valid inverses (lowest bit corresponds
    /// to the 0-th element).
    fn elligator_ristretto_flavor_inverse(&self) -> (u8, [FieldElement; 8]) {
        // Elligator2 computes a Point from a FieldElement in two steps: first
        // it computes a (s,t) on the Jacobi quartic and then computes the
        // corresponding even point on the Edwards curve.
        //
        // We invert in three steps.  Any Ristretto point has four representatives
        // as even Edwards points.  For each of those even Edwards points,
        // there are two points on the Jacobi quartic that map to it.
        // Each of those eight points on the Jacobi quartic might have an
        // Elligator2 preimage.
        //
        // Essentially we first loop over the four representatives of our point,
        // then for each of them consider both points on the Jacobi quartic and
        // check whether they have an inverse under Elligator2.  We take the
        // following shortcut though.
        //
        // We can compute two Jacobi quartic points for (x,y) and (-x,-y)
        // at the same time.  The four Jacobi quartic points are two of
        // such pairs.

        let mut mask: u8 = 0;
        let jcs = self.to_jacobi_quartic_ristretto();
        let mut ret = [FieldElement::ONE; 8];

        for i in 0..4 {
            let (ok, fe) = jcs[i].e_inv();
            let mut tmp: u8 = 0;
            ret[2 * i] = fe;
            tmp.conditional_assign(&1, ok);
            mask |= tmp << (2 * i);

            let jc = jcs[i].dual();
            let (ok, fe) = jc.e_inv();
            let mut tmp: u8 = 0;
            ret[2 * i + 1] = fe;
            tmp.conditional_assign(&1, ok);
            mask |= tmp << (2 * i + 1);
        }

        (mask, ret)
    }

    /// Find a point on the Jacobi quartic associated to each of the four
    /// points Ristretto equivalent to p.
    ///
    /// There is one exception: for (0,-1) there is no point on the quartic and
    /// so we repeat one on the quartic equivalent to (0,1).
    fn to_jacobi_quartic_ristretto(self) -> [JacobiPoint; 4] {
        let x2 = self.0.X.square(); // X^2
        let y2 = self.0.Y.square(); // Y^2
        let y4 = y2.square(); // Y^4
        let z2 = self.0.Z.square(); // Z^2
        let z_min_y = &self.0.Z - &self.0.Y; // Z - Y
        let z_pl_y = &self.0.Z + &self.0.Y; // Z + Y
        let z2_min_y2 = &z2 - &y2; // Z^2 - Y^2

        // gamma := 1/sqrt( Y^4 X^2 (Z^2 - Y^2) )
        let (_, gamma) = (&(&y4 * &x2) * &z2_min_y2).invsqrt();

        let den = &gamma * &y2;

        let s_over_x = &den * &z_min_y;
        let sp_over_xp = &den * &z_pl_y;

        let s0 = &s_over_x * &self.0.X;
        let s1 = &(-(&sp_over_xp)) * &self.0.X;

        // t_0 := -2/sqrt(-d-1) * Z * sOverX
        // t_1 := -2/sqrt(-d-1) * Z * spOverXp
        let tmp = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &self.0.Z;
        let mut t0 = &tmp * &s_over_x;
        let mut t1 = &tmp * &sp_over_xp;

        // den := -1/sqrt(1+d) (Y^2 - Z^2) gamma
        let den = &(&(-(&z2_min_y2)) * &lizard_constants::MINVSQRT_ONE_PLUS_D) * &gamma;

        // Same as before but with the substitution (X, Y, Z) = (Y, X, i*Z)
        let iz = &constants::SQRT_M1 * &self.0.Z; // iZ
        let iz_min_x = &iz - &self.0.X; // iZ - X
        let iz_pl_x = &iz + &self.0.X; // iZ + X

        let s_over_y = &den * &iz_min_x;
        let sp_over_yp = &den * &iz_pl_x;

        let mut s2 = &s_over_y * &self.0.Y;
        let mut s3 = &(-(&sp_over_yp)) * &self.0.Y;

        // t_2 := -2/sqrt(-d-1) * i*Z * sOverY
        // t_3 := -2/sqrt(-d-1) * i*Z * spOverYp
        let tmp = &lizard_constants::MDOUBLE_INVSQRT_A_MINUS_D * &iz;
        let mut t2 = &tmp * &s_over_y;
        let mut t3 = &tmp * &sp_over_yp;

        // Special case: X=0 or Y=0.  Then return
        //
        //  (0,1)   (1,-2i/sqrt(-d-1)   (-1,-2i/sqrt(-d-1))
        //
        // Note that if X=0 or Y=0, then s_i = t_i = 0.
        let x_or_y_is_zero = self.0.X.is_zero() | self.0.Y.is_zero();
        t0.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        t1.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        t2.conditional_assign(
            &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
            x_or_y_is_zero,
        );
        t3.conditional_assign(
            &lizard_constants::MIDOUBLE_INVSQRT_A_MINUS_D,
            x_or_y_is_zero,
        );
        s2.conditional_assign(&FieldElement::ONE, x_or_y_is_zero);
        s3.conditional_assign(&(-(&FieldElement::ONE)), x_or_y_is_zero);

        [
            JacobiPoint { S: s0, T: t0 },
            JacobiPoint { S: s1, T: t1 },
            JacobiPoint { S: s2, T: t2 },
            JacobiPoint { S: s3, T: t3 },
        ]
    }

    /// Interprets the given bytestring as a positive field element and computes the Ristretto
    /// Elligator map. Note this clears the bottom bit and top two bits of `bytes`.
    ///
    /// # Warning
    ///
    /// This function does not produce cryptographically random-looking Ristretto points. Use
    /// [`Self::hash_from_bytes`] for that. DO NOT USE THIS FUNCTION unless you really know what
    /// you're doing.
    pub fn map_to_curve(mut bytes: [u8; 32]) -> RistrettoPoint {
        // We only have a meaningful inverse if we give Elligator a point in its domain, ie a
        // positive (meaning low bit 0) field element. Mask off the top two bits to ensure it's less
        // than the modulus, and the bottom bit for evenness.
        bytes[0] &= 0b11111110;
        bytes[31] &= 0b00111111;

        let fe = FieldElement::from_bytes(&bytes);
        RistrettoPoint::elligator_ristretto_flavor(&fe)
    }

    /// Computes the possible bytestrings that could have produced this point via
    /// [`Self::map_to_curve`].
    /// First return value is a bitmask of which elements are valid inverses (lowest bit corresponds
    /// to the 0-th element).
    pub fn map_to_curve_inverse(&self) -> (u8, [[u8; 32]; 8]) {
        let mut ret = [[0u8; 32]; 8];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        for j in 0..8 {
            ret[j] = fes[j].to_bytes();
        }
        (mask, ret)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{edwards::EdwardsPoint, ristretto::CompressedRistretto};
    use rand_core::RngCore;
    use sha2::Sha256;

    /// Return the coset self + E\[4\]
    fn xcoset4(pt: &RistrettoPoint) -> [EdwardsPoint; 4] {
        [
            pt.0,
            pt.0 + constants::EIGHT_TORSION[2],
            pt.0 + constants::EIGHT_TORSION[4],
            pt.0 + constants::EIGHT_TORSION[6],
        ]
    }

    /// Checks
    /// `lizard_decode(lizard_encode(data)) == lizard_decode(expected_pt_bytes) == data`
    fn test_lizard_encode_helper(data: &[u8], expected_pt_bytes: &[u8]) {
        assert_eq!(data.len(), 16);
        assert_eq!(expected_pt_bytes.len(), 32);

        let p = RistrettoPoint::lizard_encode::<Sha256>(data.try_into().unwrap());
        let pt_bytes = p.compress().to_bytes();
        assert!(pt_bytes == expected_pt_bytes);
        let p = CompressedRistretto::from_slice(&pt_bytes)
            .unwrap()
            .decompress()
            .unwrap();
        let data_out = p.lizard_decode::<Sha256>().unwrap();
        assert!(&data_out == data);
    }

    #[test]
    fn test_lizard_encode() {
        // Test vectors are of the form (x, y) where y is the compressed encoding of the Ristretto
        // point given by lizard_encode(x).
        // These values come from the testLizard() function in vendor/ristretto.sage
        let test_vectors = [
            (
                "00000000000000000000000000000000",
                "f0b7e34484f74cf00f15024b738539738646bbbe1e9bc7509a676815227e774f",
            ),
            (
                "01010101010101010101010101010101",
                "cc92e81f585afc5caac88660d8d17e9025a44489a363042123f6af0702156e65",
            ),
            (
                "000102030405060708090a0b0c0d0e0f",
                "c830573f8a8e7778671f76cdc796dc0a235cf177f197d9fcba06e84e96247444",
            ),
            (
                "dddddddddddddddddddddddddddddddd",
                "ccb60554c081841037f821fa827b6a5bc2531f80e2647f1a858611f4ccfe3056",
            ),
        ];
        for tv in test_vectors {
            test_lizard_encode_helper(&hex::decode(tv.0).unwrap(), &hex::decode(tv.1).unwrap());
        }
    }

    // Tests that lizard_decode of a random point is None
    #[test]
    fn test_lizard_invalid() {
        let mut rng = rand::rng();
        for _ in 0..100 {
            let pt = RistrettoPoint::random(&mut rng);
            assert!(
                pt.lizard_decode::<Sha256>().is_none(),
                "random point {:02x?} is a valid Lizard encoding",
                pt.compress().to_bytes()
            )
        }
    }

    #[test]
    fn test_elligator_inv() {
        let mut rng = rand::rng();

        for i in 0..100 {
            let mut fe_bytes = [0u8; 32];

            if i == 0 {
                // Test for first corner-case: fe = 0
                fe_bytes = [0u8; 32];
            } else if i == 1 {
                // Test for second corner-case: fe = +sqrt(i*d)
                fe_bytes = [
                    168, 27, 92, 74, 203, 42, 48, 117, 170, 109, 234, 14, 45, 169, 188, 205, 21,
                    110, 235, 115, 153, 84, 52, 117, 151, 235, 123, 244, 88, 85, 179, 5,
                ];
            } else {
                // For the rest, just generate a random field element to test.
                rng.fill_bytes(&mut fe_bytes);
            }
            fe_bytes[0] &= 254; // positive
            fe_bytes[31] &= 127; // < 2^255-19
            let fe = FieldElement::from_bytes(&fe_bytes);

            let pt = RistrettoPoint::elligator_ristretto_flavor(&fe);
            for pt2 in xcoset4(&pt) {
                let (mask, fes) = RistrettoPoint(pt2).elligator_ristretto_flavor_inverse();

                let mut found = false;
                for (j, fe_j) in fes.iter().enumerate() {
                    if mask & (1 << j) != 0 {
                        assert_eq!(RistrettoPoint::elligator_ristretto_flavor(fe_j), pt);
                        if *fe_j == fe {
                            found = true;
                        }
                    }
                }
                assert!(found);
            }
        }
    }

    // Tests that map_to_curve_inverse ○ map_to_curve is the identity
    #[test]
    fn test_map_to_curve_inverse() {
        let mut rng = rand::rng();

        for _ in 0..100 {
            let mut input = [0u8; 32];
            rng.fill_bytes(&mut input);

            // Map to Ristretto and invert it
            let pt = RistrettoPoint::map_to_curve(input);
            let (bitmask, inverses) = pt.map_to_curve_inverse();

            // map_to_curve masks the bottom bit and top two bits of `input`
            let mut expected_inverse = input;
            expected_inverse[31] &= 0b00111111;
            expected_inverse[0] &= 0b11111110;

            // Check that one of the valid inverses matches the input
            let mut found = false;
            for (i, inv) in inverses.into_iter().enumerate() {
                let is_valid = bitmask & (1 << i) != 0;
                if is_valid && inv == expected_inverse {
                    found = true;
                }
            }
            if !found {
                panic!("did not find inverse for input {:02x?}", input);
            }
        }
    }
}
