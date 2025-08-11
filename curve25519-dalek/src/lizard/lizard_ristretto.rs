//! Defines additional methods on RistrettoPoint for Lizard

#![allow(non_snake_case)]

use digest::generic_array::typenum::U32;
use digest::Digest;

use crate::constants;
use crate::field::FieldElement;

use subtle::Choice;
use subtle::ConditionallySelectable;
use subtle::ConstantTimeEq;

use crate::edwards::EdwardsPoint;

use super::jacobi_quartic::JacobiPoint;
use super::lizard_constants;

use crate::ristretto::RistrettoPoint;
#[allow(unused_imports)]
use core::prelude::*;

impl RistrettoPoint {
    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    pub fn from_uniform_bytes_single_elligator(bytes: &[u8; 32]) -> RistrettoPoint {
        RistrettoPoint::elligator_ristretto_flavor(&FieldElement::from_bytes(bytes))
    }

    /// Encode 16 bytes of data to a RistrettoPoint, using the Lizard method
    pub fn lizard_encode<D: Digest>(data: &[u8; 16]) -> RistrettoPoint
    where
        D: Digest<OutputSize = U32>,
    {
        let mut fe_bytes: [u8; 32] = Default::default();

        let digest = D::digest(data);
        fe_bytes[0..32].copy_from_slice(digest.as_slice());
        fe_bytes[8..24].copy_from_slice(data);
        fe_bytes[0] &= 254; // make positive since Elligator on r and -r is the same
        fe_bytes[31] &= 63;
        let fe = FieldElement::from_bytes(&fe_bytes);
        RistrettoPoint::elligator_ristretto_flavor(&fe)
    }

    /// Decode 16 bytes of data from a RistrettoPoint, using the Lizard method
    pub fn lizard_decode<D: Digest>(&self) -> Option<[u8; 16]>
    where
        D: Digest<OutputSize = U32>,
    {
        let mut result: [u8; 16] = Default::default();
        let mut h: [u8; 32] = Default::default();
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();
        let mut n_found = 0;
        for (j, fe_j) in fes.iter().enumerate() {
            let mut ok = Choice::from((mask >> j) & 1);
            let buf2 = fe_j.as_bytes(); // array
            h.copy_from_slice(&D::digest(&buf2[8..24])); // array
            h[8..24].copy_from_slice(&buf2[8..24]);
            h[0] &= 254;
            h[31] &= 63;
            ok &= h.ct_eq(&buf2);
            for i in 0..16 {
                result[i] = u8::conditional_select(&result[i], &buf2[8 + i], ok);
            }
            n_found += ok.unwrap_u8();
        }
        if n_found == 1 {
            Some(result)
        } else {
            None
        }
    }

    /// Directly encode 253 bits as a RistrettoPoint, using Elligator
    pub fn encode_253_bits(data: &[u8; 32]) -> Option<RistrettoPoint> {
        if data.len() != 32 {
            return None;
        }

        let fe = FieldElement::from_bytes(data);
        let p = RistrettoPoint::elligator_ristretto_flavor(&fe);
        Some(p)
    }

    /// Directly decode a RistrettoPoint as 253 bits, using Elligator
    pub fn decode_253_bits(&self) -> (u8, [[u8; 32]; 8]) {
        let mut ret = [[0u8; 32]; 8];
        let (mask, fes) = self.elligator_ristretto_flavor_inverse();

        for j in 0..8 {
            ret[j] = fes[j].as_bytes();
        }
        (mask, ret)
    }

    /// Return the coset self + E[4], for debugging.
    pub fn xcoset4(&self) -> [EdwardsPoint; 4] {
        [
            self.0,
            self.0 + constants::EIGHT_TORSION[2],
            self.0 + constants::EIGHT_TORSION[4],
            self.0 + constants::EIGHT_TORSION[6],
        ]
    }

    /// Computes the at most 8 positive FieldElements f such that
    /// self == elligator_ristretto_flavor(f).
    /// Assumes self is even.
    ///
    /// Returns a bitmask of which elements in fes are set.
    pub fn elligator_ristretto_flavor_inverse(&self) -> (u8, [FieldElement; 8]) {
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
            let (ok, fe) = jcs[i].elligator_inv();
            let mut tmp: u8 = 0;
            ret[2 * i] = fe;
            tmp.conditional_assign(&1, ok);
            mask |= tmp << (2 * i);

            let jc = jcs[i].dual();
            let (ok, fe) = jc.elligator_inv();
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
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {

    use sha2;

    use self::sha2::Sha256;
    use super::*;
    use crate::ristretto::CompressedRistretto;
    use rand_core::RngCore;
    #[cfg(feature = "rand")]
    use rand_os::OsRng;

    fn test_lizard_encode_helper(data: &[u8; 16], result: &[u8; 32]) {
        let p = RistrettoPoint::lizard_encode::<Sha256>(data);
        let p_bytes = p.compress().to_bytes();
        assert!(&p_bytes == result);
        let p = CompressedRistretto::from_slice(&p_bytes)
            .unwrap()
            .decompress()
            .unwrap();
        let data_out = p.lizard_decode::<Sha256>().unwrap();
        assert!(&data_out == data);
    }

    #[test]
    fn test_lizard_encode() {
        test_lizard_encode_helper(
            &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            &[
                0xf0, 0xb7, 0xe3, 0x44, 0x84, 0xf7, 0x4c, 0xf0, 0xf, 0x15, 0x2, 0x4b, 0x73, 0x85,
                0x39, 0x73, 0x86, 0x46, 0xbb, 0xbe, 0x1e, 0x9b, 0xc7, 0x50, 0x9a, 0x67, 0x68, 0x15,
                0x22, 0x7e, 0x77, 0x4f,
            ],
        );

        test_lizard_encode_helper(
            &[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            &[
                0xcc, 0x92, 0xe8, 0x1f, 0x58, 0x5a, 0xfc, 0x5c, 0xaa, 0xc8, 0x86, 0x60, 0xd8, 0xd1,
                0x7e, 0x90, 0x25, 0xa4, 0x44, 0x89, 0xa3, 0x63, 0x4, 0x21, 0x23, 0xf6, 0xaf, 0x7,
                0x2, 0x15, 0x6e, 0x65,
            ],
        );

        test_lizard_encode_helper(
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            &[
                0xc8, 0x30, 0x57, 0x3f, 0x8a, 0x8e, 0x77, 0x78, 0x67, 0x1f, 0x76, 0xcd, 0xc7, 0x96,
                0xdc, 0xa, 0x23, 0x5c, 0xf1, 0x77, 0xf1, 0x97, 0xd9, 0xfc, 0xba, 0x6, 0xe8, 0x4e,
                0x96, 0x24, 0x74, 0x44,
            ],
        );
    }

    #[test]
    fn test_elligator_inv() {
        let mut rng = rand::thread_rng();

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
            for pt2 in &pt.xcoset4() {
                let (mask, fes) = RistrettoPoint(*pt2).elligator_ristretto_flavor_inverse();

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
}
