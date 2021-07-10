// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2021 isis lovecruft
// Copyright (c) 2016-2019 Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Scalar multiplication on the Montgomery form of Curve25519.
//!
//! To avoid notational confusion with the Edwards code, we use
//! variables \\( u, v \\) for the Montgomery curve, so that “Montgomery
//! \\(u\\)” here corresponds to “Montgomery \\(x\\)” elsewhere.
//!
//! Montgomery arithmetic works not on the curve itself, but on the
//! \\(u\\)-line, which discards sign information and unifies the curve
//! and its quadratic twist.  See [_Montgomery curves and their
//! arithmetic_][costello-smith] by Costello and Smith for more details.
//!
//! The `MontgomeryPoint` struct contains the affine \\(u\\)-coordinate
//! \\(u\_0(P)\\) of a point \\(P\\) on either the curve or the twist.
//! Here the map \\(u\_0 : \mathcal M \rightarrow \mathbb F\_p \\) is
//! defined by \\(u\_0((u,v)) = u\\); \\(u\_0(\mathcal O) = 0\\).  See
//! section 5.4 of Costello-Smith for more details.
//!
//! # Scalar Multiplication
//!
//! Scalar multiplication on `MontgomeryPoint`s is provided by the `*`
//! operator, which implements the Montgomery ladder.
//!
//! # Edwards Conversion
//!
//! The \\(2\\)-to-\\(1\\) map from the Edwards model to the Montgomery
//! \\(u\\)-line is provided by `EdwardsPoint::to_montgomery()`.
//!
//! To lift a `MontgomeryPoint` to an `EdwardsPoint`, use
//! `MontgomeryPoint::to_edwards()`, which takes a sign parameter.
//! This function rejects `MontgomeryPoints` which correspond to points
//! on the twist.
//!
//! [costello-smith]: https://eprint.iacr.org/2017/212.pdf

// We allow non snake_case names because coordinates in projective space are
// traditionally denoted by the capitalisation of their respective
// counterparts in affine space.  Yeah, you heard me, rustc, I'm gonna have my
// affine and projective cakes and eat both of them too.
#![allow(non_snake_case)]

use core::ops::{Mul, MulAssign};

#[cfg(not(feature = "betrusted"))]
use constants::{APLUS2_OVER_FOUR, MONTGOMERY_A, MONTGOMERY_A_NEG};
#[cfg(feature = "betrusted")]
use constants::{MONTGOMERY_A, MONTGOMERY_A_NEG}; // eliminate constants absorbed into the microcode engine

use edwards::{CompressedEdwardsY, EdwardsPoint};
use field::FieldElement;
use scalar::Scalar;

use traits::Identity;

use subtle::Choice;
use subtle::ConstantTimeEq;
use subtle::{ConditionallyNegatable, ConditionallySelectable};

use zeroize::Zeroize;

/// Holds the \\(u\\)-coordinate of a point on the Montgomery form of
/// Curve25519 or its twist.
#[derive(Copy, Clone, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MontgomeryPoint(pub [u8; 32]);

/// Equality of `MontgomeryPoint`s is defined mod p.
impl ConstantTimeEq for MontgomeryPoint {
    fn ct_eq(&self, other: &MontgomeryPoint) -> Choice {
        let self_fe = FieldElement::from_bytes(&self.0);
        let other_fe = FieldElement::from_bytes(&other.0);

        self_fe.ct_eq(&other_fe)
    }
}

impl Default for MontgomeryPoint {
    fn default() -> MontgomeryPoint {
        MontgomeryPoint([0u8; 32])
    }
}

impl PartialEq for MontgomeryPoint {
    fn eq(&self, other: &MontgomeryPoint) -> bool {
        self.ct_eq(other).unwrap_u8() == 1u8
    }
}

impl Eq for MontgomeryPoint {}

impl Zeroize for MontgomeryPoint {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl MontgomeryPoint {
    /// View this `MontgomeryPoint` as an array of bytes.
    pub fn as_bytes<'a>(&'a self) -> &'a [u8; 32] {
        &self.0
    }

    /// Convert this `MontgomeryPoint` to an array of bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Attempt to convert to an `EdwardsPoint`, using the supplied
    /// choice of sign for the `EdwardsPoint`.
    ///
    /// # Inputs
    ///
    /// * `sign`: a `u8` donating the desired sign of the resulting
    ///   `EdwardsPoint`.  `0` denotes positive and `1` negative.
    ///
    /// # Return
    ///
    /// * `Some(EdwardsPoint)` if `self` is the \\(u\\)-coordinate of a
    /// point on (the Montgomery form of) Curve25519;
    ///
    /// * `None` if `self` is the \\(u\\)-coordinate of a point on the
    /// twist of (the Montgomery form of) Curve25519;
    ///
    pub fn to_edwards(&self, sign: u8) -> Option<EdwardsPoint> {
        // To decompress the Montgomery u coordinate to an
        // `EdwardsPoint`, we apply the birational map to obtain the
        // Edwards y coordinate, then do Edwards decompression.
        //
        // The birational map is y = (u-1)/(u+1).
        //
        // The exceptional points are the zeros of the denominator,
        // i.e., u = -1.
        //
        // But when u = -1, v^2 = u*(u^2+486662*u+1) = 486660.
        //
        // Since this is nonsquare mod p, u = -1 corresponds to a point
        // on the twist, not the curve, so we can reject it early.

        let u = FieldElement::from_bytes(&self.0);

        if u == FieldElement::minus_one() { return None; }

        let one = FieldElement::one();

        let y = &(&u - &one) * &(&u + &one).invert();

        let mut y_bytes = y.to_bytes();
        y_bytes[31] ^= sign << 7;

        CompressedEdwardsY(y_bytes).decompress()
    }
}

/// Perform the Elligator2 mapping to a Montgomery point.
///
/// See https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-10#section-6.7.1
//
// TODO Determine how much of the hash-to-group API should be exposed after the CFRG
//      draft gets into a more polished/accepted state.
#[allow(unused)]
pub(crate) fn elligator_encode(r_0: &FieldElement) -> MontgomeryPoint {
    let one = FieldElement::one();
    let d_1 = &one + &r_0.square2(); /* 2r^2 */

    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* A/(1+2r^2) */

    let d_sq = &d.square();
    let au = &MONTGOMERY_A * &d;

    let inner = &(d_sq + &au) + &one;
    let eps = &d * &inner; /* eps = d^3 + Ad^2 + d */

    let (eps_is_sq, _eps) = FieldElement::sqrt_ratio_i(&eps, &one);

    let zero = FieldElement::zero();
    let Atemp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq); /* 0, or A if nonsquare*/
    let mut u = &d + &Atemp; /* d, or d+A if nonsquare */
    u.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    MontgomeryPoint(u.to_bytes())
}

/// A `ProjectivePoint` holds a point on the projective line
/// \\( \mathbb P(\mathbb F\_p) \\), which we identify with the Kummer
/// line of the Montgomery curve.
#[derive(Copy, Clone, Debug)]
pub(crate) struct ProjectivePoint {
    pub U: FieldElement,
    pub W: FieldElement,
}

impl Identity for ProjectivePoint {
    fn identity() -> ProjectivePoint {
        ProjectivePoint {
            U: FieldElement::one(),
            W: FieldElement::zero(),
        }
    }
}

impl Default for ProjectivePoint {
    fn default() -> ProjectivePoint {
        ProjectivePoint::identity()
    }
}

impl ConditionallySelectable for ProjectivePoint {
    fn conditional_select(
        a: &ProjectivePoint,
        b: &ProjectivePoint,
        choice: Choice,
    ) -> ProjectivePoint {
        ProjectivePoint {
            U: FieldElement::conditional_select(&a.U, &b.U, choice),
            W: FieldElement::conditional_select(&a.W, &b.W, choice),
        }
    }
}

impl ProjectivePoint {
    /// Dehomogenize this point to affine coordinates.
    ///
    /// # Return
    ///
    /// * \\( u = U / W \\) if \\( W \neq 0 \\);
    /// * \\( 0 \\) if \\( W \eq 0 \\);
    #[cfg(not(feature = "betrusted"))]
    pub fn to_affine(&self) -> MontgomeryPoint {
        #[cfg(all(not(test),feature="betrusted"))] // due to issue https://github.com/rust-lang/rust/issues/59168, you will have to manually comment this out when running a test on the full system and not just this crate.
        log::warn!("sw to_affine being used - check for build config errors!");

        let u = &self.U * &self.W.invert();
        MontgomeryPoint(u.to_bytes())
    }
    #[allow(dead_code)]
    #[cfg(feature = "betrusted")]
    pub fn to_affine(&self) -> MontgomeryPoint {
        let mcode = assemble_engine25519!(
            start:
                // W.invert() in %21
                // U in %29
                // W in %30
                // result in %31
                // loop counter in %28

                // from FieldElement.invert()
                    // let (t19, t3) = self.pow22501();   // t19: 249..0 ; t3: 3,1,0
                    // let t0  = self.square();           // 1         e_0 = 2^1
                    mul %0, %30, %30  // self is W, e.g. %30
                    // let t1  = t0.square().square();    // 3         e_1 = 2^3
                    mul %1, %0, %0
                    mul %1, %1, %1
                    // let t2  = self * &t1;              // 3,0       e_2 = 2^3 + 2^0
                    mul %2, %30, %1
                    // let t3  = &t0 * &t2;               // 3,1,0
                    mul %3, %0, %2
                    // let t4  = t3.square();             // 4,2,1
                    mul %4, %3, %3
                    // let t5  = &t2 * &t4;               // 4,3,2,1,0
                    mul %5, %2, %4

                    // let t6  = t5.pow2k(5);             // 9,8,7,6,5
                    psa %28, #5       // coincidentally, constant #5 is the number 5
                    mul %6, %5, %5
                pow2k_5:
                    sub %28, %28, #1  // %28 = %28 - 1
                    brz pow2k_5_exit, %28
                    mul %6, %6, %6
                    brz pow2k_5, #0
                pow2k_5_exit:
                    // let t7  = &t6 * &t5;               // 9,8,7,6,5,4,3,2,1,0
                    mul %7, %6, %5

                    // let t8  = t7.pow2k(10);            // 19..10
                    psa %28, #6        // constant #6 is the number 10
                    mul %8, %7, %7
                pow2k_10:
                    sub %28, %28, #1
                    brz pow2k_10_exit, %28
                    mul %8, %8, %8
                    brz pow2k_10, #0
                pow2k_10_exit:
                    // let t9  = &t8 * &t7;               // 19..0
                    mul %9, %8, %7

                    // let t10 = t9.pow2k(20);            // 39..20
                    psa %28, #7         // constant #7 is the number 20
                    mul %10, %9, %9
                pow2k_20:
                    sub %28, %28, #1
                    brz pow2k_20_exit, %28
                    mul %10, %10, %10
                    brz pow2k_20, #0
                pow2k_20_exit:
                    // let t11 = &t10 * &t9;              // 39..0
                    mul %11, %10, %9

                    // let t12 = t11.pow2k(10);           // 49..10
                    psa %28, #6         // constant #6 is the number 10
                    mul %12, %11, %11
                pow2k_10b:
                    sub %28, %28, #1
                    brz pow2k_10b_exit, %28
                    mul %12, %12, %12
                    brz pow2k_10b, #0
                pow2k_10b_exit:
                    // let t13 = &t12 * &t7;              // 49..0
                    mul %13, %12, %7

                    // let t14 = t13.pow2k(50);           // 99..50
                    psa %28, #8         // constant #8 is the number 50
                    mul %14, %13, %13
                pow2k_50a:
                    sub %28, %28, #1
                    brz pow2k_50a_exit, %28
                    mul %14, %14, %14
                    brz pow2k_50a, #0
                pow2k_50a_exit:
                    // let t15 = &t14 * &t13;             // 99..0
                    mul %15, %14, %13

                    // let t16 = t15.pow2k(100);          // 199..100
                    psa %28, #9         // constant #9 is the number 100
                    mul %16, %15, %15
                pow2k_100:
                    sub %28, %28, #1
                    brz pow2k_100_exit, %28
                    mul %16, %16, %16
                    brz pow2k_100, #0
                pow2k_100_exit:
                    // let t17 = &t16 * &t15;             // 199..0
                    mul %17, %16, %15

                    // let t18 = t17.pow2k(50);           // 249..50
                    psa %28, #8         // constant #8 is the number 50
                    mul %18, %17, %17
                pow2k_50b:
                    sub %28, %28, #1
                    brz pow2k_50b_exit, %28
                    mul %18, %18, %18
                    brz pow2k_50b, #0
                pow2k_50b_exit:
                    // let t19 = &t18 * &t13;             // 249..0
                    mul %19, %18, %13
                    //(t19, t3) // just a return value, values are already there, do nothing

                    //let t20 = t19.pow2k(5);            // 254..5
                    psa %28, #5
                    mul %20, %19, %19
                pow2k_5_last:
                    sub %28, %28, #1
                    brz pow2k_5_last_exit, %28
                    mul %20, %20, %20
                    brz pow2k_5_last, #0
                pow2k_5_last_exit:

                    //let t21 = &t20 * &t3;              // 254..5,3,1,0
                    mul %21, %20, %3

                // u = &self.U * &self.W.invert()
                mul %31, %29, %21
                fin  // finish execution
        );
        let mut engine = engine_25519::Engine25519::new();
        let mut job = engine_25519::Job {
            id: None,
            ucode: [0; 1024],
            uc_len: mcode.len() as u32,
            uc_start: 0,
            window: Some(0),
            rf: [0; engine_25519::RF_SIZE_IN_U32],
        };
        for (&src, dst) in mcode.iter().zip(job.ucode.iter_mut()) {
            *dst = src as u32;
        }
        copy_to_rf(self.U.to_bytes(), 29, &mut job.rf);
        copy_to_rf(self.W.to_bytes(), 30, &mut job.rf);

        // start the run
        let result_rf = engine.spawn_job(job).expect("couldn't run engine job");

        MontgomeryPoint(copy_from_rf(31, &result_rf))
    }
}

/// Perform the double-and-add step of the Montgomery ladder.
///
/// Given projective points
/// \\( (U\_P : W\_P) = u(P) \\),
/// \\( (U\_Q : W\_Q) = u(Q) \\),
/// and the affine difference
/// \\(      u\_{P-Q} = u(P-Q) \\), set
/// $$
///     (U\_P : W\_P) \gets u([2]P)
/// $$
/// and
/// $$
///     (U\_Q : W\_Q) \gets u(P + Q).
/// $$
#[cfg(not(feature = "betrusted"))]
pub(crate) fn differential_add_and_double(
    P: &mut ProjectivePoint,
    Q: &mut ProjectivePoint,
    affine_PmQ: &FieldElement,
) {
    let t0 = &P.U + &P.W;
    let t1 = &P.U - &P.W;
    let t2 = &Q.U + &Q.W;
    let t3 = &Q.U - &Q.W;

    let t4 = t0.square();   // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
    let t5 = t1.square();   // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2

    let t6 = &t4 - &t5;     // 4 U_P W_P

    let t7 = &t0 * &t3;     // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
    let t8 = &t1 * &t2;     // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q

    let t9  = &t7 + &t8;    // 2 (U_P U_Q - W_P W_Q)
    let t10 = &t7 - &t8;    // 2 (W_P U_Q - U_P W_Q)

    let t11 =  t9.square(); // 4 (U_P U_Q - W_P W_Q)^2
    let t12 = t10.square(); // 4 (W_P U_Q - U_P W_Q)^2

    let t13 = &APLUS2_OVER_FOUR * &t6; // (A + 2) U_P U_Q

    let t14 = &t4 * &t5;    // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
    let t15 = &t13 + &t5;   // (U_P - W_P)^2 + (A + 2) U_P W_P

    let t16 = &t6 * &t15;   // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)

    let t17 = affine_PmQ * &t12; // U_D * 4 (W_P U_Q - U_P W_Q)^2
    let t18 = t11;               // W_D * 4 (U_P U_Q - W_P W_Q)^2

    P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
    P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
    Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
    Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
}

#[cfg(feature = "betrusted")]
fn copy_to_rf(bytes: [u8; 32], register: usize, rf: &mut [u32; engine_25519::RF_SIZE_IN_U32]) {
    use core::convert::TryInto;
    for (byte, rf_dst) in bytes.chunks_exact(4).zip(rf[register * 8..(register+1)*8].iter_mut()) {
        *rf_dst = u32::from_le_bytes(byte.try_into().expect("chunks_exact failed us"));
    }
}

#[cfg(feature = "betrusted")]
fn copy_from_rf(register: usize, rf: &[u32; engine_25519::RF_SIZE_IN_U32]) -> [u8; 32] {
    let mut ret: [u8; 32] = [0; 32];

    for (src, dst) in rf[register*8 .. (register+1)*8].iter().zip(ret.chunks_exact_mut(4).into_iter()) {
        for (&src_byte, dst_byte) in src.to_le_bytes().iter().zip(dst.iter_mut()) {
            *dst_byte = src_byte;
        }
    }

    ret
}

#[allow(dead_code)] // absorbed into mul, but might be useful later on as a subroutine for something else
#[cfg(feature = "betrusted")]
pub(crate) fn differential_add_and_double_hw(
    P: &mut ProjectivePoint,
    Q: &mut ProjectivePoint,
    affine_PmQ: &FieldElement,
) {
    let mcode = assemble_engine25519!(
        start:
            // P.U in %20
            // P.W in %21
            // Q.U in %22
            // Q.W in %23
            // affine_PmQ in %24
            // %30 is the TRD scratch register
            // %29 is the subtraction temporary value register

            // let t0 = &P.U + &P.W;
            add %0, %20, %21
            trd %30, %0
            sub %0, %0, %30
            // let t1 = &P.U - &P.W;
            sub %21, #3, %21    // negate &P.W using #FIELDPRIME (#3)
            add %1, %20, %21
            trd %30, %1
            sub %1, %1, %30
            // let t2 = &Q.U + &Q.W;
            add %2, %22, %23
            trd %30, %2
            sub %2, %2, %30
            // let t3 = &Q.U - &Q.W;
            sub %23, #3, %23
            add %3, %22, %23
            trd %30, %3
            sub %3, %3, %30
            // let t4 = t0.square();   // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
            mul %4, %0, %0
            // let t5 = t1.square();   // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2
            mul %5, %1, %1
            // let t6 = &t4 - &t5;     // 4 U_P W_P
            sub %29, #3, %5
            add %6, %4, %29
            trd %30, %6
            sub %6, %6, %30
            // let t7 = &t0 * &t3;     // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
            mul %7, %0, %3
            // let t8 = &t1 * &t2;     // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q
            mul %8, %1, %2
            // let t9  = &t7 + &t8;    // 2 (U_P U_Q - W_P W_Q)
            add %9, %7, %8
            trd %30, %9
            sub %9, %9, %30
            // let t10 = &t7 - &t8;    // 2 (W_P U_Q - U_P W_Q)
            sub %29, #3, %8
            add %10, %7, %29
            trd %30, %10
            sub %10, %10, %30
            // let t11 =  t9.square(); // 4 (U_P U_Q - W_P W_Q)^2
            mul %11, %9, %9
            // let t12 = t10.square(); // 4 (W_P U_Q - U_P W_Q)^2
            mul %12, %10, %10
            // let t13 = &APLUS2_OVER_FOUR * &t6; // (A + 2) U_P U_Q
            mul %13, #4, %6   // #4 is A+2/4
            // let t14 = &t4 * &t5;    // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
            mul %14, %4, %5
            // let t15 = &t13 + &t5;   // (U_P - W_P)^2 + (A + 2) U_P W_P
            add %15, %13, %5
            trd %30, %15
            sub %15, %15, %30
            // let t16 = &t6 * &t15;   // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)
            mul %16, %6, %15
            // let t17 = affine_PmQ * &t12; // U_D * 4 (W_P U_Q - U_P W_Q)^2
            mul %17, %24, %12    // affine_PmQ loaded into %24

            ///// these can be eliminated down the road, but included for 1:1 algorithm correspodence to reference in early testing
            // let t18 = t11;               // W_D * 4 (U_P U_Q - W_P W_Q)^2
            psa %18, %11
            // P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
            psa %20, %14
            // P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
            psa %21, %16
            // Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
            psa %22, %18
            // Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
            psa %23, %17

            fin  // finish execution
    );
    let mut engine = engine_25519::Engine25519::new();

    let mut job = engine_25519::Job {
        id: None,
        ucode: [0; 1024],
        uc_len: mcode.len() as u32,
        uc_start: 0,
        window: Some(0),
        rf: [0; engine_25519::RF_SIZE_IN_U32],
    };

    for (&src, dst) in mcode.iter().zip(job.ucode.iter_mut()) {
        *dst = src;
    }

    // P.U in %20
    // P.W in %21
    // Q.U in %22
    // Q.W in %23
    // affine_PmQ in %24
    copy_to_rf(P.U.to_bytes(), 20, &mut job.rf);
    copy_to_rf(P.W.to_bytes(), 21, &mut job.rf);
    copy_to_rf(Q.U.to_bytes(), 22, &mut job.rf);
    copy_to_rf(Q.W.to_bytes(), 23, &mut job.rf);
    copy_to_rf(affine_PmQ.to_bytes(), 24, &mut job.rf);

    // start the run
    let result_rf = engine.spawn_job(job).expect("couldn't run engine job");

    P.U = FieldElement::from_bytes(&copy_from_rf(20, &result_rf));
    P.W = FieldElement::from_bytes(&copy_from_rf(21, &result_rf));
    Q.U = FieldElement::from_bytes(&copy_from_rf(22, &result_rf));
    Q.W = FieldElement::from_bytes(&copy_from_rf(23, &result_rf));
}

define_mul_assign_variants!(LHS = MontgomeryPoint, RHS = Scalar);

define_mul_variants!(LHS = MontgomeryPoint, RHS = Scalar, Output = MontgomeryPoint);
define_mul_variants!(LHS = Scalar, RHS = MontgomeryPoint, Output = MontgomeryPoint);

/// Multiply this `MontgomeryPoint` by a `Scalar`.
impl<'a, 'b> Mul<&'b Scalar> for &'a MontgomeryPoint {
    type Output = MontgomeryPoint;

    /// Given `self` \\( = u\_0(P) \\), and a `Scalar` \\(n\\), return \\( u\_0([n]P) \\).
    #[cfg(feature = "betrusted")]
    fn mul(self, scalar: &'b Scalar) -> MontgomeryPoint {
        log::debug!("hw mont");
        // Algorithm 8 of Costello-Smith 2017
        let affine_u = FieldElement::from_bytes(&self.0);
        let mut x0 = ProjectivePoint::identity();
        let x1 = ProjectivePoint {
            U: affine_u,
            W: FieldElement::one(),
        };

        // for now, prefer to use the fully-accelerated version where this code is local to the server
        // instead of transmitting it every call with the data...gives about a 2x performance speedup
        if false {
            #[cfg(not(test))] // due to issue https://github.com/rust-lang/rust/issues/59168, you will have to manually comment this out when running a test on the full system and not just this crate.
            log::warn!("wrong multiply being used!");

            let mcode = assemble_engine25519!(
                start:
                    // P.U in %20
                    // P.W in %21
                    // Q.U in %22
                    // Q.W in %23
                    // affine_PmQ in %24
                    // %30 is the TRD scratch register and cswap dummy
                    // %29 is the subtraction temporary value register and k_t
                    // x0.U in %25
                    // x0.W in %26
                    // x1.U in %27
                    // x1.W in %28
                    // %19 is the loop counter, starts with 254 (if 0, loop runs exactly once)
                    // %31 is the scalar
                    // %18 is the swap variable
                    psa %18, #0

                    // for i in (0..255).rev()
                mainloop:
                    // let choice: u8 = (bits[i + 1] ^ bits[i]) as u8;
                    // ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());
                    xbt %29, %31        // orignally[k_t = (k>>t) & 1] now[k_t = k[254]]
                    shl %31, %31        // k = k<<1
                    xor %18, %18, %29   // swap ^= k_t

                    // cswap x0.U (%25), x1.U (%27)
                    xor %30, %25, %27
                    msk %30, %18, %30
                    xor %25, %30, %25
                    xor %27, %30, %27
                    // cswap x0.W (%26), x1.W (%28)
                    xor %30, %26, %28
                    msk %30, %18, %30
                    xor %26, %30, %26
                    xor %28, %30, %28

                    psa %18, %29  // swap = k_t

                        // differential_add_and_double(&mut x0, &mut x1, &affine_u);
                        psa %20, %25
                        psa %21, %26
                        psa %22, %27
                        psa %23, %28
                        // affine_u is already in %24

                        // let t0 = &P.U + &P.W;
                        add %0, %20, %21
                        trd %30, %0
                        sub %0, %0, %30
                        // let t1 = &P.U - &P.W;
                        sub %21, #3, %21    // negate &P.W using #FIELDPRIME (#3)
                        add %1, %20, %21
                        trd %30, %1
                        sub %1, %1, %30
                        // let t2 = &Q.U + &Q.W;
                        add %2, %22, %23
                        trd %30, %2
                        sub %2, %2, %30
                        // let t3 = &Q.U - &Q.W;
                        sub %23, #3, %23
                        add %3, %22, %23
                        trd %30, %3
                        sub %3, %3, %30
                        // let t4 = t0.square();   // (U_P + W_P)^2 = U_P^2 + 2 U_P W_P + W_P^2
                        mul %4, %0, %0
                        // let t5 = t1.square();   // (U_P - W_P)^2 = U_P^2 - 2 U_P W_P + W_P^2
                        mul %5, %1, %1
                        // let t6 = &t4 - &t5;     // 4 U_P W_P
                        sub %29, #3, %5
                        add %6, %4, %29
                        trd %30, %6
                        sub %6, %6, %30
                        // let t7 = &t0 * &t3;     // (U_P + W_P) (U_Q - W_Q) = U_P U_Q + W_P U_Q - U_P W_Q - W_P W_Q
                        mul %7, %0, %3
                        // let t8 = &t1 * &t2;     // (U_P - W_P) (U_Q + W_Q) = U_P U_Q - W_P U_Q + U_P W_Q - W_P W_Q
                        mul %8, %1, %2
                        // let t9  = &t7 + &t8;    // 2 (U_P U_Q - W_P W_Q)
                        add %9, %7, %8
                        trd %30, %9
                        sub %9, %9, %30
                        // let t10 = &t7 - &t8;    // 2 (W_P U_Q - U_P W_Q)
                        sub %29, #3, %8
                        add %10, %7, %29
                        trd %30, %10
                        sub %10, %10, %30
                        // let t11 =  t9.square(); // 4 (U_P U_Q - W_P W_Q)^2
                        mul %11, %9, %9
                        // let t12 = t10.square(); // 4 (W_P U_Q - U_P W_Q)^2
                        mul %12, %10, %10
                        // let t13 = &APLUS2_OVER_FOUR * &t6; // (A + 2) U_P U_Q
                        mul %13, #4, %6   // #4 is A+2/4
                        // let t14 = &t4 * &t5;    // ((U_P + W_P)(U_P - W_P))^2 = (U_P^2 - W_P^2)^2
                        mul %14, %4, %5
                        // let t15 = &t13 + &t5;   // (U_P - W_P)^2 + (A + 2) U_P W_P
                        add %15, %13, %5
                        trd %30, %15
                        sub %15, %15, %30
                        // let t16 = &t6 * &t15;   // 4 (U_P W_P) ((U_P - W_P)^2 + (A + 2) U_P W_P)
                        mul %16, %6, %15
                        // let t17 = affine_PmQ * &t12; // U_D * 4 (W_P U_Q - U_P W_Q)^2
                        mul %17, %24, %12    // affine_PmQ loaded into %24

                        ///// these can be eliminated down the road, but included for 1:1 algorithm correspodence to reference in early testing
                        // P.U = t14;  // U_{P'} = (U_P + W_P)^2 (U_P - W_P)^2
                        psa %20, %14
                        // P.W = t16;  // W_{P'} = (4 U_P W_P) ((U_P - W_P)^2 + ((A + 2)/4) 4 U_P W_P)
                        psa %21, %16
                        // let t18 = t11;               // W_D * 4 (U_P U_Q - W_P W_Q)^2
                        // Q.U = t18;  // U_{Q'} = W_D * 4 (U_P U_Q - W_P W_Q)^2
                        psa %22, %11   // collapsed two to save a register
                        // Q.W = t17;  // W_{Q'} = U_D * 4 (W_P U_Q - U_P W_Q)^2
                        psa %23, %17

                        ///// 'return' arguments for next iteration, can be optimized out later
                        psa %25, %20
                        psa %26, %21
                        psa %27, %22
                        psa %28, %23

                    brz end, %19     // if loop counter is 0, quit
                    sub %19, %19, #1 // subtract one from the loop counter and run again
                    brz mainloop, #0    // go back to the top
                end:
                    // ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(bits[0] as u8));
                    // cswap x0.U (%25), x1.U (%27)
                    xor %30, %25, %27
                    msk %30, %18, %30
                    xor %25, %30, %25
                    xor %27, %30, %27
                    // cswap x0.W (%26), x1.W (%28)
                    xor %30, %26, %28
                    msk %30, %18, %30
                    xor %26, %30, %26
                    xor %28, %30, %28

                    // AFFINE SPLICE -- pass arguments to the affine block
                    psa %29, %25
                    psa %30, %26
                    // W.invert() in %21
                    // U in %29
                    // W in %30
                    // result in %31
                    // loop counter in %28

                    // from FieldElement.invert()
                        // let (t19, t3) = self.pow22501();   // t19: 249..0 ; t3: 3,1,0
                        // let t0  = self.square();           // 1         e_0 = 2^1
                        mul %0, %30, %30  // self is W, e.g. %30
                        // let t1  = t0.square().square();    // 3         e_1 = 2^3
                        mul %1, %0, %0
                        mul %1, %1, %1
                        // let t2  = self * &t1;              // 3,0       e_2 = 2^3 + 2^0
                        mul %2, %30, %1
                        // let t3  = &t0 * &t2;               // 3,1,0
                        mul %3, %0, %2
                        // let t4  = t3.square();             // 4,2,1
                        mul %4, %3, %3
                        // let t5  = &t2 * &t4;               // 4,3,2,1,0
                        mul %5, %2, %4

                        // let t6  = t5.pow2k(5);             // 9,8,7,6,5
                        psa %28, #5       // coincidentally, constant #5 is the number 5
                        mul %6, %5, %5
                    pow2k_5:
                        sub %28, %28, #1  // %28 = %28 - 1
                        brz pow2k_5_exit, %28
                        mul %6, %6, %6
                        brz pow2k_5, #0
                    pow2k_5_exit:
                        // let t7  = &t6 * &t5;               // 9,8,7,6,5,4,3,2,1,0
                        mul %7, %6, %5

                        // let t8  = t7.pow2k(10);            // 19..10
                        psa %28, #6        // constant #6 is the number 10
                        mul %8, %7, %7
                    pow2k_10:
                        sub %28, %28, #1
                        brz pow2k_10_exit, %28
                        mul %8, %8, %8
                        brz pow2k_10, #0
                    pow2k_10_exit:
                        // let t9  = &t8 * &t7;               // 19..0
                        mul %9, %8, %7

                        // let t10 = t9.pow2k(20);            // 39..20
                        psa %28, #7         // constant #7 is the number 20
                        mul %10, %9, %9
                    pow2k_20:
                        sub %28, %28, #1
                        brz pow2k_20_exit, %28
                        mul %10, %10, %10
                        brz pow2k_20, #0
                    pow2k_20_exit:
                        // let t11 = &t10 * &t9;              // 39..0
                        mul %11, %10, %9

                        // let t12 = t11.pow2k(10);           // 49..10
                        psa %28, #6         // constant #6 is the number 10
                        mul %12, %11, %11
                    pow2k_10b:
                        sub %28, %28, #1
                        brz pow2k_10b_exit, %28
                        mul %12, %12, %12
                        brz pow2k_10b, #0
                    pow2k_10b_exit:
                        // let t13 = &t12 * &t7;              // 49..0
                        mul %13, %12, %7

                        // let t14 = t13.pow2k(50);           // 99..50
                        psa %28, #8         // constant #8 is the number 50
                        mul %14, %13, %13
                    pow2k_50a:
                        sub %28, %28, #1
                        brz pow2k_50a_exit, %28
                        mul %14, %14, %14
                        brz pow2k_50a, #0
                    pow2k_50a_exit:
                        // let t15 = &t14 * &t13;             // 99..0
                        mul %15, %14, %13

                        // let t16 = t15.pow2k(100);          // 199..100
                        psa %28, #9         // constant #9 is the number 100
                        mul %16, %15, %15
                    pow2k_100:
                        sub %28, %28, #1
                        brz pow2k_100_exit, %28
                        mul %16, %16, %16
                        brz pow2k_100, #0
                    pow2k_100_exit:
                        // let t17 = &t16 * &t15;             // 199..0
                        mul %17, %16, %15

                        // let t18 = t17.pow2k(50);           // 249..50
                        psa %28, #8         // constant #8 is the number 50
                        mul %18, %17, %17
                    pow2k_50b:
                        sub %28, %28, #1
                        brz pow2k_50b_exit, %28
                        mul %18, %18, %18
                        brz pow2k_50b, #0
                    pow2k_50b_exit:
                        // let t19 = &t18 * &t13;             // 249..0
                        mul %19, %18, %13
                        //(t19, t3) // just a return value, values are already there, do nothing

                        //let t20 = t19.pow2k(5);            // 254..5
                        psa %28, #5
                        mul %20, %19, %19
                    pow2k_5_last:
                        sub %28, %28, #1
                        brz pow2k_5_last_exit, %28
                        mul %20, %20, %20
                        brz pow2k_5_last, #0
                    pow2k_5_last_exit:

                        //let t21 = &t20 * &t3;              // 254..5,3,1,0
                        mul %21, %20, %3

                    // u = &self.U * &self.W.invert()
                    mul %31, %29, %21
                    fin  // finish execution
            );
            let mut engine = engine_25519::Engine25519::new();
            let mut job = engine_25519::Job {
                id: None,
                ucode: [0; 1024],
                uc_len: mcode.len() as u32,
                uc_start: 0,
                window: Some(0),
                rf: [0; engine_25519::RF_SIZE_IN_U32],
            };

            for (&src, dst) in mcode.iter().zip(job.ucode.iter_mut()) {
                *dst = src as u32;
            }

            copy_to_rf(x0.U.to_bytes(), 25, &mut job.rf);
            copy_to_rf(x0.W.to_bytes(), 26, &mut job.rf);
            copy_to_rf(x1.U.to_bytes(), 27, &mut job.rf);
            copy_to_rf(x1.W.to_bytes(), 28, &mut job.rf);
            copy_to_rf(affine_u.to_bytes(), 24, &mut job.rf);
            copy_to_rf(scalar.bytes, 31, &mut job.rf);
            // load the number 254 into the loop index register
            copy_to_rf([
                254, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ], 19, &mut job.rf);

            // start the run
            let result_rf = engine.spawn_job(job).expect("couldn't run engine job");

            if false { // unmerged affine path
                x0.U = FieldElement::from_bytes(&copy_from_rf(25, &result_rf));
                x0.W = FieldElement::from_bytes(&copy_from_rf(26, &result_rf));

                // TODO: optimize this relatively innocuous looking call.
                // this consumes about 100ms runtime -- need to implement this using
                // curve25519 acceleration!
                x0.to_affine()
            } else {
                MontgomeryPoint(copy_from_rf(31, &result_rf))
            }
        } else {
            let mut engine = engine_25519::Engine25519::new();
            let job = engine_25519::MontgomeryJob {
                x0_u: x0.U.to_bytes(),
                x0_w: x0.W.to_bytes(),
                x1_u: x1.U.to_bytes(),
                x1_w: x1.W.to_bytes(),
                affine_u: affine_u.to_bytes(),
                scalar: scalar.bytes,
            };

            MontgomeryPoint(engine.montgomery_job(job).expect("couldn't run montgomery multiply job"))
        }
    }
    #[cfg(not(feature = "betrusted"))]
    fn mul(self, scalar: &'b Scalar) -> MontgomeryPoint {
        // Algorithm 8 of Costello-Smith 2017
        #[cfg(all(not(test),feature="betrusted"))] // due to issue https://github.com/rust-lang/rust/issues/59168, you will have to manually comment this out when running a test on the full system and not just this crate.
        log::warn!("sw montgomery multiply being used - check for build config errors!");
        let affine_u = FieldElement::from_bytes(&self.0);
        let mut x0 = ProjectivePoint::identity();
        let mut x1 = ProjectivePoint {
            U: affine_u,
            W: FieldElement::one(),
        };

        let bits: [i8; 256] = scalar.bits();

        for i in (0..255).rev() {
            let choice: u8 = (bits[i + 1] ^ bits[i]) as u8;

            debug_assert!(choice == 0 || choice == 1);

            ProjectivePoint::conditional_swap(&mut x0, &mut x1, choice.into());
            differential_add_and_double(&mut x0, &mut x1, &affine_u);
        }
        ProjectivePoint::conditional_swap(&mut x0, &mut x1, Choice::from(bits[0] as u8));

        x0.to_affine()
    }
}

impl<'b> MulAssign<&'b Scalar> for MontgomeryPoint {
    fn mul_assign(&mut self, scalar: &'b Scalar) {
        *self = (self as &MontgomeryPoint) * scalar;
    }
}

impl<'a, 'b> Mul<&'b MontgomeryPoint> for &'a Scalar {
    type Output = MontgomeryPoint;

    fn mul(self, point: &'b MontgomeryPoint) -> MontgomeryPoint {
        point * self
    }
}

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use constants;
    use core::convert::TryInto;

    use rand_core::OsRng;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_bincode_basepoint_roundtrip() {
        use bincode;

        let encoded = bincode::serialize(&constants::X25519_BASEPOINT).unwrap();
        let decoded: MontgomeryPoint = bincode::deserialize(&encoded).unwrap();

        assert_eq!(encoded.len(), 32);
        assert_eq!(decoded, constants::X25519_BASEPOINT);

        let raw_bytes = constants::X25519_BASEPOINT.as_bytes();
        let bp: MontgomeryPoint = bincode::deserialize(raw_bytes).unwrap();
        assert_eq!(bp, constants::X25519_BASEPOINT);
    }

    /// Test Montgomery -> Edwards on the X/Ed25519 basepoint
    #[test]
    fn basepoint_montgomery_to_edwards() {
        // sign bit = 0 => basepoint
        assert_eq!(
            constants::ED25519_BASEPOINT_POINT,
            constants::X25519_BASEPOINT.to_edwards(0).unwrap()
        );
        // sign bit = 1 => minus basepoint
        assert_eq!(
            - constants::ED25519_BASEPOINT_POINT,
            constants::X25519_BASEPOINT.to_edwards(1).unwrap()
        );
    }

    /// Test Edwards -> Montgomery on the X/Ed25519 basepoint
    #[test]
    fn basepoint_edwards_to_montgomery() {
        assert_eq!(
            constants::ED25519_BASEPOINT_POINT.to_montgomery(),
            constants::X25519_BASEPOINT
        );
    }

    /// Check that Montgomery -> Edwards fails for points on the twist.
    #[test]
    fn montgomery_to_edwards_rejects_twist() {
        let one = FieldElement::one();

        // u = 2 corresponds to a point on the twist.
        let two = MontgomeryPoint((&one+&one).to_bytes());

        assert!(two.to_edwards(0).is_none());

        // u = -1 corresponds to a point on the twist, but should be
        // checked explicitly because it's an exceptional point for the
        // birational map.  For instance, libsignal will accept it.
        let minus_one = MontgomeryPoint((-&one).to_bytes());

        assert!(minus_one.to_edwards(0).is_none());
    }

    #[test]
    fn eq_defined_mod_p() {
        let mut u18_bytes = [0u8; 32]; u18_bytes[0] = 18;
        let u18 = MontgomeryPoint(u18_bytes);
        let u18_unred = MontgomeryPoint([255; 32]);

        assert_eq!(u18, u18_unred);
    }

    #[test]
    fn montgomery_ladder_matches_edwards_scalarmult() {
        let mut csprng: OsRng = OsRng;

        let s: Scalar = Scalar::random(&mut csprng);
        let p_edwards: EdwardsPoint = &constants::ED25519_BASEPOINT_TABLE * &s;
        let p_montgomery: MontgomeryPoint = p_edwards.to_montgomery();

        let expected = s * p_edwards;
        let result = s * p_montgomery;

        assert_eq!(result, expected.to_montgomery())
    }

    const ELLIGATOR_CORRECT_OUTPUT: [u8; 32] = [
        0x5f, 0x35, 0x20, 0x00, 0x1c, 0x6c, 0x99, 0x36, 0xa3, 0x12, 0x06, 0xaf, 0xe7, 0xc7, 0xac,
        0x22, 0x4e, 0x88, 0x61, 0x61, 0x9b, 0xf9, 0x88, 0x72, 0x44, 0x49, 0x15, 0x89, 0x9d, 0x95,
        0xf4, 0x6e,
    ];

    #[test]
    #[cfg(feature = "std")] // Vec
    fn montgomery_elligator_correct() {
        let bytes: std::vec::Vec<u8> = (0u8..32u8).collect();
        let bits_in: [u8; 32] = (&bytes[..]).try_into().expect("Range invariant broken");

        let fe = FieldElement::from_bytes(&bits_in);
        let eg = elligator_encode(&fe);
        assert_eq!(eg.to_bytes(), ELLIGATOR_CORRECT_OUTPUT);
    }

    #[test]
    fn montgomery_elligator_zero_zero() {
        let zero = [0u8; 32];
        let fe = FieldElement::from_bytes(&zero);
        let eg = elligator_encode(&fe);
        assert_eq!(eg.to_bytes(), zero);
    }
}
