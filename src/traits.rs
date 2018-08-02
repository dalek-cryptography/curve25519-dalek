// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// Copyright (c) 2016-2018 Isis Lovecruft, Henry de Valence
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Module for common traits.

use core::borrow::Borrow;

use subtle;

use scalar::Scalar;

// ------------------------------------------------------------------------
// Public Traits
// ------------------------------------------------------------------------

/// Trait for getting the identity element of a point type.
pub trait Identity {
    /// Returns the identity element of the curve.
    /// Can be used as a constructor.
    fn identity() -> Self;
}

/// Trait for testing if a curve point is equivalent to the identity point.
pub trait IsIdentity {
    /// Return true if this element is the identity element of the curve.
    fn is_identity(&self) -> bool;
}

/// Implement generic identity equality testing for a point representations
/// which have constant-time equality testing and a defined identity
/// constructor.
impl<T> IsIdentity for T
where
    T: subtle::ConstantTimeEq + Identity,
{
    fn is_identity(&self) -> bool {
        self.ct_eq(&T::identity()).unwrap_u8() == 1u8
    }
}

/// A trait for constant-time multiscalar multiplication without precomputation.
pub trait MultiscalarMul {
    /// The type of point being multiplied, e.g., `RistrettoPoint`.
    type Point;

    /// Given an iterator of (possibly secret) scalars and an iterator of
    /// public points, compute
    /// $$
    /// Q = c\_1 P\_1 + \cdots + c\_n P\_n.
    /// $$
    ///
    /// It is an error to call this function with two iterators of different lengths.
    ///
    /// # Examples
    ///
    /// The trait bound aims for maximum flexibility: the inputs must be
    /// convertable to iterators (`I: IntoIter`), and the iterator's items
    /// must be `Borrow<Scalar>` (or `Borrow<Point>`), to allow
    /// iterators returning either `Scalar`s or `&Scalar`s.
    ///
    /// ```
    /// use curve25519_dalek::constants;
    /// use curve25519_dalek::traits::MultiscalarMul;
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // Some scalars
    /// let a = Scalar::from(87329482u64);
    /// let b = Scalar::from(37264829u64);
    /// let c = Scalar::from(98098098u64);
    ///
    /// // Some points
    /// let P = constants::RISTRETTO_BASEPOINT_POINT;
    /// let Q = P + P;
    /// let R = P + Q;
    ///
    /// // A1 = a*P + b*Q + c*R
    /// let abc = [a,b,c];
    /// let A1 = RistrettoPoint::multiscalar_mul(&abc, &[P,Q,R]);
    /// // Note: (&abc).into_iter(): Iterator<Item=&Scalar>
    ///
    /// // A2 = (-a)*P + (-b)*Q + (-c)*R
    /// let minus_abc = abc.iter().map(|x| -x);
    /// let A2 = RistrettoPoint::multiscalar_mul(minus_abc, &[P,Q,R]);
    /// // Note: minus_abc.into_iter(): Iterator<Item=Scalar>
    ///
    /// assert_eq!(A1.compress(), (-A2).compress());
    /// ```
    fn multiscalar_mul<I, J>(scalars: I, points: J) -> Self::Point
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Self::Point>;
}

/// A trait for variable-time multiscalar multiplication without precomputation.
pub trait VartimeMultiscalarMul {
    /// The type of point being multiplied, e.g., `RistrettoPoint`.
    type Point;

    /// Given an iterator of public scalars and an iterator of
    /// `Option`s of points, compute either `Some(Q)`, where
    /// $$
    /// Q = c\_1 P\_1 + \cdots + c\_n P\_n,
    /// $$
    /// if all points were `Some(P_i)`, or else return `None`.
    ///
    /// This function is particularly useful when verifying statements
    /// involving compressed points.  Accepting `Option<Point>` allows
    /// inlining point decompression into the multiscalar call,
    /// avoiding the need for temporary buffers.
    /// ```
    /// use curve25519_dalek::constants;
    /// use curve25519_dalek::traits::VartimeMultiscalarMul;
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // Some scalars
    /// let a = Scalar::from(87329482u64);
    /// let b = Scalar::from(37264829u64);
    /// let c = Scalar::from(98098098u64);
    /// let abc = [a,b,c];
    ///
    /// // Some points
    /// let P = constants::RISTRETTO_BASEPOINT_POINT;
    /// let Q = P + P;
    /// let R = P + Q;
    /// let PQR = [P, Q, R];
    ///
    /// let compressed = [P.compress(), Q.compress(), R.compress()];
    ///
    /// // Now we can compute A1 = a*P + b*Q + c*R using P, Q, R:
    /// let A1 = RistrettoPoint::vartime_multiscalar_mul(&abc, &PQR);
    ///
    /// // Or using the compressed points:
    /// let A2 = RistrettoPoint::optional_multiscalar_mul(
    ///     &abc,
    ///     compressed.iter().map(|pt| pt.decompress()),
    /// );
    ///
    /// assert_eq!(A2, Some(A1));
    ///
    /// // It's also possible to mix compressed and uncompressed points:
    /// let A3 = RistrettoPoint::optional_multiscalar_mul(
    ///     abc.iter()
    ///         .chain(abc.iter()),
    ///     compressed.iter().map(|pt| pt.decompress())
    ///         .chain(PQR.iter().map(|&pt| Some(pt))),
    /// );
    ///
    /// assert_eq!(A3, Some(A1+A1));
    /// ```
    fn optional_multiscalar_mul<I, J>(scalars: I, points: J) -> Option<Self::Point>
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator<Item = Option<Self::Point>>;

    /// Given an iterator of public scalars and an iterator of
    /// public points, compute
    /// $$
    /// Q = c\_1 P\_1 + \cdots + c\_n P\_n,
    /// $$
    /// using variable-time operations.
    ///
    /// It is an error to call this function with two iterators of different lengths.
    ///
    /// # Examples
    ///
    /// The trait bound aims for maximum flexibility: the inputs must be
    /// convertable to iterators (`I: IntoIter`), and the iterator's items
    /// must be `Borrow<Scalar>` (or `Borrow<Point>`), to allow
    /// iterators returning either `Scalar`s or `&Scalar`s.
    ///
    /// ```
    /// use curve25519_dalek::constants;
    /// use curve25519_dalek::traits::VartimeMultiscalarMul;
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    /// use curve25519_dalek::scalar::Scalar;
    ///
    /// // Some scalars
    /// let a = Scalar::from(87329482u64);
    /// let b = Scalar::from(37264829u64);
    /// let c = Scalar::from(98098098u64);
    ///
    /// // Some points
    /// let P = constants::RISTRETTO_BASEPOINT_POINT;
    /// let Q = P + P;
    /// let R = P + Q;
    ///
    /// // A1 = a*P + b*Q + c*R
    /// let abc = [a,b,c];
    /// let A1 = RistrettoPoint::vartime_multiscalar_mul(&abc, &[P,Q,R]);
    /// // Note: (&abc).into_iter(): Iterator<Item=&Scalar>
    ///
    /// // A2 = (-a)*P + (-b)*Q + (-c)*R
    /// let minus_abc = abc.iter().map(|x| -x);
    /// let A2 = RistrettoPoint::vartime_multiscalar_mul(minus_abc, &[P,Q,R]);
    /// // Note: minus_abc.into_iter(): Iterator<Item=Scalar>
    ///
    /// assert_eq!(A1.compress(), (-A2).compress());
    /// ```
    #[allow(non_snake_case)]
    fn vartime_multiscalar_mul<I, J>(scalars: I, points: J) -> Self::Point
    where
        I: IntoIterator,
        I::Item: Borrow<Scalar>,
        J: IntoIterator,
        J::Item: Borrow<Self::Point>,
        Self::Point: Clone,
    {
        Self::optional_multiscalar_mul(
            scalars,
            points.into_iter().map(|P| Some(P.borrow().clone()))
        ).unwrap()
    }
}

// ------------------------------------------------------------------------
// Private Traits
// ------------------------------------------------------------------------

/// Trait for checking whether a point is on the curve.
///
/// This trait is only for debugging/testing, since it should be
/// impossible for a `curve25519-dalek` user to construct an invalid
/// point.
pub(crate) trait ValidityCheck {
    /// Checks whether the point is on the curve. Not CT.
    fn is_valid(&self) -> bool;
}
