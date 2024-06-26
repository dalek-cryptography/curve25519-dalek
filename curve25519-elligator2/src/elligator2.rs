// -*- mode: rust; -*-

//! Functions mapping curve points to representative (random) values
//! and back again.
//!
//! ## Usage
//!
//! ```rust ignore
//! use rand::RngCore;
//! use curve25519_elligator2::{RFC9380, MapToPointVariant};
//!
//! type A = RFC9380;
//!
//! let mut rng = rand::thread_rng();
//! let mut privkey = [0_u8;32];
//! rng.fill_bytes(&mut privkey);
//! let tweak = rng.next_u32() as u8;
//!
//! let public_key = A::mul_base_clamped(privkey);
//! // only about half of points are representable, so this will fail ~50% of the time.
//! let representative = A::to_representative(&privkey, tweak)
//!     .expect("non representable point :(" );
//!
//! // The representative gets distributed in place of the public key,
//! // it can then be converted back into the curve25519 point.
//! let public_key1 = A::from_representative(&representative).unwrap();
//!
//! # let p = public_key.to_montgomery().to_bytes();
//! # let p1 = public_key1.to_montgomery().to_bytes();
//! # assert_eq!(hex::encode(&p), hex::encode(&p1));
//! ```
//!
//! The elligator2 transforms can also be applied to [`MontgomeryPoint`] and
//! [`EdwardsPoint`] objects themselves.
//!
//! ```rust
//! use rand::RngCore;
//! use curve25519_elligator2::{RFC9380, Randomized, MapToPointVariant, MontgomeryPoint, EdwardsPoint};
//!
//! // Montgomery Points can be mapped to and from elligator representatives
//! // using any algorithm variant.
//! let tweak = rand::thread_rng().next_u32() as u8;
//! let mont_point = MontgomeryPoint::default(); // example point known to be representable
//! let r = mont_point.to_representative::<RFC9380>(tweak).unwrap();
//!
//! _ = MontgomeryPoint::from_representative::<RFC9380>(&r).unwrap();
//!
//! // Edwards Points can be transformed as well.
//! let edw_point = EdwardsPoint::default(); // example point known to be representable
//! let r = edw_point.to_representative::<Randomized>(tweak).unwrap();
//!
//! _ = EdwardsPoint::from_representative::<Randomized>(&r).unwrap();
//! ```
//!
//! ### Generating Representable Points.
//!
//! As only about 50% of points are actually representable using elligator2. In
//! order to guarantee that generated points are representable we can just try
//! in a loop as the probability of overall success (given a proper source of
//! randomness) over `N` trials is approximately `P_success = 1 - (0.5)^N`.
//!
//! ```rust
//! use rand::{RngCore, CryptoRng};
//! use curve25519_elligator2::{MapToPointVariant, Randomized};
//!
//! type A = Randomized;
//! const RETRY_LIMIT: usize = 64;
//!
//! pub fn key_from_rng<R: RngCore + CryptoRng>(mut csprng: R) -> ([u8;32], u8) {
//!     let mut private = [0_u8;32];
//!     csprng.fill_bytes(&mut private);
//!
//!     // The tweak only needs generated once as it doesn't affect the overall
//!     // validity of the elligator2 representative.
//!     let tweak = csprng.next_u32() as u8;
//!
//!     let mut repres: Option<[u8; 32]> =
//!         A::to_representative(&private, tweak).into();
//!
//!     for _ in 0..RETRY_LIMIT {
//!         if repres.is_some() {
//!             return (private, tweak)
//!         }
//!         csprng.fill_bytes(&mut private);
//!         repres = A::to_representative(&private, tweak).into();
//!     }
//!
//!     panic!("failed to generate representable secret, bad RNG provided");
//! }
//!
//! let mut rng = rand::thread_rng();
//! let k = key_from_rng(&mut rng);
//! ```
//!
//! ### Which variant is right for me?
//!
//! As the variants are not equivalent and do not generate the same 1) public key
//! given a private key (`mul_base_clamped`) 2) representative given a private
//! key (`to_representative`), the variant you choose will depend on your use case.
//!
//! The major difference in use case depends on
//! whether you need to convert public keys to randomized representatives, and
//! those representatives need to be **indistinguishable from uniform random**.
//! If this is the case, use [`Randomized`].
//! If this does not describe your use case, for example, you are interested in
//! using this implementation for something like `Hash2Curve`, you should instead
//! use [`RFC9380`].
//!
//!
//! If you are unsure, you will likely want to use the [`RFC9380`] variant.
//!
//! ## Security
//!
//! As with the backing curve25519-dalek crate, all operations are implemented
//! using constant-time logic (no secret-dependent branches,
//! no secret-dependent memory accesses), unless specifically marked as being
//! variable-time code.
//!
//! The [`Randomized`] variant provides a stronger guarantee of being
//! indistinguishable from uniform randomness, both through statistical analysis
//! and computational transformations. This is comes at the cost of compatability
//! with the `Hash2Curve` RFC as the algorithms defined by RFC 9380 and implemented
//! in the [`RFC9380`] variant can be computationally transformed such that they
//! are distinguishable from unifrom random points of the field.
//!

use crate::constants::{MONTGOMERY_A, MONTGOMERY_A_NEG, SQRT_M1};
use crate::field::FieldElement;
use crate::montgomery::MontgomeryPoint;
use crate::EdwardsPoint;

use cfg_if::cfg_if;
use subtle::{
    Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
    CtOption,
};

/// bitmask for a single byte when clearing the high order two bits of a representative
pub(crate) const MASK_UNSET_BYTE: u8 = 0x3f;
/// bitmask for a single byte when setting the high order two bits of a representative
pub(crate) const MASK_SET_BYTE: u8 = 0xc0;

/// (p - 1) / 2 = 2^254 - 10
pub(crate) const DIVIDE_MINUS_P_1_2_BYTES: [u8; 32] = [
    0xf6, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f,
];

/// Common interface for the different ways to compute the elligator2 forward
/// and reverse transformations.
pub trait MapToPointVariant {
    /// Takes a public representative and returns an Edwards curve field element
    /// if one exists.
    fn from_representative(representative: &[u8; 32]) -> CtOption<EdwardsPoint>;

    /// Takes a private key value and gets a byte representation of the public representative.
    ///
    /// The `tweak` parameter is used to adjust the computed representative making
    /// it computationally indistinguishable from uniform random. If this property
    /// is not required then the provided tweak value does not matter.
    fn to_representative(point: &[u8; 32], tweak: u8) -> CtOption<[u8; 32]>;

    /// Provides direct access to the scalar base multiplication that will produce
    /// a public key point from a private key point.
    fn mul_base_clamped(bytes: [u8; 32]) -> EdwardsPoint {
        EdwardsPoint::mul_base_clamped(bytes)
    }
}

/// Converts between a point on elliptic curve E (Curve25519) and an element of
/// the finite field F over which E is defined. See section 6.7.1 of
/// [RFC 9380 specification](https://datatracker.ietf.org/doc/rfc9380/).
///
/// We add randomness to the top two bits of the generated representative as the
/// generated values always 0 in those two bits. Similarly we clear the top two
/// bits of a given representative FieldElement before mapping it to the curve.
pub struct RFC9380;

impl MapToPointVariant for RFC9380 {
    fn from_representative(representative: &[u8; 32]) -> CtOption<EdwardsPoint> {
        let mut r = *representative;
        r[31] &= MASK_UNSET_BYTE;
        let representative = FieldElement::from_bytes(&r);
        let (x, y) = map_fe_to_edwards(&representative);
        let point = EdwardsPoint {
            X: x,
            Y: y,
            Z: FieldElement::ONE,
            T: &x * &y,
        };
        CtOption::new(point, Choice::from(1))
    }

    fn to_representative(point: &[u8; 32], tweak: u8) -> CtOption<[u8; 32]> {
        let pubkey = EdwardsPoint::mul_base_clamped(*point).to_montgomery();
        let v_in_sqrt = v_in_sqrt(point);
        let p: Option<[u8; 32]> = point_to_representative(&pubkey, v_in_sqrt.into()).into();
        match p {
            None => CtOption::new([0u8; 32], Choice::from(0)),
            Some(mut a) => {
                a[31] |= MASK_SET_BYTE & tweak;
                CtOption::new(a, Choice::from(1))
            }
        }
    }
}

/// Converts between a point on elliptic curve E (Curve25519) and an element of
/// the finite field F over which E is defined. Ensures that generated field
/// elements are indistinguishable from uniform random at the cost of compatability
/// with RFC 9380.
///
/// Differs from [`RFC9380`] in the implementation of the `to_representative` function
/// as RFC9380 misses a computational distinguisher that would allow an attacker to
/// distinguish the representative from random bytes.
pub struct Randomized;

impl MapToPointVariant for Randomized {
    fn from_representative(representative: &[u8; 32]) -> CtOption<EdwardsPoint> {
        RFC9380::from_representative(representative)
    }

    fn to_representative(point: &[u8; 32], tweak: u8) -> CtOption<[u8; 32]> {
        let u = EdwardsPoint::mul_base_clamped_dirty(*point);
        representative_from_pubkey(&u, tweak)
    }

    fn mul_base_clamped(bytes: [u8; 32]) -> EdwardsPoint {
        EdwardsPoint::mul_base_clamped_dirty(bytes)
    }
}

#[cfg(feature = "digest")]
/// Converts between a point on elliptic curve E (Curve25519) and an element of
/// the finite field F over which E is defined. Supports older implementations
/// with a common implementation bug (Signal, Kleshni-C).
///
/// In contrast to the [`RFC9380`] variant, `Legacy` does NOT assume that input values are always
/// going to be the least-square-root representation of the field element.
/// This is divergent from the specifications for both elligator2 and RFC 9380,
/// however, some older implementations miss this detail. This allows us to be
/// compatible with those alternate implementations if necessary, since the
/// resulting point will be different for inputs with either of the
/// high-order two bits set. The kleshni C and Signal implementations are examples
/// of libraries that don't always use the least square root.
///
/// In general this mode should NOT be used unless there is a very specific
/// reason to do so.
///
// We return the LSR for to_representative values. This is here purely for testing
// compatability and ensuring that we understand the subtle differences that can
// influence proper implementation.
pub struct Legacy;

#[cfg(feature = "digest")]
impl MapToPointVariant for Legacy {
    fn from_representative(representative: &[u8; 32]) -> CtOption<EdwardsPoint> {
        let representative = FieldElement::from_bytes(representative);
        let (x, y) = map_fe_to_edwards(&representative);
        let point = EdwardsPoint {
            X: x,
            Y: y,
            Z: FieldElement::ONE,
            T: &x * &y,
        };
        CtOption::new(point, Choice::from(1))
    }

    fn to_representative(point: &[u8; 32], _tweak: u8) -> CtOption<[u8; 32]> {
        let pubkey = EdwardsPoint::mul_base_clamped(*point);
        let v_in_sqrt = v_in_sqrt_pubkey_edwards(&pubkey);
        point_to_representative(&MontgomeryPoint(*point), v_in_sqrt.into())
    }
}

// ===========================================================================
// Montgomery and Edwards Interfaces
// ===========================================================================

impl MontgomeryPoint {
    #[cfg(feature = "elligator2")]
    /// Perform the Elligator2 mapping to a [`MontgomeryPoint`].
    ///
    /// Calculates a point on elliptic curve E (Curve25519) from an element of
    /// the finite field F over which E is defined. See section 6.7.1 of the
    /// RFC. It is assumed that input values are always going to be the
    /// least-square-root representation of the field element in allignment
    /// with both the elligator2 specification and RFC9380.
    ///
    /// The input r and output P are elements of the field F. Note that
    /// the output P is a point on the Montgomery curve and as such it's byte
    /// representation is distinguishable from uniform random.
    ///
    /// Input:
    ///     * r -> an element of field F.
    ///
    /// Output:
    ///     * P - a point on the Montgomery elliptic curve.
    ///
    /// See <https://datatracker.ietf.org/doc/rfc9380/>
    pub fn map_to_point(r: &[u8; 32]) -> MontgomeryPoint {
        let mut clamped = *r;
        clamped[31] &= MASK_UNSET_BYTE;
        let r_0 = FieldElement::from_bytes(&clamped);
        let (p, _) = map_fe_to_montgomery(&r_0);
        MontgomeryPoint(p.as_bytes())
    }

    /// Maps a representative to a curve point.
    ///
    /// This function is the inverse of `to_representative`.
    pub fn from_representative<T: MapToPointVariant>(representative: &[u8; 32]) -> Option<Self> {
        let b: Option<EdwardsPoint> = T::from_representative(representative).into();
        b.map(|x| x.to_montgomery())
    }

    /// Mapts a point on the curve to a representative.
    pub fn to_representative<T: MapToPointVariant>(&self, tweak: u8) -> Option<[u8; 32]> {
        T::to_representative(&self.0, tweak).into()
    }
}

impl EdwardsPoint {
    #[cfg(feature = "elligator2")]
    /// Perform the Elligator2 mapping to an [`EdwardsPoint`].
    ///
    /// Calculates a point on elliptic curve E (Curve25519) from an element of
    /// the finite field F over which E is defined. See section 6.7.1 of the
    /// RFC.
    ///
    /// The input r and output P are elements of the field F. Note that
    /// the output P is a point on the edwards curve and as such it's byte
    /// representation is distinguishable from uniform random.
    ///
    /// Input:
    ///     * r -> an element of field F.
    ///
    /// Output:
    ///     * P - a point on the Edwards elliptic curve.
    ///
    /// See <https://datatracker.ietf.org/doc/rfc9380/>
    pub fn map_to_point(r: &[u8; 32]) -> EdwardsPoint {
        let mut clamped = *r;
        clamped[31] &= MASK_UNSET_BYTE;
        let r_0 = FieldElement::from_bytes(&clamped);
        let (x, y) = map_fe_to_edwards(&r_0);
        Self::from_xy(&x, &y)
    }

    #[cfg(feature = "elligator2")]
    fn from_xy(x: &FieldElement, y: &FieldElement) -> EdwardsPoint {
        let z = FieldElement::ONE;
        let t = x * y;

        EdwardsPoint {
            X: *x,
            Y: *y,
            Z: z,
            T: t,
        }
    }

    /// Maps a representative to a curve point.
    ///
    /// This function is the inverse of `to_representative`.
    pub fn from_representative<T: MapToPointVariant>(representative: &[u8; 32]) -> Option<Self> {
        T::from_representative(representative).into()
    }

    /// Mapts a point on the curve to a representative.
    pub fn to_representative<T: MapToPointVariant>(&self, tweak: u8) -> Option<[u8; 32]> {
        T::to_representative(&self.to_montgomery().0, tweak).into()
    }
}

// ===========================================================================
// Randomized implementation
// ===========================================================================

/// Gets a public representative for a key pair using the private key (RFC 9380).
///
/// The `tweak` parameter is used to adjust the computed representative making
/// it computationally indistinguishable from uniform random. If this property
/// is not required then the provided tweak value does not matter.
///
/// The tweak allows us to overcome three limitations:
/// - Representatives are not always canonical.
/// - Bit 255 (the most significant bit) was always zero.
/// - Only points from the large prime-order subgroup are represented.
///
/// In order for the returned representative to be canonical a tweak to the
/// high order two bits must be applied.
/// ```txt
/// [An adversary could] observe a representative, interpret it as a field
/// element, square it, then take the square root using the same
/// non-canonical square root algorithm. With representatives produced by
/// an affected version of [the elligator2 implementation], the output of
/// the square-then-root operation would always match the input. With
/// random strings, the output would match only half the time.
/// ```
///
/// For a more in-depth explanation see:
/// <https://github.com/agl/ed25519/issues/27>
/// <https://www.bamsoftware.com/papers/fep-flaws/>
pub fn representative_from_privkey(privkey: &[u8; 32], tweak: u8) -> Option<[u8; 32]> {
    RFC9380::to_representative(privkey, tweak).into()
}

cfg_if! {
    if #[cfg(curve25519_dalek_bits = "64")] {
        /// Low order point Edwards x-coordinate `sqrt((sqrt(d + 1) + 1) / d)`.
        const LOW_ORDER_POINT_X: FieldElement = FieldElement::from_limbs([
            0x00014646c545d14a,
            0x0006027cbc471bd4,
            0x0003792aed7064f1,
            0x0005147499cc991c,
            0x0001fd5b9a006394,
        ]);
        /// Low order point Edwards y-coordinate `-lop_x * sqrtm1`
        const LOW_ORDER_POINT_Y: FieldElement = FieldElement::from_limbs([
            0x0007b2c28f95e826,
            0x0006513e9868b604,
            0x0006b37f57c263bf,
            0x0004589c99e36982,
            0x00005fc536d88023,
        ]);
        const FE_MINUS_TWO: FieldElement = FieldElement::from_limbs([
            2251799813685227,
            2251799813685247,
            2251799813685247,
            2251799813685247,
            2251799813685247,
        ]);
    }
    else if #[cfg(curve25519_dalek_bits = "32")] {
        const LOW_ORDER_POINT_X: FieldElement = FieldElement::from_limbs([
            0x0145d14a, 0x005191b1, 0x00471bd4, 0x01809f2f, 0x017064f1,
            0x00de4abb, 0x01cc991c, 0x01451d26, 0x02006394, 0x007f56e6
        ]);
        const LOW_ORDER_POINT_Y: FieldElement = FieldElement::from_limbs([
            0x0395e826, 0x01ecb0a3, 0x0068b604, 0x01944fa6, 0x03c263bf,
            0x01acdfd5, 0x01e36982, 0x01162726, 0x02d88023, 0x0017f14d
        ]);
        const FE_MINUS_TWO: FieldElement = FieldElement::from_limbs([
            0x03ffffeb, 0x01ffffff, 0x03ffffff, 0x01ffffff, 0x03ffffff,
            0x01ffffff, 0x03ffffff, 0x01ffffff, 0x03ffffff, 0x01ffffff
        ]);
    }
}

#[allow(clippy::identity_op)]
fn select_low_order_point(a: &FieldElement, b: &FieldElement, cofactor: u8) -> FieldElement {
    // bit 0
    let c0 = !Choice::from((cofactor >> 1) & 1);
    let out = FieldElement::conditional_select(b, &FieldElement::ZERO, c0);

    // bit 1
    let c1 = !Choice::from((cofactor >> 0) & 1);
    let mut out = FieldElement::conditional_select(a, &out, c1);

    // bit 2
    let c2 = Choice::from((cofactor >> 2) & 1);
    out.conditional_negate(c2);
    out
}

#[cfg(feature = "elligator2")]
impl EdwardsPoint {
    /// Multiply the basepoint by `clamp_integer(bytes)`. For a description of clamping, see
    /// [`clamp_integer`]. This variant integrates a low order point into the resulting
    /// value in order to prevent a computational distinguisher attack that would allow
    /// an adversary to check if representatives are always points or order L when multiplied
    /// with the base point.
    ///
    /// > A scalar multiplication with the base point, even one that does not clamp the scalar, will always yield a point of order L. That is, for all s: `L × (s × B) = zero`.
    /// > A random Elligator2 representative however will only map to a point of order L 12.5% of the time.
    ///
    /// [`clamp_integer`]: crate::scalar::clamp_integer
    pub fn mul_base_clamped_dirty(privkey: [u8; 32]) -> Self {
        let lop_x = select_low_order_point(&LOW_ORDER_POINT_X, &SQRT_M1, privkey[0]);
        let (cofactor, _) = privkey[0].overflowing_add(2);
        let lop_y = select_low_order_point(&LOW_ORDER_POINT_Y, &FieldElement::ONE, cofactor);
        let lop_t = &lop_x * &lop_y;

        let low_order_point = EdwardsPoint {
            X: lop_x,
            Y: lop_y,
            Z: FieldElement::ONE,
            T: lop_t,
        };

        // add the low order point to the public key
        EdwardsPoint::mul_base_clamped(privkey) + low_order_point
    }
}

/// Gets the pulic representative using the ['EdwardsPoint'] public key.
fn representative_from_pubkey(pubkey: &EdwardsPoint, tweak: u8) -> CtOption<[u8; 32]> {
    let mut t1 = FieldElement::from_bytes(&pubkey.to_montgomery().0);

    // -2 * u * (u + A)
    let t2 = &t1 + &MONTGOMERY_A;
    let t3 = &(&t1 * &t2) * &FE_MINUS_TWO;

    let (is_sq, mut t3) = FieldElement::sqrt_ratio_i(&FieldElement::ONE, &t3);

    t1 = FieldElement::conditional_select(&t1, &t2, Choice::from(tweak & 1));
    t3 = &t1 * &t3;
    t1 = &t3 + &t3;

    let tmp: u8 = t1.as_bytes()[0] & 1;
    t3.conditional_negate(Choice::from(tmp));

    // get representative and pad with bits from the tweak.
    let mut representative = t3.as_bytes();
    representative[31] |= tweak & MASK_SET_BYTE;

    CtOption::new(representative, is_sq)
}

// ===========================================================================
// RFC9380 (and Legacy) implementation
// ===========================================================================

/// This function is used to map a curve point (i.e. an x25519 public key)
/// to a point that is effectively indistinguishable from random noise.
///
/// This operation may fail because not all curve points are capable of being
/// hidden. On failure, this function will return None.
///
/// This implementation is adapted from both:
/// - [kleshni C implementation](https://github.com/Kleshni/Elligator-2)
/// - [agl/ed25519 golang forks](https://gitlab.com/yawning/edwards25519-extra)
///
///
/// Note: the output field elements of this function are uniformly
/// distributed among the nonnegative field elements, but only if the
/// input points are also uniformly distributed among all points of
/// the curve. In particular, if the inputs are only selected from
/// members of the prime order group, then the outputs are
/// distinguishable from random.
///
/// # Inputs
///
/// * `point`: the \\(u\\)-coordinate of a point on the curve. Not all
///   points map to field elements.
///
/// * `v_in_sqrt`: true if the \\(v\\)-coordinate of the point is negative.
///
/// # Returns
///
/// Either `None`, if the point couldn't be mapped, or `Some(fe)` such
/// that `fe` is nonnegative and `map_to_point(&fe) == point`.
///
/// [elligator paper](https://elligator.cr.yp.to/elligator-20130828.pdf)
/// [elligator site](https://elligator.org/)
///
pub(crate) fn point_to_representative(
    point: &MontgomeryPoint,
    v_in_sqrt: bool,
) -> CtOption<[u8; 32]> {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // a := point
    let a = &FieldElement::from_bytes(&point.0);
    let a_neg = -a;

    let is_encodable = is_encodable(a);

    // Calculate r1 = sqrt(-a/(2*(a+A)))
    let (_r1_sqrt, r1) = FieldElement::sqrt_ratio_i(
        &a_neg,
        &(&(a + &MONTGOMERY_A) * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // Calculate  r0 = sqrt(-(a+A)/(2a))
    let (_r0_sqrt, r0) = FieldElement::sqrt_ratio_i(
        &(&a_neg - &MONTGOMERY_A),
        &(a * &(&FieldElement::ONE + &FieldElement::ONE)),
    );

    // if v_in_sqrt root=r0 otherwise r1
    let mut b = FieldElement::conditional_select(&r1, &r0, Choice::from(v_in_sqrt as u8));

    // If root > (p - 1) / 2, root := -root
    let negate = divide_minus_p_1_2.ct_gt(&b);
    FieldElement::conditional_negate(&mut b, negate);

    CtOption::new(b.as_bytes(), is_encodable)
}

/// Determines whether a point is encodable as a representative. Approximately
/// 50% of points are not encodable.
#[inline]
fn is_encodable(u: &FieldElement) -> Choice {
    let b0 = u + &MONTGOMERY_A;
    let b1 = &(&(&b0.square().square() * &b0.square()) * &b0) * u; // b1 = u * (u + A)^7
    let c = b1.pow_p58();

    let b2 = &(&b0.square().square().square() * &b0.square().square()) * &b0.square(); // (u + A)^14
    let mut chi = &(&c.square().square() * &u.square()) * &b2; // chi = -c^4 * u^2 * (u + A)^14
    chi = -&chi;

    let chi_bytes = chi.as_bytes();

    // chi[1] is either 0 or 0xff
    chi_bytes[1].ct_eq(&0_u8)
}

///  `high_y` - Montgomery points can have have two different values for a
///  single X coordinate (based on sign). The Kleshni implementation determines
///  which sign value to use with this function.
///
///  If the point is 0, this should be ignored.
#[inline]
pub(crate) fn high_y(d: &FieldElement) -> Choice {
    let d_sq = &d.square();
    let au = &MONTGOMERY_A * d;

    let inner = &(d_sq + &au) + &FieldElement::ONE;
    let eps = d * &inner; /* eps = d^3 + Ad^2 + d */

    let (eps_is_sq, _) = FieldElement::sqrt_ratio_i(&eps, &FieldElement::ONE);

    eps_is_sq
}

/// Determines if `V <= (p - 1)/2` for a Scalar (e.g an x25519 private key) and
/// returns a [`Choice`] indicating the result.
///
/// Note: When using the elligator2 transformations on x25519 keypairs this
/// requires the use of the clamped scalar_base_mult of the private key to
/// get the edwards representation of the public key, otherwise we need to know
/// the correct sign value for the edwards conversion or the derivation of
/// the `V` value will be broken. As noted in [`EdwardsPoint::to_montgomery`],
/// the sign information about the X coordinate is lost on conversion so we
/// have to use the edwards point derived from the private key to guarantee the
/// correct value here.
///
/// Alternatively you can keep track of the public key and sign bit manually
/// and construct an EdwardsPoint for which [`v_in_sqrt_pubkey_edwards`] will
/// give you the same result.
///
// As an interface, using the private key should work just fine. This allows
// us to match the existing [`PublicKey`] generation interface for the
// [`PublicRepresentative`] in the [`x25519_dalek`] crate. AFAIK there is no
// need for anyone with only the public key to be able to generate the
// representative.
pub(crate) fn v_in_sqrt(key_input: &[u8; 32]) -> Choice {
    let mut masked_pk = *key_input;
    masked_pk[0] &= 0xf8;
    masked_pk[31] &= 0x7f;
    masked_pk[31] |= 0x40;

    let pubkey = EdwardsPoint::mul_base_clamped(masked_pk);
    v_in_sqrt_pubkey_edwards(&pubkey)
}

/// Determines if `V <= (p - 1)/2` for an EdwardsPoint (e.g an x25519 public key)
/// and returns a [`Choice`] indicating the result.
pub(crate) fn v_in_sqrt_pubkey_edwards(pubkey: &EdwardsPoint) -> Choice {
    let divide_minus_p_1_2 = FieldElement::from_bytes(&DIVIDE_MINUS_P_1_2_BYTES);

    // sqrtMinusAPlus2 is sqrt(-(486662+2))
    let (_, sqrt_minus_a_plus_2) = FieldElement::sqrt_ratio_i(
        &(&MONTGOMERY_A_NEG - &(&FieldElement::ONE + &FieldElement::ONE)),
        &FieldElement::ONE,
    );

    // inv1 = 1/((A.Z - A.y) * A.X)
    let inv1 = (&(&pubkey.Z - &pubkey.Y) * &pubkey.X).invert();

    // t0 = A.Y + A.Z
    let t0 = &pubkey.Y + &pubkey.Z;

    // v = t0 * inv1 * A.Z * sqrtMinusAPlus2
    let v = &(&t0 * &inv1) * &(&pubkey.Z * &sqrt_minus_a_plus_2);

    // is   v <= (q-1)/2  ?
    divide_minus_p_1_2.ct_gt(&v)
}

// ============================================================================
// ============================================================================

fn map_to_curve_parts(
    r: &FieldElement,
) -> (FieldElement, FieldElement, FieldElement, FieldElement) {
    let zero = FieldElement::ZERO;
    let one = FieldElement::ONE;
    let minus_one = -&FieldElement::ONE;

    // Exceptional case 2u^2 == -1
    let mut tv1 = r.square2();
    tv1.conditional_assign(&zero, tv1.ct_eq(&minus_one));

    let d_1 = &one + &tv1; /* 1 + 2u^2 */
    let d = &MONTGOMERY_A_NEG * &(d_1.invert()); /* d = -A/(1+2u^2) */

    let inner = &(&d.square() + &(&d * &MONTGOMERY_A)) + &one;
    let gx1 = &d * &inner; /* gx1 = d^3 + Ad^2 + d */
    let gx2 = &gx1 * &tv1;

    let eps_is_sq = high_y(&d);

    // complete X
    /* A_temp = 0, or A if nonsquare*/
    let a_temp = FieldElement::conditional_select(&MONTGOMERY_A, &zero, eps_is_sq);
    let mut x = &d + &a_temp; /* d, or d+A if nonsquare */
    x.conditional_negate(!eps_is_sq); /* d, or -d-A if nonsquare */

    // complete Y
    let y2 = FieldElement::conditional_select(&gx2, &gx1, eps_is_sq);
    let (_, mut y) = FieldElement::sqrt_ratio_i(&y2, &one);
    y.conditional_negate(eps_is_sq ^ y.is_negative());

    (&x * &d_1, d_1, y, one)
}

pub(crate) fn map_fe_to_montgomery(r: &FieldElement) -> (FieldElement, FieldElement) {
    let (xmn, xmd, y, _) = map_to_curve_parts(r);
    (&xmn * &(xmd.invert()), y)
}

pub(crate) fn map_fe_to_edwards(r: &FieldElement) -> (FieldElement, FieldElement) {
    // 1.  (xMn, xMd, yMn, yMd) = map_to_curve_elligator2_curve25519(u)
    let (xmn, xmd, ymn, ymd) = map_to_curve_parts(r);
    // c1 = sqrt(-486664)
    // this cannot fail as it computes a constant
    let c1 = &(&MONTGOMERY_A_NEG - &FieldElement::ONE) - &FieldElement::ONE;
    let (_, c1) = FieldElement::sqrt_ratio_i(&c1, &FieldElement::ONE);

    // 2.  xn = xMn * yMd
    // 3.  xn = xn * c1
    let mut xn = &(&xmn * &ymd) * &c1;

    // 4.  xd = xMd * yMn    # xn / xd = c1 * xM / yM
    let mut xd = &xmd * &ymn;

    // 5.  yn = xMn - xMd
    let mut yn = &xmn - &xmd;
    // 6.  yd = xMn + xMd    # (n / d - 1) / (n / d + 1) = (n - d) / (n + d)
    let mut yd = &xmn + &xmd;

    // 7. tv1 = xd * yd
    // 8.   e = tv1 == 0
    let cond = (&xd * &yd).is_zero();

    // 9.  xn = CMOV(xn, 0, e)
    // 10. xd = CMOV(xd, 1, e)
    // 11. yn = CMOV(yn, 1, e)
    // 12. yd = CMOV(yd, 1, e)
    xn = FieldElement::conditional_select(&xn, &FieldElement::ZERO, cond);
    xd = FieldElement::conditional_select(&xd, &FieldElement::ONE, cond);
    yn = FieldElement::conditional_select(&yn, &FieldElement::ONE, cond);
    yd = FieldElement::conditional_select(&yd, &FieldElement::ONE, cond);

    // 13. return (xn, xd, yn, yd)
    (&xn * &(xd.invert()), &yn * &(yd.invert()))
}

// ========================================================================
// Tests
// ========================================================================

#[cfg(test)]
#[cfg(feature = "elligator2")]
#[cfg(feature = "alloc")]
mod compatibility;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod rfc9380;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod randomness;

#[cfg(test)]
#[cfg(feature = "elligator2")]
mod subgroup;

#[cfg(test)]
#[cfg(feature = "elligator2")]
#[cfg(feature = "digest")]
mod legacy;
