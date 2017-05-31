// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all
// copyright and related or neighboring rights to curve25519-dalek,
// using the Creative Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full
// details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

//! Arithmetic for scalar multiplication.
//!
//! The Ed25519 basepoint P has prime order
//!
//! l = 2^252 + 27742317777372353535851937790883648493.
//!
//! Thus a multiple `aP` of the basepoint (with a ∈ ℤ) depends only
//! on the value of `a (mod l)`, or equivalently, the image of `a` in
//! the quotient ℤ/lℤ.
//!
//! The `Scalar` struct represents an element in ℤ/lℤ.
//!
//! Arithmetic operations on `Scalar`s are done using 12 21-bit limbs.
//! However, in contrast to `FieldElement`s, `Scalar`s are stored in
//! memory as bytes, allowing easy access to the bits of the `Scalar`
//! when multiplying a point by a scalar.  For efficient arithmetic
//! between two scalars, the `UnpackedScalar` struct is stored as
//! limbs.

use core::fmt::Debug;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Sub, SubAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Index, IndexMut};
use core::cmp::{Eq, PartialEq};

#[cfg(feature = "std")]
use rand::Rng;

use digest::Digest;
use generic_array::typenum::U64;

use constants;
use utils::{load3, load4};
use subtle::CTAssignable;
use subtle::CTEq;
use subtle::arrays_equal;

/// The `Scalar` struct represents an element in ℤ/lℤ, where
///
/// l = 2^252 + 27742317777372353535851937790883648493
///
/// is the order of the basepoint.  The `Scalar` is stored as bytes.
#[derive(Copy, Clone)]
pub struct Scalar(pub [u8; 32]);

impl Debug for Scalar {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "Scalar: {:?}", &self.0[..])
    }
}

impl Eq for Scalar {}
impl PartialEq for Scalar {
    /// Test equality between two `Scalar`s.
    ///
    /// # Warning
    ///
    /// This function is *not* guaranteed to be constant time and should only be
    /// used for debugging purposes.
    ///
    /// # Returns
    ///
    /// True if they are equal, and false otherwise.
    fn eq(&self, other: &Self) -> bool {
        arrays_equal(&self.0, &other.0) == 1u8
    }
}

impl CTEq for Scalar {
    /// Test equality between two `Scalar`s in constant time.
    ///
    /// # Returns
    ///
    /// `1u8` if they are equal, and `0u8` otherwise.
    fn ct_eq(&self, other: &Self) -> u8 {
        arrays_equal(&self.0, &other.0)
    }
}

impl Index<usize> for Scalar {
    type Output = u8;

    fn index(&self, _index: usize) -> &u8 {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for Scalar {
    fn index_mut(&mut self, _index: usize) -> &mut u8 {
        &mut (self.0[_index])
    }
}

impl<'b> MulAssign<&'b Scalar> for Scalar {
    fn mul_assign(&mut self, _rhs: &'b Scalar) {
        let result = (self as &Scalar) * _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Mul<&'b Scalar> for &'a Scalar {
    type Output = Scalar;
    fn mul(self, _rhs: &'b Scalar) -> Scalar {
        Scalar::multiply_add(self, _rhs, &Scalar::zero())
    }
}

impl<'b> AddAssign<&'b Scalar> for Scalar {
    fn add_assign(&mut self, _rhs: &'b Scalar) {
        *self = Scalar::multiply_add(&Scalar::one(), self, _rhs);
    }
}

impl<'a, 'b> Add<&'b Scalar> for &'a Scalar {
    type Output = Scalar;
    fn add(self, _rhs: &'b Scalar) -> Scalar {
        Scalar::multiply_add(&Scalar::one(), self, _rhs)
    }
}

impl<'b> SubAssign<&'b Scalar> for Scalar {
    fn sub_assign(&mut self, _rhs: &'b Scalar) {
        // (l-1)*_rhs + self = self - _rhs
        *self = Scalar::multiply_add(&constants::l_minus_1, _rhs, self);
    }
}

impl<'a, 'b> Sub<&'b Scalar> for &'a Scalar {
    type Output = Scalar;
    fn sub(self, _rhs: &'b Scalar) -> Scalar {
        // (l-1)*_rhs + self = self - _rhs
        Scalar::multiply_add(&constants::l_minus_1, _rhs, self)
    }
}

impl<'a> Neg for &'a Scalar {
    type Output = Scalar;
    fn neg(self) -> Scalar {
        self * &constants::l_minus_1
    }
}

impl CTAssignable for Scalar {
    /// Conditionally assign another Scalar to this one.
    ///
    /// ```
    /// # extern crate curve25519_dalek;
    /// # extern crate subtle;
    /// # use curve25519_dalek::scalar::Scalar;
    /// # use subtle::CTAssignable;
    /// # fn main() {
    /// let a = Scalar([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    ///                 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]);
    /// let b = Scalar([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    ///                 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]);
    /// let mut t = a;
    /// t.conditional_assign(&b, 0u8);
    /// assert!(t[0] == a[0]);
    /// t.conditional_assign(&b, 1u8);
    /// assert!(t[0] == b[0]);
    /// # }
    /// ```
    ///
    /// # Preconditions
    ///
    /// * `choice` in {0,1}
    // XXX above test checks first byte because Scalar does not impl Eq
    fn conditional_assign(&mut self, other: &Scalar, choice: u8) {
        // if choice = 0u8, mask = (-0i8) as u8 = 00000000
        // if choice = 1u8, mask = (-1i8) as u8 = 11111111
        let mask = -(choice as i8) as u8;
        for i in 0..32 {
            self[i] ^= mask & (self[i] ^ other[i]);
        }
    }
}

#[cfg(feature = "serde")]
use serde::{self, Serialize, Deserialize, Serializer, Deserializer};
#[cfg(feature = "serde")]
use serde::de::Visitor;

#[cfg(feature = "serde")]
impl Serialize for Scalar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_bytes(self.as_bytes())
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>
    {
        struct ScalarVisitor;

        impl<'de> Visitor<'de> for ScalarVisitor {
            type Value = Scalar;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a 32-byte scalar value")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Scalar, E>
                where E: serde::de::Error
            {
                if v.len() == 32 {
                    // array_ref turns &[u8] into &[u8;32]
                    Ok(Scalar(*array_ref!(v, 0, 32)))
                } else {
                    Err(serde::de::Error::invalid_length(v.len(), &self))
                }
            }
        }

        deserializer.deserialize_bytes(ScalarVisitor)
    }
}

impl Scalar {
    /// Return a `Scalar` chosen uniformly at random using a user-provided RNG.
    ///
    /// # Inputs
    ///
    /// * `rng`: any RNG which implements the `rand::Rng` interface.
    ///
    /// # Returns
    ///
    /// A random scalar within ℤ/lℤ.
    #[cfg(feature = "std")]
    pub fn random<T: Rng>(rng: &mut T) -> Self {
        let mut scalar_bytes = [0u8; 64];
        rng.fill_bytes(&mut scalar_bytes);
        Scalar::reduce(&scalar_bytes)
    }

    /// Hash a slice of bytes into a scalar.
    ///
    /// Takes a type parameter `D`, which is any `Digest` producing 64
    /// bytes (512 bits) of output.
    ///
    /// Convenience wrapper around `from_hash`.
    ///
    /// # Example
    ///
    /// ```
    /// # extern crate curve25519_dalek;
    /// # use curve25519_dalek::scalar::Scalar;
    /// extern crate sha2;
    /// use sha2::Sha512;
    ///
    /// # // Need fn main() here in comment so the doctest compiles
    /// # // See https://doc.rust-lang.org/book/documentation.html#documentation-as-tests
    /// # fn main() {
    /// let msg = "To really appreciate architecture, you may even need to commit a murder";
    /// let s = Scalar::hash_from_bytes::<Sha512>(msg.as_bytes());
    /// # }
    /// ```
    ///
    pub fn hash_from_bytes<D>(input: &[u8]) -> Scalar
        where D: Digest<OutputSize = U64> + Default
    {
        let mut hash = D::default();
        hash.input(input);
        Scalar::from_hash(hash)
    }

    /// Construct a scalar from an existing `Digest` instance.
    ///
    /// Use this instead of `hash_from_bytes` if it is more convenient
    /// to stream data into the `Digest` than to pass a single byte
    /// slice.
    pub fn from_hash<D>(hash: D) -> Scalar
        where D: Digest<OutputSize = U64> + Default
    {
        // XXX this seems clumsy
        let mut output = [0u8; 64];
        output.copy_from_slice(hash.result().as_slice());
        Scalar::reduce(&output)
    }

    /// View this `Scalar` as a sequence of bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Construct the additive identity
    pub fn zero() -> Self {
        Scalar([0u8; 32])
    }

    /// Construct the multiplicative identity
    pub fn one() -> Self {
        Scalar([ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    }

    /// Construct a scalar from the given `u64`.
    pub fn from_u64(x: u64) -> Scalar {
        let mut s = Scalar::zero();
        for i in 0..8 {
            s[i] = (x >> (i*8)) as u8;
        }
        s
    }

    /// Compute the multiplicative inverse of this scalar.
    pub fn invert(&self) -> Scalar {
        self.unpack().invert().pack()
    }

    /// Get the bits of the scalar.
    pub fn bits(&self) -> [i8; 256] {
        let mut bits = [0i8; 256];
        for i in 0..256 {
            // As i runs from 0..256, the bottom 3 bits index the bit,
            // while the upper bits index the byte.
            bits[i] = ((self.0[i>>3] >> (i&7)) & 1u8) as i8;
        }
        bits
    }

    /// Compute a width-5 "Non-Adjacent Form" of this scalar.
    ///
    /// A width-`w` NAF of a positive integer `k` is an expression
    /// `k = sum(k[i]*2^i for i in range(l))`, where each nonzero
    /// coefficient `k[i]` is odd and bounded by `|k[i]| < 2^(w-1)`,
    /// `k[l-1]` is nonzero, and at most one of any `w` consecutive
    /// coefficients is nonzero.  (Hankerson, Menezes, Vanstone; def 3.32).
    ///
    /// Intuitively, this is like a binary expansion, except that we
    /// allow some coefficients to grow up to `2^(w-1)` so that the
    /// nonzero coefficients are as sparse as possible.
    pub fn non_adjacent_form(&self) -> [i8; 256] {
        // Step 1: write out bits of the scalar
        let mut naf = self.bits();

        // Step 2: zero coefficients by carrying them upwards or downwards 
        'bits: for i in 0..256 {
            if naf[i] == 0 { continue 'bits; }
            'window: for b in 1..6 {
                if     i+b  >= 256  { break 'window; }
                if naf[i+b] == 0    { continue 'window; }
                let potential_carry = naf[i+b] << b;
                if  naf[i+b] + potential_carry <= 15 {
                    // Eliminate naf[i+b] by carrying its value onto naf[i]
                    naf[i] += potential_carry;
                    naf[i+b] = 0;
                } else if naf[i+b] - potential_carry >= -15 {
                    // Eliminate naf[i+b] by carrying its value upwards.
                    naf[i] -= potential_carry; // Subtract 2^(i+b)
                    'carry: for k in i+b..256 {
                        if naf[k] != 0 {
                            // Since naf[k] = 0 or 1 for k > i, naf[k] == 1.
                            naf[k] = 0; // Subtract 2^k
                        } else {
                            // By now we have subtracted 2^k = 
                            // 2^(i+b) + 2^(i+b) + 2^(i+b+1) + ... + 2^(k-1).
                            naf[k] = 1; // Add back 2^k.
                            break 'carry;
                        }
                    }
                }
            }
        }

        naf
    }

    // Unpack a scalar into 12 21-bit limbs.
    fn unpack(&self) -> UnpackedScalar {
        let mask_21bits: i64 = (1 << 21) - 1;
        let mut a = UnpackedScalar([0i64; 12]);
        a[ 0]  = mask_21bits &  load3(&self.0[ 0..])      ;
        a[ 1]  = mask_21bits & (load4(&self.0[ 2..]) >> 5);
        a[ 2]  = mask_21bits & (load3(&self.0[ 5..]) >> 2);
        a[ 3]  = mask_21bits & (load4(&self.0[ 7..]) >> 7);
        a[ 4]  = mask_21bits & (load4(&self.0[10..]) >> 4);
        a[ 5]  = mask_21bits & (load3(&self.0[13..]) >> 1);
        a[ 6]  = mask_21bits & (load4(&self.0[15..]) >> 6);
        a[ 7]  = mask_21bits & (load3(&self.0[18..]) >> 3);
        a[ 8]  = mask_21bits &  load3(&self.0[21..])      ;
        a[ 9]  = mask_21bits & (load4(&self.0[23..]) >> 5);
        a[10]  = mask_21bits & (load3(&self.0[26..]) >> 2);
        a[11]  =                load4(&self.0[28..]) >> 7 ;

        a
    }

    /// Write this scalar in radix 16, with coefficients in `[-8,8)`,
    /// i.e., compute `a_i` such that
    ///
    ///    a = a_0 + a_1*16^1 + ... + a_63*16^63,
    ///
    /// with `-8 ≤ a_i < 8` for `0 ≤ i < 63` and `-8 ≤ a_63 ≤ 8`.
    ///
    /// Precondition: self[31] <= 127.  This is the case whenever
    /// `self` is reduced.
    pub fn to_radix_16(&self) -> [i8; 64] {
        debug_assert!(self[31] <= 127);
        let mut output = [0i8; 64];

        // Step 1: change radix.
        // Convert from radix 256 (bytes) to radix 16 (nibbles)
        #[inline(always)]
        fn bot_half(x: u8) -> u8 { (x >> 0) & 15 }
        #[inline(always)]
        fn top_half(x: u8) -> u8 { (x >> 4) & 15 }

        for i in 0..32 {
            output[2*i  ] = bot_half(self[i]) as i8;
            output[2*i+1] = top_half(self[i]) as i8;
        }
        // Precondition note: since self[31] <= 127, output[63] <= 7

        // Step 2: recenter coefficients from [0,16) to [-8,8)
        for i in 0..63 {
            let carry    = (output[i] + 8) >> 4;
            output[i  ] -= carry << 4;
            output[i+1] += carry;
        }
        // Precondition note: output[63] is not recentered.  It
        // increases by carry <= 1.  Thus output[63] <= 8.

        output
    }

    /// Compute `ab+c (mod l)`.
    /// XXX should this exist, or should we just have Mul, Add etc impls
    /// that unpack and then call UnpackedScalar::multiply_add ?
    pub fn multiply_add(a: &Scalar, b: &Scalar, c: &Scalar) -> Scalar {
        // Unpack scalars into limbs
        let al = a.unpack();
        let bl = b.unpack();
        let cl = c.unpack();

        // Multiply and repack
        UnpackedScalar::multiply_add(&al, &bl, &cl).pack()
    }

    /// Reduce a 512-bit little endian number mod l
    pub fn reduce(input: &[u8; 64]) -> Scalar {
        let mut s = [0i64; 24];

        // XXX express this as two unpack_limbs
        // some issues re: masking with the top byte of the 32byte input
        let mask_21bits: i64 = (1 << 21) -1;
        s[0]  = mask_21bits &  load3(&input[ 0..])      ;
        s[1]  = mask_21bits & (load4(&input[ 2..]) >> 5);
        s[2]  = mask_21bits & (load3(&input[ 5..]) >> 2);
        s[3]  = mask_21bits & (load4(&input[ 7..]) >> 7);
        s[4]  = mask_21bits & (load4(&input[10..]) >> 4);
        s[5]  = mask_21bits & (load3(&input[13..]) >> 1);
        s[6]  = mask_21bits & (load4(&input[15..]) >> 6);
        s[7]  = mask_21bits & (load3(&input[18..]) >> 3);
        s[8]  = mask_21bits &  load3(&input[21..])      ;
        s[9]  = mask_21bits & (load4(&input[23..]) >> 5);
        s[10] = mask_21bits & (load3(&input[26..]) >> 2);
        s[11] = mask_21bits & (load4(&input[28..]) >> 7);
        s[12] = mask_21bits & (load4(&input[31..]) >> 4);
        s[13] = mask_21bits & (load3(&input[34..]) >> 1);
        s[14] = mask_21bits & (load4(&input[36..]) >> 6);
        s[15] = mask_21bits & (load3(&input[39..]) >> 3);
        s[16] = mask_21bits &  load3(&input[42..])      ;
        s[17] = mask_21bits & (load4(&input[44..]) >> 5);
        s[18] = mask_21bits & (load3(&input[47..]) >> 2);
        s[19] = mask_21bits & (load4(&input[49..]) >> 7);
        s[20] = mask_21bits & (load4(&input[52..]) >> 4);
        s[21] = mask_21bits & (load3(&input[55..]) >> 1);
        s[22] = mask_21bits & (load4(&input[57..]) >> 6);
        s[23] =                load4(&input[60..]) >> 3 ;

        // XXX replacing the previous code in this function with the
        // call to reduce_limbs adds two extra carry passes (the ones
        // at the top of the reduce_limbs function).  Otherwise they
        // are identical.  The test seems to work OK but it would be
        // good to check that this really is OK to add.
        UnpackedScalar::reduce_limbs(&mut s).pack()
    }
}

/// The `UnpackedScalar` struct represents an element in ℤ/lℤ as 12
/// 21-bit limbs.
#[derive(Copy,Clone)]
pub struct UnpackedScalar(pub [i64; 12]);

impl Index<usize> for UnpackedScalar {
    type Output = i64;

    fn index(&self, _index: usize) -> &i64 {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for UnpackedScalar {
    fn index_mut(&mut self, _index: usize) -> &mut i64 {
        &mut (self.0[_index])
    }
}

impl UnpackedScalar {
    /// Pack the limbs of this `UnpackedScalar` into a `Scalar`.
    fn pack(&self) -> Scalar {
        let mut s = Scalar::zero();
        s[0]  =  (self.0[ 0] >>  0)                      as u8;
        s[1]  =  (self.0[ 0] >>  8)                      as u8;
        s[2]  = ((self.0[ 0] >> 16) | (self.0[ 1] << 5)) as u8;
        s[3]  =  (self.0[ 1] >>  3)                      as u8;
        s[4]  =  (self.0[ 1] >> 11)                      as u8;
        s[5]  = ((self.0[ 1] >> 19) | (self.0[ 2] << 2)) as u8;
        s[6]  =  (self.0[ 2] >>  6)                      as u8;
        s[7]  = ((self.0[ 2] >> 14) | (self.0[ 3] << 7)) as u8;
        s[8]  =  (self.0[ 3] >>  1)                      as u8;
        s[9]  =  (self.0[ 3] >>  9)                      as u8;
        s[10] = ((self.0[ 3] >> 17) | (self.0[ 4] << 4)) as u8;
        s[11] =  (self.0[ 4] >>  4)                      as u8;
        s[12] =  (self.0[ 4] >> 12)                      as u8;
        s[13] = ((self.0[ 4] >> 20) | (self.0[ 5] << 1)) as u8;
        s[14] =  (self.0[ 5] >>  7)                      as u8;
        s[15] = ((self.0[ 5] >> 15) | (self.0[ 6] << 6)) as u8;
        s[16] =  (self.0[ 6] >>  2)                      as u8;
        s[17] =  (self.0[ 6] >> 10)                      as u8;
        s[18] = ((self.0[ 6] >> 18) | (self.0[ 7] << 3)) as u8;
        s[19] =  (self.0[ 7] >>  5)                      as u8;
        s[20] =  (self.0[ 7] >> 13)                      as u8;
        s[21] =  (self.0[ 8] >>  0)                      as u8;
        s[22] =  (self.0[ 8] >>  8)                      as u8;
        s[23] = ((self.0[ 8] >> 16) | (self.0[ 9] << 5)) as u8;
        s[24] =  (self.0[ 9] >>  3)                      as u8;
        s[25] =  (self.0[ 9] >> 11)                      as u8;
        s[26] = ((self.0[ 9] >> 19) | (self.0[10] << 2)) as u8;
        s[27] =  (self.0[10] >>  6)                      as u8;
        s[28] = ((self.0[10] >> 14) | (self.0[11] << 7)) as u8;
        s[29] =  (self.0[11] >>  1)                      as u8;
        s[30] =  (self.0[11] >>  9)                      as u8;
        s[31] =  (self.0[11] >> 17)                      as u8;

        s
    }

    /// Return the zero scalar.
    pub fn zero() -> UnpackedScalar {
        UnpackedScalar([0,0,0,0,0,0,0,0,0,0,0,0])
    }

    /// Return the one scalar.
    pub fn one() -> UnpackedScalar {
        UnpackedScalar([1,0,0,0,0,0,0,0,0,0,0,0])
    }

    /// Compute the multiplicative inverse of this scalar.
    pub fn invert(&self) -> UnpackedScalar {
        let mut y = UnpackedScalar::one();
        // Run through bits of l-2 from highest to least
        for bit in constants::l_minus_2.bits().iter().rev() {
            y = UnpackedScalar::multiply_add(&y, &y, &UnpackedScalar::zero());
            if *bit == 1 {
                y = UnpackedScalar::multiply_add(&y, self, &UnpackedScalar::zero());
            }
        }
        y
    }

    /// Compute `ab+c (mod l)`.
    pub fn multiply_add(a: &UnpackedScalar,
                        b: &UnpackedScalar,
                        c: &UnpackedScalar) -> UnpackedScalar {
        let mut result = [0i64; 24];

        // Multiply a and b, and add c
        result[0]  =         c[0] +  a[0]*b[0];
        result[1]  =         c[1] +  a[0]*b[1]  +  a[1]*b[0];
        result[2]  =         c[2] +  a[0]*b[2]  +  a[1]*b[1] +  a[2]*b[0];
        result[3]  =         c[3] +  a[0]*b[3]  +  a[1]*b[2] +  a[2]*b[1] +  a[3]*b[0];
        result[4]  =         c[4] +  a[0]*b[4]  +  a[1]*b[3] +  a[2]*b[2] +  a[3]*b[1] +  a[4]*b[0];
        result[5]  =         c[5] +  a[0]*b[5]  +  a[1]*b[4] +  a[2]*b[3] +  a[3]*b[2] +  a[4]*b[1] +  a[5]*b[0];
        result[6]  =         c[6] +  a[0]*b[6]  +  a[1]*b[5] +  a[2]*b[4] +  a[3]*b[3] +  a[4]*b[2] +  a[5]*b[1] +  a[6]*b[0];
        result[7]  =         c[7] +  a[0]*b[7]  +  a[1]*b[6] +  a[2]*b[5] +  a[3]*b[4] +  a[4]*b[3] +  a[5]*b[2] +  a[6]*b[1] +  a[7]*b[0];
        result[8]  =         c[8] +  a[0]*b[8]  +  a[1]*b[7] +  a[2]*b[6] +  a[3]*b[5] +  a[4]*b[4] +  a[5]*b[3] +  a[6]*b[2] +  a[7]*b[1] +  a[8]*b[0];
        result[9]  =         c[9] +  a[0]*b[9]  +  a[1]*b[8] +  a[2]*b[7] +  a[3]*b[6] +  a[4]*b[5] +  a[5]*b[4] +  a[6]*b[3] +  a[7]*b[2] +  a[8]*b[1] +  a[9]*b[0];
        result[10] =        c[10] +  a[0]*b[10] +  a[1]*b[9] +  a[2]*b[8] +  a[3]*b[7] +  a[4]*b[6] +  a[5]*b[5] +  a[6]*b[4] +  a[7]*b[3] +  a[8]*b[2] +  a[9]*b[1] + a[10]*b[0];
        result[11] =        c[11] +  a[0]*b[11] + a[1]*b[10] +  a[2]*b[9] +  a[3]*b[8] +  a[4]*b[7] +  a[5]*b[6] +  a[6]*b[5] +  a[7]*b[4] +  a[8]*b[3] +  a[9]*b[2] + a[10]*b[1] + a[11]*b[0];
        result[12] =   a[1]*b[11] +  a[2]*b[10] +  a[3]*b[9] +  a[4]*b[8] +  a[5]*b[7] +  a[6]*b[6] +  a[7]*b[5] +  a[8]*b[4] +  a[9]*b[3] + a[10]*b[2] + a[11]*b[1];
        result[13] =   a[2]*b[11] +  a[3]*b[10] +  a[4]*b[9] +  a[5]*b[8] +  a[6]*b[7] +  a[7]*b[6] +  a[8]*b[5] +  a[9]*b[4] + a[10]*b[3] + a[11]*b[2];
        result[14] =   a[3]*b[11] +  a[4]*b[10] +  a[5]*b[9] +  a[6]*b[8] +  a[7]*b[7] +  a[8]*b[6] +  a[9]*b[5] + a[10]*b[4] + a[11]*b[3];
        result[15] =   a[4]*b[11] +  a[5]*b[10] +  a[6]*b[9] +  a[7]*b[8] +  a[8]*b[7] +  a[9]*b[6] + a[10]*b[5] + a[11]*b[4];
        result[16] =   a[5]*b[11] +  a[6]*b[10] +  a[7]*b[9] +  a[8]*b[8] +  a[9]*b[7] + a[10]*b[6] + a[11]*b[5];
        result[17] =   a[6]*b[11] +  a[7]*b[10] +  a[8]*b[9] +  a[9]*b[8] + a[10]*b[7] + a[11]*b[6];
        result[18] =   a[7]*b[11] +  a[8]*b[10] +  a[9]*b[9] + a[10]*b[8] + a[11]*b[7];
        result[19] =   a[8]*b[11] +  a[9]*b[10] + a[10]*b[9] + a[11]*b[8];
        result[20] =   a[9]*b[11] + a[10]*b[10] + a[11]*b[9];
        result[21] =  a[10]*b[11] + a[11]*b[10];
        result[22] =  a[11]*b[11];
        result[23] =          0i64;

        // Reduce limbs
        UnpackedScalar::reduce_limbs(&mut result)
    }

    /// Reduce 24 limbs to 12, consuming the input. Reduction is mod
    ///
    ///   l = 2^252 + 27742317777372353535851937790883648493,
    ///
    /// so
    ///
    ///   2^252 = -27742317777372353535851937790883648493 (mod l).
    ///
    /// We can write the right-hand side in 21-bit limbs as
    ///
    /// rhs =    666643 * 2^0
    ///        + 470296 * 2^21
    ///        + 654183 * 2^42
    ///        - 997805 * 2^63
    ///        + 136657 * 2^84
    ///        - 683901 * 2^105
    ///
    /// The (12+k)-th limb of `limbs` is the coefficient of
    ///
    ///    2^(252 + 21*k)
    ///
    /// since 12*21 = 252.  By the above, we have that
    ///
    ///    c * 2^(252 + 21*k) =   c * 666643 * 2^(21*k)
    ///                         + c * 470296 * 2^(42*k) + ...
    ///
    /// so we can eliminate it by adding those values to the lower
    /// limbs.  Reduction mod l amounts to eliminating all of the
    /// high limbs while carrying as appropriate to prevent
    /// overflows in the lower limbs.
    fn reduce_limbs(mut limbs: &mut [i64; 24]) -> UnpackedScalar {
        #[inline]
        #[allow(dead_code)]
        fn do_reduction(limbs: &mut [i64; 24], i: usize) {
            limbs[i - 12] += limbs[i] * 666643;
            limbs[i - 11] += limbs[i] * 470296;
            limbs[i - 10] += limbs[i] * 654183;
            limbs[i -  9] -= limbs[i] * 997805;
            limbs[i -  8] += limbs[i] * 136657;
            limbs[i -  7] -= limbs[i] * 683901;
            limbs[i] = 0;
        }
        /// Carry excess from the `i`-th limb into the `(i+1)`-th limb.
        /// Postcondition: `0 <= limbs[i] < 2^21`.
        #[inline]
        #[allow(dead_code)]
        fn do_carry_uncentered(limbs: &mut [i64; 24], i: usize) {
            let carry: i64 = limbs[i] >> 21;
            limbs[i+1] += carry;
            limbs[i  ] -= carry << 21;
        }
        #[inline]
        #[allow(dead_code)]
        /// Carry excess from the `i`-th limb into the `(i+1)`-th limb.
        /// Postcondition: `-2^20 <= limbs[i] < 2^20`.
        fn do_carry_centered(limbs: &mut [i64; 24], i: usize) {
            let carry: i64 = (limbs[i] + (1<<20)) >> 21;
            limbs[i+1] += carry;
            limbs[i  ] -= carry << 21;
        }

        for i in 0..23 {
            do_carry_centered(&mut limbs, i);
        }
        for i in (0..23).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 23);
        do_reduction(&mut limbs, 22);
        do_reduction(&mut limbs, 21);
        do_reduction(&mut limbs, 20);
        do_reduction(&mut limbs, 19);
        do_reduction(&mut limbs, 18);

        for i in (6..18).filter(|x| x % 2 == 0) {
            do_carry_centered(&mut limbs, i);
        }
        for i in (6..16).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 17);
        do_reduction(&mut limbs, 16);
        do_reduction(&mut limbs, 15);
        do_reduction(&mut limbs, 14);
        do_reduction(&mut limbs, 13);
        do_reduction(&mut limbs, 12);

        for i in (0..12).filter(|x| x % 2 == 0) {
            do_carry_centered(&mut limbs, i);
        }
        for i in (0..12).filter(|x| x % 2 == 1) {
            do_carry_centered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 12);

        for i in 0..12 {
            do_carry_uncentered(&mut limbs, i);
        }

        do_reduction(&mut limbs, 12);

        for i in 0..11 {
            do_carry_uncentered(&mut limbs, i);
        }

        UnpackedScalar(*array_ref!(limbs, 0, 12))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// x = 2238329342913194256032495932344128051776374960164957527413114840482143558222
    pub static X: Scalar = Scalar(
        [0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
         0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
         0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
         0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04]);
    /// y = 2592331292931086675770238855846338635550719849568364935475441891787804997264
    pub static Y: Scalar = Scalar(
        [0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4,
         0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83, 0x86, 0xc3,
         0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d,
         0xe8, 0xef, 0x7a, 0xc3, 0x1f, 0x35, 0xbb, 0x05]);
    /// z = 5033871415930814945849241457262266927579821285980625165479289807629491019013
    pub static Z: Scalar = Scalar(
        [0x05, 0x9d, 0x3e, 0x0b, 0x09, 0x26, 0x50, 0x3d,
         0xa3, 0x84, 0xa1, 0x3c, 0x92, 0x7a, 0xc2, 0x06,
         0x41, 0x98, 0xcf, 0x34, 0x3a, 0x24, 0xd5, 0xb7,
         0xeb, 0x33, 0x6a, 0x2d, 0xfc, 0x11, 0x21, 0x0b]);
    /// w = 3486911242272497535104403593250518247409663771668155364040899665266216860804
    static W: Scalar = Scalar(
        [0x84, 0xfc, 0xbc, 0x4f, 0x78, 0x12, 0xa0, 0x06,
         0xd7, 0x91, 0xd9, 0x7a, 0x3a, 0x27, 0xdd, 0x1e,
         0x21, 0x43, 0x45, 0xf7, 0xb1, 0xb9, 0x56, 0x7a,
         0x81, 0x30, 0x73, 0x44, 0x96, 0x85, 0xb5, 0x07]);

    /// x*y = 5690045403673944803228348699031245560686958845067437804563560795922180092780
    static X_TIMES_Y: Scalar = Scalar(
        [0x6c, 0x33, 0x74, 0xa1, 0x89, 0x4f, 0x62, 0x21,
         0x0a, 0xaa, 0x2f, 0xe1, 0x86, 0xa6, 0xf9, 0x2c,
         0xe0, 0xaa, 0x75, 0xc2, 0x77, 0x95, 0x81, 0xc2,
         0x95, 0xfc, 0x08, 0x17, 0x9a, 0x73, 0x94, 0x0c]);

    static A_SCALAR: Scalar = Scalar([
        0x1a, 0x0e, 0x97, 0x8a, 0x90, 0xf6, 0x62, 0x2d,
        0x37, 0x47, 0x02, 0x3f, 0x8a, 0xd8, 0x26, 0x4d,
        0xa7, 0x58, 0xaa, 0x1b, 0x88, 0xe0, 0x40, 0xd1,
        0x58, 0x9e, 0x7b, 0x7f, 0x23, 0x76, 0xef, 0x09]);

    static A_NAF: [i8; 256] =
        [0,13,0,0,0,0,0,0,0,7,0,0,0,0,0,0,-9,0,0,0,0,-11,0,0,0,0,3,0,0,0,0,1,
         0,0,0,0,9,0,0,0,0,-5,0,0,0,0,0,0,3,0,0,0,0,11,0,0,0,0,11,0,0,0,0,0,
         -9,0,0,0,0,0,-3,0,0,0,0,9,0,0,0,0,0,1,0,0,0,0,0,0,-1,0,0,0,0,0,9,0,
         0,0,0,-15,0,0,0,0,-7,0,0,0,0,-9,0,0,0,0,0,5,0,0,0,0,13,0,0,0,0,0,-3,0,
         0,0,0,-11,0,0,0,0,-7,0,0,0,0,-13,0,0,0,0,11,0,0,0,0,-9,0,0,0,0,0,1,0,0,
         0,0,0,-15,0,0,0,0,1,0,0,0,0,7,0,0,0,0,0,0,0,0,5,0,0,0,0,0,13,0,0,0,
         0,0,0,11,0,0,0,0,0,15,0,0,0,0,0,-9,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,7,
         0,0,0,0,0,-15,0,0,0,0,0,15,0,0,0,0,15,0,0,0,0,15,0,0,0,0,0,1,0,0,0,0];

    #[test]
    fn non_adjacent_form() {
        let naf = A_SCALAR.non_adjacent_form();
        for i in 0..256 {
            assert_eq!(naf[i], A_NAF[i]);
        }
    }

    #[test]
    fn from_unsigned() {
        let val = 0xdeadbeefdeadbeef;
        let s = Scalar::from_u64(val);
        assert_eq!(s[7], 0xde);
        assert_eq!(s[6], 0xad);
        assert_eq!(s[5], 0xbe);
        assert_eq!(s[4], 0xef);
        assert_eq!(s[3], 0xde);
        assert_eq!(s[2], 0xad);
        assert_eq!(s[1], 0xbe);
        assert_eq!(s[0], 0xef);
    }

    #[test]
    fn scalar_multiply_by_one() {
        let one = Scalar::one();
        let zero = Scalar::zero();
        let test_scalar = Scalar::multiply_add(&X, &one, &zero);
        for i in 0..32 {
            assert!(test_scalar[i] == X[i]);
        }
    }

    #[test]
    fn impl_add() {
        let mut two = Scalar::zero(); two[0] = 2;
        let two = two;
        let one = Scalar::one();
        let should_be_two = &one + &one;
        assert_eq!(should_be_two, two);
    }

    #[test]
    fn impl_sub() {
        let should_be_one = &constants::l - &constants::l_minus_1;
        assert_eq!(should_be_one, Scalar::one());
    }

    #[allow(non_snake_case)]
    #[test]
    fn impl_mul() {
        let should_be_X_times_Y = &X * &Y;
        assert_eq!(should_be_X_times_Y, X_TIMES_Y);
    }

    #[test]
    fn scalar_multiply_add() {
        let test_scalar = Scalar::multiply_add(&X, &Y, &Z);
        for i in 0..32 {
            assert!(test_scalar[i] == W[i]);
        }
    }

    #[test]
    fn scalar_reduce() {
        let mut bignum = [0u8; 64];
        // set bignum = x + 2^256x
        for i in 0..32 {
            bignum[   i] = X[i];
            bignum[32+i] = X[i];
        }
        // 3958878930004874126169954872055634648693766179881526445624823978500314864344
        // = x + 2^256x (mod l)
        let reduced = Scalar([216, 154, 179, 139, 210, 121,   2,  71,
                               69,  99, 158, 216,  23, 173,  63, 100,
                              204,   0,  91,  50, 219, 153,  57, 249,
                               28,  82,  31, 197, 100, 165, 192,   8]);
        let test_red = Scalar::reduce(&bignum);
        for i in 0..32 {
            assert!(test_red[i] == reduced[i]);
        }
    }

    #[allow(non_snake_case)]
    #[test]
    fn invert() {
        let inv_X = X.invert();
        let should_be_one = &inv_X * &X;
        assert_eq!(should_be_one, Scalar::one());
    }

    // Negating a scalar twice should result in the original scalar.
    #[allow(non_snake_case)]
    #[test]
    fn neg_twice_is_identity() {
        let negative_X = -&X;
        let should_be_X = -&negative_X;

        assert_eq!(should_be_X, X);
    }

    #[cfg(feature = "serde")]
    use serde_cbor;

    #[test]
    #[cfg(feature = "serde")]
    fn serde_cbor_scalar_roundtrip() {
        let output = serde_cbor::to_vec(&X).unwrap();
        let parsed: Scalar = serde_cbor::from_slice(&output).unwrap();
        assert_eq!(parsed, X);
    }
}

#[cfg(all(test, feature = "bench"))]
mod bench {
    use rand::OsRng;
    use test::Bencher;

    use super::*;
    use super::test::{X, Y, Z};

    #[bench]
    fn scalar_random(b: &mut Bencher) {
        let mut csprng: OsRng = OsRng::new().unwrap();

        b.iter(|| Scalar::random(&mut csprng));
    }

    #[bench]
    fn scalar_multiply_add(b: &mut Bencher) {
        b.iter(|| Scalar::multiply_add(&X, &Y, &Z));
    }

    #[bench]
    fn invert(b: &mut Bencher) {
        let x = X.unpack();
        b.iter(|| x.invert());
    }

    #[bench]
    fn scalar_unpacked_multiply_add(b: &mut Bencher) {
        let x = X.unpack();
        let y = Y.unpack();
        let z = Z.unpack();
        b.iter(|| UnpackedScalar::multiply_add(&x, &y, &z));
    }
}
