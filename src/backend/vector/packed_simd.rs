// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// See LICENSE for licensing information.

use core::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitXor, BitXorAssign, Sub};

macro_rules! impl_shared {
    (
        $ty:ident,
        $lane_ty:ident,
        $add_intrinsic:ident,
        $sub_intrinsic:ident,
        $shl_intrinsic:ident,
        $shr_intrinsic:ident,
        $extract_intrinsic:ident
    ) => {
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Debug)]
        #[repr(transparent)]
        pub struct $ty(core::arch::x86_64::__m256i);

        impl From<$ty> for core::arch::x86_64::__m256i {
            #[inline]
            fn from(value: $ty) -> core::arch::x86_64::__m256i {
                value.0
            }
        }

        impl From<core::arch::x86_64::__m256i> for $ty {
            #[inline]
            fn from(value: core::arch::x86_64::__m256i) -> $ty {
                $ty(value)
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, rhs: &$ty) -> bool {
                unsafe {
                    // This compares each pair of 8-bit packed integers and returns either 0xFF or 0x00
                    // depending on whether they're equal.
                    //
                    // So the values are equal if (and only if) this returns a value that's filled with only 0xFF.
                    //
                    // Pseudocode of what this does:
                    //   self.0.bytes().zip(rhs.0.bytes()).map(|a, b| if a == b { 0xFF } else { 0x00 }).join();
                    let m = core::arch::x86_64::_mm256_cmpeq_epi8(self.0, rhs.0);

                    // Now we need to reduce the 256-bit value to something on which we can branch.
                    //
                    // This will just take the most significant bit of every 8-bit packed integer
                    // and build an `i32` out of it. If the values we previously compared were equal
                    // then all off the most significant bits will be equal to 1, which means that
                    // this will return 0xFFFFFFFF, which is equal to -1 when represented as an `i32`.
                    core::arch::x86_64::_mm256_movemask_epi8(m) == -1
                }
            }
        }

        impl Eq for $ty {}

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::$add_intrinsic(self.0, rhs.0).into() }
            }
        }

        impl AddAssign for $ty {
            #[inline]
            fn add_assign(&mut self, rhs: $ty) {
                *self = *self + rhs
            }
        }

        impl Sub for $ty {
            type Output = Self;

            #[inline]
            fn sub(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::$sub_intrinsic(self.0, rhs.0).into() }
            }
        }

        impl BitAnd for $ty {
            type Output = Self;

            #[inline]
            fn bitand(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::_mm256_and_si256(self.0, rhs.0).into() }
            }
        }

        impl BitXor for $ty {
            type Output = Self;

            #[inline]
            fn bitxor(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::_mm256_xor_si256(self.0, rhs.0).into() }
            }
        }

        impl BitAndAssign for $ty {
            #[inline]
            fn bitand_assign(&mut self, rhs: $ty) {
                *self = *self & rhs;
            }
        }

        impl BitXorAssign for $ty {
            #[inline]
            fn bitxor_assign(&mut self, rhs: $ty) {
                *self = *self ^ rhs;
            }
        }

        #[allow(dead_code)]
        impl $ty {
            #[inline]
            pub fn shl<const N: i32>(self) -> Self {
                unsafe { core::arch::x86_64::$shl_intrinsic(self.0, N).into() }
            }

            #[inline]
            pub fn shr<const N: i32>(self) -> Self {
                unsafe { core::arch::x86_64::$shr_intrinsic(self.0, N).into() }
            }

            #[inline]
            pub fn extract<const N: i32>(self) -> $lane_ty {
                unsafe { core::arch::x86_64::$extract_intrinsic(self.0, N) as $lane_ty }
            }
        }
    };
}

macro_rules! impl_conv {
    ($src:ident => $($dst:ident),+) => {
        $(
            impl From<$src> for $dst {
                #[inline]
                fn from(value: $src) -> $dst {
                    $dst(value.0)
                }
            }
        )+
    }
}

impl_shared!(
    u64x4,
    u64,
    _mm256_add_epi64,
    _mm256_sub_epi64,
    _mm256_slli_epi64,
    _mm256_srli_epi64,
    _mm256_extract_epi64
);
impl_shared!(
    u32x8,
    u32,
    _mm256_add_epi32,
    _mm256_sub_epi32,
    _mm256_slli_epi32,
    _mm256_srli_epi32,
    _mm256_extract_epi32
);

impl_conv!(u64x4 => u32x8);

#[allow(dead_code)]
impl u64x4 {
    #[inline]
    pub const fn new_const(x0: u64, x1: u64, x2: u64, x3: u64) -> Self {
        unsafe { Self(core::mem::transmute([x0, x1, x2, x3])) }
    }

    #[inline]
    pub const fn splat_const<const N: u64>() -> Self {
        Self::new_const(N, N, N, N)
    }

    #[inline]
    pub fn new(x0: u64, x1: u64, x2: u64, x3: u64) -> Self {
        unsafe {
            Self(core::arch::x86_64::_mm256_set_epi64x(
                x3 as i64, x2 as i64, x1 as i64, x0 as i64,
            ))
        }
    }

    #[inline]
    pub fn splat(x: u64) -> Self {
        unsafe { Self(core::arch::x86_64::_mm256_set1_epi64x(x as i64)) }
    }
}

#[allow(dead_code)]
impl u32x8 {
    #[inline]
    pub const fn new_const(
        x0: u32,
        x1: u32,
        x2: u32,
        x3: u32,
        x4: u32,
        x5: u32,
        x6: u32,
        x7: u32,
    ) -> Self {
        unsafe { Self(core::mem::transmute([x0, x1, x2, x3, x4, x5, x6, x7])) }
    }

    #[inline]
    pub const fn splat_const<const N: u32>() -> Self {
        Self::new_const(N, N, N, N, N, N, N, N)
    }

    #[inline]
    pub fn new(x0: u32, x1: u32, x2: u32, x3: u32, x4: u32, x5: u32, x6: u32, x7: u32) -> Self {
        unsafe {
            Self(core::arch::x86_64::_mm256_set_epi32(
                x7 as i32, x6 as i32, x5 as i32, x4 as i32, x3 as i32, x2 as i32, x1 as i32,
                x0 as i32,
            ))
        }
    }

    #[inline]
    pub fn splat(x: u32) -> Self {
        unsafe { Self(core::arch::x86_64::_mm256_set1_epi32(x as i32)) }
    }

    /// Multiplies the low unsigned 32-bits from each packed 64-bit element
    /// and returns the unsigned 64-bit results.
    ///
    /// (This ignores the upper 32-bits from each packed 64-bits!)
    #[inline]
    pub fn mul32(self, rhs: u32x8) -> u64x4 {
        // NOTE: This ignores the upper 32-bits from each packed 64-bits.
        unsafe { core::arch::x86_64::_mm256_mul_epu32(self.0, rhs.0).into() }
    }
}
