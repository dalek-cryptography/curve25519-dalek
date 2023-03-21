// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// See LICENSE for licensing information.

use core::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitXor, BitXorAssign, Sub};

pub trait IntoBits<T> {
    fn into_bits(self) -> T;
}

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

        impl IntoBits<core::arch::x86_64::__m256i> for $ty {
            #[inline]
            fn into_bits(self) -> core::arch::x86_64::__m256i {
                self.0
            }
        }

        impl IntoBits<$ty> for core::arch::x86_64::__m256i {
            #[inline]
            fn into_bits(self) -> $ty {
                $ty(self)
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, rhs: &$ty) -> bool {
                unsafe {
                    let m = core::arch::x86_64::_mm256_cmpeq_epi8(self.0, rhs.0);
                    core::arch::x86_64::_mm256_movemask_epi8(m) == -1
                }
            }
        }

        impl Eq for $ty {}

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::$add_intrinsic(self.0, rhs.0).into_bits() }
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
                unsafe { core::arch::x86_64::$sub_intrinsic(self.0, rhs.0).into_bits() }
            }
        }

        impl BitAnd for $ty {
            type Output = Self;

            #[inline]
            fn bitand(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::_mm256_and_si256(self.0, rhs.0).into_bits() }
            }
        }

        impl BitXor for $ty {
            type Output = Self;

            #[inline]
            fn bitxor(self, rhs: $ty) -> Self {
                unsafe { core::arch::x86_64::_mm256_xor_si256(self.0, rhs.0).into_bits() }
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
                unsafe { core::arch::x86_64::$shl_intrinsic(self.0, N).into_bits() }
            }

            #[inline]
            pub fn shr<const N: i32>(self) -> Self {
                unsafe { core::arch::x86_64::$shr_intrinsic(self.0, N).into_bits() }
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
            impl IntoBits<$dst> for $src {
                #[inline]
                fn into_bits(self) -> $dst {
                    $dst(self.0)
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
impl_shared!(
    i32x8,
    i32,
    _mm256_add_epi32,
    _mm256_sub_epi32,
    _mm256_slli_epi32,
    _mm256_srli_epi32,
    _mm256_extract_epi32
);

impl_conv!(u64x4 => u32x8, i32x8);

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
}

impl i32x8 {
    #[inline]
    pub fn new(x0: i32, x1: i32, x2: i32, x3: i32, x4: i32, x5: i32, x6: i32, x7: i32) -> Self {
        unsafe {
            Self(core::arch::x86_64::_mm256_set_epi32(
                x7, x6, x5, x4, x3, x2, x1, x0,
            ))
        }
    }

    #[inline]
    pub fn splat(x: i32) -> Self {
        unsafe { Self(core::arch::x86_64::_mm256_set1_epi32(x)) }
    }
}
