// -*- mode: rust; -*-
//
// This file is part of curve25519-dalek.
// See LICENSE for licensing information.

//! This module defines wrappers over platform-specific SIMD types to make them
//! more convenient to use.
//!
//! This is an adaptation of `crate::backend::vector::packed_simd.rs` for aarch64.

use core::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitXor, BitXorAssign, Sub};

macro_rules! impl_shared {
    (
        $ty:ident, // Name of the struct
        $lane_ty:ident,
        $internal_ty: ident,
        $beq_intrinsic:ident,
        $add_intrinsic:ident,
        $sub_intrinsic:ident,
        $and_intrinsic:ident,
        $xor_intrinsic:ident,
        $shl_intrinsic:ident,
        $shr_intrinsic:ident,
        $extract_intrinsic:ident
    ) => {
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Debug)]
        #[repr(transparent)]
        pub struct $ty(pub core::arch::aarch64::$internal_ty);

        impl From<$ty> for core::arch::aarch64::$internal_ty {
            #[inline]
            fn from(value: $ty) -> core::arch::aarch64::$internal_ty {
                value.0
            }
        }

        impl From<core::arch::aarch64::$internal_ty> for $ty {
            #[inline]
            fn from(value: core::arch::aarch64::$internal_ty) -> $ty {
                $ty(value)
            }
        }

        impl PartialEq for $ty {
            #[inline]
            fn eq(&self, rhs: &$ty) -> bool {
                unsafe {
                    let m = core::arch::aarch64::$beq_intrinsic(self.0, rhs.0);
                    Self(m).extract::<0>() != 0
                }
            }
        }

        impl Eq for $ty {}

        impl Add for $ty {
            type Output = Self;

            #[inline]
            fn add(self, rhs: $ty) -> Self {
                unsafe { core::arch::aarch64::$add_intrinsic(self.0, rhs.0).into() }
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
                unsafe { core::arch::aarch64::$sub_intrinsic(self.0, rhs.0).into() }
            }
        }

        impl BitAnd for $ty {
            type Output = Self;

            #[inline]
            fn bitand(self, rhs: $ty) -> Self {
                unsafe { core::arch::aarch64::$and_intrinsic(self.0, rhs.0).into() }
            }
        }

        impl BitAndAssign for $ty {
            #[inline]
            fn bitand_assign(&mut self, rhs: $ty) {
                *self = *self & rhs;
            }
        }

        impl BitXor for $ty {
            type Output = Self;

            #[inline]
            fn bitxor(self, rhs: $ty) -> Self {
                unsafe { core::arch::aarch64::$xor_intrinsic(self.0, rhs.0).into() }
            }
        }

        impl BitXorAssign for $ty {
            #[inline]
            fn bitxor_assign(&mut self, rhs: $ty) {
                *self = *self ^ rhs;
            }
        }

        impl $ty {
            #[inline]
            pub fn extract<const N: i32>(self) -> $lane_ty {
                unsafe { core::arch::aarch64::$extract_intrinsic(self.0, N) as $lane_ty }
            }

            #[inline]
            pub fn shl<const N: i32>(self) -> Self {
                unsafe { core::arch::aarch64::$shl_intrinsic(self.0, N).into() }
            }

            #[inline]
            pub fn shr<const N: i32>(self) -> Self {
                unsafe { core::arch::aarch64::$shr_intrinsic(self.0, N).into() }
            }
        }
    };
}

impl_shared!(
    u32x4,
    u32,
    uint32x4_t,
    vceqq_u32,
    vaddq_u32,
    vsubq_u32,
    vandq_u32,
    veorq_u32,
    vshlq_n_u32,
    vshrq_n_u32,
    vgetq_lane_u32
);

impl u32x4 {
    #[inline]
    pub const fn new_const(x0: u32, x1: u32, x2: u32, x3: u32) -> Self {
        // SAFETY: Transmuting between an array and a SIMD type is safe
        // https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
        unsafe { core::mem::transmute::<[u32; 4], Self>([x0, x1, x2, x3]) }
    }

    #[inline]
    pub const fn splat_const(x: u32) -> Self {
        Self::new_const(x, x, x, x)
    }

    #[inline]
    pub fn new(x0: u32, x1: u32, x2: u32, x3: u32) -> Self {
        unsafe { core::arch::aarch64::vld1q_u32([x0, x1, x2, x3].as_ptr()).into() } 
    }

    #[inline]
    pub fn splat(x: u32) -> Self {
        unsafe { core::arch::aarch64::vld1q_dup_u32([x].as_ptr()).into() }
    }
}

impl From<u64x2> for core::arch::aarch64::uint32x4_t {
    #[inline]
    fn from(value: u64x2) -> core::arch::aarch64::uint32x4_t {
        unsafe { core::arch::aarch64::vreinterpretq_u32_u64(value.into()) }
    }
}

impl From<core::arch::aarch64::uint64x2_t> for u32x4 {
    #[inline]
    fn from(value: core::arch::aarch64::uint64x2_t) -> u32x4 {
        unsafe { core::arch::aarch64::vreinterpretq_u32_u64(value).into() }
    }
}

impl From<u64x2> for u32x4 {
    #[inline]
    fn from(value: u64x2) -> u32x4 {
        Into::<core::arch::aarch64::uint32x4_t>::into(value).into()
    }
}

impl_shared!(
    u32x2,
    u32,
    uint32x2_t,
    vceq_u32,
    vadd_u32,
    vsub_u32,
    vand_u32,
    veor_u32,
    vshl_n_u32,
    vshr_n_u32,
    vget_lane_u32
);

impl u32x2 {
    #[inline]
    pub const fn new_const(x0: u32, x1: u32) -> Self {
        // SAFETY: Transmuting between an array and a SIMD type is safe
        // https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
        unsafe { core::mem::transmute::<[u32; 2], Self>([x0, x1]) }
    }

    #[inline]
    pub const fn splat_const(x: u32) -> Self {
        Self::new_const(x, x)
    }

    #[inline]
    pub fn new(x0: u32, x1: u32) -> Self {
        unsafe { core::arch::aarch64::vld1_u32([x0, x1].as_ptr()).into() } 
    }

    #[inline]
    pub fn splat(x: u32) -> Self {
        unsafe { core::arch::aarch64::vld1_dup_u32([x].as_ptr()).into() }
    }
}

impl_shared!(
    u64x2,
    u64,
    uint64x2_t,
    vceqq_u64,
    vaddq_u64,
    vsubq_u64,
    vandq_u64,
    veorq_u64,
    vshlq_n_u64,
    vshrq_n_u64,
    vgetq_lane_u64
);

impl u64x2 {
    #[inline]
    pub const fn new_const(x0: u64, x1: u64) -> Self {
        // SAFETY: Transmuting between an array and a SIMD type is safe
        // https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
        unsafe { core::mem::transmute::<[u64; 2], Self>([x0, x1]) }
    }

    #[inline]
    pub const fn splat_const(x: u64) -> Self {
        Self::new_const(x, x)
    }

        #[inline]
    pub fn new(x0: u64, x1: u64) -> Self {
        unsafe { core::arch::aarch64::vld1q_u64([x0, x1].as_ptr()).into() } 
    }

    #[inline]
    pub fn splat(x: u64) -> Self {
        unsafe { core::arch::aarch64::vld1q_dup_u64([x].as_ptr()).into() }
    }
}

impl From<core::arch::aarch64::uint32x4_t> for u64x2 {
    #[inline]
    fn from(value: core::arch::aarch64::uint32x4_t) -> u64x2 {
        unsafe { core::arch::aarch64::vreinterpretq_u64_u32(value).into() }
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct u32x4x2(pub core::arch::aarch64::uint32x4x2_t);

impl PartialEq for u32x4x2 {
    fn eq(&self, other: &Self) -> bool {
        u32x4::from(self.0 .0) == u32x4::from(other.0 .0)
            && u32x4::from(self.0 .1) == u32x4::from(other.0 .1)
    }
}

impl From<u32x4x2> for core::arch::aarch64::uint32x4x2_t {
    #[inline]
    fn from(value: u32x4x2) -> core::arch::aarch64::uint32x4x2_t {
        value.0
    }
}

impl From<core::arch::aarch64::uint32x4x2_t> for u32x4x2 {
    #[inline]
    fn from(value: core::arch::aarch64::uint32x4x2_t) -> u32x4x2 {
        u32x4x2(value)
    }
}

impl BitXor for u32x4x2 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new(
            u32x4::from(self.0 .0) ^ u32x4::from(rhs.0 .0),
            u32x4::from(self.0 .1) ^ u32x4::from(rhs.0 .1),
        )
    }
}

impl BitXorAssign for u32x4x2 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl BitAnd for u32x4x2 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new(
            u32x4::from(self.0 .0) & u32x4::from(rhs.0 .0),
            u32x4::from(self.0 .1) & u32x4::from(rhs.0 .1),
        )
    }
}

impl Add for u32x4x2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            u32x4::from(self.0 .0) + u32x4::from(rhs.0 .0),
            u32x4::from(self.0 .1) + u32x4::from(rhs.0 .1),
        )
    }
}

impl Sub for u32x4x2 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(
            u32x4::from(self.0 .0) - u32x4::from(rhs.0 .0),
            u32x4::from(self.0 .1) - u32x4::from(rhs.0 .1),
        )
    }
}

impl u32x4x2 {
    #[inline]
    pub const fn new(x0: u32x4, x1: u32x4) -> Self {
        Self(core::arch::aarch64::uint32x4x2_t(x0.0, x1.0))
    }

    #[inline]
    pub const fn splat(x: u32) -> Self {
        Self(core::arch::aarch64::uint32x4x2_t(
            u32x4::splat_const(x).0,
            u32x4::splat_const(x).0,
        ))
    }

    #[inline]
    pub fn extract<const N: i32>(self) -> u32 {
        match N {
            0 => u32x4::from(self.0 .0).extract::<0>(),
            1 => u32x4::from(self.0 .0).extract::<1>(),
            2 => u32x4::from(self.0 .0).extract::<2>(),
            3 => u32x4::from(self.0 .0).extract::<3>(),
            4 => u32x4::from(self.0 .1).extract::<0>(),
            5 => u32x4::from(self.0 .1).extract::<1>(),
            6 => u32x4::from(self.0 .1).extract::<2>(),
            7 => u32x4::from(self.0 .1).extract::<3>(),
            _ => unreachable!(),
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct u32x2x2(pub core::arch::aarch64::uint32x2x2_t);

impl PartialEq for u32x2x2 {
    fn eq(&self, other: &Self) -> bool {
        u32x2::from(self.0 .0) == u32x2::from(other.0 .0)
            && u32x2::from(self.0 .1) == u32x2::from(other.0 .1)
    }
}

impl Add for u32x2x2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            u32x2::from(self.0 .0) + u32x2::from(rhs.0 .0),
            u32x2::from(self.0 .1) + u32x2::from(rhs.0 .1),
        )
    }
}

impl u32x2x2 {
    #[inline]
    pub const fn new(x0: u32x2, x1: u32x2) -> Self {
        Self(core::arch::aarch64::uint32x2x2_t(x0.0, x1.0))
    }

    #[inline]
    pub fn shl<const N: i32>(self) -> Self {
        Self(core::arch::aarch64::uint32x2x2_t(
            u32x2::from(self.0 .0).shl::<N>().0,
            u32x2::from(self.0 .1).shl::<N>().0,
        ))
    }

    #[inline]
    #[allow(dead_code)]
    pub fn extract<const N: i32>(self) -> u32 {
        match N {
            0 => u32x2::from(self.0 .0).extract::<0>(),
            1 => u32x2::from(self.0 .0).extract::<1>(),
            2 => u32x2::from(self.0 .1).extract::<0>(),
            3 => u32x2::from(self.0 .1).extract::<1>(),
            _ => unreachable!(),
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct i32x4(core::arch::aarch64::int32x4_t);

impl From<i32x4> for core::arch::aarch64::int32x4_t {
    #[inline]
    fn from(value: i32x4) -> core::arch::aarch64::int32x4_t {
        value.0
    }
}

impl From<core::arch::aarch64::int32x4_t> for i32x4 {
    #[inline]
    fn from(value: core::arch::aarch64::int32x4_t) -> i32x4 {
        i32x4(value)
    }
}

impl i32x4 {
    #[inline]
    pub const fn new_const(x0: i32, x1: i32, x2: i32, x3: i32) -> Self {
        // SAFETY: Transmuting between an array and a SIMD type is safe
        // https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
        unsafe { core::mem::transmute::<[i32; 4], Self>([x0, x1, x2, x3]) }
    }

    #[inline]
    pub fn new(x0: i32, x1: i32, x2: i32, x3: i32) -> Self {
        unsafe { core::arch::aarch64::vld1q_s32([x0, x1, x2, x3].as_ptr()).into() }
    }
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct u64x2x2(pub core::arch::aarch64::uint64x2x2_t);

impl Add for u64x2x2 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(core::arch::aarch64::uint64x2x2_t(
            (u64x2::from(self.0 .0) + u64x2::from(rhs.0 .0)).into(),
            (u64x2::from(self.0 .1) + u64x2::from(rhs.0 .1)).into(),
        ))
    }
}

impl BitAnd for u64x2x2 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(core::arch::aarch64::uint64x2x2_t(
            (u64x2::from(self.0 .0) & u64x2::from(rhs.0 .0)).into(),
            (u64x2::from(self.0 .1) & u64x2::from(rhs.0 .1)).into(),
        ))
    }
}

impl u64x2x2 {
    #[inline]
    pub const fn new(x0: u64x2, x1: u64x2) -> Self {
        Self(core::arch::aarch64::uint64x2x2_t(x0.0, x1.0))
    }

    #[inline]
    pub const fn splat_const(x: u64) -> Self {
        Self::new(u64x2::splat_const(x), u64x2::splat_const(x))
    }

    #[inline]
    pub fn shl<const N: i32>(self) -> Self {
        Self(core::arch::aarch64::uint64x2x2_t(
            u64x2::from(self.0 .0).shl::<N>().into(),
            u64x2::from(self.0 .1).shl::<N>().into(),
        ))
    }

    #[inline]
    pub fn shr<const N: i32>(self) -> Self {
        Self(core::arch::aarch64::uint64x2x2_t(
            u64x2::from(self.0 .0).shr::<N>().into(),
            u64x2::from(self.0 .1).shr::<N>().into(),
        ))
    }
}
