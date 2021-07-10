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

//! Field arithmetic modulo \\(p = 2\^{255} - 19\\), using \\(32\\)-bit
//! limbs with \\(64\\)-bit products.
//!
//! This code was originally derived from Adam Langley's Golang ed25519
//! implementation, and was then rewritten to use unsigned limbs instead
//! of signed limbs.

use core::fmt::Debug;
use core::ops::Neg;
use core::ops::{Add, AddAssign};
use core::ops::{Mul, MulAssign};
use core::ops::{Sub, SubAssign};

use subtle::Choice;
use subtle::ConditionallySelectable;

use zeroize::Zeroize;

/// A `Engine25519` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 32-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{25.5}\\) as ten `u32`s.  This means that a field
/// element \\(x\\) is represented as
/// $$
/// x = \sum\_{i=0}\^9 x\_i 2\^{\lceil i \frac {51} 2 \rceil}
///   = x\_0 + x\_1 2\^{26} + x\_2 2\^{51} + x\_3 2\^{77} + \cdots + x\_9 2\^{230};
/// $$
/// the coefficients are alternately bounded by \\(2\^{25}\\) and
/// \\(2\^{26}\\).  The limbs are allowed to grow between reductions up
/// to \\(2\^{25+b}\\) or \\(2\^{26+b}\\), where \\(b = 1.75\\).
///
/// # Note
///
/// The `curve25519_dalek::field` module provides a type alias
/// `curve25519_dalek::field::FieldElement` to either `FieldElement51`
/// or `Engine25519`.
///
/// The backend-specific type `Engine25519` should not be used
/// outside of the `curve25519_dalek::field` module.

//#[macro_use]
//mod debug;

#[macro_use]
use debug;

#[derive(Copy, Clone, Debug)]
pub struct Engine25519(
    pub (crate) [u8; 32]
);
#[derive(Debug)]
pub(crate) enum EngineOp {
    Mul,
    Add,
    Sub,
}

pub(crate) fn engine(a: &[u8; 32], b: &[u8; 32], op: EngineOp) -> Engine25519 {
    use core::convert::TryInto;
    use utralib::generated::*;
    let mut engine = utralib::CSR::new(utra::engine::HW_ENGINE_BASE as *mut u32);
    let mcode: &'static mut [u32] = unsafe{ core::slice::from_raw_parts_mut(utralib::HW_ENGINE_MEM as *mut u32, 1024) };
    // allocate the first three registers
    let rf: [&'static mut [u32]; 3] =
    unsafe { [
        core::slice::from_raw_parts_mut((utralib::HW_ENGINE_MEM + 0x1_0000 + 0 * 32) as *mut u32, 8),
        core::slice::from_raw_parts_mut((utralib::HW_ENGINE_MEM + 0x1_0000 + 1 * 32) as *mut u32, 8),
        core::slice::from_raw_parts_mut((utralib::HW_ENGINE_MEM + 0x1_0000 + 2 * 32) as *mut u32, 8),
    ] };
    match op {
        EngineOp::Mul => {
            let prog = assemble_engine25519!(
                start:
                    mul %2, %0, %1
                    fin
            );
            for (&src, dest) in prog.iter().zip(mcode.iter_mut()) {
                *dest = src;
            }
            engine.wfo(utra::engine::MPLEN_MPLEN, prog.len() as u32);
        },
        EngineOp::Add => {
            let prog = assemble_engine25519!(
            start:
                add %2, %0, %1
                trd %30, %2
                sub %2, %2, %30
                fin
            );
            for (&src, dest) in prog.iter().zip(mcode.iter_mut()) {
                *dest = src;
            }
            engine.wfo(utra::engine::MPLEN_MPLEN, prog.len() as u32);
        },
        EngineOp::Sub => {
            let prog = assemble_engine25519!(
            start:
                sub %1, #3, %1
                add %2, %0, %1
                trd %30, %2
                sub %2, %2, %30
                fin
            );
            for (&src, dest) in prog.iter().zip(mcode.iter_mut()) {
                *dest = src;
            }
            engine.wfo(utra::engine::MPLEN_MPLEN, prog.len() as u32);
        },
    }
    // copy a arg
    for (src, dst) in a.chunks_exact(4).zip(rf[0].iter_mut()) {
        unsafe{ (dst as *mut u32).write_volatile(u32::from_le_bytes(src[0..4].try_into().unwrap()));}
    }

    // copy b arg
    for (src, dst) in b.chunks_exact(4).zip(rf[1].iter_mut()) {
        unsafe{ (dst as *mut u32).write_volatile(u32::from_le_bytes(src[0..4].try_into().unwrap()));}
    }

    engine.wfo(utra::engine::CONTROL_GO, 1);
    while engine.rf(utra::engine::STATUS_RUNNING) != 0 {}

    // return result, always in reg 2
    let mut result: [u8; 32] = [0; 32];
    for (&src, dst) in rf[2].iter().zip(result.chunks_exact_mut(4)) {
        for (&sb, db) in src.to_le_bytes().iter().zip(dst.iter_mut()) {
            *db = sb;
        }
    }

    Engine25519 {
        0: result
    }
}

impl Zeroize for Engine25519 {
    fn zeroize(&mut self) {
        self.0.zeroize();
    }
}

impl<'b> AddAssign<&'b Engine25519> for Engine25519 {
    fn add_assign(&mut self, _rhs: &'b Engine25519) {
        self.0 = engine(&self.0, &_rhs.0, EngineOp::Add).0;
    }
}

impl<'a, 'b> Add<&'b Engine25519> for &'a Engine25519 {
    type Output = Engine25519;
    fn add(self, _rhs: &'b Engine25519) -> Engine25519 {
        let mut output = *self;
        output += _rhs;
        output
    }
}

impl<'b> SubAssign<&'b Engine25519> for Engine25519 {
    fn sub_assign(&mut self, _rhs: &'b Engine25519) {
        self.0 = engine(&self.0, &_rhs.0, EngineOp::Sub).0;
    }
}

impl<'a, 'b> Sub<&'b Engine25519> for &'a Engine25519 {
    type Output = Engine25519;
    fn sub(self, _rhs: &'b Engine25519) -> Engine25519 {
        let mut output = *self;
        output -= _rhs;
        output
    }
}

impl<'b> MulAssign<&'b Engine25519> for Engine25519 {
    fn mul_assign(&mut self, _rhs: &'b Engine25519) {
        let result = (self as &Engine25519) * _rhs;
        self.0 = result.0;
    }
}

impl<'a, 'b> Mul<&'b Engine25519> for &'a Engine25519 {
    type Output = Engine25519;
    fn mul(self, _rhs: &'b Engine25519) -> Engine25519 {
        let ret = engine(&self.0, &_rhs.0, EngineOp::Mul);
        //println!("a:{:?}\n\rb:{:?}\n\rout:{:?}", self.0, _rhs.0, ret.0);
        ret
    }
}

impl<'a> Neg for &'a Engine25519 {
    type Output = Engine25519;
    fn neg(self) -> Engine25519 {
        let mut output = *self;
        output.negate();
        output
    }
}

impl ConditionallySelectable for Engine25519 {
    fn conditional_select(
        a: &Engine25519,
        b: &Engine25519,
        choice: Choice,
    ) -> Engine25519 {
        Engine25519([
            u8::conditional_select(&a.0[0], &b.0[0], choice),
            u8::conditional_select(&a.0[1], &b.0[1], choice),
            u8::conditional_select(&a.0[2], &b.0[2], choice),
            u8::conditional_select(&a.0[3], &b.0[3], choice),
            u8::conditional_select(&a.0[4], &b.0[4], choice),
            u8::conditional_select(&a.0[5], &b.0[5], choice),
            u8::conditional_select(&a.0[6], &b.0[6], choice),
            u8::conditional_select(&a.0[7], &b.0[7], choice),
            u8::conditional_select(&a.0[8], &b.0[8], choice),
            u8::conditional_select(&a.0[9], &b.0[9], choice),
            u8::conditional_select(&a.0[10], &b.0[10], choice),
            u8::conditional_select(&a.0[11], &b.0[11], choice),
            u8::conditional_select(&a.0[12], &b.0[12], choice),
            u8::conditional_select(&a.0[13], &b.0[13], choice),
            u8::conditional_select(&a.0[14], &b.0[14], choice),
            u8::conditional_select(&a.0[15], &b.0[15], choice),
            u8::conditional_select(&a.0[16], &b.0[16], choice),
            u8::conditional_select(&a.0[17], &b.0[17], choice),
            u8::conditional_select(&a.0[18], &b.0[18], choice),
            u8::conditional_select(&a.0[19], &b.0[19], choice),
            u8::conditional_select(&a.0[20], &b.0[20], choice),
            u8::conditional_select(&a.0[21], &b.0[21], choice),
            u8::conditional_select(&a.0[22], &b.0[22], choice),
            u8::conditional_select(&a.0[23], &b.0[23], choice),
            u8::conditional_select(&a.0[24], &b.0[24], choice),
            u8::conditional_select(&a.0[25], &b.0[25], choice),
            u8::conditional_select(&a.0[26], &b.0[26], choice),
            u8::conditional_select(&a.0[27], &b.0[27], choice),
            u8::conditional_select(&a.0[28], &b.0[28], choice),
            u8::conditional_select(&a.0[29], &b.0[29], choice),
            u8::conditional_select(&a.0[30], &b.0[30], choice),
            u8::conditional_select(&a.0[31], &b.0[31], choice),
        ])
    }

    fn conditional_assign(&mut self, other: &Engine25519, choice: Choice) {
        self.0[0].conditional_assign(&other.0[0], choice);
        self.0[1].conditional_assign(&other.0[1], choice);
        self.0[2].conditional_assign(&other.0[2], choice);
        self.0[3].conditional_assign(&other.0[3], choice);
        self.0[4].conditional_assign(&other.0[4], choice);
        self.0[5].conditional_assign(&other.0[5], choice);
        self.0[6].conditional_assign(&other.0[6], choice);
        self.0[7].conditional_assign(&other.0[7], choice);
        self.0[8].conditional_assign(&other.0[8], choice);
        self.0[9].conditional_assign(&other.0[9], choice);
        self.0[10].conditional_assign(&other.0[10], choice);
        self.0[11].conditional_assign(&other.0[11], choice);
        self.0[12].conditional_assign(&other.0[12], choice);
        self.0[13].conditional_assign(&other.0[13], choice);
        self.0[14].conditional_assign(&other.0[14], choice);
        self.0[15].conditional_assign(&other.0[15], choice);
        self.0[16].conditional_assign(&other.0[16], choice);
        self.0[17].conditional_assign(&other.0[17], choice);
        self.0[18].conditional_assign(&other.0[18], choice);
        self.0[19].conditional_assign(&other.0[19], choice);
        self.0[20].conditional_assign(&other.0[20], choice);
        self.0[21].conditional_assign(&other.0[21], choice);
        self.0[22].conditional_assign(&other.0[22], choice);
        self.0[23].conditional_assign(&other.0[23], choice);
        self.0[24].conditional_assign(&other.0[24], choice);
        self.0[25].conditional_assign(&other.0[25], choice);
        self.0[26].conditional_assign(&other.0[26], choice);
        self.0[27].conditional_assign(&other.0[27], choice);
        self.0[28].conditional_assign(&other.0[28], choice);
        self.0[29].conditional_assign(&other.0[29], choice);
        self.0[30].conditional_assign(&other.0[30], choice);
        self.0[31].conditional_assign(&other.0[31], choice);
    }

    fn conditional_swap(a: &mut Engine25519, b: &mut Engine25519, choice: Choice) {
        u8::conditional_swap(&mut a.0[0], &mut b.0[0], choice);
        u8::conditional_swap(&mut a.0[1], &mut b.0[1], choice);
        u8::conditional_swap(&mut a.0[2], &mut b.0[2], choice);
        u8::conditional_swap(&mut a.0[3], &mut b.0[3], choice);
        u8::conditional_swap(&mut a.0[4], &mut b.0[4], choice);
        u8::conditional_swap(&mut a.0[5], &mut b.0[5], choice);
        u8::conditional_swap(&mut a.0[6], &mut b.0[6], choice);
        u8::conditional_swap(&mut a.0[7], &mut b.0[7], choice);
        u8::conditional_swap(&mut a.0[8], &mut b.0[8], choice);
        u8::conditional_swap(&mut a.0[9], &mut b.0[9], choice);
        u8::conditional_swap(&mut a.0[10], &mut b.0[10], choice);
        u8::conditional_swap(&mut a.0[11], &mut b.0[11], choice);
        u8::conditional_swap(&mut a.0[12], &mut b.0[12], choice);
        u8::conditional_swap(&mut a.0[13], &mut b.0[13], choice);
        u8::conditional_swap(&mut a.0[14], &mut b.0[14], choice);
        u8::conditional_swap(&mut a.0[15], &mut b.0[15], choice);
        u8::conditional_swap(&mut a.0[16], &mut b.0[16], choice);
        u8::conditional_swap(&mut a.0[17], &mut b.0[17], choice);
        u8::conditional_swap(&mut a.0[18], &mut b.0[18], choice);
        u8::conditional_swap(&mut a.0[19], &mut b.0[19], choice);
        u8::conditional_swap(&mut a.0[20], &mut b.0[20], choice);
        u8::conditional_swap(&mut a.0[21], &mut b.0[21], choice);
        u8::conditional_swap(&mut a.0[22], &mut b.0[22], choice);
        u8::conditional_swap(&mut a.0[23], &mut b.0[23], choice);
        u8::conditional_swap(&mut a.0[24], &mut b.0[24], choice);
        u8::conditional_swap(&mut a.0[25], &mut b.0[25], choice);
        u8::conditional_swap(&mut a.0[26], &mut b.0[26], choice);
        u8::conditional_swap(&mut a.0[27], &mut b.0[27], choice);
        u8::conditional_swap(&mut a.0[28], &mut b.0[28], choice);
        u8::conditional_swap(&mut a.0[29], &mut b.0[29], choice);
        u8::conditional_swap(&mut a.0[30], &mut b.0[30], choice);
        u8::conditional_swap(&mut a.0[31], &mut b.0[31], choice);
    }
}

impl Engine25519 {
    /// Invert the sign of this field element
    pub fn negate(&mut self) {
        let zero: [u8; 32] = [0; 32];
        *self = engine(&zero, &self.0, EngineOp::Sub);
    }

    /// Construct zero.
    pub fn zero() -> Engine25519 {
        Engine25519([ 0 ; 32 ])
    }

    /// Construct one.
    pub fn one() -> Engine25519 {
        Engine25519([   1, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0,
            ])
    }

    /// Construct -1.
    pub fn minus_one() -> Engine25519 {
        Engine25519([236, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127])
    }

    /// Given `k > 0`, return `self^(2^k)`.
    pub fn pow2k(&self, k: u32) -> Engine25519 {
        debug_assert!( k > 0 );
        let mut z = self.square();
        for _ in 1..k {
            z = z.square();
        }
        z
    }

    /// Load a `Engine25519` from the low 255 bits of a 256-bit
    /// input.
    ///
    /// # Warning
    ///
    /// This function does not check that the input used the canonical
    /// representative.  It masks the high bit, but it will happily
    /// decode 2^255 - 18 to 1.  Applications that require a canonical
    /// encoding of every field element should decode, re-encode to
    /// the canonical encoding, and check that the input was
    /// canonical.
    pub fn from_bytes(data: &[u8; 32]) -> Engine25519 { //FeFromBytes
        let mut mask_data = data.clone();
        mask_data[31] &= 0x7F; // mask off the high bit per comment above
        Engine25519 {
            0: mask_data,
        }
    }

    /// Serialize this `FieldElement51` to a 32-byte array.  The
    /// encoding is canonical.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }

    /// Compute `self^2`.
    pub fn square(&self) -> Engine25519 {
        let a = self.0;
        let b = self.0;
        engine(&a, &b, EngineOp::Mul)
    }

    /// Compute `2*self^2`.
    pub fn square2(&self) -> Engine25519 {
        let a = self.0;
        let b = self.0;
        let innersq = engine(&a, &b, EngineOp::Mul).0;
        engine(&innersq, &innersq, EngineOp::Add)
    }
}
