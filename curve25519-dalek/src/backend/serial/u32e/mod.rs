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

//! The `u32` backend uses `u32`s and a `(u32, u32) -> u64` multiplier.
//!
//! This code is intended to be portable, but it requires that
//! multiplication of two \\(32\\)-bit values to a \\(64\\)-bit result
//! is constant-time on the target platform.

use utralib::generated::*;

pub mod field;

pub mod scalar;

pub mod constants;

pub(crate) static mut ENGINE_BASE: Option<xous::MemoryRange> = None;
pub(crate) static mut ENGINE_MEM: Option<xous::MemoryRange> = None;

pub(crate) const NUM_REGS: usize = 32;
pub(crate) const BITWIDTH: usize = 256;
pub(crate) const NUM_WINDOWS: usize = 16;
pub(crate) const RF_SIZE_IN_U32: usize = NUM_REGS * (BITWIDTH / 32); // 32 registers, 256 bits/register/32 bits per u32
pub(crate) const TOTAL_RF_SIZE_IN_U32: usize = NUM_REGS * (BITWIDTH / 32) * NUM_WINDOWS; // 32 registers, 256 bits/register/32 bits per u32, times 16 windows
pub(crate) const RF_U8_BASE: usize = 0x1_0000;
#[allow(dead_code)]
pub(crate) const RF_U32_BASE: usize = 0x1_0000 / 4;

pub fn free_engine() {
    log::debug!("free engine");
    if let Some(base) = unsafe { ENGINE_BASE.take() } {
        xous::unmap_memory(base).unwrap();
    }
    if let Some(mem) = unsafe { ENGINE_MEM.take() } {
        xous::unmap_memory(mem).unwrap();
    }
}

pub fn ensure_engine() {
    if unsafe { ENGINE_BASE.is_none() } {
        let base = xous::syscall::map_memory(
            xous::MemoryAddress::new(utra::engine::HW_ENGINE_BASE),
            None,
            4096,
            xous::MemoryFlags::R | xous::MemoryFlags::W,
        )
        .expect("couldn't map engine CSR range");
        log::debug!("claiming engine csr {:x?}", base.as_ptr());
        unsafe {
            ENGINE_BASE = Some(base);
        }
    }
    if unsafe { ENGINE_MEM.is_none() } {
        let mem = xous::syscall::map_memory(
            xous::MemoryAddress::new(HW_ENGINE_MEM),
            None,
            HW_ENGINE_MEM_LEN,
            xous::MemoryFlags::R | xous::MemoryFlags::W,
        )
        .expect("couldn't map engine memory window range");
        log::debug!("claiming engine mem {:x?}", mem.as_ptr());
        unsafe { ENGINE_MEM = Some(mem) };
    }
}

pub(crate) fn copy_to_rf(bytes: [u8; 32], register: usize, rf: &mut [u32], window: usize) {
    use core::convert::TryInto;
    for (byte, rf_dst) in bytes.chunks_exact(4).zip(
        rf[window * RF_SIZE_IN_U32 + register * 8..window * RF_SIZE_IN_U32 + (register + 1) * 8]
            .iter_mut(),
    ) {
        *rf_dst = u32::from_le_bytes(byte.try_into().expect("chunks_exact failed us"));
    }
}

pub(crate) fn copy_from_rf(register: usize, rf: &[u32], window: usize) -> [u8; 32] {
    let mut ret: [u8; 32] = [0; 32];

    for (src, dst) in rf
        [window * RF_SIZE_IN_U32 + register * 8..window * RF_SIZE_IN_U32 + (register + 1) * 8]
        .iter()
        .zip(ret.chunks_exact_mut(4).into_iter())
    {
        for (&src_byte, dst_byte) in src.to_le_bytes().iter().zip(dst.iter_mut()) {
            *dst_byte = src_byte;
        }
    }

    ret
}

pub(crate) fn get_single_result(rf_hw: &[u32], window: usize, r: usize) -> [u8; 32] {
    // TODO: put handlers for illegal opcodes, suspend/resume catch

    let mut ret_r: [u8; 32] = [0; 32];
    for (&src, dst) in rf_hw[window * RF_SIZE_IN_U32 + r * 8..window * RF_SIZE_IN_U32 + (r + 1) * 8]
        .iter()
        .zip(ret_r.chunks_exact_mut(4))
    {
        for (&src_byte, dst_byte) in src.to_le_bytes().iter().zip(dst.iter_mut()) {
            *dst_byte = src_byte;
        }
    }
    ret_r
}

/// This assumes that arguments have been loaded in appropriate locations for the microcode
/// and that the result is always in r31.
pub(crate) fn run_job(
    ucode_hw: &mut [u32],
    rf_hw: &[u32],
    mcode: &[i32],
    window: usize,
) -> [u8; 32] {
    let mut engine = utralib::CSR::new(unsafe { ENGINE_BASE.unwrap() }.as_mut_ptr() as *mut u32);

    let mpstart = 0;

    for (&src, dst) in mcode.iter().zip(ucode_hw[mpstart as usize..].iter_mut()) {
        unsafe { (dst as *mut u32).write_volatile(src as u32) };
    }
    let job_len = mcode.len() as u32;

    engine.wfo(utra::engine::WINDOW_WINDOW, window as u32); // this value should now be validated because an invalid window would cause a panic on slice copy
    engine.wfo(utra::engine::MPSTART_MPSTART, mpstart);
    engine.wfo(utra::engine::MPLEN_MPLEN, job_len);

    engine.wfo(utra::engine::CONTROL_GO, 1);
    while engine.rf(utra::engine::STATUS_RUNNING) != 0 {}

    get_single_result(&rf_hw, window, 31)
}
