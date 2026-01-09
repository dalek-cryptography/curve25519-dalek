use core::ffi::c_char;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::short_weierstrass::SwPoint;
use std::ffi::CStr;

/// Affine point layout compatible with SPPARK `affine_t` (host-side).
///
/// Coordinates are canonical little-endian limb arrays; SPPARK expects
/// Montgomery form, so call-side conversion is still required.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpparkAffine {
    pub x: [u64; 4],
    pub y: [u64; 4],
}

/// Scalar layout compatible with SPPARK `fr_t` (host-side).
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpparkScalar {
    pub limbs: [u64; 4],
}

/// Byte-serialized affine layout for SPPARK conversion helpers.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpparkAffineBytes {
    pub x: [u8; 32],
    pub y: [u8; 32],
}

/// Byte-serialized scalar layout for SPPARK conversion helpers.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpparkScalarBytes {
    pub s: [u8; 32],
}

/// Error type matching SPPARK's FFI error layout.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpparkError {
    pub code: i32,
    pub str: *mut c_char,
}

fn le_bytes_to_u64x4(bytes: [u8; 32]) -> [u64; 4] {
    let mut limbs = [0u64; 4];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&bytes[i * 8..(i + 1) * 8]);
        *limb = u64::from_le_bytes(buf);
    }
    limbs
}

/// Convert a short Weierstrass point into SPPARK affine layout.
///
/// The identity is encoded as (0, 0) to match SPPARK `affine_t` rules.
pub fn sw_point_to_sppark_affine(point: &SwPoint) -> SpparkAffine {
    match point.to_affine_le_bytes() {
        Some((x, y)) => SpparkAffine {
            x: le_bytes_to_u64x4(x),
            y: le_bytes_to_u64x4(y),
        },
        None => SpparkAffine {
            x: [0u64; 4],
            y: [0u64; 4],
        },
    }
}

/// Convert a scalar into SPPARK scalar limb layout.
pub fn scalar_to_sppark_scalar(scalar: &Scalar) -> SpparkScalar {
    let bytes = scalar.to_bytes();
    SpparkScalar {
        limbs: le_bytes_to_u64x4(bytes),
    }
}

/// Convert a short Weierstrass point into byte-serialized affine layout.
pub fn sw_point_to_sppark_affine_bytes(point: &SwPoint) -> SpparkAffineBytes {
    match point.to_affine_le_bytes() {
        Some((x, y)) => SpparkAffineBytes { x, y },
        None => SpparkAffineBytes {
            x: [0u8; 32],
            y: [0u8; 32],
        },
    }
}

/// Convert a scalar into byte-serialized layout.
pub fn scalar_to_sppark_scalar_bytes(scalar: &Scalar) -> SpparkScalarBytes {
    SpparkScalarBytes {
        s: scalar.to_bytes(),
    }
}

unsafe extern "C" {
    pub fn mult_pippenger_curve25519_bytes_affine(
        out: *mut SpparkAffineBytes,
        points: *const SpparkAffineBytes,
        npoints: usize,
        scalars: *const SpparkScalarBytes,
    ) -> SpparkError;
}

/// Execute MSM on the CUDA backend using byte-serialized affine inputs.
pub fn msm_curve25519_gpu(points: &[SwPoint], scalars: &[Scalar]) -> Result<SwPoint, String> {
    let out = msm_curve25519_gpu_bytes(points, scalars)?;
    if out.x == [0u8; 32] && out.y == [0u8; 32] {
        return Ok(SwPoint::Identity);
    }
    SwPoint::from_affine_le_bytes(out.x, out.y)
        .ok_or_else(|| "invalid point returned from CUDA".to_string())
}

fn msm_curve25519_cpu(points: &[SwPoint], scalars: &[Scalar]) -> Result<SwPoint, String> {
    use curve25519_dalek::edwards::EdwardsPoint;
    use curve25519_dalek::traits::Identity;
    use curve25519_dalek::traits::VartimeMultiscalarMul;
    use rayon::prelude::*;

    if points.len() != scalars.len() {
        return Err("length mismatch".to_string());
    }
    if points.is_empty() {
        return Ok(SwPoint::Identity);
    }

    let ed_points: Vec<EdwardsPoint> = points
        .par_iter()
        .map(|point| {
            point
                .to_edwards()
                .ok_or_else(|| "invalid short-weierstrass point".to_string())
        })
        .collect::<Result<_, _>>()?;

    let chunk = 1024usize.max(points.len() / rayon::current_num_threads().max(1));
    let ed_out = ed_points
        .par_chunks(chunk)
        .zip(scalars.par_chunks(chunk))
        .map(|(pchunk, schunk)| EdwardsPoint::vartime_multiscalar_mul(schunk, pchunk))
        .reduce(EdwardsPoint::identity, |a, b| a + b);
    Ok(SwPoint::from_edwards(&ed_out))
}

/// Execute MSM using CUDA when available, otherwise fall back to CPU in Rust.
pub fn msm_curve25519(points: &[SwPoint], scalars: &[Scalar]) -> Result<SwPoint, String> {
    if let Ok(out) = msm_curve25519_gpu(points, scalars) {
        return Ok(out);
    }
    msm_curve25519_cpu(points, scalars)
}

/// Execute MSM on the CUDA backend and return byte-serialized affine output.
pub fn msm_curve25519_gpu_bytes(
    points: &[SwPoint],
    scalars: &[Scalar],
) -> Result<SpparkAffineBytes, String> {
    if points.len() != scalars.len() {
        return Err("length mismatch".to_string());
    }

    let point_bytes: Vec<SpparkAffineBytes> =
        points.iter().map(sw_point_to_sppark_affine_bytes).collect();
    let scalar_bytes: Vec<SpparkScalarBytes> =
        scalars.iter().map(scalar_to_sppark_scalar_bytes).collect();

    let mut out = SpparkAffineBytes {
        x: [0u8; 32],
        y: [0u8; 32],
    };

    let err = unsafe {
        mult_pippenger_curve25519_bytes_affine(
            &mut out as *mut _,
            point_bytes.as_ptr(),
            point_bytes.len(),
            scalar_bytes.as_ptr(),
        )
    };

    if err.code != 0 {
        let message = if !err.str.is_null() {
            unsafe { CStr::from_ptr(err.str) }
                .to_str()
                .unwrap_or("sppark error")
                .to_string()
        } else {
            format!("sppark error code {}", err.code)
        };
        return Err(message);
    }

    Ok(out)
}

#[cfg(test)]
mod tests;
