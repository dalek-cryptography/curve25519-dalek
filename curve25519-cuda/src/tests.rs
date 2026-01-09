
use super::{
    msm_curve25519, scalar_to_sppark_scalar, scalar_to_sppark_scalar_bytes,
    sw_point_to_sppark_affine, sw_point_to_sppark_affine_bytes,
};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::short_weierstrass::SwPoint;
use rayon::prelude::*;

fn cpu_expected(points: &[SwPoint], scalars: &[Scalar]) -> SwPoint {
    use curve25519_dalek::traits::VartimeMultiscalarMul;
    let mut ed_points = Vec::with_capacity(points.len());
    for point in points {
        ed_points.push(point.to_edwards().expect("valid sw point"));
    }
    let out = EdwardsPoint::vartime_multiscalar_mul(scalars, &ed_points);
    SwPoint::from_edwards(&out)
}

fn require_cuda() {
    assert!(cfg!(curve25519_cuda), "CUDA backend not available");
}

#[test]
fn sppark_affine_identity_is_zero() {
    let affine = sw_point_to_sppark_affine(&SwPoint::Identity);
    assert_eq!(affine.x, [0u64; 4]);
    assert_eq!(affine.y, [0u64; 4]);
}

#[test]
fn sppark_scalar_one_is_one() {
    let scalar = scalar_to_sppark_scalar(&Scalar::ONE);
    assert_eq!(scalar.limbs, [1u64, 0, 0, 0]);
}

#[test]
fn sppark_affine_bytes_identity_is_zero() {
    let affine = sw_point_to_sppark_affine_bytes(&SwPoint::Identity);
    assert_eq!(affine.x, [0u8; 32]);
    assert_eq!(affine.y, [0u8; 32]);
}

#[test]
fn sppark_scalar_bytes_one_is_one() {
    let scalar = scalar_to_sppark_scalar_bytes(&Scalar::ONE);
    let mut expected = [0u8; 32];
    expected[0] = 1;
    assert_eq!(scalar.s, expected);
}

#[test]
fn msm_curve25519_rejects_length_mismatch() {
    let base = SwPoint::from_edwards(&curve25519_dalek::constants::ED25519_BASEPOINT_POINT);
    let points = vec![base, base];
    let scalars = vec![Scalar::ONE];
    let err = msm_curve25519(&points, &scalars).unwrap_err();
    assert!(err.contains("length mismatch"));
}

#[test]
fn msm_curve25519_empty_returns_identity() {
    let out = msm_curve25519(&[], &[]).expect("empty msm");
    assert_eq!(out, SwPoint::Identity);
}

#[test]
fn msm_curve25519_matches_cpu_small() {
    let base = SwPoint::from_edwards(&curve25519_dalek::constants::ED25519_BASEPOINT_POINT);
    let points = vec![base, base, base.add(&base)];
    let scalars = vec![Scalar::ONE, Scalar::from(2u64), Scalar::from(3u64)];
    let out = msm_curve25519(&points, &scalars).expect("msm");
    let expected = cpu_expected(&points, &scalars);
    assert_eq!(out, expected);
}

#[test]
fn msm_curve25519_high_bit_scalars() {
    let base = SwPoint::from_edwards(&curve25519_dalek::constants::ED25519_BASEPOINT_POINT);
    let points = vec![base, base.add(&base)];
    let mut high = [0u8; 32];
    high[31] = 0x80;
    let scalars = vec![Scalar::from_bytes_mod_order(high), Scalar::from(5u64)];
    let out = msm_curve25519(&points, &scalars).expect("msm");
    let expected = cpu_expected(&points, &scalars);
    assert_eq!(out, expected);
}

#[test]
fn msm_curve25519_infinity_points() {
    let base = SwPoint::from_edwards(&curve25519_dalek::constants::ED25519_BASEPOINT_POINT);
    let points = vec![SwPoint::Identity, base, SwPoint::Identity];
    let scalars = vec![Scalar::from(7u64), Scalar::from(9u64), Scalar::from(11u64)];
    let out = msm_curve25519(&points, &scalars).expect("msm");
    let expected = cpu_expected(&points, &scalars);
    assert_eq!(out, expected);
}

fn edwards_msm(
    points: &[curve25519_dalek::edwards::EdwardsPoint],
    scalars: &[Scalar],
) -> curve25519_dalek::edwards::EdwardsPoint {
    use curve25519_dalek::traits::Identity;

    let mut acc = curve25519_dalek::edwards::EdwardsPoint::identity();
    for (p, s) in points.iter().zip(scalars.iter()) {
        acc = acc + (p * s);
    }
    acc
}

fn splitmix64(state: &mut u64) -> u64 {
    let mut z = {
        *state = state.wrapping_add(0x9e3779b97f4a7c15);
        *state
    };
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

fn bytes_from_seed(seed: u64) -> [u8; 32] {
    let mut state = seed;
    let mut out = [0u8; 32];
    for chunk in out.chunks_exact_mut(8) {
        let v = splitmix64(&mut state).to_le_bytes();
        chunk.copy_from_slice(&v);
    }
    out
}

fn negate_field_bytes(y: [u8; 32]) -> [u8; 32] {
    if y == [0u8; 32] {
        return y;
    }
    let p = [
        0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ];
    let mut out = [0u8; 32];
    let mut borrow = 0u16;
    for i in 0..32 {
        let pi = p[i] as i16;
        let yi = y[i] as i16;
        let mut val = pi - yi - borrow as i16;
        if val < 0 {
            val += 256;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out[i] = val as u8;
    }
    out
}

fn affine_bytes_match(out: &crate::SpparkAffineBytes, expected: &crate::SpparkAffineBytes) -> bool {
    if out.x != expected.x {
        return false;
    }
    if out.y == expected.y {
        return true;
    }
    out.y == negate_field_bytes(expected.y)
}

#[test]
fn cuda_msm_matches_cpu() {
    use super::msm_curve25519_gpu_bytes;
    use curve25519_dalek::constants;

    require_cuda();

    let p_ed = constants::ED25519_BASEPOINT_POINT;
    let p = SwPoint::from_edwards(&p_ed);
    let points = vec![p, p];
    let scalars = vec![Scalar::ONE, Scalar::from(2u64)];

    let expected_ed = edwards_msm(&[p_ed, p_ed], &scalars);
    let expected = SwPoint::from_edwards(&expected_ed);
    let expected_bytes = sw_point_to_sppark_affine_bytes(&expected);
    let out = msm_curve25519_gpu_bytes(&points, &scalars).expect("cuda msm");

    assert!(
        affine_bytes_match(&out, &expected_bytes),
        "unexpected MSM output"
    );
}

#[test]
fn cuda_single_scalar_mul() {
    use super::msm_curve25519_gpu_bytes;
    use curve25519_dalek::constants;

    require_cuda();

    let base_ed = constants::ED25519_BASEPOINT_POINT;
    let base = SwPoint::from_edwards(&base_ed);

    // Test basepoint with small scalars
    let scalar3 = Scalar::from(3u64);

    let expected_ed_3 = base_ed * scalar3;
    let expected_3 = SwPoint::from_edwards(&expected_ed_3);
    let expected_bytes_3 = sw_point_to_sppark_affine_bytes(&expected_3);
    let out_3 = msm_curve25519_gpu_bytes(&[base], &[scalar3]).expect("cuda msm");

    assert!(
        affine_bytes_match(&out_3, &expected_bytes_3),
        "BASEPOINT * 3 should match"
    );

    // Test basepoint with random scalar
    let scalar_random = Scalar::from_bytes_mod_order(bytes_from_seed(0xabcdefu64));

    let expected_ed_base = base_ed * scalar_random;
    let expected_base = SwPoint::from_edwards(&expected_ed_base);
    let expected_bytes_base = sw_point_to_sppark_affine_bytes(&expected_base);
    let out_base = msm_curve25519_gpu_bytes(&[base], &[scalar_random]).expect("cuda msm");

    assert!(
        affine_bytes_match(&out_base, &expected_bytes_base),
        "BASEPOINT * scalar should match"
    );

    // Generate a random point
    let s = Scalar::from_bytes_mod_order(bytes_from_seed(0x1337u64));
    let p_ed = base_ed * s;
    let p = SwPoint::from_edwards(&p_ed);
    assert_eq!(p.to_edwards(), Some(p_ed), "round-trip failed");

    // Test random point with scalar = 1
    let scalar = Scalar::ONE;
    let expected_ed = p_ed * scalar;
    let expected = SwPoint::from_edwards(&expected_ed);
    let expected_bytes = sw_point_to_sppark_affine_bytes(&expected);
    let out = msm_curve25519_gpu_bytes(&[p], &[scalar]).expect("cuda msm");
    assert!(
        affine_bytes_match(&out, &expected_bytes),
        "P * 1 should equal P"
    );

    // Test random point with scalar = 2
    let scalar2 = Scalar::from(2u64);
    let expected_ed2 = p_ed * scalar2;
    let expected2 = SwPoint::from_edwards(&expected_ed2);
    let expected_bytes2 = sw_point_to_sppark_affine_bytes(&expected2);
    let out2 = msm_curve25519_gpu_bytes(&[p], &[scalar2]).expect("cuda msm");
    assert!(
        affine_bytes_match(&out2, &expected_bytes2),
        "P * 2 should match"
    );

    // Test random point with random scalar (the failing case)
    let scalar3 = Scalar::from_bytes_mod_order(bytes_from_seed(0xdeadbeefu64));
    let expected_ed3 = p_ed * scalar3;
    let expected3 = SwPoint::from_edwards(&expected_ed3);
    let expected_bytes3 = sw_point_to_sppark_affine_bytes(&expected3);
    let out3 = msm_curve25519_gpu_bytes(&[p], &[scalar3]).expect("cuda msm");
    assert!(
        affine_bytes_match(&out3, &expected_bytes3),
        "P * scalar should match"
    );
}

#[test]
fn cuda_msm_randomized_batches() {
    use super::msm_curve25519_gpu_bytes;
    use curve25519_dalek::constants;

    require_cuda();

    let base = constants::ED25519_BASEPOINT_POINT;
    let sizes = [1usize, 2, 4, 8, 16];

    for &n in &sizes {
        let pairs: Vec<(SwPoint, Scalar)> = (0..n)
            .into_par_iter()
            .map(|i| {
                let seed = ((n as u64) << 32) ^ (i as u64);
                let s_bytes = bytes_from_seed(seed ^ 0x6a09e667f3bcc909);
                let p_scalar = Scalar::from_bytes_mod_order(s_bytes);
                let p_ed = base * p_scalar;
                let point = SwPoint::from_edwards(&p_ed);

                let sc_bytes = bytes_from_seed(seed ^ 0xbb67ae8584caa73b);
                let scalar = Scalar::from_bytes_mod_order(sc_bytes);
                (point, scalar)
            })
            .collect();

        let mut points = Vec::with_capacity(n);
        let mut points_ed = Vec::with_capacity(n);
        let mut scalars = Vec::with_capacity(n);
        for (point, scalar) in pairs {
            points_ed.push(point.to_edwards().expect("valid sw point"));
            points.push(point);
            scalars.push(scalar);
        }

        let expected_ed = edwards_msm(&points_ed, &scalars);
        let expected = SwPoint::from_edwards(&expected_ed);

        let expected_bytes = sw_point_to_sppark_affine_bytes(&expected);
        let out = msm_curve25519_gpu_bytes(&points, &scalars).expect("cuda msm");
        assert!(
            affine_bytes_match(&out, &expected_bytes),
            "unexpected MSM output"
        );
    }
}
