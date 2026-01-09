use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::short_weierstrass::SwPoint;
use rayon::prelude::*;

fn cpu_msm(points: &[SwPoint], scalars: &[Scalar]) -> SwPoint {
    use curve25519_dalek::traits::{Identity, VartimeMultiscalarMul};
    assert_eq!(points.len(), scalars.len());

    let ed_points: Vec<EdwardsPoint> = points
        .par_iter()
        .map(|point| point.to_edwards().expect("valid sw point"))
        .collect();

    let chunk_size =
        (ed_points.len().max(1) + rayon::current_num_threads() - 1) / rayon::current_num_threads();
    let out = ed_points
        .par_chunks(chunk_size)
        .zip(scalars.par_chunks(chunk_size))
        .map(|(point_chunk, scalar_chunk)| {
            EdwardsPoint::vartime_multiscalar_mul(scalar_chunk, point_chunk)
        })
        .reduce(EdwardsPoint::identity, |acc, partial| acc + partial);

    SwPoint::from_edwards(&out)
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

fn build_inputs(log_n: usize) -> (Vec<SwPoint>, Vec<Scalar>) {
    let npoints = 1usize << log_n;
    let base = curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
    let pairs: Vec<(SwPoint, Scalar)> = (0..npoints)
        .into_par_iter()
        .map(|i| {
            let seed = ((log_n as u64) << 32) ^ (i as u64);
            let s_bytes = bytes_from_seed(seed ^ 0x6a09e667f3bcc909);
            let p_scalar = Scalar::from_bytes_mod_order(s_bytes);
            let p_ed = base * p_scalar;
            let point = SwPoint::from_edwards(&p_ed);

            let sc_bytes = bytes_from_seed(seed ^ 0xbb67ae8584caa73b);
            let scalar = Scalar::from_bytes_mod_order(sc_bytes);
            (point, scalar)
        })
        .collect();

    let mut points = Vec::with_capacity(npoints);
    let mut scalars = Vec::with_capacity(npoints);
    for (point, scalar) in pairs {
        points.push(point);
        scalars.push(scalar);
    }

    (points, scalars)
}

fn bench_cpu_vs_gpu(c: &mut Criterion) {
    let logs = [1usize, 2, 4, 8, 12, 16, 20];

    for &log_n in &logs {
        let (points, scalars) = build_inputs(log_n);

        let mut cpu_group = c.benchmark_group("msm_cpu");
        cpu_group.sample_size(10);
        cpu_group.bench_with_input(
            BenchmarkId::from_parameter(format!("log2={}", log_n)),
            &log_n,
            |b, _| {
                b.iter(|| {
                    let _ = cpu_msm(&points, &scalars);
                });
            },
        );
        cpu_group.finish();

        let mut gpu_group = c.benchmark_group("msm_gpu");
        gpu_group.sample_size(10);
        gpu_group.bench_with_input(
            BenchmarkId::from_parameter(format!("log2={}", log_n)),
            &log_n,
            |b, _| {
                b.iter(|| {
                    let _ = curve25519_cuda::msm_curve25519_gpu(&points, &scalars);
                });
            },
        );
        gpu_group.finish();
    }
}

criterion_group!(benches, bench_cpu_vs_gpu);
criterion_main!(benches);
