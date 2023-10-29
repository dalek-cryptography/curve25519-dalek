use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_dalek::{constants::RISTRETTO_BASEPOINT_POINT as G, ecdlp, Scalar};
use rand::Rng;

pub fn ecdlp_bench(c: &mut Criterion) {
    c.bench_function("fast ecdlp", |b| {
        let num = rand::thread_rng().gen_range(0u64..(1 << ecdlp::L));
        let point = Scalar::from(num) * G;
        b.iter(|| ecdlp::decode(black_box(point), 0, 1 << ecdlp::L, true));
    });
}

criterion_group!(ecdlp, ecdlp_bench);
criterion_main!(ecdlp);
