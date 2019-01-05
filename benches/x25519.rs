// -*- mode: rust; -*-
//
// This file is part of x25519-dalek.
// Copyright (c) 2017 Isis Lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

//! Benchmark the Diffie-Hellman operation.

#[macro_use]
extern crate criterion;
extern crate rand_os;
extern crate x25519_dalek;

use criterion::Criterion;

use rand_os::OsRng;

use x25519_dalek::generate_public;
use x25519_dalek::generate_secret;
use x25519_dalek::diffie_hellman;

fn bench_diffie_hellman(c: &mut Criterion) {
    let mut csprng: OsRng = OsRng::new().unwrap();
    let alice_secret: [u8; 32] = generate_secret(&mut csprng);
    let bob_secret: [u8; 32] = generate_secret(&mut csprng);
    let bob_public: [u8; 32] = generate_public(&bob_secret).to_bytes();

    c.bench_function("diffie_hellman", move |b| {
        b.iter(||
               diffie_hellman(&alice_secret, &bob_public)
        )
    });
}

criterion_group!{
    name = x25519_benches;
    config = Criterion::default();
    targets =
        bench_diffie_hellman,
}
criterion_main!{
    x25519_benches,
}
