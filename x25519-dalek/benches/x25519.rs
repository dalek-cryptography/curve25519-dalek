// -*- mode: rust; -*-
//
// This file is part of x25519-dalek.
// Copyright (c) 2017-2019 isis agora lovecruft
// Copyright (c) 2019 DebugSteven
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>
// - DebugSteven <debugsteven@gmail.com>

//! Benchmark the Diffie-Hellman operation.

use criterion::{Criterion, criterion_group, criterion_main};

use rand::{TryRngCore, rngs::SysRng};

use x25519_dalek::EphemeralSecret;
use x25519_dalek::PublicKey;

fn bench_diffie_hellman(c: &mut Criterion) {
    let bob_secret = EphemeralSecret::random_from_rng(&mut SysRng.unwrap_err());
    let bob_public = PublicKey::from(&bob_secret);

    c.bench_function("diffie_hellman", move |b| {
        b.iter_with_setup(
            || EphemeralSecret::random_from_rng(&mut SysRng.unwrap_err()),
            |alice_secret| alice_secret.diffie_hellman(&bob_public),
        )
    });
}

fn bench_pubkey_constructor(c: &mut Criterion) {
    let bob_secret = EphemeralSecret::random_from_rng(&mut SysRng.unwrap_err());

    c.bench_function("PublicKey::from", move |b| {
        b.iter(|| PublicKey::from(&bob_secret))
    });
}

criterion_group! {
    name = x25519_benches;
    config = Criterion::default();
    targets =
        bench_diffie_hellman,
        bench_pubkey_constructor,
}
criterion_main! {
    x25519_benches,
}
