// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2018-2019 isis lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - isis agora lovecruft <isis@patternsinthevoid.net>

use criterion::{criterion_group, criterion_main, Criterion};

mod ed25519_benches {
    use super::*;
    use ed25519_dalek::verify_batch;
    use ed25519_dalek::Signature;
    use ed25519_dalek::Signer;
    use ed25519_dalek::SigningKey;
    use ed25519_dalek::VerifyingKey;
    use rand::prelude::ThreadRng;
    use rand::thread_rng;

    fn sign(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: SigningKey = SigningKey::generate(&mut csprng);
        let msg: &[u8] = b"";

        c.bench_function("Ed25519 signing", move |b| b.iter(|| keypair.sign(msg)));
    }

    fn verify(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: SigningKey = SigningKey::generate(&mut csprng);
        let msg: &[u8] = b"";
        let sig: Signature = keypair.sign(msg);

        c.bench_function("Ed25519 signature verification", move |b| {
            b.iter(|| keypair.verify(msg, &sig))
        });
    }

    fn verify_strict(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: SigningKey = SigningKey::generate(&mut csprng);
        let msg: &[u8] = b"";
        let sig: Signature = keypair.sign(msg);

        c.bench_function("Ed25519 strict signature verification", move |b| {
            b.iter(|| keypair.verify_strict(msg, &sig))
        });
    }

    fn verify_batch_signatures(c: &mut Criterion) {
        static BATCH_SIZES: [usize; 8] = [4, 8, 16, 32, 64, 96, 128, 256];

        // TODO: use BenchmarkGroups instead.
        #[allow(deprecated)]
        c.bench_function_over_inputs(
            "Ed25519 batch signature verification",
            |b, &&size| {
                let mut csprng: ThreadRng = thread_rng();
                let keypairs: Vec<SigningKey> = (0..size)
                    .map(|_| SigningKey::generate(&mut csprng))
                    .collect();
                let msg: &[u8] = b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
                let messages: Vec<&[u8]> = (0..size).map(|_| msg).collect();
                let signatures: Vec<Signature> =
                    keypairs.iter().map(|key| key.sign(&msg)).collect();
                let verifying_keys: Vec<VerifyingKey> =
                    keypairs.iter().map(|key| key.verifying_key()).collect();

                b.iter(|| verify_batch(&messages[..], &signatures[..], &verifying_keys[..]));
            },
            &BATCH_SIZES,
        );
    }

    fn key_generation(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();

        c.bench_function("Ed25519 keypair generation", move |b| {
            b.iter(|| SigningKey::generate(&mut csprng))
        });
    }

    criterion_group! {
        name = ed25519_benches;
        config = Criterion::default();
        targets =
            sign,
            verify,
            verify_strict,
            verify_batch_signatures,
            key_generation,
    }
}

criterion_main!(ed25519_benches::ed25519_benches);
