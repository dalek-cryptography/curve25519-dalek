// -*- mode: rust; -*-
//
// This file is part of ed25519-dalek.
// Copyright (c) 2018 Isis Lovecruft
// See LICENSE for licensing information.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>

#[macro_use]
extern crate criterion;
extern crate ed25519_dalek;
extern crate rand;
extern crate sha2;

use criterion::Criterion;

mod ed25519_benches {
    use super::*;
    use ed25519_dalek::ExpandedSecretKey;
    use ed25519_dalek::Keypair;
    use ed25519_dalek::Signature;
    use rand::thread_rng;
    use rand::ThreadRng;
    use sha2::Sha512;

    fn sign(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
        let msg: &[u8] = b"";

        c.bench_function("Ed25519 signing", move |b| {
                         b.iter(| | keypair.sign::<Sha512>(msg))
        });
    }

    fn sign_expanded_key(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
        let expanded: ExpandedSecretKey = keypair.secret.expand::<Sha512>();
        let msg: &[u8] = b"";
        
        c.bench_function("Ed25519 signing with an expanded secret key", move |b| {
                         b.iter(| | expanded.sign::<Sha512>(msg, &keypair.public))
        });
    }

    fn verify(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();
        let keypair: Keypair = Keypair::generate::<Sha512, _>(&mut csprng);
        let msg: &[u8] = b"";
        let sig: Signature = keypair.sign::<Sha512>(msg);
        
        c.bench_function("Ed25519 signature verification", move |b| {
                         b.iter(| | keypair.verify::<Sha512>(msg, &sig))
        });
    }

    fn key_generation(c: &mut Criterion) {
        let mut csprng: ThreadRng = thread_rng();

        c.bench_function("Ed25519 keypair generation", move |b| {
                         b.iter(| | Keypair::generate::<Sha512, _>(&mut csprng))
        });
    }

    criterion_group!{
        name = ed25519_benches;
        config = Criterion::default();
        targets =
            sign,
            sign_expanded_key,
            verify,
            key_generation,
    }
}

criterion_main!(
    ed25519_benches::ed25519_benches,
);
