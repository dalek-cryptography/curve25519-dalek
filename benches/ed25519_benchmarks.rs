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

mod helpers {
    use rand::CryptoRng;
    use rand::Error;
    use rand::RngCore;

    /// A fake RNG which simply returns zeroes.
    pub struct ZeroRng;

    impl ZeroRng {
        pub fn new() -> ZeroRng {
            ZeroRng
        }
    }

    impl RngCore for ZeroRng {
        fn next_u32(&mut self) -> u32 { 0u32 }

        fn next_u64(&mut self) -> u64 { 0u64 }

        fn fill_bytes(&mut self, bytes: &mut [u8]) {
            for i in 0 .. bytes.len() {
                bytes[i] = 0;
            }
        }

        fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Error> {
            Ok(self.fill_bytes(bytes))
        }
    }

    impl CryptoRng for ZeroRng { }
}

mod ed25519_benches {
    use super::*;
    use super::helpers::ZeroRng;
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
        let mut rng: ZeroRng = ZeroRng::new();

        c.bench_function("Ed25519 keypair generation", move |b| {
                         b.iter(| | Keypair::generate::<Sha512, _>(&mut rng))
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
