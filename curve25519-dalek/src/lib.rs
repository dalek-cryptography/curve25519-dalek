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

#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, doc(auto_cfg(hide(docsrs))))]
//------------------------------------------------------------------------
// Documentation:
//------------------------------------------------------------------------
#![doc(
    html_logo_url = "https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png"
)]
#![doc = include_str!("../README.md")]
//------------------------------------------------------------------------
// Linting:
//------------------------------------------------------------------------
#![cfg_attr(allow_unused_unsafe, allow(unused_unsafe))]
#![warn(
    clippy::mod_module_files,
    clippy::unwrap_used,
    missing_docs,
    rust_2018_idioms,
    unused_lifetimes,
    unused_qualifications
)]

//------------------------------------------------------------------------
// External dependencies:
//------------------------------------------------------------------------

#[cfg(feature = "alloc")]
#[allow(unused_imports)]
#[macro_use]
extern crate alloc;

// TODO: move std-dependent tests to `tests/`
#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(feature = "digest")]
pub use digest;

// Internal macros. Must come first!
#[macro_use]
pub(crate) mod macros;

//------------------------------------------------------------------------
// curve25519-dalek public modules
//------------------------------------------------------------------------

// Scalar arithmetic mod l = 2^252 + ..., the order of the Ristretto group
pub mod scalar;

// Point operations on the Montgomery form of Curve25519
pub mod montgomery;

// Point operations on the Edwards form of Curve25519
pub mod edwards;

// Group operations on the Ristretto group
pub mod ristretto;

// Useful constants, like the Ed25519 basepoint
pub mod constants;

// External (and internal) traits.
pub mod traits;

//------------------------------------------------------------------------
// curve25519-dalek internal modules
//------------------------------------------------------------------------

// Finite field arithmetic mod p = 2^255 - 19
pub(crate) mod field;

// Arithmetic backends (using u32, u64, etc) live here
#[cfg(docsrs)]
pub mod backend;
#[cfg(not(docsrs))]
pub(crate) mod backend;

// Generic code for window lookups
pub(crate) mod window;

#[cfg(feature = "lizard")]
mod lizard;

pub use crate::{
    edwards::EdwardsPoint, montgomery::MontgomeryPoint, ristretto::RistrettoPoint, scalar::Scalar,
};

// Build time diagnostics for validation
#[cfg(curve25519_dalek_diagnostics = "build")]
mod diagnostics;

mod wnaf_experiment {
    use alloc::vec::Vec;
    use core::{iter::repeat_with, time::Duration};
    extern crate std;
    use std::time::Instant;

    use criterion::{BenchmarkGroup, Criterion, measurement::Measurement};
    use group::Wnaf;
    use rand_core::{CryptoRng, RngCore, UnwrapErr};

    use crate::{EdwardsPoint, Scalar};

    // Make a dummy version of WnafGroup that just returns the input
    impl group::WnafGroup for EdwardsPoint {
        fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
            num_scalars
        }
    }

    fn wnaf_esimates<M: Measurement>(c: &mut Criterion) {
        let mut rng = UnwrapErr(getrandom::SysRng);
        let mut wnaf_backer = Wnaf::new();

        let window_size = 4;
        let mut wnaf = wnaf_backer.base(crate::constants::ED25519_BASEPOINT_POINT, window_size);

        bench_with_wnaf(&mut rng, c, &mut wnaf, window_size, num_scalars);
    }

    fn bench_with_wnaf<'a>(
        rng: &mut impl CryptoRng,
        c: &mut Criterion,
        wnaf: &mut Wnaf<usize, &[EdwardsPoint], &mut Vec<i64>>,
        window_size: usize,
        num_scalars: usize,
    ) -> u128 {
        let mut ret = 0u128;

        c.bench_function(
            &format!("Trying WNAF<win={window_size}> with {num_scalars} scalars"),
            move |b| {
                b.iter_custom(|iters| {
                    let random_scalars: Vec<Scalar> =
                        core::iter::repeat_with(|| Scalar::random(rng))
                            .take(32)
                            .collect();
                    let start = Instant::now();
                    for _ in 0..iters {
                        let scalars = random_scalars.iter().cycle().take(num_scalars);
                        scalars.for_each(|s| {
                            wnaf.scalar(s);
                        });
                    }
                    ret = start.elapsed().as_micros();

                    start.elapsed()
                })
            },
        );

        ret
    }
}
