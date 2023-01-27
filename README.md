# ed25519-dalek [![](https://img.shields.io/crates/v/ed25519-dalek.svg)](https://crates.io/crates/ed25519-dalek) [![](https://docs.rs/ed25519-dalek/badge.svg)](https://docs.rs/ed25519-dalek) [![](https://travis-ci.org/dalek-cryptography/ed25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/ed25519-dalek?branch=master)

Fast and efficient Rust implementation of ed25519 key generation, signing, and
verification in Rust.

# Use

To use, add the following to your project's `Cargo.toml`:

```toml
[dependencies.ed25519-dalek]
version = "1"
```

# Feature Flags

This crate is `#[no_std]` compatible with `default-features = false`

| Feature                | Default? | Description |
| :---                   | :---     | :---        |
| `alloc`                | ✓        | Enables features that require dynamic heap allocation |
| `std`                  | ✓        | std::error::Error types |
| `zeroize`              | ✓        | Enables `Zeroize` for `SigningKey` |
| `asm`                  |          | Assembly implementation of SHA-2 compression functions |
| `batch`                |          | Batch verification. Requires `alloc` |
| `digest`               |          | TODO |
| `legacy_compatibility` |          | See: A Note on Signature Malleability |
| `pkcs8`                |          | PKCS#8 Support |
| `pem`                  |          | PEM Support |
| `rand_core`            |          | TODO        |

# Major Changes

See [CHANGELOG.md](CHANGELOG.md) for a list of changes made in past version of this crate.

## 2.0.0 Breaking Changes

* Update the MSRV from 1.41 to 1.60
* `batch` is now `batch_deterministic`
* Removed `ExpandedSecretKey` API
* [curve25519-backend selection] is more automatic

[curve25519-backend selection]: https://github.com/dalek-cryptography/curve25519-dalek/#backends

# Documentation

Documentation is available [here](https://docs.rs/ed25519-dalek).

# Policies

All on-by-default features of this library are covered by semantic versioning (SemVer)

SemVer exemptions are outlined below for MSRV and public API.

## Minimum Supported Rust Version

| Releases | MSRV   |
| :---     | :---   |
| 2.x      | 1.60   |
| 1.x      | 1.41   |

MSRV changes will be accompanied by a minor version bump.

## Public API SemVer Exemptions

Breaking changes to SemVer exempted components affecting the public API will be accompanied by some version bump.

Below are the specific policies:

| Releases | Public API Component(s) | Policy |
| :---     | :---                    | :---   |
| 2.x      | Dependencies `digest`, `pkcs8` and `rand_core` | Minor SemVer bump |

## Safety

This crate does not require any unsafe and forbids all unsafe in-crate outside tests.

# Performance

Performance is a secondary goal behind correctness, safety, and clarity, but we
aim to be competitive with other implementations.

## Benchmarks

Benchmarks are run using [criterion.rs](https://github.com/japaric/criterion.rs):

```sh
cargo bench --features "batch"
# Uses avx2 or ifma only if compiled for an appropriate target.
export RUSTFLAGS='--cfg curve25519_dalek_backend="simd" -C target_cpu=native'
cargo +nightly bench --features "batch"
```

On an Intel 10700K running at stock comparing between the `curve25519-dalek` backends.

| Benchmark                       | u64       | simd +avx2         | fiat               |
| :---                            | :----     | :---               | :---               |
| signing                         | 15.017 µs | 13.906 µs -7.3967% | 15.877 µs +14.188% |
| signature verification          | 40.144 µs | 25.963 µs -35.603% | 42.118 µs +62.758% |
| strict signature verification   | 41.334 µs | 27.874 µs -32.660% | 43.985 µs +57.763% |
| batch signature verification/4  | 109.44 µs | 81.778 µs -25.079% | 117.80 µs +43.629% |
| batch signature verification/8  | 182.75 µs | 138.40 µs -23.871% | 195.86 µs +40.665% |
| batch signature verification/16 | 328.67 µs | 251.39 µs -23.744% | 351.55 µs +39.901% |
| batch signature verification/32 | 619.49 µs | 477.36 µs -23.053% | 669.41 µs +39.966% |
| batch signature verification/64 | 1.2136 ms | 936.85 µs -22.543% | 1.3028 ms +38.808% |
| batch signature verification/96 | 1.8677 ms | 1.2357 ms -33.936% | 2.0552 ms +66.439% |
| batch signature verification/128| 2.3281 ms | 1.5795 ms -31.996% | 2.5596 ms +61.678% |
| batch signature verification/256| 4.1868 ms | 2.8864 ms -31.061% | 4.6494 ms +61.081% |
| keypair generation              | 13.973 µs | 13.108 µs -6.5062% | 15.099 µs +15.407% |

Additionally, if you're using a CSPRNG from the `rand` crate, the `nightly`
feature will enable `u128`/`i128` features there, resulting in potentially
faster performance.

## Batch Performance

If your protocol or application is able to batch signatures for verification,
the `verify_batch()` function has greatly improved performance.

As you can see, there's an optimal batch size for each machine, so you'll likely
want to test the benchmarks on your target CPU to discover the best size.

## (Micro)Architecture Specific Backends

`ed25519-dalek` uses the backends from the `curve25519-dalek` crate.

By default the serial backend is used and depending on the target
platform either the 32 bit or the 64 bit serial formula is automatically used.

To address variety of  usage scenarios various backends are available that
include hardware optimisations as well as a formally verified fiat crypto
backend that does not use any hardware optimisations.

These backends can be overriden with various configuration predicates (cfg)

Please see the [curve25519_dalek backend documentation](https://docs.rs/curve25519-dalek/latest/curve25519_dalek).

# Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md)

# A Note on Signature Malleability

The signatures produced by this library are malleable, as discussed in
[the original paper](https://ed25519.cr.yp.to/ed25519-20110926.pdf):

![](https://cdn.jsdelivr.net/gh/dalek-cryptography/ed25519-dalek/docs/assets/ed25519-malleability.png)

While the scalar component of our `Signature` struct is strictly *not*
malleable, because reduction checks are put in place upon `Signature`
deserialisation from bytes, for all types of signatures in this crate,
there is still the question of potential malleability due to the group
element components.

We could eliminate the latter malleability property by multiplying by the curve
cofactor, however, this would cause our implementation to *not* match the
behaviour of every other implementation in existence.  As of this writing,
[RFC 8032](https://tools.ietf.org/html/rfc8032), "Edwards-Curve Digital
Signature Algorithm (EdDSA)," advises that the stronger check should be done.
While we agree that the stronger check should be done, it is our opinion that
one shouldn't get to change the definition of "ed25519 verification" a decade
after the fact, breaking compatibility with every other implementation.

However, if you require this, please see the documentation for the
`verify_strict()` function, which does the full checks for the group elements.
This functionality is available by default.

If for some reason—although we strongly advise you not to—you need to conform
to the original specification of ed25519 signatures as in the excerpt from the
paper above, you can disable scalar malleability checking via
`--features='legacy_compatibility'`.  **WE STRONGLY ADVISE AGAINST THIS.**

## The `legacy_compatibility` Feature

By default, this library performs a stricter check for malleability in the
scalar component of a signature, upon signature deserialisation.  This stricter
check, that `s < \ell` where `\ell` is the order of the basepoint, is
[mandated by RFC8032](https://tools.ietf.org/html/rfc8032#section-5.1.7).
However, that RFC was standardised a decade after the original paper, which, as
described above, (usually, falsely) stated that malleability was inconsequential.

Because of this, most ed25519 implementations only perform a limited, hackier
check that the most significant three bits of the scalar are unset.  If you need
compatibility with legacy implementations, including:

* ed25519-donna
* Golang's /x/crypto ed25519
* libsodium (only when built with `-DED25519_COMPAT`)
* NaCl's "ref" implementation
* probably a bunch of others

then enable `ed25519-dalek`'s `legacy_compatibility` feature.  Please note and
be forewarned that doing so allows for signature malleability, meaning that
there may be two different and "valid" signatures with the same key for the same
message, which is obviously incredibly dangerous in a number of contexts,
including—but not limited to—identification protocols and cryptocurrency
transactions.

## The `verify_strict()` Function

The scalar component of a signature is not the only source of signature
malleability, however.  Both the public key used for signature verification and
the group element component of the signature are malleable, as they may contain
a small torsion component as a consequence of the curve25519 group not being of
prime order, but having a small cofactor of 8.

If you wish to also eliminate this source of signature malleability, please
review the
[documentation for the `verify_strict()` function](https://docs.rs/ed25519-dalek/latest/ed25519_dalek/struct.PublicKey.html#method.verify_strict).

## Batch Signature Verification

The standard variants of batch signature verification (i.e. many signatures made
with potentially many different public keys over potentially many different
messages) is available via the `batch` feature.  It uses synthetic randomness, as
noted above. Batch verification requires allocation, so this won't function in
heapless settings.
