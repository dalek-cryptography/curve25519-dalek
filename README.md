
# curve25519-dalek [![](https://img.shields.io/crates/v/curve25519-dalek.svg)](https://crates.io/crates/curve25519-dalek) [![](https://img.shields.io/badge/dynamic/json.svg?label=docs&uri=https%3A%2F%2Fcrates.io%2Fapi%2Fv1%2Fcrates%2Fcurve25519-dalek%2Fversions&query=%24.versions%5B0%5D.num&colorB=4F74A6)](https://doc.dalek.rs) [![](https://travis-ci.org/dalek-cryptography/curve25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/curve25519-dalek)

<img
 width="33%"
 align="right"
 src="https://doc.dalek.rs/assets/dalek-logo-clear.png"/>

**A pure-Rust implementation of group operations on Ristretto and Curve25519.**

`curve25519-dalek` is a library providing group operations on the Edwards and
Montgomery forms of Curve25519, and on the prime-order Ristretto group.

`curve25519-dalek` is not intended to provide implementations of any particular
crypto protocol.  Rather, implementations of those protocols (such as
[`x25519-dalek`][x25519-dalek] and [`ed25519-dalek`][ed25519-dalek]) should use
`curve25519-dalek` as a library.

`curve25519-dalek` is intended to provide a clean and safe _mid-level_ API for use
implementing a wide range of ECC-based crypto protocols, such as key agreement,
signatures, anonymous credentials, rangeproofs, and zero-knowledge proof
systems.

In particular, `curve25519-dalek` implements Ristretto, which constructs a
prime-order group from a non-prime-order Edwards curve.  This provides the
speed and safety benefits of Edwards curve arithmetic, without the pitfalls of
cofactor-related abstraction mismatches.

## Stability

We have recently released a `1.0.0-pre.0` version of `curve25519-dalek` and
would greatly appreciate testing and feedback on our API and performance.

# Documentation

The semver-stable, public-facing `curve25519-dalek` API is documented
[here][docs-external].  In addition, the unstable internal implementation
details are documented [here][docs-internal].

The `curve25519-dalek` documentation requires a custom HTML header to include
KaTeX for math support. Unfortunately `cargo doc` does not currently support
this, but docs can be built using
```sh
make doc
make doc-internal
```

# Use

To import `curve25519-dalek`, add the following to the dependencies section of
your project's `Cargo.toml`:
```toml
curve25519-dalek = "^0.18"
```
Then import the crate as:
```rust,no_run
extern crate curve25519_dalek;
```

# Backends and Features

The `yolocrypto` feature enables experimental features.  The name `yolocrypto`
is meant to indicate that it is not considered production-ready, and we do not
consider `yolocrypto` features to be covered by semver guarantees.

The `std` feature is enabled by default, but it can be disabled.

The `nightly` feature enables nightly-only features.  **It is recommended for security**.

Curve arithmetic is implemented using one of the following backends:

* a `u32` backend using `u64` products;
* a `u64` backend using `u128` products;
* an `avx2` backend using parallel formulas, available when compiling for a
  target with `target_feature=+avx2`.

By default the `u64` backend is selected.  To select a specific backend, use:
```sh
cargo build --no-default-features --features "std u32_backend"
cargo build --no-default-features --features "std u64_backend"
cargo build --no-default-features --features "std avx2_backend"
```
Crates using `curve25519-dalek` can either select a backend on behalf of their
users, or expose feature flags that control the `curve25519-dalek` backend.

Benchmarks are run using [`criterion.rs`][criterion]:

```sh
# You must set RUSTFLAGS to enable AVX2 support.
export RUSTFLAGS="-C target_cpu=native"
cargo bench --no-default-features --features "std u32_backend"
cargo bench --no-default-features --features "std u64_backend"
cargo bench --no-default-features --features "std avx2_backend"
```

# Contributing

Please see [CONTRIBUTING.md][contributing].

Patches and pull requests should be make against the `develop`
branch, **not** `master`.

# About

**SPOILER ALERT:** *The Twelfth Doctor's first encounter with the Daleks is in
his second full episode, "Into the Dalek". A beleaguered ship of the "Combined
Galactic Resistance" has discovered a broken Dalek that has turned "good",
desiring to kill all other Daleks. The Doctor, Clara and a team of soldiers
are miniaturized and enter the Dalek, which the Doctor names Rusty. They
repair the damage, but accidentally restore it to its original nature, causing
it to go on the rampage and alert the Dalek fleet to the whereabouts of the
rebel ship. However, the Doctor manages to return Rusty to its previous state
by linking his mind with the Dalek's: Rusty shares the Doctor's view of the
universe's beauty, but also his deep hatred of the Daleks. Rusty destroys the
other Daleks and departs the ship, determined to track down and bring an end
to the Dalek race.*

`curve25519-dalek` is authored by Isis Agora Lovecruft and Henry de Valence. 

Portions of this library were originally a port of [Adam Langley's
Golang ed25519 library](https://github.com/agl/ed25519), which was in
turn a port of the reference `ref10` implementation.  Most of this code,
including the 32-bit field arithmetic, has since been rewritten.

The fast `u32` and `u64` scalar arithmetic was implemented by Andrew Moon, and
the addition chain for scalar inversion was provided by Brian Smith.

The `no_std` support was contributed by Tony Arcieri.

Thanks also to Ashley Hauck, Lucas Salibian, and Manish Goregaokar for their
contributions.

[ed25519-dalek]: https://github.com/dalek-cryptography/ed25519-dalek
[x25519-dalek]: https://github.com/dalek-cryptography/x25519-dalek
[contributing]: https://github.com/dalek-cryptography/curve25519-dalek/blob/master/CONTRIBUTING.md
[docs-external]: https://doc.dalek.rs/curve25519_dalek/
[docs-internal]: https://doc-internal.dalek.rs/curve25519_dalek/
[criterion]: https://github.com/japaric/criterion.rs
