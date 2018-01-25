
# curve25519-dalek  [![](https://img.shields.io/crates/v/curve25519-dalek.svg)](https://crates.io/crates/curve25519-dalek) [![](https://docs.rs/curve25519-dalek/badge.svg)](https://docs.rs/curve25519-dalek) [![](https://travis-ci.org/dalek-cryptography/curve25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/curve25519-dalek)

<img
 width="33%"
 align="right"
 src="https://user-images.githubusercontent.com/797/34898472-83686016-f7f3-11e7-967b-24b2aadd623a.png"/>

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

## WARNING

We do not yet consider this code to be production-ready.  We intend to
stabilize a production-ready version `1.0` soon.

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
curve25519-dalek = "^0.14"
```
Then import the crate as:
```rust,no_run
extern crate curve25519_dalek;
```

# Backends and Features

Curve arithmetic is implemented using one of the following backends:

* a `u32` backend using `u64` products;
* a `u64` backend using `u128` products, available using the `nightly` feature;
* an experimental AVX2 backend, available using the `yolocrypto` feature when
  compiling for a target with `target_feature=+avx2`.

By default, the benchmarks are not compiled without the `bench`
feature.  Benchmarks can be run via:

```sh
cargo bench --features="bench"                    # u32 backend
cargo bench --features="bench nightly"            # u64 backend
cargo bench --features="bench nightly yolocrypto" # u64 or avx2 if available
```

The `yolocrypto` feature enables experimental features.  The name `yolocrypto`
is meant to indicate that it is not considered production-ready, and we do not
consider `yolocrypto` features to be covered by semver guarantees.

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
turn a port of the reference `ref10` implementation.

The fast `u32` and `u64` scalar arithmetic was implemented by Andrew Moon, and
the addition chain for scalar inversion was provided by Brian Smith.  The
`no_std` support was contributed by Tony Arcieri.

[ed25519-dalek]: https://github.com/dalek-cryptography/ed25519-dalek
[x25519-dalek]: https://github.com/dalek-cryptography/x25519-dalek
[contributing]: https://github.com/dalek-cryptography/curve25519-dalek/blob/master/CONTRIBUTING.md
