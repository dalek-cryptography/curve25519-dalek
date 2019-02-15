# Changelog

Entries are listed in reverse chronological order.

## 1.1.2

* Disabled KaTeX on `docs.rs` pending proper [support upstream](https://github.com/rust-lang/docs.rs/issues/302).

## 1.1.1

* Fixed an issue related to `#[cfg(rustdoc)]` which prevented documenting multiple backends.

## 1.1.0

* Adds support for precomputation for multiscalar multiplication.
* Restructures the internal source tree into `serial` and `vector` backends (no change to external API).
* Adds a new IFMA backend which sets speed records.
* The `avx2_backend` feature is now an alias for the `simd_backend` feature, which autoselects an appropriate vector backend (currently AVX2 or IFMA).
* Replaces the `rand` dependency with `rand_core`.
* Generalizes trait bounds on `RistrettoPoint::random()` and `Scalar::random()` to allow owned and borrowed RNGs and to allow `RngCore` instead of `Rng`.

## 1.0.3

* Adds `ConstantTimeEq` implementation for compressed points.

## 1.0.2

* Fixes a typo in the naming of variables in Ristretto formulas (no change to functionality).

## 1.0.1

* Depends on the stable `2.0` version of `subtle` instead of `2.0.0-pre.0`.

## 1.0.0

Initial stable release.  Yanked due to a dependency mistake (see above).

