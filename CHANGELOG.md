# Changelog

Entries are listed in reverse chronological order.

## 1.1.0-pre.0

* Restructures the source tree into `serial` and `vector` backends.
* Adds a new IFMA backend which sets speed records.
* Adds support for precomputation for multiscalar multiplication.
* Replaces the `rand` dependency with `rand_core`.
* Generalizes trait bounds on 
  - `RistrettoPoint::random()`
  - `Scalar::random()`
  to allow owned and borrowed RNGs and to allow `RngCore` instead of
  `Rng`.

## 1.0.3

* Adds `ConstantTimeEq` implementation for compressed points.

## 1.0.2

* Fixes a typo in the naming of variables in Ristretto formulas (no change to functionality).

## 1.0.1

* Depends on the stable `2.0` version of `subtle` instead of `2.0.0-pre.0`.

## 1.0.0

Initial stable release.  Yanked due to a dependency mistake (see above).

