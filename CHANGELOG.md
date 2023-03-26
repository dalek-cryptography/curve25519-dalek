# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Entries are listed in reverse chronological order per undeprecated major series.

# 2.x series

##  2.0.0

### Breaking changes

* Bump MSRV from 1.41 to 1.60.0
* Bump Rust edition
* Bump `signature` dependency to 2.0
* Make `digest` an optional dependency
* Make `zeroize` an optional dependency
* Make `rand_core` an optional dependency
* Adopt [curve25519-backend selection](https://github.com/dalek-cryptography/curve25519-dalek/#backends) over features
* Make all batch verification deterministic remove `batch_deterministic` ([#256](https://github.com/dalek-cryptography/ed25519-dalek/pull/256))
* Remove `ExpandedSecretKey` API ((#205)[https://github.com/dalek-cryptography/ed25519-dalek/pull/205])
* Rename `Keypair` → `SigningKey` and `PublicKey` → `VerifyingKey`

### Other changes

* Add `Context` type for prehashed signing
* Add `VerifyingKey::{verify_prehash_strict, is_weak}`
* Add `pkcs` feature to support PKCS #8 (de)serialization of `SigningKey` and `VerifyingKey`
* Add `fast` feature to include basepoint tables
* Add tests for validation criteria
* Impl `DigestSigner`/`DigestVerifier` for `SigningKey`/`VerifyingKey`, respectively
* Impl `Hash` for `VerifyingKey`
* Impl `Clone`, `Drop`, and `ZeroizeOnDrop` for `SigningKey`
* Remove `rand` dependency
* Improve key deserialization diagnostics
