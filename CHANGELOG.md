# Changelog

Entries are listed in reverse chronological order.

## 0.6.0

* Updates `rand_core` version to `0.5`.
* Adds `serde` support.
* Replaces `clear_on_drop` with `zeroize`.
* Use Rust 2018.

## 0.5.2

* Implement `Clone` for `StaticSecret`.

## 0.5.1

* Implement `Copy, Clone, Debug` for `PublicKey`.
* Remove doctests.

## 0.5.0

* Adds support for static and ephemeral keys.

