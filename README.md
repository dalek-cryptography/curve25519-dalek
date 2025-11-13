<p align="center">
<img
 alt="dalek-cryptography logo: a dalek with edwards curves as sparkles coming out of its radar-schnozzley blaster thingies"
 width="200px"
 src="https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png"/>
</p>

# Dalek elliptic curve cryptography

This repo contains pure-Rust crates for elliptic curve cryptography:

|                 Crate                    |   Description  | Crates.io | Docs | CI                                                                                                                                                                                                                          |
-------------------------------------------|----------------|-----------|------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
| [`curve25519‑dalek`](./curve25519-dalek) | A library for arithmetic over the Curve25519 and Ristretto elliptic curves and their associated scalars. | [![](https://img.shields.io/crates/v/curve25519-dalek.svg)](https://crates.io/crates/curve25519-dalek) | [![](https://img.shields.io/docsrs/curve25519-dalek)](https://docs.rs/curve25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/curve25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/curve25519-dalek.yml) |
| [`ed25519‑dalek`](./ed25519-dalek)       | An implementation of the EdDSA digital signature scheme over Curve25519. | [![](https://img.shields.io/crates/v/ed25519-dalek.svg)](https://crates.io/crates/ed25519-dalek) | [![](https://docs.rs/ed25519-dalek/badge.svg)](https://docs.rs/ed25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/ed25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/ed25519-dalek.yml)       |
| [`x25519‑dalek`](./x25519-dalek)         | An implementation of elliptic curve Diffie-Hellman key exchange over Curve25519. | [![](https://img.shields.io/crates/v/x25519-dalek.svg)](https://crates.io/crates/x25519-dalek) | [![](https://docs.rs/x25519-dalek/badge.svg)](https://docs.rs/x25519-dalek) | [![CI](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/x25519-dalek.yml/badge.svg?branch=main)](https://github.com/dalek-cryptography/curve25519-dalek/actions/workflows/x25519-dalek.yml)         |

There is also the [`curve25519-dalek-derive`](./curve25519-dalek-derive) crate, which is just a helper crate with some macros that make curve25519-dalek easier to write.

# Contributing

Please see [`CONTRIBUTING.md`](./CONTRIBUTING.md).

# Code of Conduct

We follow the [Rust Code of Conduct](http://www.rust-lang.org/conduct.html),
with the following additional clauses:

* We respect the rights to privacy and anonymity for contributors and people in
  the community.  If someone wishes to contribute under a pseudonym different to
  their primary identity, that wish is to be respected by all contributors.

# Beneficial AI Foundation note

This repo is based on the `signal-curve25519-4.1.3` tag of https://github.com/signalapp/curve25519-dalek, with these changes:
- removed all crates besides `curve25519-dalek`
- removed all backends except for `serial/u64`
- commented out unit tests
- removed most CI workflows

# Setup
1. Install Rust: https://rust-lang.org/learn/get-started/
2. Download and unzip a verus binary from https://github.com/verus-lang/verus/releases/tag/release%2F0.2025.10.05.bf8e97e. It's important to use exactly this version
3. The unzipped verus folder will contains a file called `verus` and a file called `cargo-verus`. Run these commands:

``` sh
cd ~/.cargo/bin
ln -s /path/to/cargo-verus
ln -s /path/to/verus
```
4. If you're on a Mac, the first time you run `cargo verus verify` inside dalek-lite, you may be prompted to approve the unknown applications: `cargo-verus`, `verus`, and `z3`. See https://support.apple.com/en-gb/guide/mac-help/mh40616/mac.
5. Success looks like:
```
cd dalek-lite
cargo verus verify
... (many warnings)
verification results:: 313 verified, 0 errors
warning: `curve25519-dalek` (lib) generated 43 warnings (19 duplicates)
    Finished `dev` profile [optimized + debuginfo] target(s) in 8.99s
```

## How to install verusfmt

``` sh
cargo install --git https://github.com/Beneficial-AI-Foundation/verusfmt --rev 025d10eeb5a98052dcb7f262e5d0102d23996809
```
This is a version of verusfmt patched to support more Rust syntax.

See https://github.com/verus-lang/verusfmt?tab=readme-ov-file#installing-and-using-verusfmt for usage.
In particular, if you want to format all Rust files, run
```bash
find . -name "*.rs" -type f | xargs -P 0 -n 1 verusfmt
```

## Using bacon

`bacon verus` will show the live verification status as you make edits and save files,
and it will put error messages at the top.

Install bacon from https://github.com/Canop/bacon
