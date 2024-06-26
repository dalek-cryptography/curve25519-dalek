<p align="center">
<img
 alt="dalek-cryptography logo: a dalek with edwards curves as sparkles coming out of its radar-schnozzley blaster thingies"
 width="200px"
 src="https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png"/>
</p>

# Dalek elliptic curve cryptography

## THIS IS A FORK FOR CONVENIENCE

This fork contains an implementation of `elligator2` that is awaiting potential
inclusion in the mainstream curve25519-dalek crates. This crate exists for
use in the interim period. 


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
