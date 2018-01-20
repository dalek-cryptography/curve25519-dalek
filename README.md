
# curve25519-dalek  [![](https://img.shields.io/crates/v/curve25519-dalek.svg)](https://crates.io/crates/curve25519-dalek) [![](https://docs.rs/curve25519-dalek/badge.svg)](https://docs.rs/curve25519-dalek) [![](https://travis-ci.org/dalek-cryptography/curve25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/curve25519-dalek)

<img
 width="50%"
 align="right"
 src="https://user-images.githubusercontent.com/797/34898472-83686016-f7f3-11e7-967b-24b2aadd623a.png"/>

**A low-level cryptographic library for point, group, field, and scalar
operations on a curve isomorphic to the twisted Edwards curve defined by -x²+y²
= 1 - 121665/121666 x²y² over GF(2²⁵⁵ - 19).**

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

Significant portions of this code are ported from [Adam Langley's
Golang ed25519 library](https://github.com/agl/ed25519), which is in
turn a port of the reference `ref10` implementation.

## Warning

This code has **not** yet received sufficient peer review by other qualified
cryptographers to be considered in any way, shape, or form, safe.  Further,
this library does **not** provide high-level routines such as encryption and
decryption or signing and verification.  Instead, it is a low-level library,
intended for other cryptographers who would like to implement their own
primitives using this curve.  (For an example of how one would implement a
signature scheme using this library, see
[ed25519-dalek](https://github.com/dalek-cryptography/ed25519-dalek).)

**USE AT YOUR OWN RISK**

## Documentation

Extensive documentation is available [here](https://docs.rs/curve25519-dalek).

# Installation

To install, add the following to the dependencies section of your project's
`Cargo.toml`:

```toml
curve25519-dalek = "^0.14"
```

Then, in your library or executable source, add:

    extern crate curve25519_dalek;

## Features

On nightly Rust, using the `nightly` feature enables a radix-51 field
arithmetic implementation using `u128`s, which is approximately twice as
fast.  It will also enable additional developer documentation when
compiling via `make doc-internal`.

By default, the benchmarks are not compiled without the `bench`
feature.  To run the benchmarks, do:

```sh
cargo bench --features="bench"
```

## TODO

We intend to stabilise the following before curve25519-dalek-1.0.0:

* Implement hashing to a point on the curve (Elligator).
* Finish Ristretto documentation.

## Contributing

Please see
[CONTRIBUTING.md](https://github.com/dalek-cryptography/curve25519-dalek/blob/master/CONTRIBUTING.md).

Patches and pull requests should be make against the `develop`
branch, **not** `master`.
