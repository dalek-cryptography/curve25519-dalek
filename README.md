# ed25519-dalek [![](https://img.shields.io/crates/v/ed25519-dalek.svg)](https://crates.io/crates/ed25519-dalek) [![](https://docs.rs/ed25519-dalek/badge.svg)](https://docs.rs/ed25519-dalek) [![](https://travis-ci.org/isislovecruft/ed25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/ed25519-dalek?branch=master)

Fast and efficient Rust implementation of ed25519 key generation, signing, and
verification in Rust.

# Documentation

Documentation is available [here](https://docs.rs/ed25519-dalek).

# Benchmarks

You need to pass the `--features="bench"` flag to run the benchmarks.  The
reason for feature-gating the benchmarks is that Rust's `test::Bencher` is
unstable, and thus only works on the nightly channel.  (We'd like people to be
able to compile and test on the stable and beta channels too!)

On an Intel i5 Sandy Bridge running at 2.6 GHz, with TurboBoost enabled (and
also running in QubesOS with *lots* of other VMs executing), this code
achieves the following performance benchmarks:

    ∃!isisⒶwintermute:(master *=)~/code/rust/ed25519-dalek ∴ cargo bench --features="nightly bench"
       Compiling ed25519-dalek v0.7.0 (file:///home/isis/code/rust/ed25519-dalek)
        Finished release [optimized] target(s) in 3.11s
         Running target/release/deps/ed25519_dalek-ae92163eefd0cc80

    running 9 tests
    test ed25519::test::golden ... ignored
    test ed25519::test::public_key_from_bytes ... ignored
    test ed25519::test::sign_verify ... ignored
    test ed25519::test::unmarshal_marshal ... ignored
    test ed25519::bench::key_generation                   ... bench:      30,711 ns/iter (+/- 10,936)
    test ed25519::bench::sign                             ... bench:      39,432 ns/iter (+/- 21,387)
    test ed25519::bench::sign_expanded_key                ... bench:      45,753 ns/iter (+/- 25,261)
    test ed25519::bench::underlying_scalar_mult_basepoint ... bench:      25,455 ns/iter (+/- 10,587)
    test ed25519::bench::verify                           ... bench:      91,408 ns/iter (+/- 31,193)

    test result: ok. 0 passed; 0 failed; 4 ignored; 5 measured; 0 filtered out

In comparison, the equivalent package in Golang performs as follows:

    ∃!isisⒶwintermute:(master *=)~/code/go/src/github.com/agl/ed25519 ∴ go test -bench .
    PASS
    BenchmarkKeyGeneration     20000             85880 ns/op
    BenchmarkSigning           20000             89115 ns/op
    BenchmarkVerification      10000            212585 ns/op
    ok      github.com/agl/ed25519  7.500s

Making key generation, signing, and verification a rough average of 33%
faster, 44% faster, and 43% faster respectively.  Of course, this
is just my machine, and these results—nowhere near rigorous—should be taken
with a handful of salt.

Translating to a rough cycle count: we multiply by a factor of 2.6 to convert
nanoseconds to cycles per second on a 2591 Mhz CPU, that's 237660 cycles for
verification and 102523 for signing, which for signing is competitive
with optimised assembly versions.

Additionally, if you're on the Rust nightly channel, be sure to build with
`cargo build --features="nightly"` which enables more secure compiler
optimisation protections in the
[subtle](https://github.com/dalek-cryptography/subtle) crate.  Additionally, if
you're using a CSPRNG from the `rand` crate, the `nightly` feature will enable
`u128`/`i128` features there, resulting in potentially faster performance.

Additionally, thanks to Rust, this implementation has both type and memory
safety.  It's also easily readable by a much larger set of people than those who
can read qhasm, making it more readily and more easily auditable.  We're of
the opinion that, ultimately, these features—combined with speed—are more
valuable than simply cycle counts alone.

# Warnings

ed25519-dalek and
[our elliptic curve library](https://github.com/isislovecruft/curve25519-dalek)
(which this code uses) have received *one* formal cryptographic and security
review.  Neither have yet received what we would consider *sufficient* peer
review by other qualified cryptographers to be considered in any way, shape,
or form, safe.

**USE AT YOUR OWN RISK.**


### A Note on Signature Malleability

The signatures produced by this library are malleable, as discussed in
[the original paper](https://ed25519.cr.yp.to/ed25519-20110926.pdf):

![](https://github.com/dalek-cryptography/ed25519-dalek/blob/master/res/ed25519-malleability.png)

We could eliminate the malleability property by multiplying by the curve
cofactor, however, this would cause our implementation to *not* match the
behaviour of every other implementation in existence.  As of this writing,
[RFC 8032](https://tools.ietf.org/html/rfc8032), "Edwards-Curve Digital
Signature Algorithm (EdDSA)," advises that the stronger check should be done.
While we agree that the stronger check should be done, it is our opinion that
one shouldn't get to change the definition of "ed25519 verification" a decade
after the fact, breaking compatibility with every other implementation.

In short, if malleable signatures are bad for your protocol, don't use them.
Consider using a curve25519-based Verifiable Random Function (VRF), such as
[Trevor Perrin's VXEdDSA](https://www.whispersystems.org/docs/specifications/xeddsa/),
instead.  We
[plan](https://github.com/dalek-cryptography/curve25519-dalek/issues/9) to
eventually support VXEdDSA in curve25519-dalek.

# Installation

To install, add the following to your project's `Cargo.toml`:

```toml
[dependencies.ed25519-dalek]
version = "^0.7"
```

Then, in your library or executable source, add:

```rust
extern crate ed25519_dalek;
```

# Features

To cause your application to build `ed25519-dalek` with the nightly feature
enabled by default, instead do:

```toml
[dependencies.ed25519-dalek]
version = "^0.7"
features = ["nightly"]
```

To cause your application to instead build with the nightly feature enabled
when someone builds with `cargo build --features="nightly"` add the following
to the `Cargo.toml`:

```toml
[features]
nightly = ["ed25519-dalek/nightly"]
```

To enable [serde](https://serde.rs) support, build `ed25519-dalek` with:

```toml
[dependencies.ed25519-dalek]
version = "^0.7"
features = ["serde"]
```

By default, `ed25519-dalek` builds against `curve25519-dalek`'s `u64_backend`
feature, which uses Rust's `i128` feature to achieve roughly double the speed as
the `u32_backend` feature.  When targetting 32-bit systems, however, you'll
likely want to compile with
 `cargo build --no-default-features --features="u32_backend"`.
If you're building for a machine with avx2 instructions, there's also the
experimental `avx2_backend`.  To use it, compile with
`RUSTFLAGS="-C target_cpu=native" cargo build --no-default-features --features="avx2_backend"`

# TODO

 * Batch signature verification, maybe?
 * We can probably make this go even faster if we implement SHA512,
   rather than using the rust-crypto implementation whose API requires
   that we allocate memory and bzero it before mutating to store the
   digest.
 * Incorporate ed25519-dalek into Brian Smith's
   [crypto-bench](https://github.com/briansmith/crypto-bench).
