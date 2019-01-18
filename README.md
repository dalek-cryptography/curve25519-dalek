# ed25519-dalek [![](https://img.shields.io/crates/v/ed25519-dalek.svg)](https://crates.io/crates/ed25519-dalek) [![](https://docs.rs/ed25519-dalek/badge.svg)](https://docs.rs/ed25519-dalek) [![](https://travis-ci.org/dalek-cryptography/ed25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/ed25519-dalek?branch=master)

Fast and efficient Rust implementation of ed25519 key generation, signing, and
verification in Rust.

# Documentation

Documentation is available [here](https://docs.rs/ed25519-dalek).

# Benchmarks

On an Intel Skylake i9-7900X running at 3.30 GHz, without TurboBoost, this code achieves
the following performance benchmarks:

    ∃!isisⒶmistakenot:(master *=)~/code/rust/ed25519-dalek ∴ cargo bench
       Compiling ed25519-dalek v0.7.0 (file:///home/isis/code/rust/ed25519-dalek)
        Finished release [optimized] target(s) in 3.11s
          Running target/release/deps/ed25519_benchmarks-721332beed423bce

    Ed25519 signing                     time:   [15.617 us 15.630 us 15.647 us]
    Ed25519 signature verification      time:   [45.930 us 45.968 us 46.011 us]
    Ed25519 keypair generation          time:   [15.440 us 15.465 us 15.492 us]

By enabling the avx2 backend (on machines with compatible microarchitectures),
the performance for signature verification is greatly improved:

    ∃!isisⒶmistakenot:(master *=)~/code/rust/ed25519-dalek ∴ export RUSTFLAGS=-Ctarget_cpu=native
    ∃!isisⒶmistakenot:(master *=)~/code/rust/ed25519-dalek ∴ cargo bench --features=avx2_backend
       Compiling ed25519-dalek v0.7.0 (file:///home/isis/code/rust/ed25519-dalek)
        Finished release [optimized] target(s) in 4.28s
          Running target/release/deps/ed25519_benchmarks-e4866664de39c84d
    Ed25519 signing                     time:   [15.923 us 15.945 us 15.967 us]
    Ed25519 signature verification      time:   [33.382 us 33.411 us 33.445 us]
    Ed25519 keypair generation          time:   [15.246 us 15.260 us 15.275 us]

In comparison, the equivalent package in Golang performs as follows:

    ∃!isisⒶmistakenot:(master *=)~/code/go/src/github.com/agl/ed25519 ∴ go test -bench .
    BenchmarkKeyGeneration     30000             47007 ns/op
    BenchmarkSigning           30000             48820 ns/op
    BenchmarkVerification      10000            119701 ns/op
    ok      github.com/agl/ed25519  5.775s

Making key generation and signing a rough average of 2x faster, and
verification 2.5-3x faster depending on the availability of avx2.  Of course, this
is just my machine, and these results—nowhere near rigorous—should be taken
with a handful of salt.

Translating to a rough cycle count: we multiply by a factor of 3.3 to convert
nanoseconds to cycles per second on a 3300 Mhz CPU, that's 110256 cycles for
verification and 52618 for signing, which is competitive with hand-optimised
assembly implementations.

Additionally, if you're using a CSPRNG from the `rand` crate, the `nightly`
feature will enable `u128`/`i128` features there, resulting in potentially
faster performance.

If your protocol or application is able to batch signatures for verification,
the `verify_batch()` function has greatly improved performance.  On the
aforementioned Intel Skylake i9-7900X, verifying a batch of 96 signatures takes
1.7673ms.  That's 18.4094us, or roughly 60750 cycles, per signature verification,
more than double the speed of batch verification given in the original paper
(this is likely not a fair comparison as that was a Nehalem machine).
The numbers after the `/` in the test name refer to the size of the batch:

    ∃!isisⒶmistakenot:(master *=)~/code/rust/ed25519-dalek ∴ export RUSTFLAGS=-Ctarget_cpu=native
    ∃!isisⒶmistakenot:(master *=)~/code/rust/ed25519-dalek ∴ cargo bench --features=avx2_backend batch
       Compiling ed25519-dalek v0.8.0 (file:///home/isis/code/rust/ed25519-dalek)
        Finished release [optimized] target(s) in 34.16s
          Running target/release/deps/ed25519_benchmarks-cf0daf7d68fc71b6
    Ed25519 batch signature verification/4   time:   [105.20 us 106.04 us 106.99 us]
    Ed25519 batch signature verification/8   time:   [178.66 us 179.01 us 179.39 us]
    Ed25519 batch signature verification/16  time:   [325.65 us 326.67 us 327.90 us]
    Ed25519 batch signature verification/32  time:   [617.96 us 620.74 us 624.12 us]
    Ed25519 batch signature verification/64  time:   [1.1862 ms 1.1900 ms 1.1943 ms]
    Ed25519 batch signature verification/96  time:   [1.7611 ms 1.7673 ms 1.7742 ms]
    Ed25519 batch signature verification/128 time:   [2.3320 ms 2.3376 ms 2.3446 ms]
    Ed25519 batch signature verification/256 time:   [5.0124 ms 5.0290 ms 5.0491 ms]

As you can see, there's an optimal batch size for each machine, so you'll likely
want to your the benchmarks on your target CPU to discover the best size.  For
this machine, around 100 signatures per batch is the optimum:

![](https://github.com/dalek-cryptography/ed25519-dalek/blob/master/res/batch-violin-benchmark.svg)

Additionally, thanks to Rust, this implementation has both type and memory
safety.  It's also easily readable by a much larger set of people than those who
can read qhasm, making it more readily and more easily auditable.  We're of
the opinion that, ultimately, these features—combined with speed—are more
valuable than simply cycle counts alone.

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
version = "1"
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
version = "1"
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
version = "1"
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
