# ed25519-dalek ![](https://img.shields.io/crates/v/ed25519-dalek.svg) ![](https://docs.rs/ed25519-dalek/badge.svg) ![](https://travis-ci.org/isislovecruft/ed25519-dalek.svg?branch=master)

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

    ∃!isisⒶwintermute:(develop *$)~/code/rust/ed25519 ∴ cargo bench --features="bench"
        Finished release [optimized] target(s) in 0.0 secs
         Running target/release/deps/ed25519_dalek-281c2d7a2379edae

    running 6 tests
    test ed25519::test::golden ... ignored
    test ed25519::test::sign_verify ... ignored
    test ed25519::test::unmarshal_marshal ... ignored
    test ed25519::bench::key_generation ... bench:      54,571 ns/iter (+/- 7,861)
    test ed25519::bench::sign           ... bench:      70,009 ns/iter (+/- 22,812)
    test ed25519::bench::verify         ... bench:     185,619 ns/iter (+/- 24,117)

    test result: ok. 0 passed; 0 failed; 3 ignored; 3 measured

In comparison, the equivalent package in Golang performs as follows:

    ∃!isisⒶwintermute:(master *=)~/code/go/src/github.com/agl/ed25519 ∴ go test -bench .
    PASS
    BenchmarkKeyGeneration     20000             85880 ns/op
    BenchmarkSigning           20000             89115 ns/op
    BenchmarkVerification      10000            212585 ns/op
    ok      github.com/agl/ed25519  7.500s

Making key generation, signing, and verification a rough average of one third
faster, one fifth faster, and one eighth faster respectively.  Of course, this
is just my machine, and these results—nowhere near rigorous—should be taken
with a handful of salt.

Additionally, if you're on the Rust nightly channel, be sure to build with
`cargo build --features="nightly"`, which uses Rust's experimental support for
the `u128` type in curve25519-dalek to speed up field arithmetic by roughly a
factor of two.  The benchmarks using nightly (on the same machine as above)
are:

    ∃!isisⒶwintermute:(develop *$)~/code/rust/ed25519 ∴ cargo bench --features="bench nightly"
        Finished release [optimized] target(s) in 0.0 secs
         Running target/release/deps/ed25519_dalek-9d7f8674ae11ac39

    running 6 tests
    test ed25519::test::golden ... ignored
    test ed25519::test::sign_verify ... ignored
    test ed25519::test::unmarshal_marshal ... ignored
    test ed25519::bench::key_generation ... bench:      31,160 ns/iter (+/- 8,597)
    test ed25519::bench::sign           ... bench:      40,565 ns/iter (+/- 4,758)
    test ed25519::bench::verify         ... bench:     106,146 ns/iter (+/- 2,796)

    test result: ok. 0 passed; 0 failed; 3 ignored; 3 measured

Translating to a rough cycle count: we multiply by a factor of 2.6 to convert
nanoseconds to cycles per second on a 2.6 GHz CPU, that's 275979 cycles for
verification and 105469 for signing, which is
[competitive with the optimised assembly version](https://ed25519.cr.yp.to/)
included in the SUPERCOP benchmarking suite (albeit their numbers are for the
older Nehalem microarchitecture).

Additionally, thanks to Rust, this implementation has both type and memory
safety.  It's also easily readable a much larger set of people than those who
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

![](https://github.com/isislovecruft/ed25519-dalek/blob/develop/res/ed25519-malleability.png)

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
[plan](https://github.com/isislovecruft/curve25519-dalek/issues/9) to
eventually support VXEdDSA in curve25519-dalek.

# Installation

To install, add the following to your project's `Cargo.toml`:

    [dependencies.ed25519-dalek]
    version = "^0.3"

Then, in your library or executable source, add:

    extern crate ed25519_dalek

To cause your application to build `ed25519-dalek` with the nightly feature
enabled by default, instead do:

    [dependencies.ed25519-dalek]
    version = "^0.3"
    features = ["nightly"]

To cause your application to instead build with the nightly feature enabled
when someone builds with `cargo build --features="nightly"` add the following
to the `Cargo.toml`:

    [features]
    nightly = ["ed25519-dalek/nightly"]


# TODO

 * Maybe add methods to make exporting keys for backup easier.  Maybe using
   serde?
 * We can probably make this go even faster if we implement SHA512,
   rather than using the rust-crypto implementation whose API requires
   that we allocate memory and memzero it before mutating to store the
   digest.
 * Incorporate ed25519-dalek into Brian Smith's
   [crypto-bench](https://github.com/briansmith/crypto-bench).
