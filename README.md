# x25519-dalek  [![](https://img.shields.io/crates/v/x25519-dalek.svg)](https://crates.io/crates/x25519-dalek) [![](https://docs.rs/x25519-dalek/badge.svg)](https://docs.rs/x25519-dalek) [![](https://travis-ci.org/dalek-cryptography/x25519-dalek.svg?branch=master)](https://travis-ci.org/dalek-cryptography/x25519-dalek)

A pure-Rust implementation of x25519 elliptic curve Diffie-Hellman key exchange,
with curve operations provided by 
[curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek).

This crate provides two levels of API: a bare byte-oriented `x25519`
function which matches the function specified in [RFC7748][rfc7748], as
well as a higher-level Rust API for ephemeral Diffie-Hellman.

## Examples

<a href="https://shop.bubblesort.io">
<img 
  style="float: right; width: auto; height: 300px;"
  src="https://raw.githubusercontent.com/dalek-cryptography/x25519-dalek/master/res/bubblesort-zines-secret-messages-cover.jpeg"/>
</a>

Alice and Bob are two adorable kittens who have lost their mittens, and they
wish to be able to send secret messages to each other to coordinate finding
them, otherwise—if their caretaker cat finds out—they will surely be called
naughty kittens and be given no pie!

But the two kittens are quite clever.  Even though their paws are still too big
and the rest of them is 90% fuzziness, these clever kittens have been studying
up on modern public key cryptography and have learned a nifty trick called
*elliptic curve Diffie-Hellman key exchange*.  With the right incantations, the
kittens will be able to secretly organise to find their mittens, and then spend
the rest of the afternoon nomming some yummy pie!

First, Alice uses `EphemeralSecret::new()` and then
`EphemeralPublic::from()` to produce her secret and public keys:

```rust
extern crate x25519_dalek;
extern crate rand;

use x25519_dalek::EphemeralPublic;
use x25519_dalek::EphemeralSecret;
use rand::OsRng;

let mut alice_csprng = OsRng::new().unwrap();
let     alice_secret = EphemeralSecret::new(&mut alice_csprng);
let     alice_public = EphemeralPublic::from(&alice_secret);
```

Bob does the same:

```rust
let mut bob_csprng = OsRng::new().unwrap();
let     bob_secret = EphemeralSecret::new(&mut bob_csprng);
let     bob_public = EphemeralPublic::from(&bob_secret);
```

Alice meows across the room, telling `alice_public` to Bob, and Bob
loudly meows `bob_public` back to Alice.  Alice now computes her
shared secret with Bob by doing:

```rust
use x25519_dalek::EphemeralPublic;
use x25519_dalek::EphemeralSecret;

let shared_secret = EphemeralSecret::diffie_hellman(alice_secret, &bob_public);
```

Similarly, Bob computes the same shared secret by doing:

```rust
let shared_secret = EphemeralSecret::diffie_hellman(bob_secret, &alice_public);
```

Voilá!  Alice and Bob can now use their shared secret to encrypt their
meows, for example, by using it to generate a key and nonce for an
authenticated-encryption cipher.

# Installation

To install, add the following to your project's `Cargo.toml`:

```toml
[dependencies.x25519-dalek]
version = "^0.4"
```

# Documentation

Documentation is available [here](https://docs.rs/x25519-dalek).

# Note

This code matches the [RFC7748][rfc7748] test vectors.
The elliptic curve
operations are provided by `curve25519-dalek`, which makes a best-effort
attempt to prevent software side-channels.

"Secret Messages" cover image and [zine](https://shop.bubblesort.io/products/secret-messages-zine)
copyright © Amy Wibowo ([@sailorhg](https://twitter.com/sailorhg))

[rfc7748]: https://tools.ietf.org/html/rfc7748
