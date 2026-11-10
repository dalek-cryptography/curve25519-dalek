# Lean verification of curve25519-dalek

Specifications of curve25519-dalek's public API in Lean 4, proved against an
[Aeneas](https://github.com/AeneasVerif/aeneas) translation of the Rust code.

| Library | Content |
|---|---|
| `Curve25519Dalek` | The Aeneas translation (`Funs.lean`, `Types.lean`, generated) and the hand-written external functions and types (`FunsExternal.lean`, `TypesExternal.lean`). |
| `Specs` | One spec summary per Rust file: each public item's statement and the axioms it depends on. |
| `Defs` | The definitions the statements use, and `ToAeneas/`, staged for upstreaming to Aeneas: the bridge `Array.toVector` from Aeneas byte arrays to Lean's `Vector UInt8`, and the finite iterators `Iterator.Yields`. |
| `Proofs` | The proofs, one file per Rust item. |
| `Curve25519` | Curve25519's models and facts, and the Niels coordinates, encodings and Ristretto relation of the implementation, independent of dalek (repository root); `Curve25519/ToEllipticCurve` stages generic results for the `EllipticCurve` library, and `Curve25519/Proofs` holds unaudited kernel certificates. |
| `Subtle`, `Zeroize` | Models of the `subtle` and `zeroize` crates (repository root). |
| `Curve25519Fast`, `Curve25519Test` | Not audited and not built by default (`lake build Curve25519Test`): a fast X25519 proved equal to `x25519Nat`, and RFC 7748's iterated X25519 test after 1,000 and 1,000,000 iterations, evaluated by `native_decide`, which trusts the Lean compiler (repository root). |

The elliptic curves and their models (`Curve`, `MontgomeryModel`, `TwistedEdwardsModel`), the
projective, extended and completed coordinates with their formulas, and the Montgomery ladder come
from the [`EllipticCurve`](https://github.com/Beneficial-AI-Foundation/elliptic-curve) library, a
dependency in `lakefile.toml`.

To trust the result, read `Specs`, `Defs` (with `ToAeneas/`), `Curve25519` (except
`Curve25519/Proofs`), the definitions of `EllipticCurve`,
`Curve25519Dalek/{Types,Funs}External.lean`, `Subtle/{Types,Contract}.lean` and
`Zeroize/Contract.lean`; the proofs need not be read.

Build from the repository root with `lake exe cache get && lake build`. To regenerate the
translation: `scripts/aeneas-install.sh`, then `scripts/aeneas-translate.sh`.
