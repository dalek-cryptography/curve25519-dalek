# Lean verification of curve25519-dalek

Specifications of curve25519-dalek's public API in Lean 4, proved against an
[Aeneas](https://github.com/AeneasVerif/aeneas) translation of the Rust code.

| Library | Content |
|---|---|
| `Curve25519Dalek` | The Aeneas translation (`Funs.lean`, `Types.lean`, generated) and the hand-written external functions and types (`FunsExternal.lean`, `TypesExternal.lean`). |
| `Specs` | `Specs/Basic.lean` says how to read a spec. Then one spec file per Rust file: each public item's statement, as a theorem proved in one line from `Proofs`. Items that depend on the configuration are written once, for `x86_64-tables`; `scripts/gen-config-specs.py` generates the other three configurations' copies in `Specs/<File>/`. `Specs/Axioms.lean` checks that every spec uses only Lean's axioms and the external crates' contracts. |
| `Defs` | The definitions the statements use, and `ToAeneas/`, staged for upstreaming to Aeneas: the bridge `Array.toVector` from Aeneas byte arrays to Lean's `Vector UInt8`, and the finite iterators `Iterator.Yields`. |
| `Proofs` | The proofs, one file per Rust item. |
| `Curve25519` | Curve25519's models and facts, and the Niels coordinates, encodings and Ristretto relation of the implementation, independent of dalek; `Curve25519/ToEllipticCurve` stages generic results for the `EllipticCurve` library, and `Curve25519/Proofs` holds unaudited kernel certificates. |
| `Subtle`, `Zeroize` | Models of the `subtle` and `zeroize` crates. |

The elliptic curves and their models (`Curve`, `MontgomeryModel`, `TwistedEdwardsModel`), the
projective, extended and completed coordinates with their formulas, and the Montgomery ladder come
from the [`EllipticCurve`](https://github.com/Beneficial-AI-Foundation/elliptic-curve) library, a
dependency in `lakefile.lean`. The Aeneas version is pinned in `AENEAS_VERSION.txt`.

To trust the result, read `Specs` (except the generated `Specs/<File>/` copies, which
`scripts/gen-config-specs.py --check` keeps equal to their templates up to the configuration's
names), `Defs` (with `ToAeneas/`), `Curve25519` (except
`Curve25519/Proofs`), the definitions of `EllipticCurve`,
`Curve25519Dalek/{Types,Funs}External.lean`, `Subtle/{Types,Contract}.lean` and
`Zeroize/Contract.lean`; the proofs need not be read.

Build from this directory with `lake exe cache get && lake build`. To regenerate the
translation: `scripts/aeneas-install.sh`, then `scripts/aeneas-translate.sh`.
