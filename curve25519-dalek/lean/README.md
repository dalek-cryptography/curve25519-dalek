# Lean Verification of `curve25519-dalek`

This directory contains specs, theorems, axioms, and proofs about `curve25519-dalek`. The Rust code is translated to Lean 4 using [Aeneas](https://github.com/AeneasVerif/aeneas), and then various theorems are proved about it.

## How to Run

Run `make` to do all of the below.

| Command | Effect |
|---|---|
| `make check` | Checks Copies up to date, strict build, linters. |
| `make gen` | Regenerates template-based files (via `scripts/gen-config-specs.py`) |
| `make axioms` | Checks that only the axioms listed in `ForHumans/Theorems/Axioms.lean` appear in proofs. Silent on success. |
| `make definitions` | Checks that `ForHumans/` is self-contained, and doesn't rely on, e.g., definitions in `Proofs/`. Silent on success. |
|  `make coverage` | Checks that every Rust function returning a point, table, precomputation, or scalar has a theorem about it (or is explicitly exempted). This is intended to ensure that we check the well-formedness of all values that are publicly constructible. Silent on success. |
| `make lint` | Runs Lean linters on `ForHumans/` and `Proofs/`. |
| `make shake` | Lists unneeded imports in `ForHumans`. Prune with `lake shake ForHumans --fix`. |
| `make translate` | Reruns Aeneas, thus re-extarcting the Rust code to Lean. |

The Aeneas version is pinned in `AENEAS_VERSION.txt`.

## What the Theorems Cover

Our proofs cover the `u32` and `u64` backends, both with and without the `precomputed-tables` feature. We list Rust files along with theorems proved about them, notes, and properties not covered:

| Rust file | Theorems | Notes | Not covered |
|---|---|---|---|
| `scalar.rs` | `Scalar.lean` | A `Scalar` is its unreduced little-endian value `asNat`. A `HalfWidthScalar` has value `< 2^128`; constructors state it, consumers assume it. | Derived `Clone`/`Copy`; non-public items (`reduce`, `as_radix_16`, …, proved in `Proofs/Scalar/`). Not translated: `Debug`, `Hash`, `from_bits`, `random`, `hash_from_bytes`, `from_hash`, `group`, `serde`. |
| `traits.rs` | `Traits.lean` | Only the blanket `IsIdentity`; the other traits are covered with their implementing types. | |
| `edwards.rs` | `Edwards.lean` | Points via `toPoint` under `OnCurve`, `IsBounded`; tables via `point` under `IsTable`, `IsBounded`; precomputations via `points` under `IsValid`, `IsBounded`. Scalars act by `asNat < 2^255`. Iterators are given by the lists they yield. Multiscalar theorems are about the patched code (`translation-patches/edwards-*multiscalar_mul.patch`), which requires as many scalars as points. | Not translated: `Debug`, `Hash`, `group`, `serde`, `random`, hash-to-curve, provided trait methods. |
| `ristretto.rs`, `ristretto/elligator.rs` | `Ristretto.lean` | A `RistrettoPoint` is an `EdwardsPoint`; it stands for a ristretto255 element when even. Constructors state evenness. `ct_eq`/`eq` decide `Rel`. `compress`/`decompress` are RFC 9496 `encodeRep`/`decodeRep`, `from_uniform_bytes` is `fromUniformRep`, `map_to_curve` is `mapRep`. Multiscalar as for Edwards (`translation-patches/ristretto-*multiscalar_mul.patch`). | Derived `Clone`/`Copy`; `elligator_ristretto_flavor` (`pub(crate)`) and `coset4` (private), proved in their proof files. Not translated: `Debug`, `Hash`, `random`, `try_random`, `hash_from_bytes`, `from_hash`, `group`, `serde`. |
| `montgomery.rs` | `Montgomery.lean` | Inputs via `decodeUCoordinate`, results as `encodeUCoordinate`. Scalar multiplication is RFC 7748's ladder, computing `u(n • Q)` on the curve or its twist. | Not translated: `Debug`, `Hash`, `serde`. |
| `constants.rs` | `Constants.lean` | Includes the backend constants it re-exports. Tables exist only with precomputed tables. | `BASEPOINT_ORDER` (`pub(crate)`, proved in `Proofs/Constants/BasepointOrder.lean`). |

We currently do not have any proofs for any functions that rely on the features: `legacy_compatibility`, `group`, `digest`, `lizard`, or `rand_core`. We also have no proofs for the crate when compiled with backends `fiat` or `simd`.

## Things that Humans Audit

The `ForHumans/` directory has all the stuff that humans need to read in order to be convinced of the safety of this crate:

- `ForHumans/Specs/` contains the definitions used by all theorems (types, operators, constants).
- `ForHumans/Specs/External/` contains axioms about this crate's Rust dependencies, i.e., `subtle`, `zerioize`, and `alloc`.
- `ForHumans/Theorems/` contains all top-level theorems proved about the crate. It is organized such that each Lean file corresponds to one Rust file.
- `ForHumans/AxiomCheck.lean` contains a list of all the places that axioms can come from, and checks that no Lean proofs use any axioms outside of those.
- `ForHumans/Coverage.lean` checks that every Rust function returning a point, table, precomputation, or scalar has a theorem about it (or is explicitly exempted). This is intended to ensure that we check the well-formedness of all values that are publicly constructible.
- `ForHumans/TestVectors.lean` (optional) contains correctness checks against RFC test vectors.

One syntax hint: when `f` is an Aeneas-translated function, `f args ⦃ r => P r ⦄` means that that `f args` returns a value `r` satisfying predicate `P`. This also guarantees that `r` exists, and no panic or other no-return condition happened.

**Autogenerated files.** Just for completeness, we also include autogenerated files in the `ForHumans/` dir. These files are backend-specific, and are autogenerated from a template file by `scripts/gen-config-specs.py`. When auditing, you should just read the template file. Anything of the form `ForHumans/Theorems/<File>/*` is autogenerated from the template `ForHumans/Theorems/<File>.lean`. Similarly, `ForHumans/Specs/Representation/<File>/*` is autogenerated from a template in `ForHumans/Specs/Representation/<File>.lean`.

**Lean dependencies.** We use mathlib and also an elliptic curve [math library](https://github.com/Beneficial-AI-Foundation/elliptic-curve/tree/4015c7cfab714640e77500bdbde6e64face3fbaa) from BAIF. An extra careful human auditor must also review this.

## Other Dirs

`Proofs/` contains all proofs, and `Curve25519Dalek/` contains all code generated by Aeneas.
