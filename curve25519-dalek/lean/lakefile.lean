import Lake
open Lake DSL

-- Elliptic curves and their models over a field, independent of any curve.
require EllipticCurve from git "https://github.com/Beneficial-AI-Foundation/elliptic-curve.git"
  @ "4015c7cfab714640e77500bdbde6e64face3fbaa"

-- The pinned Aeneas version, read from `AENEAS_VERSION.txt` (a GitHub release tag), which
-- `scripts/aeneas-install.sh` also reads to download the charon/aeneas binaries.
def aeneasRev : String := (include_str "AENEAS_VERSION.txt").trimAscii.toString
require aeneas from git "https://github.com/AeneasVerif/aeneas.git"
  @ aeneasRev / "backends/lean"

package «curve25519-dalek» where
  keywords := #["formal verification"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxRecDepth, .ofNat 10000⟩]

-- Hand-written library for the `subtle` crate.
@[default_target]
lean_lib Subtle

-- Hand-written library for the `zeroize` crate.
@[default_target]
lean_lib Zeroize

-- Aeneas-generated Lean translation.
@[default_target]
lean_lib Curve25519Dalek

-- Curve25519 in general (parameters, models, encodings; `Curve25519/Models`, and
-- `Curve25519/ToEllipticCurve` staged for the EllipticCurve library), independent of dalek.
@[default_target]
lean_lib Curve25519

-- Definitions needed to state the specs and `ToAeneas/` staged for Aeneas.
@[default_target]
lean_lib Defs where
  globs := #[.andSubmodules `Defs, .submodules `ToAeneas]

-- Spec summaries, one per Rust file.
@[default_target]
lean_lib Specs where
  globs := #[.andSubmodules `Specs]

-- Proofs, one file per Rust item, and the helper theorems they use.
@[default_target]
lean_lib Proofs where
  globs := #[.andSubmodules `Proofs]
