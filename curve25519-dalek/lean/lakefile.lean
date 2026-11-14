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

-- What a reviewer reads: the specifications (`ForHumans/Specs/`) and the theorems about the Rust
-- code (`ForHumans/Theorems/`).
@[default_target]
lean_lib ForHumans where
  globs := #[.andSubmodules `ForHumans]

-- Aeneas-generated Lean translation.
@[default_target]
lean_lib Curve25519Dalek

-- Everything else: the proofs and the lemmas they use.
@[default_target]
lean_lib Proofs where
  globs := #[.andSubmodules `Proofs]
