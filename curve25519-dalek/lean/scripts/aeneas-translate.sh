#!/usr/bin/env bash
# Translate curve25519-dalek to Lean: copy the Cargo workspace to .llbc/work/, apply
# translation-patches/ to the copy, run charon on it and aeneas on the result.
# Runs in curve25519-dalek/lean/, the Lean project; the Cargo workspace is two levels up.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$PWD
repo=$(cd ../.. && pwd)

TAG=$(tr -d '[:space:]' < AENEAS_VERSION.txt)
: "${TAG:?AENEAS_VERSION.txt is empty}"
[[ "$(.aeneas/aeneas -version 2>/dev/null)" == "aeneas $TAG" ]] \
    || { echo "run ./scripts/aeneas-install.sh: .aeneas/ is not $TAG" >&2; exit 1; }

# The workspace
work=.llbc/work
mkdir -p "$work"
(cd "$repo" && rsync -a --delete --exclude=target/ --exclude=/curve25519-dalek/lean/ \
    Cargo.toml Cargo.lock curve25519-dalek curve25519-dalek-derive ed25519-dalek x25519-dalek \
    "$root/$work/")

shopt -s nullglob
for patch in "$root"/translation-patches/*.patch; do
    (cd "$work" && GIT_CEILING_DIRECTORIES="$root/.llbc" git apply "$patch")
done

mkdir -p .llbc
# Four configurations, merged by charon's multi-target translation:
# {64-bit, 32-bit} x {with precomputed-tables, without precomputed-tables}
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
rustc="$(.aeneas/charon toolchain-path)/bin/rustc"
serial='--cfg curve25519_dalek_backend="serial"'
# Every configuration is a JSON target spec copied from a Linux triple of that word size; the spec
# file name is the target name that suffixes the Lean items (`«64bit-tables»`, `«64bit-notables»`, …).
targets=()
for bits_triple in 64:x86_64-unknown-linux-gnu 32:i686-unknown-linux-gnu; do
    bits=${bits_triple%%:*} triple=${bits_triple#*:}
    for spec in "${bits}bit-tables" "${bits}bit-notables"; do
        "$rustc" -Z unstable-options --print target-spec-json --target "$triple" > ".llbc/$spec.json"
        targets+=(--targets "$PWD/.llbc/$spec.json")
    done
    export "CARGO_TARGET_${bits}BIT_TABLES_RUSTFLAGS=$serial --cfg feature=\"precomputed-tables\""
    export "CARGO_TARGET_${bits}BIT_NOTABLES_RUSTFLAGS=$serial"
done
(cd "$work/curve25519-dalek" && "$root/.aeneas/charon" cargo --preset=aeneas "${targets[@]}" \
    --dest-file "$root/.llbc/curve25519_dalek.llbc" \
    -- --locked --no-default-features --features alloc,zeroize \
    -Zjson-target-spec -Zbuild-std=core,alloc)
.aeneas/aeneas -backend lean -split-files -emit-json -namespace Curve25519Dalek \
    -dest . -subdir Curve25519Dalek .llbc/curve25519_dalek.llbc
# The external declarations are in ForHumans/Specs/External/ (their specs in Proofs/External/),
# not in the {Types,Funs}External modules Aeneas imports.
sed -i 's/^public import Curve25519Dalek\.TypesExternal$/public import ForHumans.Specs.External.Subtle.Types/' \
    Curve25519Dalek/Types.lean
sed -i 's/^public import Curve25519Dalek\.FunsExternal$/public import Proofs.External.Alloc/' \
    Curve25519Dalek/Funs.lean
rm -f Curve25519Dalek/TypesExternal_Template.lean Curve25519Dalek/FunsExternal_Template.lean
