#!/usr/bin/env bash
# Translate curve25519-dalek to Lean: copy the Cargo workspace to .llbc/work/, apply
# curve25519-dalek/translation-patches/ to the copy, run charon on it and aeneas on the result.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$PWD

TAG=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml)
: "${TAG:?no aeneas rev in lakefile.toml}"
[[ "$(.aeneas/aeneas -version 2>/dev/null)" == "aeneas $TAG" ]] \
    || { echo "run ./scripts/aeneas-install.sh: .aeneas/ is not $TAG" >&2; exit 1; }

# The workspace
work=.llbc/work
mkdir -p "$work"
rsync -a --delete --exclude=target/ --exclude=/curve25519-dalek/lean/ \
    Cargo.toml Cargo.lock curve25519-dalek curve25519-dalek-derive ed25519-dalek x25519-dalek \
    "$work/"

shopt -s nullglob
for patch in curve25519-dalek/translation-patches/*.patch; do
    (cd "$work" && GIT_CEILING_DIRECTORIES="$root/.llbc" git apply "$root/$patch")
done

mkdir -p .llbc
# Four configurations, merged by charon's multi-target translation:
# {64-bit, 32-bit} x {with precomputed-tables, without precomputed-tables}
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
rustc="$(.aeneas/charon toolchain-path)/bin/rustc"
serial='--cfg curve25519_dalek_backend="serial"'
# Every configuration is a JSON target spec copied from the Linux triple; the spec file name is the
# target name that suffixes the Lean items (`«x86_64-tables»`, `«x86_64-no-tables»`, …).
targets=()
for arch in x86_64 i686; do
    triple=$arch-unknown-linux-gnu
    for spec in "$arch-tables" "$arch-no-tables"; do
        "$rustc" -Z unstable-options --print target-spec-json --target "$triple" > ".llbc/$spec.json"
        targets+=(--targets "$PWD/.llbc/$spec.json")
    done
    export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$arch-tables")_RUSTFLAGS=$serial --cfg feature=\"precomputed-tables\""
    export "CARGO_TARGET_$(tr 'a-z-' 'A-Z_' <<< "$arch-no-tables")_RUSTFLAGS=$serial"
done
(cd "$work/curve25519-dalek" && "$root/.aeneas/charon" cargo --preset=aeneas "${targets[@]}" \
    --dest-file "$root/.llbc/curve25519_dalek.llbc" \
    -- --locked --no-default-features --features alloc,zeroize \
    -Zjson-target-spec -Zbuild-std=core,alloc)
.aeneas/aeneas -backend lean -split-files -emit-json -namespace Curve25519Dalek \
    -dest curve25519-dalek/lean -subdir Curve25519Dalek .llbc/curve25519_dalek.llbc
