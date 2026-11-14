#!/usr/bin/env bash
# Install the charon + aeneas release pinned in lakefile.toml into .aeneas/.
set -euo pipefail
cd "$(dirname "$0")/.."

TAG=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml)
: "${TAG:?no aeneas rev in lakefile.toml}"
# Linux x86_64 -> linux-x86_64, Linux aarch64 -> linux-aarch64, Darwin arm64 -> macos-aarch64
ASSET=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz

if [[ "$(.aeneas/aeneas -version 2>/dev/null)" != "aeneas $TAG" ]]; then
    rm -rf .aeneas && mkdir .aeneas
    curl -fsSL --proto '=https' \
        "https://github.com/AeneasVerif/aeneas/releases/download/$TAG/$ASSET" \
        | tar -xz -C .aeneas
fi
# The nightly (with rustc-dev) that charon-driver was built against, per the bundle's rust-toolchain.
(cd .aeneas && rustup toolchain install --no-self-update)
cp .aeneas/backends/lean/lean-toolchain lean-toolchain
