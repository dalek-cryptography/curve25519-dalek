#!/usr/bin/env bash
# Install the charon + aeneas release pinned in AENEAS_VERSION.txt into .aeneas/.
set -euo pipefail
cd "$(dirname "$0")/.."

TAG=$(tr -d '[:space:]' < AENEAS_VERSION.txt)
: "${TAG:?AENEAS_VERSION.txt is empty}"
# Linux x86_64 -> linux-x86_64, Linux aarch64 -> linux-aarch64, Darwin arm64 -> macos-aarch64
ASSET=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz

if [[ "$(.aeneas/aeneas -version 2>/dev/null)" != "aeneas $TAG" ]]; then
    rm -rf .aeneas && mkdir .aeneas
    curl -fsSL --proto '=https' \
        "https://github.com/AeneasVerif/aeneas/releases/download/$TAG/$ASSET" \
        | tar -xz -C .aeneas
fi
# The nightly (with rustc-dev) that charon-driver was built against, per the bundle's rust-toolchain.
# Named explicitly: rustup before 1.28 cannot install from the file.
channel=$(sed -n 's/^channel = "\(.*\)"$/\1/p' .aeneas/rust-toolchain)
components=$(sed -n 's/^components = \[\(.*\)\]$/\1/p' .aeneas/rust-toolchain | tr -d ' "')
rustup toolchain install --no-self-update --profile minimal "$channel" --component "$components"
cp .aeneas/backends/lean/lean-toolchain lean-toolchain
