#!/bin/bash

function match_and_report() {
    PATTERN=$1
    FILE=$2

    if grep -q "$PATTERN" "$FILE"; then
      echo build OK "$FILE" : "$PATTERN"
    else
      echo build ERROR "$FILE" : "$PATTERN"
      echo ">>>>>>>>>>>>>>>>>>>>>>>>>>"
      cat "$FILE"
      echo "<<<<<<<<<<<<<<<<<<<<<<<<<<"
      exit 1
    fi
}

# Assuming naively 64 bit host
OUT=build_default.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'auto'" "$OUT"
match_and_report "curve25519_dalek_bits is '64'" "$OUT"

# Override to 32 bits assuming naively 64 bit build host
OUT=build_default_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_bits=\"32\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'auto'" "$OUT"
match_and_report "curve25519_dalek_bits is '32'" "$OUT"

# Override to 64 bits on 32 bit target
OUT=build_default_64_on_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_bits=\"64\"" cargo build --target i686-unknown-linux-gnu > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'auto'" "$OUT"
match_and_report "curve25519_dalek_bits is '64'" "$OUT"

# 32 bit target default
OUT=build_default_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\"" cargo build --target i686-unknown-linux-gnu > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'auto'" "$OUT"
match_and_report "curve25519_dalek_bits is '32'" "$OUT"

# wasm 32 bit target default
OUT=build_default_wasm_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\"" cargo build --target wasm32-unknown-unknown > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'auto'" "$OUT"
match_and_report "curve25519_dalek_bits is '32'" "$OUT"

# fiat override with default 64 bit naive host assumption
OUT=build_fiat_64.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_backend=\"fiat\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'fiat'" "$OUT"
match_and_report "curve25519_dalek_bits is '64'" "$OUT"

# fiat 32 bit override
OUT=build_fiat_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_backend=\"fiat\" --cfg curve25519_dalek_bits=\"32\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'fiat'" "$OUT"
match_and_report "curve25519_dalek_bits is '32'" "$OUT"

# serial override with default 64 bit naive host assumption
OUT=build_serial_64.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_backend=\"serial\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'serial'" "$OUT"
match_and_report "curve25519_dalek_bits is '64'" "$OUT"

# serial 32 bit override
OUT=build_serial_32.txt
env RUSTFLAGS="--cfg curve25519_dalek_diagnostics=\"build\" --cfg curve25519_dalek_backend=\"serial\" --cfg curve25519_dalek_bits=\"32\"" cargo build > "$OUT" 2>&1
match_and_report "curve25519_dalek_backend is 'serial'" "$OUT"
match_and_report "curve25519_dalek_bits is '32'" "$OUT"
