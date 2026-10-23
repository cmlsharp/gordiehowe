#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Builds Baum–Beckmann's blind_mldsa (with patches/bb-private-message.patch
# applied) and the driver examples/pop_bench.rs, in release mode with the
# crate's own settings: .cargo/config.toml (-C target-cpu=native,
# --cfg aes_armv8, which only gates aarch64 code in the aes crate) and
# [profile.release] (opt-level 3, lto = true, codegen-units = 1), under the
# pinned rustc 1.95.0 (rust-toolchain.toml, through rustup).
#
#   bb_build.sh DIR    DIR holds swanky/ and blind_mldsa/ side by side
set -euo pipefail
dir="$1"
cd "$dir/blind_mldsa"
# Never run flatc from swanky's build scripts: the generated files are in the tree.
export SWANKY_FLATBUFFER_DO_NOT_GENERATE=1
rustc -vV
cargo -V
cargo build --release -j "${BUILD_JOBS:-6}" --example pop_bench
ls -la target/release/examples/pop_bench
