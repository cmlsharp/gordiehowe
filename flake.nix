# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

{
  description = "GordieHowe: proofs of possession and their comparisons, built on Longfellow ZK";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = with pkgs;
              [
                # Build tools
                cmake
                clang
                gnumake
                ccache

                # Dependencies
                openssl
                zstd
                zlib
                gtest
                gbenchmark

                # Benchmark runner and report generation
                python3
                git

                # The binius64 comparison (benchmarks/pq_binius.sh), whose
                # rust-toolchain.toml pins this nixpkgs's rustc (1.98.1)
                rustc
                cargo
              ]
              ++ pkgs.lib.optionals pkgs.stdenv.isLinux [pkgs.util-linux];

            shellHook = ''
              export CXX=clang++
              export CC=clang
              # Keep -march=native when a build asks for it: stdenv sets this
              # to 1, and the cc-wrapper then strips the flag silently.
              export NIX_ENFORCE_NO_NATIVE=0
            '';
          };
        }
        # The aarch64 cross build (scripts/cross_aarch64.sh) from an x86-64
        # host: nixpkgs' aarch64-multiplatform toolchain with clang (the
        # clang of the default shell, from the same nixpkgs) and aarch64
        # libraries; CC and CXX are the cross compilers.
        // pkgs.lib.optionalAttrs (system == "x86_64-linux") (let
          # nixpkgs' OpenSSL picks its Configure target from a table of
          # host systems that lacks aarch64-linux; a native build runs
          # ./config, which detects linux-aarch64, but a cross build falls
          # through to linux-generic64, which has no assembly: no ARMv8
          # SHA-2, AES or PMULL code (openssl/default.nix, configureScript,
          # at the pinned nixpkgs). No nixpkgs issue reports it for
          # aarch64; the same fallback was fixed for x86_64-musl
          # (https://github.com/NixOS/nixpkgs/pull/82708) and riscv64
          # (https://github.com/NixOS/nixpkgs/pull/141817). The stdenv plays
          # no part: gcc's cross OpenSSL gets the same target. This overlay
          # configures it as linux-aarch64, and the build fails if the
          # ARMv8 SHA-256 assembly (sha512-armv8.pl's CRYPTOGAMS banner) is
          # missing from libcrypto, e.g. after a nixpkgs bump changes the
          # configure line.
          # Only the aarch64 package set's OpenSSL: overlays also reach the
          # build platform's (x86-64) packages, which keep theirs.
          opensslAarch64Asm = final: prev: {
            openssl =
              if !final.stdenv.hostPlatform.isAarch64
              then prev.openssl
              else
                prev.openssl.overrideAttrs (old: {
                  configureScript = "./Configure linux-aarch64";
                  postInstall =
                    (old.postInstall or "")
                    + ''
                      if ! grep -q "SHA256 block transform for ARMv8" $out/lib/libcrypto.so.*; then
                        echo "libcrypto lacks the ARMv8 SHA-256 assembly" >&2
                        exit 1
                      fi
                    '';
                });
          };
          cross = pkgs.pkgsCross.aarch64-multiplatform.appendOverlays [opensslAarch64Asm];
        in {
          aarch64-cross = (cross.mkShell.override {stdenv = cross.clangStdenv;}) {
            nativeBuildInputs = with pkgs; [cmake gnumake ccache python3];
            buildInputs = with cross; [openssl zstd zlib gtest gbenchmark];
            shellHook = ''
              export NIX_ENFORCE_NO_NATIVE=0
            '';
          };
        });
      }
    );
}
