# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

{
  description = "Build shell for the longfellow-baselines repository (upstream longfellow-zk and the baselines built on it)";

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
        devShells.default = pkgs.mkShell {
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
              ripgrep
              git
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
    );
}
