# GordieHowe

GordieHowe is a zero-knowledge proof compiler and proof system, by Chad
Sharp and Paul Grubbs.

**This is research code, not for production use.** It has not been audited,
and its interfaces, proof formats and parameters may change without notice.

## Build and test

Requires an x86-64 Linux host, git, and Nix with flakes; the build enters a
pinned shell (clang 21, CMake and the libraries) and needs no other tools.

```sh
scripts/build.sh            # build everything and run every test
nix develop -c ctest --test-dir build -R MLDSAEmulated   # one test
```

`--jobs N` sets the build's parallelism (default: every CPU) and
`--test-jobs N` CTest's (default at most 8). The post-quantum mDL tests
at the QROM parameters need about 1.2 GB each. On a 64-core host the
build and tests take about 20 minutes. Without GFNI and AVX-512, three
GFNI kernel tests report as skipped.

### aarch64

On aarch64, GF(2^128) and GF(2^256) arithmetic uses PMULL and the
bit-sliced kernels use NEON (`lib/sumcheck/skip_neon.h`); defining
`PROOFS_NO_NEON` selects the portable code. The aarch64 build is a cross
build on an x86-64 Linux host, in the flake's `aarch64-cross` shell:

```sh
scripts/cross_aarch64.sh                # lib/: the benches, report_bench and the aarch64 tests
scripts/cross_aarch64.sh --baselines    # the ML-DSA and Falcon split baselines
scripts/cross_aarch64.sh --closure build-aarch64   # the /nix/store paths they load
```

The flags default to a Cortex-A76 (Raspberry Pi 5) with the crypto
extension; `AARCH64_CXXFLAGS` sets others, which must keep the crypto
extension. The executables load the shell's aarch64 libraries from
`/nix/store`, so the target needs Nix and those store paths:
`nix-store --export $(nix-store -qR PATH...) | ssh HOST nix-store --import`
copies the paths `--closure` lists with their dependencies, and
`nix-store --add-root LINK --realise PATH` on the target keeps each from
garbage collection. The executables then run there from a copy of the
build directory.
The shell's OpenSSL is built with its ARMv8 assembly (SHA-2, AES, PMULL);
`openssl_asm_test` checks it on the target.

## Running an example

```sh
nix develop -c build/bench/mldsa_emulated_bench bench --profile narrow --reps 3
```

Each application has such an executable in `build/bench/`; `--profile
narrow` selects the ROM parameters and `--profile wide` the QROM
parameters. `lib/gordiehowe/examples/README.md` says which file to read in
each application.

## Reproducing the papers' tables

`repro.sh` reruns every measurement behind the papers' tables, and
`repro.sh --smoke` checks each stage for correctness only. The paper's figures
were measured on a 128-core AMD EPYC 9754 with no other large jobs running;
`repro.sh` warns when the host could disturb the timings.

## Layout

- `lib/gordiehowe/`: the language, compiler, proof system and tests;
  `examples/` holds the applications.
- `lib/`: also the Longfellow files we modified or derived from, at their
  Longfellow paths, and our host and library code beside them;
  `docs/longfellow-changes.md` lists each one and its change.
- `third_party/longfellow/`: the Longfellow files we use unchanged, from
  Longfellow at d5e6be77.
- `comparisons/longfellow/`: the Longfellow baselines, on upstream at
  d5e6be77.
- `benchmarks/`, `analysis/`: the benchmark driver, comparisons and table
  scripts.
- `formal/`: the Lean library (`formal/README.md`).

## License

Apache License 2.0 (`LICENSE`). Includes code from Longfellow ZK (Google
LLC, Apache-2.0) and XKCP (CC0 1.0, one file under the CRYPTOGAMS license);
see `NOTICE`.
