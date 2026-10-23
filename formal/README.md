# GordieHowe Lean library

The Lean 4 formalization of the security analysis in "GordieHowe: Fast Hash-Based Zero-Knowledge
Proofs Bridging Binary and Large-Characteristic Fields", by Chad Sharp and Paul Grubbs, built on
Mathlib. Appendix J of the paper ("Machine-checked results") maps each machine-checked result to
its Lean declarations; `GordieHowe/PaperManifest.lean` holds that map, and the theorems the paper
claims carry `@[headline]`. Names below are relative to the namespace `GordieHowe`.

## What is proved

- **spBCS** (Theorem 6.6), for every series–parallel IOP, in the ROM and the QROM: knowledge
  soundness, weak online simulation extractability, everlasting zero knowledge, unconditional
  witness indistinguishability, completeness and soundness (namespace `SPBCS`).
- **The proof system** (Theorem 5.3), for every valid realized program: completeness,
  honest-verifier zero knowledge and round-by-round knowledge soundness
  (`RealizedProgram.ProofSystem.FieldBranches`).
- **The non-interactive argument** (Theorem 6.7), in general and for each of the ten
  configurations `MLDSA44.{Emulated, Native}.{ROMParams, QROMParams}` and
  `Falcon512.{Native, Ring.Native, Ring.Carrier}.{ROMParams, QROMParams}`; the generic statements
  are in `Configuration.Common`. The paper's ML-DSA-44 figures are those of `MLDSA44.Emulated`.
- **The ML-DSA-44 source program** is complete and round-by-round knowledge sound for the FIPS 204
  verification relation (`MLDSA44.Emulated.*.source_rbr_knowledge_soundness`), with ExpandA
  bounded as FIPS 204 Appendix C permits. For this application Theorem 6.7 is machine-checked
  from the source program to the non-interactive argument.

The library also formalizes the results from the literature it uses, among them Zhandry's
compressed oracle, the compressed-oracle and BCS lemmas of Chiesa, Manohar and Spooner, and the
one-way-to-hiding lemma of Ambainis, Hamburg and Unruh.

## Assumptions

The library declares no axioms, contains no `sorry` and never uses `native_decide`. The C++
compiler exports each application's realized program as Lean definitions, and the kernel checks
that it is valid and that its realizations meet their conditions.

The GKR circuits are not exported. The configuration theorems take as hypotheses
(`RealizedProgram.CircuitsEnforce`, `RealizedProgram.CircuitsAccept`,
`GordieHowe/Language/Assumptions.lean`) that each compiled circuit enforces the checks assigned to
it, accepts the honest input, and stays within its listed layer and wire counts. Beyond these we
assume that the export records the program the prover and verifier use, that the C++ implements
the Lean model, and that the ML-DSA, SHAKE128 and SHAKE256 specifications adapted from VCVio follow
FIPS 204 and FIPS 202 (known-answer tests in `Vendor/HashSigTest/`). The extractors' and
simulators' running times are argued in their docstrings, which `scripts/CostLint.lean` checks
for.

## Layout

- `GordieHowe/`: the library, organized as the paper: `Foundations/`, `Model/` (IOPs, NARGs, the
  quantum model, QROM, ROM), `Language/` (realized programs), `ProofSystem/`, `SPBCS/`,
  `Applications/`, and `Errata/` (machine-checked counterexamples to published analyses of
  Ligero's masked tests).
- `GordieHowe/Generated/`: the exported plans and programs with their validity proofs, emitted by
  the C++ compiler. Each header names its configuration, C++ commit and system digest. Do not edit
  by hand.
- `Vendor/`: vendored Lean code from VCVio and ArkLib and its dependencies; `Vendor/README.md`
  records the provenance file by file.
- `Test/`: `#guard`/`#eval` tests of the ML-DSA specification against OpenSSL and the C++
  reference, and of the executable fields (`scripts/lake.sh build GordieHoweTest`).
- `scripts/`: `check.sh` and the lints and audits it runs.

## Building and checking

Lean `v4.34.0` (`lean-toolchain`) and Mathlib at `5ed29652` (`lakefile.toml`). From this directory:

```sh
lake exe cache get
scripts/check.sh --quiet
```

Never build Mathlib from source; `check.sh` refuses to start if the cache is incomplete. It builds
the library and checks the running-time lint, the headline theorems' statement closure
(`audit/statement_closure.txt`), `sorry` counts, the axioms and `native_decide`.

`check.sh` caps memory: `LEAN_NUM_THREADS` (default 12) sets the parallelism and `PQ_MEM_MAX`
(default `96G`) the limit; lower both together on a smaller machine. With 12 threads a check
takes about 18 minutes and peaks at about 53 GiB; with 64 threads, about 12 minutes and 67 GiB.
Do not run a bare `lake build`, which bypasses the cap.

`scripts/paper_manifest.py --paper-dir DIR` writes the Lean names into the paper's LaTeX source at
`DIR`, and `--check` verifies them without writing.

## Regenerating the exported plans

From the repository root, inside the pinned Nix shell:

```sh
./run_bench.sh --profile narrow --hash-check-only --export-lean
./run_bench.sh --profile wide --hash-check-only --export-lean
```

`narrow` writes the `ROMParams` files and `wide` the `QROMParams` files. Then rerun
`scripts/check.sh`.

## License

Copyright 2026 Chad Sharp and Paul Grubbs, Apache License 2.0 (`../LICENSE`). Vendored code keeps
its own Apache-2.0 licenses, whose texts are in `Vendor/`.
