# GordieHowe Lean library

The Lean 4 formalization of the security analysis in "GordieHowe: Fast Hash-Based Zero-Knowledge
Proofs Bridging Binary and Large-Characteristic Fields", by Chad Sharp and Paul Grubbs, built on
Mathlib. Appendix J of the paper ("Machine-checked results") maps each machine-checked result to
its Lean declarations; `GordieHoweCerts/PaperManifest.lean` holds that map, and the theorems the paper
claims carry `@[headline]`. Names below are relative to the namespace `GordieHowe`.

## What is proved

- **spBCS** (Theorem 6.6), for every series–parallel IOP, in the ROM and the QROM: knowledge
  soundness, weak online simulation extractability, everlasting zero knowledge, unconditional
  witness indistinguishability, completeness and soundness (namespace `SPBCS`).
- **The proof system** (Theorem 5.3), for every valid realized program: completeness,
  honest-verifier zero knowledge and round-by-round knowledge soundness
  (`RealizedProgram.ProofSystem.FieldBranches`).
- **The non-interactive argument** (Theorem 6.7), in general and for each of the twelve
  configurations `MLDSA44.{Emulated, Native}.{ROMParams, QROMParams}` and
  `Falcon512.{Native, Emulated, Ring.Native, Ring.Carrier}.{ROMParams, QROMParams}`; the generic statements
  are in `Configuration.Common`. The paper's ML-DSA-44 figures are those of `MLDSA44.Emulated`.
- **The ML-DSA-44 source program** is complete and round-by-round knowledge sound for the FIPS 204
  verification relation (`MLDSA44.Emulated.*.source_rbr_knowledge_soundness`), with ExpandA
  bounded as FIPS 204 Appendix C permits. For this application Theorem 6.7 is machine-checked
  from the source program to the non-interactive argument.

The library also formalizes the results from the literature it uses, among them Zhandry's
compressed oracle, the compressed-oracle and BCS lemmas of Chiesa, Manohar and Spooner, and the
one-way-to-hiding lemma of Ambainis, Hamburg and Unruh.

## Assumptions

The library declares no axioms and contains no `sorry`. The C++ compiler exports each
application's realized program as Lean definitions, and the kernel checks that it is valid and
that its realizations meet their conditions.

Each program's `programOk` checks validity, realization, the program facts, completeness, shapes,
figures, source roles and the GKR certificates of its circuits. The generated `Core` and `Certified`
modules project its soundness theorem. The field table, the tableaus and the packing descriptors'
agreement with the field registry (`Pending/Small`) and the interpretation's model (`Pending/Model`)
are separate kernel checks of each program.

`scripts/cert_mode.sh kernel|native` selects the source directory of `GordieHoweCheck` in
`lakefile.toml`. Kernel sources use `decide +kernel` leaves and compositions, with the GKR certificate
checks as their own modules. Native sources run one `gh_native_check` per program, trusting the
compiled checkers through an axiom per invocation (`<theorem>._native.native_decide.ax_<i>_<j>`). No
mode definition or tactic option switches proof evaluation. Lake rebuilds the selected modules and
their dependents after a switch. The published check runs in kernel mode. With `--certs` in native
mode, `check.sh` requires `--dev` and reports every headline whose axioms include a compiled-check
axiom or `Lean.ofReduceBool`.

The GKR circuits are exported with certificates. `RealizedProgram.CircuitsEnforce` and
`RealizedProgram.CircuitsAccept` (`GordieHowe/Language/Assumptions.lean`), that each circuit enforces
the checks assigned to it, accepts the honest input and stays within its listed layer and wire
counts, are fields of the proof system, proved from the checked certificates, and no headline takes
them as hypotheses. The extractors' and simulators' running times are argued in their docstrings,
which `scripts/CostLint.lean` checks for.

### What the C++ and the Lean must agree on

The Lean proves its theorems about the exported programs and its model of the proof system. These
correspondences with the C++ are outside what it checks:

- **The proof system.** The C++ prover and verifier implement the Lean model. Their transcripts are
  not proved identical to the model's byte for byte.
- **The export.** The exported program, circuits and plan, including the Ligero parameters and query
  counts, are the ones the prover and verifier use.
- **Specifications.** The ML-DSA, SHAKE128 and SHAKE256 specifications adapted from VCVio follow FIPS
  204 and FIPS 202 (known-answer tests in `Vendor/HashSigTest/`).
- **Opaque functions.** A public value computed outside the constraints (`mac.target_bits`,
  `key.coefficients`, `device.e2_point`, `issuer.q_table`) is implemented separately in the C++ and
  in the Lean (`OpaqueKey.fn`) and matched by name.
- **Fields.** A plan's field specification selects a Lean field from the registry, and packing node
  names select its subgroups. The packing facts are checked in the Lean; that the C++ computes in the
  same field and tower is not.
- **Encodings.** `FieldInterp.decode` and `toNat` read the C++ encoding of an element, and bit views
  use its basis. The `.ghc` readers decode the C++ writer's format; this holds in both check modes.
- **Other names.** The pad-copy map `polynomialBits`, statement members (`statement.<member>`), the
  `codec` names and hash names carry their meaning by string.
- **Reported sizes.** The byte sizes in the figures are stated in the model.

The SHA-256, SHA3, RSA and mDL programs have certificates only: the exported program is checked, and
no theorem relates it to the function it is meant to compute. The ML-DSA-44 and Falcon-512 source
programs are proved against their schemes' verification relations.

The cryptographic assumptions (Module-LWE, Module-SIS, SelfTargetMSIS, and the unforgeability
of the base signature schemes) are defined games with hardness predicates on a class of
adversaries, never axioms; a theorem that uses one takes the predicate, or a bound on an explicit
adversary, as a hypothesis. `GordieHowe/Assumptions.lean` lists each with its definition, its
source and its uses, together with the idealizations the proofs use (`ExpandA`, `ExpandS`,
`SampleInBall`, `ExpandMask` modeled as random oracles; the uniform-`t` key model) and the
results that still carry an idealization-dependent term.

## Layout

- `GordieHowe/`: the library, organized as the paper: `Foundations/`, `Model/` (IOPs, NARGs, the
  quantum model, QROM, ROM), `Language/` (realized programs), `ProofSystem/`, `SPBCS/`,
  `Applications/`, and `Errata/` (machine-checked counterexamples to published analyses of
  Ligero's masked tests).
- `GordieHoweCerts/`: the certificate library `GordieHoweCerts`, opt in, with modules named
  `GordieHoweCerts.<path>`. `GordieHoweCerts/Generated/` holds the exported plans and programs with
  their validity proofs, emitted by the C++ compiler; each header names its configuration, C++
  commit and system digest; do not edit them by hand. The rest are the modules importing one (the
  applications' concrete instantiations with their headline theorems, the paper manifest). The
  declarations keep their `GordieHowe.` namespaces. The root `GordieHoweCerts.lean` imports them and
  the gate's other certificates. Every module of the library imports a generated one, directly or
  through another, and the default target `GordieHowe` imports none of them
  (`scripts/cert_boundary.py`).
- `Vendor/`: vendored Lean code from VCVio and ArkLib and its dependencies; `Vendor/README.md`
  records the provenance file by file.
- `Test/`: `#guard`/`#eval` tests of the ML-DSA specification against OpenSSL and the C++
  reference, and of the executable fields (`scripts/lake.sh build GordieHoweTest`); the tests that
  read exported programs or certificates are the library `GordieHoweCertsTest`.
- `scripts/`: `check.sh` and the lints and audits it runs.

## Building and checking

Lean `v4.34.0` (`lean-toolchain`) and Mathlib at `5ed29652` (`lakefile.toml`). From this directory:

```sh
lake exe cache get
scripts/check.sh --quiet --certs
```

Never build Mathlib from source; `check.sh` refuses to start if the cache is incomplete. It builds
the library `GordieHowe` and checks the running-time lint, the headline theorems' statement closure,
`sorry` counts, the axioms, the certificate check mode, `native_decide` and the headline theorems'
axioms (`scripts/HeadlineAxioms.lean`). Without `--certs` it checks no certificate and the audits
read `GordieHowe` only; `--certs` also builds `GordieHoweCerts`, runs the audits over it and writes
the recorded closure `audit/statement_closure.txt`.

`check.sh` caps memory: `PQ_MEM_MAX` (default `96G`) is the limit, and Lake runs `PQ_LAKE_JOBS`
modules at once, by default `PQ_MEM_MAX` divided by 12 GiB (`scripts/lake.sh`); lower `PQ_MEM_MAX`
on a smaller machine. Do not run a bare `lake build`, which bypasses the cap.

`scripts/paper_manifest.py --paper-dir DIR` writes the Lean names into the paper's LaTeX source at
`DIR`, and `--check` verifies them without writing.

## Regenerating the exported plans

Build the C++ (the exporters are its `*_bench` targets) and run the script from the repository
root, inside the pinned Nix shell:

```sh
cmake --build build -j "$(nproc)"
scripts/regenerate_exports.py --build build
```

A list of `--target`s builds one target at a time, so build the whole directory.

This regenerates every program's files under `GordieHoweCerts/Generated/` and `Check/{Native,Kernel}/`,
`.ghc` files included, from one build, with the run id `exports` and the commit placeholder
`EXPORTER_COMMIT`. It removes the files an export no longer writes and compares the tree with the
exports byte for byte. With `--check` it compares only, and a difference fails. Then rerun
`scripts/check.sh`.

## License

Copyright 2026 Chad Sharp and Paul Grubbs, Apache License 2.0 (`../LICENSE`). Vendored code keeps
its own Apache-2.0 licenses, whose texts are in `Vendor/`.
