-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. Known-answer tests checking the vendored, closed ML-DSA-44
verifier (`MLDSA.Concrete.expandA`, `MLDSA.Concrete.sampleInBallPoly`,
`MLDSA.Concrete.verify44`) and, where a vector exists, ML-DSA-65's `verify65`, against the
test vectors already checked into
`third_party/longfellow/lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test_vectors.inc`,
`lib/circuits/tests/pq/ml_dsa/ml_dsa_44_benchmark.inc`, and the ML-DSA-65 vectors and examples
of the C++ reference tests. This is the first check of these
primitives against anything outside their own SHAKE known-answer tests (see
`Vendor/LatticeCrypto/MLDSA/ConcretePrimitives.lean`'s header and `Vendor/README.md`).

No Falcon known-answer vectors exist in the C++ Falcon tests: every
test there either builds a synthetic (non-FIPS-206-compliant) instance at runtime or checks
`HashToPoint` in-circuit against the same host implementation for self-consistency only, with
no externally-sourced expected output. `Falcon.Concrete.hashToPoint` / `verify512` are
therefore not checked here.

The runners' top-level `#eval`s are why these files use a plain `import`, not `module` /
`public import`: see `Vendor/README.md`'s "Lake / module-system notes" for why a `module`
file's top-level `#eval` fails to find the native implementation of an imported declaration.

The checks run in three modules that build in parallel, each a top-level `#eval` that prints its
results and throws if a check fails, so that the build of `GordieHoweTest` fails:
`MLDSAVectorsVerify.lean` (ExpandA, SampleInBall, verify44, verify65), `MLDSAVectorsKeyGen.lean`
(key generation) and `MLDSAVectorsSign.lean` (deterministic signing). This module imports them.
Run with `lake build GordieHoweTest 2>&1 | tail -n 30` (the `#eval` output goes to stdout, at build
time), or one runner with `lake env lean Test/GordieHoweTest/MLDSAVectorsSign.lean`.
Vector data was produced by `Test/scripts/gen_vectors.py`; see that script's docstring to
regenerate.
-/
import GordieHoweTest.MLDSAVectorsVerify
import GordieHoweTest.MLDSAVectorsKeyGen
import GordieHoweTest.MLDSAVectorsSign
