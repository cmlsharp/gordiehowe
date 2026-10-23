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

This file's own top-level `#eval` (below) is why it uses a plain `import`, not `module` /
`public import`: see `Vendor/README.md`'s "Lake / module-system notes" for why a `module`
file's top-level `#eval` fails to find the native implementation of an imported declaration.

Run with `lake build GordieHoweTest 2>&1 | tail -n 30` (the `#eval` output goes to stdout, at build
time), or interactively with `lake env lean --run Test/GordieHoweTest/MLDSAVectors.lean`. Vector data
was produced by `Test/scripts/gen_vectors.py`; see that script's docstring to regenerate.
-/
import GordieHoweTest.ExpandA44Check
import GordieHoweTest.SampleInBall44Check
import GordieHoweTest.Verify44Check
import GordieHoweTest.ExpandA65Check
import GordieHoweTest.Verify65Check

namespace GordieHoweTest

def runAllChecks : IO Unit := do
  let mut allOk := true

  IO.println "(a) ExpandA (ML-DSA-44) vs kExpectedExpandAVectors[4][4][256]:"
  let okA ← checkExpandA44
  IO.println (if okA then "PASS ExpandA44" else "FAIL ExpandA44 (see mismatches above)")
  allOk := allOk && okA
  IO.println ""

  IO.println "(b) SampleInBall (ML-DSA-44) vs the 10 GetSampleInBallTests() vectors:"
  let okB ← checkSampleInBall44
  IO.println (if okB then "PASS SampleInBall44" else "FAIL SampleInBall44 (see mismatches above)")
  allOk := allOk && okB
  IO.println ""

  IO.println "(c) verify44 vs the ML-DSA-44 benchmark (message, pk, ctx, sig) fixture, \
    positive and negative (flipped message byte):"
  let okC ← checkVerify44
  IO.println (if okC then "PASS Verify44" else "FAIL Verify44 (see above)")
  allOk := allOk && okC
  IO.println ""

  IO.println "(d) ExpandA (ML-DSA-65) vs kExpectedExpandAVectors[6][5][256]:"
  let okD ← checkExpandA65
  IO.println (if okD then "PASS ExpandA65" else "FAIL ExpandA65 (see mismatches above)")
  allOk := allOk && okD
  IO.println ""

  IO.println "(d) verify65 vs the first GetMlDsa65Examples() (message, pk, ctx, sig) fixture, \
    positive and negative (flipped message byte):"
  let okE ← checkVerify65
  IO.println (if okE then "PASS Verify65" else "FAIL Verify65 (see above)")
  allOk := allOk && okE
  IO.println ""

  IO.println "(e) Falcon hashToPoint / verify512: SKIPPED, no known-answer vectors exist \
    in the C++ Falcon tests (see this file's header)."
  IO.println ""

  IO.println (if allOk then "ALL CHECKS PASSED" else "SOME CHECKS FAILED (see above)")

#eval runAllChecks

end GordieHoweTest
