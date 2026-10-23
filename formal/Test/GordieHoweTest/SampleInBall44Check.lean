-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. Known-answer test for `MLDSA.Concrete.sampleInBallPoly` at
ML-DSA-44, against the ten vectors in `GetSampleInBallTests()` /
`kNumSampleInBallTests = 10` from `third_party/longfellow/lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test_vectors.inc`,
exercised by the C++ reference test `MlDsaRefTest<MLDsa44Params>.SampleInBall`. Each test's
32-byte `in` is fed to `SampleInBall`; the expected `out` is 256 coefficients already reduced
mod `q` (so `0`, `1`, or `q - 1` for `-1`), matching `Coeff := ZMod modulus`'s canonical
representatives directly.

Exposes `checkSampleInBall44 : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectors.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.SampleInBall44

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

/-- Check `sampleInBallPoly mldsa44` against the ten `GetSampleInBallTests()` vectors. -/
def checkSampleInBall44 : IO Bool := do
  let mut ok := true
  for idx in [0:sampleInBall44Tests.size] do
    let (inHex, expectedOut) := sampleInBall44Tests[idx]!
    let cTilde : CommitHashBytes mldsa44 := byteArrayToVector (hexToBytes inHex) 0 32
    let got := sampleInBallPoly mldsa44 cTilde
    let expected := rqOfNats expectedOut
    if got ≠ expected then
      ok := false
      IO.println s!"FAIL SampleInBall44: mismatch at test case {idx}"
  return ok

end GordieHoweTest
