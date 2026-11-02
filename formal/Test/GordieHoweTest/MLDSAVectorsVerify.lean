-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Runs the known-answer checks of `ExpandA`, `SampleInBall`, `verify44` and `verify65` (see
`MLDSAVectors.lean`); a failed check fails the build.

Not a `module`: see `MLDSAVectors.lean`'s header on `#eval` in modules.
-/
import GordieHoweTest.ExpandA44Check
import GordieHoweTest.SampleInBall44Check
import GordieHoweTest.Verify44Check
import GordieHoweTest.ExpandA65Check
import GordieHoweTest.Verify65Check

namespace GordieHoweTest

#eval requireChecks "MLDSAVectorsVerify" do
  let mut allOk := true
  IO.println "(a) ExpandA (ML-DSA-44) vs kExpectedExpandAVectors[4][4][256]:"
  let ok ← checkExpandA44
  IO.println (if ok then "PASS ExpandA44" else "FAIL ExpandA44 (see above)")
  allOk := allOk && ok
  IO.println "(b) SampleInBall (ML-DSA-44) vs the 10 GetSampleInBallTests() vectors:"
  let ok ← checkSampleInBall44
  IO.println (if ok then "PASS SampleInBall44" else "FAIL SampleInBall44 (see above)")
  allOk := allOk && ok
  IO.println "(c) verify44 vs the ML-DSA-44 benchmark (message, pk, ctx, sig) fixture, \
    positive and negative (flipped message byte):"
  let ok ← checkVerify44
  IO.println (if ok then "PASS Verify44" else "FAIL Verify44 (see above)")
  allOk := allOk && ok
  IO.println "(d) ExpandA (ML-DSA-65) vs kExpectedExpandAVectors[6][5][256]:"
  let ok ← checkExpandA65
  IO.println (if ok then "PASS ExpandA65" else "FAIL ExpandA65 (see above)")
  allOk := allOk && ok
  IO.println "(d) verify65 vs the first GetMlDsa65Examples() (message, pk, ctx, sig) fixture, \
    positive and negative (flipped message byte):"
  let ok ← checkVerify65
  IO.println (if ok then "PASS Verify65" else "FAIL Verify65 (see above)")
  allOk := allOk && ok
  return allOk

end GordieHoweTest
