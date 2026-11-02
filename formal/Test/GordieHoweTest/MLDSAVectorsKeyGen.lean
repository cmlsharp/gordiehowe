-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Runs the known-answer check of `keyGenFromSeed` against OpenSSL (see `MLDSAVectors.lean`); a
failed check fails the build.

Not a `module`: see `MLDSAVectors.lean`'s header on `#eval` in modules.
-/
import GordieHoweTest.KeyGenCheck

namespace GordieHoweTest

#eval requireChecks "MLDSAVectorsKeyGen" do
  let mut allOk := true
  IO.println "(e) keyGenFromSeed at concretePrimitivesKeyGen (ML-DSA-44, 65, 87) vs OpenSSL \
    3.6.4 pk and sk bytes, seeds (j, 0, ..., 0) for j = 0, 1, 2:"
  let ok ← checkKeyGen
  IO.println (if ok then "PASS KeyGen" else "FAIL KeyGen (see above)")
  allOk := allOk && ok
  return allOk

end GordieHoweTest
