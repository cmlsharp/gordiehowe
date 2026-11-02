-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Runs the known-answer check of deterministic signing against OpenSSL (see `MLDSAVectors.lean`); a
failed check fails the build.

Not a `module`: see `MLDSAVectors.lean`'s header on `#eval` in modules.
-/
import GordieHoweTest.SignCheck

namespace GordieHoweTest

#eval requireChecks "MLDSAVectorsSign" do
  let mut allOk := true
  IO.println "(f) deterministic signing at concretePrimitivesFIPS (ML-DSA-44, 65, 87) vs \
    OpenSSL 3.6.4 deterministic signatures, seeds (j, 0, ..., 0) for j = 0, 1, 2, message 00..1f:"
  let ok ← checkSign
  IO.println (if ok then "PASS Sign" else "FAIL Sign (see above)")
  allOk := allOk && ok
  return allOk

end GordieHoweTest
