-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. Known-answer test for `MLDSA.Concrete.expandA` at ML-DSA-65,
against the ML-DSA-65 `kExpectedExpandAVectors` of the C++ reference tests, at the fixed reference seed
`ExpandASeed()` used by `MlDsaRefTest<MLDsa65Params>.ExpandA` (bytes `0..31`). See
`ExpandA44Check.lean` for why the raw table entries compare directly against `Tq`
coefficients (both sides build `Â` in NTT domain via rejection sampling, no separate NTT
step).

Exposes `checkExpandA65 : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectors.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.ExpandA65

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

/-- Check `expandA mldsa65` against `kExpectedExpandAVectors` at the fixed reference seed. -/
def checkExpandA65 : IO Bool := do
  let rho : Bytes 32 := byteArrayToVector (hexToBytes expandASeed65Hex) 0 32
  let a := expandA mldsa65 rho
  let mut ok := true
  for r in List.finRange 6 do
    for s in List.finRange 5 do
      -- expandA65Expected is flattened row-major (r, s, i), stride 256 per (r, s) pair.
      let base := (r.val * 5 + s.val) * 256
      let expected := tqOfNats (expandA65Expected.extract base (base + 256))
      let got := (a.get r).get s
      if got ≠ expected then
        ok := false
        IO.println s!"FAIL ExpandA65: mismatch at r={r} s={s}"
  return ok

end GordieHoweTest
