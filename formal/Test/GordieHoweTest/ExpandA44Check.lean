-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. Known-answer test for `MLDSA.Concrete.expandA` at ML-DSA-44,
against `kExpectedExpandAVectors` from
`third_party/longfellow/lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test_vectors.inc` (read via the
C++ reference test `MlDsaRefTest.ExpandA`, which calls
`ExpandA<MLDsa44Params>(ExpandASeed())` and compares every coefficient, in NTT domain,
against the table). The C++ reference builds `Â[r][s]` as an NTT-domain polynomial directly
via rejection sampling (no separate NTT step), and so does the vendored `expandAPoly`; the
raw table entries are therefore compared directly against `Tq` coefficients, no transform
needed on either side.

The relation of the proofs of possession reads `ExpandA` through `GordieHowe.MLDSA44.ExpandAWithin`
and `GordieHowe.MLDSA44.expandABounded` (`GordieHowe/Applications/MLDSA44/Spec/ExpandA.lean`). The
check also evaluates `GordieHowe.MLDSA44.expandAWithinB`, which decides `ExpandAWithin`
(`expandAWithinB_iff`), at the seed. Where `ExpandAWithin` holds,
`GordieHowe.MLDSA44.expandA_eq_expandABounded` proves the vendored `expandA` equal to
`expandABounded`, so the table tests `expandABounded` too.

Exposes `checkExpandA44 : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectors.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.ExpandA44
import GordieHowe.Applications.MLDSA44.Spec.ExpandA

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

/-- Check `expandA mldsa44` against `kExpectedExpandAVectors` at the fixed reference seed, and
decide `ExpandAWithin` there (`expandAWithinB`). -/
def checkExpandA44 : IO Bool := do
  let rho : Bytes 32 := byteArrayToVector (hexToBytes expandASeed44Hex) 0 32
  let a := expandA mldsa44 rho
  let mut ok := true
  if GordieHowe.MLDSA44.expandAWithinB mldsa44 rho then
    IO.println "  ok: ExpandAWithin holds at the seed"
  else
    ok := false
    IO.println "FAIL ExpandA44: ExpandAWithin fails at the seed"
  for r in List.finRange 4 do
    for s in List.finRange 4 do
      -- expandA44Expected is flattened row-major (r, s, i), stride 256 per (r, s) pair.
      let base := (r.val * 4 + s.val) * 256
      let expected := tqOfNats (expandA44Expected.extract base (base + 256))
      let got := (a.get r).get s
      if got ≠ expected then
        ok := false
        IO.println s!"FAIL ExpandA44: mismatch at r={r} s={s}"
  return ok

end GordieHoweTest
