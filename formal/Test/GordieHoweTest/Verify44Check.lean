-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. End-to-end known-answer test for `MLDSA.Concrete.verify44`
(`MLDSA.fipsVerify` closed over the concrete ML-DSA-44 primitives), against the OpenSSL
3.6.4-signed example fixture `GetMlDsa44BenchmarkExample()` /
`lib/circuits/tests/pq/ml_dsa/ml_dsa_44_benchmark.inc`: a real `(message, public key,
context, signature)` tuple, not a synthetic circuit-only fixture. The public key and
signature are byte arrays decoded here with the vendored `MLDSA.Concrete.pkDecode` /
`MLDSA.Concrete.sigDecode` (FIPS 204 Algorithms 23 and 27), so this exercises the encoding
layer along with `expandA`, `sampleInBall`, the hash primitives, and `fipsVerify` itself, all
at once.

`MLDSA.fipsVerify`'s `msg` parameter is Algorithm 8's already-preprocessed `M'`, not the raw
message (see `GordieHoweTest.preprocessMessage`'s docstring); the context here is empty, so
`M' = 0x00 ‖ 0x00 ‖ message`.

Compiled code runs the NTT through the loop kernels `loopNTT`, `loopInvNTT` and
`loopMultiplyNTTs` (`@[implemented_by]` in `Vendor/LatticeCrypto/MLDSA/Concrete/NTT.lean`);
`GordieHowe.MLDSA44.NTTLoop.ntt_eq_loopNTT`, `invNTT_eq_loopInvNTT` and
`multiplyNTTs_eq_loopMultiplyNTTs` prove them equal to the structural definitions that the
proofs use, so this check tests the same `verify44`.

A second check flips one byte of the message before preprocessing and checks that
`verify44` then returns `false` (the commitment hash recomputation fails since `μ` changes).

A third check runs the checks of the relation of the proofs of possession on the fixture: it
decides `GordieHowe.MLDSA44.ExpandAWithin` at the key (`expandAWithinB`) and evaluates
`GordieHowe.MLDSA44.verifyChecks` at the vendored `expandA(ρ)`. Where `ExpandAWithin` holds that
matrix is `expandABounded(ρ)` (`GordieHowe.MLDSA44.expandA_eq_expandABounded`), the matrix the
relation reads (`GordieHowe.MLDSA44.expandABounded_eq_expandAFull`).

Exposes `checkVerify44 : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectors.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.Benchmark44
import GordieHowe.Applications.MLDSA44.Spec.Basic
import GordieHowe.Applications.MLDSA44.Spec.ExpandA

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

private def bench44PublicKey : PublicKey mldsa44 (concretePrimitives mldsa44) :=
  let (rho, t1) := pkDecode mldsa44 (hexToBytes bench44PkHex)
  ⟨rho, t1⟩

private def bench44Signature : Option (FIPSSignature mldsa44 (concretePrimitives mldsa44)) :=
  match sigDecode mldsa44 (hexToBytes bench44SigHex) with
  | some (cTilde, z, h) => some ⟨cTilde, z, h⟩
  | none => none

/-- Check `verify44` accepts the benchmark fixture, and rejects it once the message is
tampered with (first byte flipped). -/
def checkVerify44 : IO Bool := do
  let msg := hexToByteList bench44MsgHex
  let ctx := hexToByteList bench44CtxHex
  match bench44Signature with
  | none =>
    IO.println "FAIL Verify44: sigDecode rejected the benchmark signature bytes"
    return false
  | some sig =>
    let mPrime := preprocessMessage msg ctx
    let acceptResult := verify44 bench44PublicKey mPrime sig
    let mut ok := true
    if acceptResult then
      IO.println "  ok: Verify44 positive (verify44 pk M' sig = true)"
    else
      ok := false
      IO.println "FAIL Verify44 positive: verify44 pk M' sig = false, expected true"
    if GordieHowe.MLDSA44.expandAWithinB mldsa44 bench44PublicKey.rho &&
        GordieHowe.MLDSA44.verifyChecks (expandA mldsa44 bench44PublicKey.rho)
          bench44PublicKey mPrime sig then
      IO.println "  ok: Verify44 relation checks (ExpandAWithin, verifyChecks)"
    else
      ok := false
      IO.println "FAIL Verify44 relation checks: ExpandAWithin or verifyChecks rejected the \
        fixture"
    -- Negative check: flip the first message byte.
    match msg with
    | [] =>
      IO.println "FAIL Verify44 negative: benchmark message is empty, cannot flip a byte"
      return false
    | b0 :: rest =>
      let flippedMsg := (b0 ^^^ 0xFF) :: rest
      let mPrimeFlipped := preprocessMessage flippedMsg ctx
      let rejectResult := verify44 bench44PublicKey mPrimeFlipped sig
      if rejectResult then
        ok := false
        IO.println "FAIL Verify44 negative: verify44 accepted a signature over a tampered \
          message (expected false)"
      else
        IO.println "  ok: Verify44 negative (flipped message byte correctly rejected)"
    return ok

end GordieHoweTest
