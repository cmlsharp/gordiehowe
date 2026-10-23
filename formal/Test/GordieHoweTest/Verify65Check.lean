-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
New file: not from VCVio. End-to-end known-answer test for `MLDSA.Concrete.verify65`, against
the first entry of `GetMlDsa65Examples()` of the C++ tests: a real ML-DSA-65
`(message, public key, context, signature)` tuple with a non-empty 9-byte context, decoded
with the vendored `MLDSA.Concrete.pkDecode` / `MLDSA.Concrete.sigDecode`. See
`Verify44Check.lean` for why the message must be preprocessed with `GordieHoweTest.preprocessMessage`
before being passed to `verify65`.

Exposes `checkVerify65 : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectors.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.Example65

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

private def example65PublicKey : PublicKey mldsa65 (concretePrimitives mldsa65) :=
  let (rho, t1) := pkDecode mldsa65 (hexToBytes example65PkHex)
  ⟨rho, t1⟩

private def example65Signature : Option (FIPSSignature mldsa65 (concretePrimitives mldsa65)) :=
  match sigDecode mldsa65 (hexToBytes example65SigHex) with
  | some (cTilde, z, h) => some ⟨cTilde, z, h⟩
  | none => none

/-- Check `verify65` accepts the first `GetMlDsa65Examples()` fixture, and rejects it once the
message is tampered with (first byte flipped). -/
def checkVerify65 : IO Bool := do
  let msg := hexToByteList example65MsgHex
  let ctx := hexToByteList example65CtxHex
  match example65Signature with
  | none =>
    IO.println "FAIL Verify65: sigDecode rejected the example signature bytes"
    return false
  | some sig =>
    let mPrime := preprocessMessage msg ctx
    let acceptResult := verify65 example65PublicKey mPrime sig
    let mut ok := true
    if acceptResult then
      IO.println "  ok: Verify65 positive (verify65 pk M' sig = true)"
    else
      ok := false
      IO.println "FAIL Verify65 positive: verify65 pk M' sig = false, expected true"
    match msg with
    | [] =>
      IO.println "FAIL Verify65 negative: example message is empty, cannot flip a byte"
      return false
    | b0 :: rest =>
      let flippedMsg := (b0 ^^^ 0xFF) :: rest
      let mPrimeFlipped := preprocessMessage flippedMsg ctx
      let rejectResult := verify65 example65PublicKey mPrimeFlipped sig
      if rejectResult then
        ok := false
        IO.println "FAIL Verify65 negative: verify65 accepted a signature over a tampered \
          message (expected false)"
      else
        IO.println "  ok: Verify65 negative (flipped message byte correctly rejected)"
    return ok

end GordieHoweTest
