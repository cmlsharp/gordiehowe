-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Known-answer test for deterministic FIPS 204 signing at
`GordieHowe.MLDSA.Spec.concretePrimitivesFIPS` (the vendored concrete primitives with the
FIPS 204 `ExpandS` and `ExpandMask` of `GordieHowe/Applications/MLDSA/Spec/ExpandS.lean` and
`ExpandMask.lean`) and the concrete NTT, at ML-DSA-44, 65 and 87: `sigEncode` of the signature of
the message bytes `00..1f` (empty context) under the key of seed `ξ = (j, 0, …, 0)`, `j = 0, 1, 2`,
with `rnd = 0^32` (FIPS 204 Algorithm 2, deterministic variant), against OpenSSL 3.6.4's
deterministic signatures (`Test/GordieHoweTest/Data/SignOpenSSL.lean`).

The signature is FIPS 204 Algorithm 7: `μ = H(tr ‖ M′, 64)`, `ρ'' = H(K ‖ rnd ‖ μ, 64)`, and the
vendored `MLDSA.fipsSignLoop` over the counters `κ = 0, ℓ, 2ℓ, …`. The accepted attempt's
`z = y + c·s₁` contains the whole mask `y = ExpandMask(ρ'', κ)`, so a byte-equal signature checks
`ExpandMask` at that counter, along with `ExpandA`, `ExpandS`, `SampleInBall`, the rounding and
hint functions, and the encodings.

Exposes `checkSign : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectorsSign.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.Signature
import GordieHoweTest.Hex
import GordieHoweTest.KeyGenCheck
import GordieHoweTest.Data.SignOpenSSL
import GordieHowe.Applications.MLDSA.Spec.ExpandMask

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

attribute [local instance] concreteNTTRingOps

/-- The number of signing attempts tried before giving up. -/
def signMaxAttempts : ℕ := 1000

/-- The deterministic signature (`rnd = 0^32`) of the message bytes `00..1f` with empty context
under the key of seed `ξ = (j, 0, …, 0)`, at `concretePrimitivesFIPS p`, encoded by `sigEncode`,
with the index of the accepted attempt. -/
def signEncoding (p : Params) (j : ℕ) : Option (ByteArray × ℕ) :=
  let P := GordieHowe.MLDSA.Spec.concretePrimitivesFIPS p
  let (pk, sk) := keyGenFromSeed p P (keyGenSeed j)
  let msg := preprocessMessage ((List.range 32).map Nat.toUInt8) []
  let mu := P.hashMessage sk.tr msg
  let rnd : Bytes 32 := Vector.replicate 32 0
  let rhoDoublePrime := P.hashPrivateSeed sk.key rnd mu
  let aHat := P.expandA pk.rho
  (List.range signMaxAttempts).findSome? fun i =>
    (fipsSignAttempt p P sk aHat mu rhoDoublePrime (i * p.l)).map fun sig =>
      (sigEncode p sig.cTilde sig.z sig.h, i)

/-- Compare one deterministic signature against the OpenSSL bytes. -/
def checkSignOne (label : String) (p : Params) (j : ℕ) (sigHex : String) : IO Bool := do
  match signEncoding p j with
  | none =>
    IO.println s!"  {label} seed {j}: MISMATCH (no attempt accepted)"
    return false
  | some (sig, i) =>
    let ok := sig.data == (hexToBytes sigHex).data
    IO.println s!"  {label} seed {j}: sig {if ok then "ok" else "MISMATCH"} ({sig.size} bytes, \
      accepted at attempt {i}, κ = {i * p.l})"
    return ok

/-- Check all nine signatures. -/
def checkSign : IO Bool := do
  let r ← [ checkSignOne "ML-DSA-44" mldsa44 0 sign44Seed0SigHex,
    checkSignOne "ML-DSA-44" mldsa44 1 sign44Seed1SigHex,
    checkSignOne "ML-DSA-44" mldsa44 2 sign44Seed2SigHex,
    checkSignOne "ML-DSA-65" mldsa65 0 sign65Seed0SigHex,
    checkSignOne "ML-DSA-65" mldsa65 1 sign65Seed1SigHex,
    checkSignOne "ML-DSA-65" mldsa65 2 sign65Seed2SigHex,
    checkSignOne "ML-DSA-87" mldsa87 0 sign87Seed0SigHex,
    checkSignOne "ML-DSA-87" mldsa87 1 sign87Seed1SigHex,
    checkSignOne "ML-DSA-87" mldsa87 2 sign87Seed2SigHex ].mapM id
  return r.all id

end GordieHoweTest
