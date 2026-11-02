-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

/-
Known-answer test for `MLDSA.keyGenFromSeed` at `GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen`
(the vendored concrete primitives with the FIPS 204 `ExpandS` of
`GordieHowe/Applications/MLDSA/Spec/ExpandS.lean`) and the concrete NTT, at ML-DSA-44, 65 and
87: `pkEncode` and `skEncode` of the generated key against OpenSSL 3.6.4's public and private
key bytes for the seeds `ξ = (j, 0, …, 0)`, `j = 0, 1, 2`
(`Test/GordieHoweTest/Data/KeyGenOpenSSL.lean`).
The public key checks `ExpandA`, `ExpandS`, the matrix product and `Power2Round`'s `t₁`; the
secret key checks `ExpandS` directly (`s₁`, `s₂`), `t₀`, `K` and `tr`.

Exposes `checkKeyGen : IO Bool`, run from `Test/GordieHoweTest/MLDSAVectorsKeyGen.lean`'s `#eval`.
-/
import LatticeCrypto.MLDSA.ConcretePrimitives
import GordieHoweTest.Hex
import GordieHoweTest.Data.KeyGenOpenSSL
import GordieHowe.Applications.MLDSA.Spec.ExpandS

namespace GordieHoweTest

open MLDSA MLDSA.Concrete

attribute [local instance] concreteNTTRingOps

/-- The seed `ξ = (j, 0, …, 0)`. -/
def keyGenSeed (j : ℕ) : Bytes 32 :=
  Vector.ofFn fun i : Fin 32 => if i.val = 0 then j.toUInt8 else 0

/-- `pkEncode` and `skEncode` of `keyGenFromSeed` at `concretePrimitivesKeyGen p` and seed
`ξ = (j, 0, …, 0)`. -/
def keyGenEncodings (p : Params) (j : ℕ) : ByteArray × ByteArray :=
  let (pk, sk) := keyGenFromSeed p (GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen p) (keyGenSeed j)
  (pkEncode p pk.rho pk.t1, skEncode p sk.rho sk.key sk.tr sk.s1 sk.s2 sk.t0)

/-- Compare one generated key against the OpenSSL bytes. -/
def checkKeyGenOne (label : String) (p : Params) (j : ℕ) (pkHex skHex : String) : IO Bool := do
  let (pk, sk) := keyGenEncodings p j
  let okPk := pk.data == (hexToBytes pkHex).data
  let okSk := sk.data == (hexToBytes skHex).data
  IO.println s!"  {label} seed {j}: pk {if okPk then "ok" else "MISMATCH"} ({pk.size} bytes), \
    sk {if okSk then "ok" else "MISMATCH"} ({sk.size} bytes)"
  return okPk && okSk

/-- Check all nine keys. -/
def checkKeyGen : IO Bool := do
  let r ← [ checkKeyGenOne "ML-DSA-44" mldsa44 0 keyGen44Seed0PkHex keyGen44Seed0SkHex,
    checkKeyGenOne "ML-DSA-44" mldsa44 1 keyGen44Seed1PkHex keyGen44Seed1SkHex,
    checkKeyGenOne "ML-DSA-44" mldsa44 2 keyGen44Seed2PkHex keyGen44Seed2SkHex,
    checkKeyGenOne "ML-DSA-65" mldsa65 0 keyGen65Seed0PkHex keyGen65Seed0SkHex,
    checkKeyGenOne "ML-DSA-65" mldsa65 1 keyGen65Seed1PkHex keyGen65Seed1SkHex,
    checkKeyGenOne "ML-DSA-65" mldsa65 2 keyGen65Seed2PkHex keyGen65Seed2SkHex,
    checkKeyGenOne "ML-DSA-87" mldsa87 0 keyGen87Seed0PkHex keyGen87Seed0SkHex,
    checkKeyGenOne "ML-DSA-87" mldsa87 1 keyGen87Seed1PkHex keyGen87Seed1SkHex,
    checkKeyGenOne "ML-DSA-87" mldsa87 2 keyGen87Seed2PkHex keyGen87Seed2SkHex ].mapM id
  return r.all id

end GordieHoweTest
