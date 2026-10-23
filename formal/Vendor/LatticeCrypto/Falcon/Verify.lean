/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao

Vendored from VCVio LatticeCrypto/Falcon/Scheme.lean at commit
eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79.
adapted: this file is not a verbatim copy of `Scheme.lean`. `Scheme.lean`'s
`verify` (copied verbatim below) is stated against `Falcon.Primitives`, a
structure that also carries the signing-side `samplerZ : ℝ → ℝ → ProbComp ℤ`
field and the `ffSampling`/`FalconTree`/discrete-Gaussian machinery, none of
which `verify` uses; that structure and its surrounding file
(`LatticeCrypto/Falcon/Primitives.lean`) are monadic (`ProbComp` is
`OracleComp unifSpec`) and depend on `VCVio.OracleComp` and on
`LatticeCrypto.DiscreteGaussian`'s real-analysis development, so they are not
vendored here. In its place this file declares `VerifyPrimitives`, a new
structure holding exactly the three fields `verify` reads off `Primitives`
(`publicKeyBytes`, `hashToPoint`, `decompress`) plus the `hashToPointForPublicKey`
helper specialized to it. `PublicKey`, `Signature`, and `verify` are copied
verbatim from `Scheme.lean` with `Primitives p` replaced by `VerifyPrimitives p`
throughout, with one change: `hashToPoint` returns `Option`, `none` when its bounded
rejection-sampling loop runs out of candidates, and `verify` then rejects.
-/

module
public import LatticeCrypto.Falcon.Arithmetic

/-!
# Falcon Verification (Algorithm 16)

The pure, executable subset of the Falcon signature scheme needed to state and
run `Falcon.verify`: the public key and signature formats, and `verify` itself.

## References

- Falcon specification v1.2, Algorithm 16
- FIPS 206 (FN-DSA) draft
-/

@[expose] public section


namespace Falcon

variable (p : Params)

/-- The primitive algorithms `Falcon.verify` needs: hashing a salted message to a point
in `R_q`, keyed by the public-key bytes, and decompressing a signature's `s₂` payload. -/
structure VerifyPrimitives where
  /-- External verification-key bytes used by the raw-message FN-DSA hash-to-point path. -/
  publicKeyBytes : Rq p.n → ByteArray
  /-- `HashToPoint(nonce, vrfy_key, message, q, n)` (FIPS 206, raw-message mode), or `none` if a
  bounded implementation of its rejection loop runs out of candidates. -/
  hashToPoint : Bytes 40 → ByteArray → List Byte → Option (Rq p.n)
  /-- `Decompress(bytes, sbytelen, n)` (Algorithm 18). -/
  decompress : List Byte → ℕ → Option (IntPoly p.n)

/-- Hash a message using the verification-key bytes derived from `pk`. -/
@[inline] def VerifyPrimitives.hashToPointForPublicKey {p : Params} (prims : VerifyPrimitives p)
    (pk : Rq p.n) (salt : Bytes 40) (msg : List Byte) : Option (Rq p.n) :=
  prims.hashToPoint salt (prims.publicKeyBytes pk) msg

/-- The Falcon public key: a single polynomial `h ∈ R_q` where `h = g · f⁻¹ mod q`. -/
structure PublicKey where
  h : Rq p.n

/-- A Falcon signature: a 40-byte random salt `r` paired with the compressed
representation of the short polynomial `s₂`. -/
structure Signature where
  salt : Bytes 40
  compressedS2 : List Byte

variable (prims : VerifyPrimitives p)

/-- Falcon verification (Algorithm 16).

Given `(pk, message, signature)`:
1. Decompress `s₂` from the signature.
2. Recompute `c = HashToPoint(r, pk, message)`; reject if the hash runs out of candidates.
3. Compute `s₁ = c - s₂ · h mod q`.
4. Accept iff `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. -/
def verify (pk : PublicKey p) (msg : List Byte) (sig : Signature) : Bool :=
  match prims.decompress sig.compressedS2 p.sbytelen with
  | none => false
  | some s2Int =>
    match prims.hashToPointForPublicKey pk.h sig.salt msg with
    | none => false
    | some c =>
    let s2 := IntPoly.toRq s2Int
    let s1 := c - negacyclicMul s2 pk.h
    decide (pairL2NormSq s1 s2 ≤ p.betaSquared)

end Falcon
