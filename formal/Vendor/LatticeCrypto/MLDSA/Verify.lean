/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao

Vendored from VCVio LatticeCrypto/MLDSA/Scheme.lean and
LatticeCrypto/MLDSA/Signature.lean at commit
eb0f6e456a8dffee6a0ba8a2f66ca2a5b50dfd79.
adapted: this file is not a verbatim copy of a single VCVio source file. It
collects the pure, non-monadic declarations that `fipsVerify` depends on out
of `Scheme.lean` (the `PublicKey` structure, `computeWApprox`) and
`Signature.lean` (the `FIPSSignature` structure, `fipsVerify` itself), leaving
out `SecretKey`, `SigningState`, `Commitment`, `Response`, `validKeyPair`,
`identificationScheme`, `keyGenFromSeed`, the monadic `fipsSign`/`fipsKeyGen`,
and every correctness theorem about signing, none of which `fipsVerify` needs.
Declarations below are copied verbatim from their source files except for
this note.
-/

module
public import LatticeCrypto.MLDSA.Primitives

/-!
# ML-DSA FIPS 204 Verification (Algorithm 3 / Algorithm 8)

The pure, executable subset of the FIPS 204 signature algorithms needed to
state and run `ML-DSA.Verify`: the public key, the FIPS signature format, the
approximate-commitment reconstruction `computeWApprox`, and `fipsVerify`
itself.

## References

- NIST FIPS 204, Algorithm 3 (outer API) and Algorithm 8 (internal algorithm)
-/

@[expose] public section


open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p)

section Scheme

variable [nttOps : NTTRingOps]

/-- The semantic public key: the public seed `ρ` and the power-2 rounded key vector `t₁`. -/
structure PublicKey where
  rho : Bytes 32
  t1 : Vector prims.Power2High p.k

/-- Compute `w'_Approx = NTT⁻¹(Â · NTT(z) - NTT(c) · NTT(t₁ · 2^d))` (Algorithm 8, line 9). -/
def computeWApprox (aHat : TqMatrix p.k p.l) (c : ChallengePoly) (z : RqVec p.l)
    (t1 : Vector prims.Power2High p.k) : RqVec p.k :=
  let cHat := nttOps.toHat c
  let zHat := nttOps.hatVec z
  let t1Shifted := prims.power2RoundShiftVec t1
  let t1ShiftedHat := nttOps.hatVec t1Shifted
  let azHat := nttOps.matVecMul aHat zHat
  let ct1Hat := nttOps.scalarVecMul cHat t1ShiftedHat
  nttOps.unhatVec (azHat - ct1Hat)

/-- The FIPS 204 signature format: `(c̃, z, h)`. -/
structure FIPSSignature where
  cTilde : CommitHashBytes p
  z : RqVec p.l
  h : Vector prims.Hint p.k

/-- ML-DSA.Verify (Algorithm 3 / Algorithm 8): verify a signature.

1. Expand `Â = ExpandA(ρ)` from the public key
2. Compute `tr = H(pk)`, `μ = H(tr ‖ M')`
3. Derive `c = SampleInBall(c̃)` and compute `w'_Approx = Az - c·(t₁·2^d)`
4. Apply hint: `w₁' = UseHint(h, w'_Approx)`
5. Recompute `c̃' = H(μ ‖ w1Encode(w₁'))`
6. Accept iff `‖z‖∞ < γ₁ - β`, `c̃' = c̃`, and `hintWeight(h) ≤ ω` -/
def fipsVerify (pk : PublicKey p prims) (msg : List Byte)
    (sig : FIPSSignature p prims) : Bool :=
  let aHat := prims.expandA pk.rho
  let tr := prims.hashPublicKey pk.rho pk.t1
  let mu := prims.hashMessage tr msg
  let c := prims.sampleInBall sig.cTilde
  let wApprox := computeWApprox p prims aHat c sig.z pk.t1
  let w1' := prims.useHintVec sig.h wApprox
  let cTildeRecomputed := prims.hashCommitment mu (prims.w1Encode w1')
  decide (polyVecNorm sig.z < p.gamma1 - p.beta) &&
  decide (cTildeRecomputed = sig.cTilde) &&
  decide (prims.hintWeight sig.h ≤ p.omega)

end Scheme

end MLDSA
