-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.MLDSA.Regularity.SignerRegularity

@[expose] public section

/-!
# The keys of key generation as keys of the regularity argument

The regularity bounds of `Regularity/` are stated at keys `keyOf sk₀ (A s₁)`: the secret key
`sk₀` with `t₀` recomputed from `A s₁ + s₂`, `A = NTT⁻¹(Â)`. Key generation (FIPS 204
Algorithm 6) assembles `idealSecretKey ρ K Â (s₁, s₂)`. The two give the same regularity gap.

* `ringRegGap_congr`: `ringRegGap` reads the secret key only through `s₁`, `s₂` and `t₀`.
* `mul_eq_ofFn_keyMap`: `Â · s₁ = A s₁` as vectors.
* `ringRegGap_idealSecretKey_eq`: with `SampleInBall = G` (`withSampleInBall`,
  `concreteWithSampleInBall`), the gap at `idealSecretKey ρ K Â (s₁, s₂)` equals the gap at
  `keyOf sk₀ (A s₁)` for any `sk₀` with the same `s₁`, `s₂`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **`ringRegGap` reads the key only through `s₁`, `s₂` and `t₀`.** -/
theorem ringRegGap_congr (prims : Primitives p) {sk sk' : SecretKey p} (h1 : sk.s1 = sk'.s1)
    (h2 : sk.s2 = sk'.s2) (h0 : sk.t0 = sk'.t0) (aHat : TqMatrix p.k p.l) (βmin : ℚ≥0) :
    ringRegGap prims sk aHat βmin = ringRegGap prims sk' aHat βmin := by
  obtain ⟨r, k, tr, s1, s2, t0⟩ := sk
  obtain ⟨r', k', tr', s1', s2', t0'⟩ := sk'
  dsimp only at h1 h2 h0
  subst h1 h2 h0
  rfl

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- `Â · s₁ = A s₁` with `A = NTT⁻¹(Â)`, as a vector. -/
theorem mul_eq_ofFn_keyMap {k l : ℕ} (aHat : TqMatrix k l) (s : RqVec l) :
    aHat * s = Vector.ofFn (keyMap (fun b => s.get b) (matOfHat aHat)) := by
  have := concreteNTTRingLaws
  apply (rqVecCoeffEquiv k).injective
  change rqVecCoeffs (aHat * s) = rqVecCoeffs _
  rw [rqVecCoeffs_mul_eq_matAct]
  funext ic
  rw [rqVecCoeffs_apply, Vector.get_ofFn]
  rfl

/-- **The gap at the key of FIPS 204 Algorithm 6 is the gap of the regularity argument**: with
`SampleInBall = G`, at `idealSecretKey ρ K Â (s₁, s₂)` and at `keyOf sk₀ (A s₁)` for any `sk₀`
with the same `s₁, s₂`. -/
theorem ringRegGap_idealSecretKey_eq (G : CommitHashBytes p → ChallengePoly)
    (rho key : _root_.MLDSA.Bytes 32) (aHat : TqMatrix p.k p.l) (s : RqVec p.l × RqVec p.k)
    (sk₀ : SecretKey p) (h1 : sk₀.s1 = s.1) (h2 : sk₀.s2 = s.2) (βmin : ℚ≥0) :
    ringRegGap (withSampleInBall (concretePrimitivesKeyGen p) G)
        (idealSecretKey (withSampleInBall (concretePrimitivesKeyGen p) G) rho key aHat s) aHat
        βmin =
      ringRegGap (concreteWithSampleInBall p G)
        (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))) aHat βmin := by
  refine ringRegGap_congr (withSampleInBall (concretePrimitivesKeyGen p) G) h1.symm h2.symm ?_
    aHat βmin
  change ((concretePrimitives p).power2RoundVec (aHat * s.1 + s.2)).2 =
    ((concretePrimitives p).power2RoundVec (Vector.ofFn _ + sk₀.s2)).2
  rw [h1, h2, mul_eq_ofFn_keyMap]

end GordieHowe.Ring.MLDSAW1
