-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1IdealDist
public import GordieHowe.Applications.MLDSA.Signing.KeyFree

@[expose] public section

/-!
# The key-free call of the ML-DSA ring publishing `w₁`

One call of the ring signer (`T` masks, the first accepted at its commitment hash, kept by a coin
on `Fin D` against the flattening weight, `weightedAttemptMasksFin`) as an ideal call
(`idealCall`, `GordieHowe/Applications/MLDSA/Signing/KeyFree.lean`), and the law of the ideal call
at the ring's weights as the law of a key-free call that reads only the signer's published key
`(ρ, t₁, t₀)`.

* `idealCall_eq_weightedAttemptMasksFin`: at masks `ys` and commitment hashes `cs` with
  `H (i, w₁(y_t)) = c̃_t` for every `t`, the ideal call kept with weight
  `κ(w₁, c̃) · otherWeight(w₁)` is `weightedAttemptMasksFin` with the commitment hashes of `H`.
* `idealCallLaw_ring_eq_keyFreeCallLaw`: for an honest key at the position `i` of a ring, the
  ideal call with `T` independent uniform pairs `(y_t, c̃_t)` and a uniform keep coin, kept with
  the signer's flattening coin times the other members' weights, has the law of the key-free call
  of the published key `R_i`, kept with the same weight read from the published `t₀` of `R_i`
  (`t0Weight`, the weight of `keepBit`).
* `idealCallLaw_ring_eq_keyFreeCallLaw_concrete`: the same at the concrete primitives, for every
  seed at every approved parameter set.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature PMF

section Bridge

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The ideal call at the hashes of an oracle is the finite-coin call**: at masks `ys` and
commitment hashes `cs` with `H (i, HighBits(Â·y_t)) = c̃_t` for every `t`, the ideal call kept with
weight `κ(w₁, c̃) · otherWeight(w₁)` is `weightedAttemptMasksFin` with the attempt's checks, the
weight `κ` and the hashes of `H`. -/
theorem idealCall_eq_weightedAttemptMasksFin [Nonempty (MaskBox p)] {T D : ℕ}
    (s : RingWeights ι (BucketVec p) (CommitHashBytes p)) (i : ι) (sk : SecretKey p)
    (aHat : TqMatrix p.k p.l) (κ : BucketVec p × CommitHashBytes p → ℝ≥0∞)
    (H : ι × BucketVec p → CommitHashBytes p) (ys : Fin T → MaskBox p)
    (cs : Fin T → CommitHashBytes p) (hH : ∀ t, H (i, realBuckets aHat (ys t)) = cs t)
    (u : Fin D) :
    idealCall prims sk aHat (fun vc => κ vc * s.otherWeight i H vc.1) (fun t => (ys t, cs t)) u =
      weightedAttemptMasksFin s i (realBuckets aHat) (attemptAccept prims sk aHat) κ
        (fun y c => attemptOutput prims sk aHat (y, c)) H D ys u := by
  have hatt : (fun t => idealAttemptW1 prims sk aHat (ys t, cs t)) = fun t =>
      if attemptAccept prims sk aHat (ys t) (H (i, realBuckets aHat (ys t))) then
        some (realBuckets aHat (ys t), attemptOutput prims sk aHat (ys t, H (i, realBuckets aHat (ys t))))
      else none := by
    funext t
    rw [hH t]
    rfl
  unfold idealCall keptCall weightedAttemptMasksFin
  rw [hatt, List.findSome?_ite_eq_map_find?]
  rcases (List.finRange T).find? _ with _ | t <;> rfl

end Bridge

section Ring

variable {p : Params} [NeZero (bucketCount p)] {prims : Primitives p} [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {N : ℕ}

/-- **The ring call of an honest key has the law of a key-free call of its published key**: for the
key of `seed` with `‖s₁‖∞, ‖s₂‖∞ ≤ η` at the position `i` of the ring `R`, the ideal call (`T`
independent pairs of a uniform mask and a uniform commitment hash, a uniform keep coin on `Fin D`)
kept with the signer's flattening coin `min(1, β_min / aw_i)` times the other members' weights at
`H` has the law of the key-free call of the published key `R_i = (ρ, t₁, t₀)`, kept with the same
weight with `aw_i` the acceptance weight of the published `t₀` (`t0Weight`), given the signing and
verification laws and an encoding coherent with `bucketsOf`. -/
theorem idealCallLaw_ring_eq_keyFreeCallLaw (T D : ℕ) [NeZero D] (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs1 : polyVecBounded (keyGen prims seed).2.s1 p.eta)
    (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hRi : R.1.get i = (keyGen prims seed).1) (βmin : ℚ≥0)
    (H : Fin R.1.length × BucketVec p → CommitHashBytes p) :
    idealCallLaw prims T D (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho)
        (fun vc => flattenCoin prims (keyGen prims seed).2 (Cutoff.const βmin) vc *
          (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i H vc.1) =
      keyFreeCallLaw prims T D (pubPk prims (R.1.get i)) (R.1.get i).2.2
        (fun vc => PMF.flattenKeep (fun a => (t0Weight prims (R.1.get i).2.2 a : ℝ≥0∞)) βmin vc *
          (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i H vc.1) := by
  rw [hRi]
  exact idealCallLaw_flattenCoin_eq T D h_laws hv henc (seed := seed) rfl hs1 hs2 βmin
    fun v => ((ringWeights prims βmin (ringT0s prims R.1)).otherWeight i H v : ℝ≥0∞)

end Ring

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {N : ℕ}

/-- **The ring call at the concrete primitives**: `idealCallLaw_ring_eq_keyFreeCallLaw` at the
vendored FIPS 204 primitives with the FIPS 204 `ExpandS` and the concrete NTT, for every seed at
every approved parameter set, with the hypotheses discharged by `signingLaws_concreteKeyGen`,
`verifyLaws_concreteKeyGen`, `concreteEnc_highBitsVec_keyGen`, `keyGenFromSeed_s1_bounded` and
`keyGenFromSeed_s2_bounded`. -/
theorem idealCallLaw_ring_eq_keyFreeCallLaw_concrete (hp : p.isApproved) (T D : ℕ) [NeZero D]
    (seed : Bytes 32) (R : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N)
    (i : Fin R.1.length) (hRi : R.1.get i = (keyGen (concretePrimitivesKeyGen p) seed).1)
    (βmin : ℚ≥0) (H : Fin R.1.length × BucketVec p → CommitHashBytes p) :
    idealCallLaw (concretePrimitivesKeyGen p) T D (keyGen (concretePrimitivesKeyGen p) seed).2
        ((concretePrimitivesKeyGen p).expandA (keyGen (concretePrimitivesKeyGen p) seed).2.rho)
        (fun vc => flattenCoin (concretePrimitivesKeyGen p)
          (keyGen (concretePrimitivesKeyGen p) seed).2 (Cutoff.const βmin) vc *
          (ringWeights (concretePrimitivesKeyGen p) βmin
            (ringT0s (concretePrimitivesKeyGen p) R.1)).otherWeight i H vc.1) =
      keyFreeCallLaw (concretePrimitivesKeyGen p) T D
        (pubPk (concretePrimitivesKeyGen p) (R.1.get i)) (R.1.get i).2.2
        (fun vc => PMF.flattenKeep
            (fun a => (t0Weight (concretePrimitivesKeyGen p) (R.1.get i).2.2 a : ℝ≥0∞)) βmin vc *
          (ringWeights (concretePrimitivesKeyGen p) βmin
            (ringT0s (concretePrimitivesKeyGen p) R.1)).otherWeight i H vc.1) :=
  idealCallLaw_ring_eq_keyFreeCallLaw T D (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (keyGenFromSeed_s1_bounded hp seed) (keyGenFromSeed_s2_bounded hp seed) R i hRi βmin H

end Concrete

end GordieHowe.Ring.MLDSAW1
