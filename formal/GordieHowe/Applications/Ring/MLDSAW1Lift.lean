-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Rejection
public import GordieHowe.Model.Signature.RejectionRelay
public import GordieHowe.Model.Signature.RejectionRelayCount

@[expose] public section

/-!
# The ring game of the ML-DSA ring publishing `w₁` from the standard call game

At the concrete primitives of an approved parameter set, the base signer of the ML-DSA ring
publishing `w₁` (`w1ConcreteBase`, `GordieHowe/Applications/Ring/MLDSAW1Ring.lean`) is a rejection
form (`IsRejectionOn`, `GordieHowe/Model/Signature/Rejection.lean`) whose attempt is one call of the
FIPS 204 signer at one nonce (`w1Rejection`, `GordieHowe/Applications/Ring/MLDSAW1Rejection.lean`),
and its ordinary signer is its first attempt (`IsStdOn`). The lifting lemmas of
`GordieHowe/Model/Signature/RejectionCtx.lean` then bound each MU game of the ring-aware signing
oracle by the same game of the standard call oracle (`Rejection.stdOracle`) at `k · Q` requests.

The standard call game is the multi-user game (MU-EUF-CMA^corr) of FIPS 204 with public keys that
include `t₀` (FIPS 204 §6.1: `t₀` "need not be regarded as secret") and the signing oracle hedged
Algorithm 7 with its loop capped at `T` attempts (FIPS 204 §6.2 and Appendix C).

- `isRejectionOn_w1ConcreteBase`: the rejection form at the concrete primitives.
- `muEufProb_w1ConcreteBase_le_relay`: MU-EUF-CMA^corr of the ring-aware game (`SignOracle.ring`).
- `muSufProb_w1ConcreteBase_le_muVerifyProb_relay`: MU-SUF-CMA^corr of the ring-aware game at most
  the probability that the relayed adversary outputs a signature verifying under an uncorrupted
  user's key (`muVerifyProb`; not a reduction to MU-SUF-CMA^corr).
- `muEufProb_w1ConcreteBase_le_relay_ringStd`,
  `muSufProb_w1ConcreteBase_le_muVerifyProb_relay_ringStd`: the same for the key-reuse game
  (`SignOracle.ringStd`).
- `muEufProbWithin_w1ConcreteBase_le_relay`, `muEufProbWithin_w1ConcreteBase_le_relay_ringStd`: the
  MU-EUF-CMA^corr lifts with at most `Qs` signing and corruption requests in the ring-aware or
  key-reuse game and at most `k · Qs` in the standard call game (`muEufProbWithin_le_relay`).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.Signature
open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec
open scoped ENNReal

attribute [local instance] concreteNTTRingOps

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} [NeZero (bucketCount p)]
  [Nonempty (MaskBox p)] {N reps : ℕ} [Fintype Msg] [DecidableEq Msg]
  (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps) (M : MaskOracle X Y p T Msg)
  (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  (bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg)

variable (p) in
/-- **The rejection form of the concrete base signer**: `w1Rejection` at the concrete primitives
and the hedged mask source. -/
noncomputable abbrev w1ConcreteRejection : Rejection (w1ConcreteBase p O M βmin tol k D bmsg) :=
  w1Rejection (concretePrimitivesKeyGen p) (MaskSource.hedged M) O βmin tol k D (concreteEnc p)
    bmsg

/-- **The concrete base signer is a rejection form** at every approved parameter set
(`isRejectionOn_w1Base` with the signing and verification laws of the concrete primitives, the
coherence of `concreteEnc` and `‖s₂‖∞ ≤ η` for every honest key). -/
theorem isRejectionOn_w1ConcreteBase (hp : p.isApproved) :
    IsRejectionOn (w1ConcreteBase p O M βmin tol k D bmsg)
      (w1ConcreteRejection p O M βmin tol k D bmsg) k (w1CoinEquiv (MaskSource.hedged M) k D) :=
  isRejectionOn_w1Base _ _ O βmin tol k D (concreteEnc p) bmsg (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (fun seed => keyGenFromSeed_s2_bounded hp seed)

/-- **The ordinary signer of the concrete base signer is its first attempt.** -/
theorem isStdOn_w1ConcreteBase (hk : 0 < k) :
    IsStdOn (w1ConcreteBase p O M βmin tol k D bmsg)
      (w1ConcreteRejection p O M βmin tol k D bmsg) k (w1CoinEquiv (MaskSource.hedged M) k D) hk :=
  isStdOn_w1Base _ _ O βmin tol k D (concreteEnc p) bmsg hk

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t n : ℕ}

/-- **MU-EUF-CMA^corr of the ring-aware game from the standard call game**: every adversary `A`
of the ring-aware game of the concrete base signer with `Q` requests has at most the success
probability of its relayed adversary (at most `t + Q · (qCheck + k · qKeep)` queries) in the game
of the standard call oracle with `k · Q` requests. -/
theorem muEufProb_w1ConcreteBase_le_relay (hp : p.isApproved) (hk : 0 < k) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring (w1ConcreteBase p O M βmin tol k D bmsg)) n V t) (Q : ℕ) :
    muEufProb A Q ≤
      muEufProb (relayMUAdversary (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) :=
  muEufProb_le_relay hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp) i₀ A Q

/-- **MU-SUF-CMA^corr of the ring-aware game against the standard call game**: at most the
probability that the relayed adversary, in the game of the standard call oracle with `k · Q`
requests, outputs a signature verifying under the key of an uncorrupted user (`muVerifyProb`).
This is not a reduction to MU-SUF-CMA^corr (`muSufProb_le_muVerifyProb_relay`). -/
theorem muSufProb_w1ConcreteBase_le_muVerifyProb_relay (hp : p.isApproved) (hk : 0 < k)
    (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring (w1ConcreteBase p O M βmin tol k D bmsg)) n V t) (Q : ℕ) :
    muSufProb A Q ≤
      muVerifyProb (relayMUAdversary (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) :=
  muSufProb_le_muVerifyProb_relay hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp) i₀ A Q

/-- **MU-EUF-CMA^corr of the key-reuse game from the standard call game**: every adversary `A` of
the key-reuse game of the concrete base signer (ring requests and base messages) with `Q` requests
has at most the success probability of its relayed adversary in the game of the standard call
oracle with `k · Q` requests. -/
theorem muEufProb_w1ConcreteBase_le_relay_ringStd (hp : p.isApproved) (hk : 0 < k) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd (w1ConcreteBase p O M βmin tol k D bmsg)) n V t)
    (Q : ℕ) :
    muEufProb A Q ≤
      muEufProb (relayMUAdversaryStd (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) :=
  muEufProb_le_relay_ringStd hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp)
    (isStdOn_w1ConcreteBase O M βmin tol k D bmsg hk) i₀ A Q

/-- **MU-SUF-CMA^corr of the key-reuse game against the standard call game**: the form of
`muSufProb_w1ConcreteBase_le_muVerifyProb_relay` for `SignOracle.ringStd`. -/
theorem muSufProb_w1ConcreteBase_le_muVerifyProb_relay_ringStd (hp : p.isApproved) (hk : 0 < k)
    (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd (w1ConcreteBase p O M βmin tol k D bmsg)) n V t)
    (Q : ℕ) :
    muSufProb A Q ≤
      muVerifyProb (relayMUAdversaryStd (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) :=
  muSufProb_le_muVerifyProb_relay_ringStd hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp)
    (isStdOn_w1ConcreteBase O M βmin tol k D bmsg hk) i₀ A Q

/-- **MU-EUF-CMA^corr with the count, from the standard call game**: the probability that `A` wins
the ring-aware game of the concrete base signer (`Q` requests) with at most `Qs` signing and
corruption requests is at most the probability that its relayed adversary wins the game of the
standard call oracle (`k · Q` requests) with at most `k · Qs`. -/
theorem muEufProbWithin_w1ConcreteBase_le_relay (hp : p.isApproved) (hk : 0 < k) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring (w1ConcreteBase p O M βmin tol k D bmsg)) n V t)
    (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (relayMUAdversary (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) (k * Qs) :=
  muEufProbWithin_le_relay hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp) i₀ A Q Qs

/-- **The key-reuse form of `muEufProbWithin_w1ConcreteBase_le_relay`.** -/
theorem muEufProbWithin_w1ConcreteBase_le_relay_ringStd (hp : p.isApproved) (hk : 0 < k)
    (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd (w1ConcreteBase p O M βmin tol k D bmsg)) n V t)
    (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin
        (relayMUAdversaryStd (w1ConcreteRejection p O M βmin tol k D bmsg) k n hk i₀ A Q)
        (k * Q) (k * Qs) :=
  muEufProbWithin_le_relay_ringStd hk (isRejectionOn_w1ConcreteBase O M βmin tol k D bmsg hp)
    (isStdOn_w1ConcreteBase O M βmin tol k D bmsg hk) i₀ A Q Qs

end GordieHowe.Ring.MLDSAW1
