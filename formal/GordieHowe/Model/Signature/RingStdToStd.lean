-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.RejectionRelayCount

@[expose] public section

/-!
# The combined signing oracle reduced to the standard one

For a base signer whose ring-aware signer signs as the ordinary signer on the base message
(`BaseSigner.RingSignsStd`: `bsign sk R i m c` runs as `ssign sk (bmsg R m) c`, as for the Falcon-512
and ML-DSA base signers of the generic rings), a ring-signing request `(R, m)` is an ordinary signing
request on `bmsg R m`. The ring-aware signer is then the rejection form with one attempt, no check
and no rejection (`stdRejection`), whose standard oracle is the ordinary one (`SignOracle.std`), and
the lifting lemma of `GordieHowe/Model/Signature/RejectionRelayCount.lean` at one attempt bounds the
multi-user game with the combined oracle (`SignOracle.ringStd`) by the standard multi-user game, with
the same numbers of requests and of signing and corruption requests.

- `BaseSigner.RingSignsStd`: the ring-aware signer signs as the ordinary signer on the base message.
- `stdRejection`, `stdRejection_stdOracle`, `stdCoins`: the rejection form with one attempt, its
  standard oracle the ordinary one, and its coins.
- `isRejection_stdRejection`, `isStdOn_stdRejection`: the rejection form of such a base signer.
- `ringStdToStd`, `muEufProbWithin_ringStd_le_std`: the relayed adversary of the standard game and the
  bound.
- `ringToStd`, `muEufProbWithin_ring_le_std`: the same for the multi-user game with the ring-aware
  oracle (`SignOracle.ring`).
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} (B : BaseSigner X Y N TB)

/-- **The ring-aware signer signs as the ordinary signer on the base message**: at every oracle, for
every secret key, ring, position, message and coins, the run of `bsign` is the run of `ssign` on
`bmsg R m` with the same coins. -/
def _root_.GordieHowe.RingSignature.BaseSigner.RingSignsStd : Prop :=
  ∀ (H : X → Y) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins),
    (B.bsign sk R i m c).run H = (B.ssign sk (B.bmsg R m) c).run H

/-- **The rejection form with one attempt and no rejection**: the ordinary signer as the standard
signer with the base signer's coins, no keep coins, a check and a keep decision that accept without
a query. -/
def stdRejection : Rejection B where
  StdCoins := B.Coins
  KeepCoins := Unit
  qStd := B.q
  std := B.ssign
  std_queries := B.ssign_queries
  qCheck := 0
  check _ := .pure true
  check_queries _ := OracleProg.QueriesLE.pure _ _
  qKeep := 0
  keep _ _ _ _ _ := .pure true
  keep_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _

/-- **The standard oracle of `stdRejection` is the ordinary signing oracle.** -/
theorem stdRejection_stdOracle : (stdRejection B).stdOracle = SignOracle.std B :=
  rfl

/-- **The coins of one attempt**: the base signer's coins as one pair of standard coins and the
keep coin. -/
def stdCoins : B.Coins ≃ (Fin 1 → (stdRejection B).StdCoins × (stdRejection B).KeepCoins) where
  toFun c _ := (c, ())
  invFun f := (f 0).1
  left_inv _ := rfl
  right_inv f := funext fun j => by
    fin_cases j
    exact Prod.ext rfl rfl

variable {B}

/-- **A ring-aware signer signing as the ordinary signer is the rejection form `stdRejection` with
one attempt.** -/
theorem isRejection_stdRejection (h : B.RingSignsStd) :
    IsRejection B (stdRejection B) 1 (stdCoins B) := by
  intro H sk R i m c
  rw [h, Rejection.run_rejectSign]
  rw [show ((stdRejection B).check R).run H = true from rfl, if_pos rfl, List.ofFn_succ,
    List.ofFn_zero, List.findSome?_cons, List.findSome?_nil]
  have hcc : (stdCoins B) c 0 = (c, ()) := rfl
  rw [hcc]
  rcases hσ : (B.ssign sk (B.bmsg R m) c).run H with _ | σ <;>
    simp [Rejection.att, stdRejection, hσ]

/-- **The ordinary signer is the standard signer of `stdRejection`.** -/
theorem isStdOn_stdRejection : IsStdOn B (stdRejection B) 1 (stdCoins B) Nat.one_pos :=
  fun _ _ _ _ => rfl

variable {n : ℕ} {V : OracleView X Y} {t : ℕ} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [AddGroup Y]

/-- **The relayed adversary of the standard multi-user game** for an adversary `A` of the game with
the combined oracle (`relayMUAdversaryStd` at `stdRejection`): it asks every request of `A` of the
standard challenger, a ring-signing request `(R, m)` as the ordinary signing request on `bmsg R m`,
padding with the public-key request of user `i₀`. -/
noncomputable abbrev ringStdToStd (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q : ℕ) : MUAdversary (SignOracle.std B) n V (t + Q * (0 + 1 * 0)) :=
  relayMUAdversaryStd (stdRejection B) 1 n Nat.one_pos i₀ A Q

/-- **The multi-user game with the combined oracle is bounded by the standard multi-user game** for a
ring-aware signer signing as the ordinary signer (`h`): an adversary winning with at most `Qs`
signing and corruption requests against `Q` requests has at most the success probability of
`ringStdToStd` winning with at most `Qs` signing and corruption requests against `Q` requests
(`muEufProbWithin_le_relay_ringStd` at one attempt). -/
theorem muEufProbWithin_ringStd_le_std (h : B.RingSignsStd) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd B) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤ muEufProbWithin (ringStdToStd i₀ A Q) Q Qs := by
  have h1 := muEufProbWithin_le_relay_ringStd (J := stdRejection B) (K := 1) (e := stdCoins B)
    Nat.one_pos (isRejection_stdRejection h).isRejectionOn isStdOn_stdRejection i₀ A Q Qs
  rwa [Nat.one_mul Q, Nat.one_mul Qs] at h1

/-- **The relayed adversary of the standard multi-user game** for an adversary `A` of the game with
the ring-aware oracle (`relayMUAdversary` at `stdRejection`): it asks every request of `A` of the
standard challenger, a ring-signing request `(R, m)` as the ordinary signing request on `bmsg R m`,
padding with the public-key request of user `i₀`. -/
noncomputable abbrev ringToStd (i₀ : Fin n) (A : MUAdversary (SignOracle.ring B) n V t)
    (Q : ℕ) : MUAdversary (SignOracle.std B) n V (t + Q * (0 + 1 * 0)) :=
  relayMUAdversary (stdRejection B) 1 n Nat.one_pos i₀ A Q

/-- **The multi-user game with the ring-aware oracle is bounded by the standard multi-user game**
for a ring-aware signer signing as the ordinary signer (`h`): an adversary winning with at most `Qs`
signing and corruption requests against `Q` requests has at most the success probability of
`ringToStd` winning with at most `Qs` signing and corruption requests against `Q` requests
(`muEufProbWithin_le_relay` at one attempt). -/
theorem muEufProbWithin_ring_le_std (h : B.RingSignsStd) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤ muEufProbWithin (ringToStd i₀ A Q) Q Qs := by
  have h1 := muEufProbWithin_le_relay (J := stdRejection B) (K := 1) (e := stdCoins B)
    Nat.one_pos (isRejection_stdRejection h).isRejectionOn i₀ A Q Qs
  rwa [Nat.one_mul Q, Nat.one_mul Qs] at h1

end GordieHowe.Signature
