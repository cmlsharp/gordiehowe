-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Completeness
public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# Anonymity against full key exposure

The anonymity game of a `RingScheme`, BKM06 Definition 4 (ePrint 2005/304, p. 6, anonymity
against full key exposure), with `Q` adaptive challenges, against the adversaries of
`GordieHowe/Model/RingSignature/Adversary.lean`.

- `AnonRequest S n`: a challenge `(R, m, u₀, u₁)`: a ring, a message and two of the `n` honest
  users. `AnonRequest.Valid`: both users' public keys are in the ring. A challenge with `u₀ = u₁`
  is a signing query.
- `anonChallenger S n keys b Q`: the challenger of experiment `b` at the users' key coins `keys`:
  each of the first `Q` challenges is answered, if it is valid, by `S.sign` of user `u_b` with fresh
  uniform signing coins (a refusal `⊥` is the reply `none`, which the adversary sees); an invalid
  one among them gets `none` and uses up its slot, and the challenges after the `Q`-th get `none`.
- `AnonAdversary S n V t`: a `t`-query adversary whose start input is all honest users' key coins
  and the table `V` of the oracle, outputting a bit.
- `anonLaw`, `anonAcceptProb`, `anonAdvantage`: the run of experiment `b` (keys and oracle uniform),
  the probability of the output `1`, and the advantage `|Pr[1 | b = 0] - Pr[1 | b = 1]|`.
- Sanity: `anonChallenger_respond_of_user_eq` (a signing query is answered alike in both
  experiments), `anonChallenger_respond_of_not_valid` (an invalid challenge gets `⊥` in both),
  `valid_pair` (the valid challenges are not vacuous), `anonAdvantage_le_one`,
  `anonAdvantage_eq_zero_of_eq` and `trivial_anonAdvantage` (the trivial scheme has advantage `0`).

## Comparison with BKM06 Definition 4

BKM06's game: `n` key pairs from coins `ω_i`, the public keys given to `A`; a signing oracle
`OSign(s, M, R)` for rings with `PK_s ∈ R` (Definition 3, arbitrary keys allowed); a challenge
`(M, i₀, i₁, R)` with distinct `i₀, i₁` and `PK_{i₀}, PK_{i₁} ∈ R`, answered by
`Sign_{SK_{i_b}}(M, R)` after `{ω_i}` is handed out; `A` outputs `b'`. The deliberate differences:

1. **`Q` adaptive challenges** in place of one challenge and a signing oracle. A challenge with
   `u₀ = u₁` is BKM06's signing query `OSign(u₀, M, R)`, and a challenge with distinct users is a
   challenge; the adversary may interleave them and pose several challenges, all answered with the
   same bit. One challenge and signing queries is the case of at most one challenge with distinct
   users, so the game is at least as strong; a hybrid over the challenges relates the two, at a
   factor `Q`.
2. **All key coins at the start** (stronger timing, as CCLM22, ePrint 2021/1616, Experiment 2,
   p. 21, and BKP20, ePrint 2020/646, p. 7): BKM06 hands out `{ω_i}` with the challenge. Every
   signing query is then also asked with the coins known.
3. **Refusals are visible**: a challenge the signer refuses (`S.sign` returns `none`: an
   unsupported ring, the signer's own public check) is answered by `none`. The refusal rule of a
   scheme that is anonymous reads only public data, so `none` comes with the same probability in
   both experiments; the game does not assume it.
4. **Invalid challenges are answered by `none`** in both experiments (BKM06 requires the adversary
   to output a valid one).
5. **Rings are ordered lists with repetitions** (`KeyRing`); the signer finds its own position.
6. **Quantum adversaries in the QROM** with at most `t` superposition queries, the part `V` of the
   oracle handed out whole (`OracleView`): `OracleView.whole` for the statistical results.
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TS : RingTypes} (S : RingScheme X Y N TS) (n : ℕ)

/-- **A challenge of the anonymity game over its components**: a ring of keys in `PK`, a message in
`Msg` and two honest users. With `user₀ = user₁` it is a signing query. -/
structure AnonRequestOf (PK Msg : Type) (N n : ℕ) where
  /-- The ring. -/
  ring : KeyRing PK N
  /-- The message. -/
  msg : Msg
  /-- The user signing in experiment `0`. -/
  user₀ : Fin n
  /-- The user signing in experiment `1`. -/
  user₁ : Fin n
deriving DecidableEq

/-- Challenges as tuples. -/
def AnonRequestOf.equivProd (PK Msg : Type) (N n : ℕ) :
    AnonRequestOf PK Msg N n ≃ KeyRing PK N × Msg × Fin n × Fin n where
  toFun c := (c.ring, c.msg, c.user₀, c.user₁)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {PK Msg : Type} [Fintype PK] [DecidableEq PK] [Fintype Msg] {N n : ℕ} :
    Fintype (AnonRequestOf PK Msg N n) :=
  Fintype.ofEquiv _ (AnonRequestOf.equivProd PK Msg N n).symm

/-- **A challenge of the anonymity game** of the scheme `S` (`AnonRequestOf` at its key and
message types): a ring, a message and two honest users. Schemes with the same keys and messages
have the same challenges. -/
abbrev AnonRequest : Type := AnonRequestOf S.PK S.Msg N n

namespace AnonRequest

/-- Challenges as tuples. -/
abbrev equivProd : AnonRequest S n ≃ KeyRing S.PK N × S.Msg × Fin n × Fin n :=
  AnonRequestOf.equivProd S.PK S.Msg N n

variable {S n}

/-- **The user of a challenge in experiment `b`.** -/
def user (c : AnonRequest S n) (b : Bool) : Fin n := bif b then c.user₁ else c.user₀

/-- **A valid challenge** for the users' key coins `keys` (BKM06 Definition 4, step 2:
`PK_{i₀}, PK_{i₁} ∈ R`): both users' public keys are in the ring. -/
def Valid (keys : Fin n → S.KeyCoins) (c : AnonRequest S n) : Prop :=
  S.pk (keys c.user₀) ∈ c.ring.1 ∧ S.pk (keys c.user₁) ∈ c.ring.1

instance instDecidableValid [DecidableEq TS.PK] (keys : Fin n → S.KeyCoins) (c : AnonRequest S n) :
    Decidable (c.Valid keys) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **A valid challenge's signer is in the ring**, in both experiments. -/
theorem Valid.pk_mem {keys : Fin n → S.KeyCoins} {c : AnonRequest S n} (h : c.Valid keys)
    (b : Bool) : S.pk (keys (c.user b)) ∈ c.ring.1 := by
  cases b
  · exact h.1
  · exact h.2

/-- **Valid challenges exist** for any two users when rings of two keys are allowed: the ring of
their two public keys. -/
theorem valid_pair (hN : 2 ≤ N) (keys : Fin n → S.KeyCoins) (m : S.Msg) (u₀ u₁ : Fin n) :
    AnonRequest.Valid keys
      (⟨⟨[S.pk (keys u₀), S.pk (keys u₁)], by simpa using hN⟩, m, u₀, u₁⟩ : AnonRequest S n) :=
  ⟨by simp, by simp⟩

end AnonRequest

section Challenger

variable [DecidableEq TS.PK] [Fintype TS.SignCoins] [DecidableEq TS.SignCoins]
  [Nonempty TS.SignCoins]

/-- **The challenger of experiment `b` of the anonymity game** at the honest users' key coins
`keys`, answering `Q` challenges: challenge number `j < Q`, if valid, is answered by the scheme's
signer of user `u_b` with the signing coins `ω j` (uniform), its refusal `none` included; an invalid
challenge, and every challenge after the `Q`-th, gets `none`. It reprograms nothing. -/
noncomputable def anonChallenger (keys : Fin n → S.KeyCoins) (b : Bool) (Q : ℕ) :
    Challenger X Y (AnonRequest S n) S.Sig where
  Coins := Fin Q → S.SignCoins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := S.q
  respond ω hist c :=
    if h : hist.length < Q then
      if c.Valid keys then
        (S.sign (S.keyGen (keys (c.user b))) c.ring c.msg (ω ⟨hist.length, h⟩)).bind fun o =>
          .pure ⟨o, []⟩
      else .pure ⟨none, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist c H := by
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact S.sign_queries _ _ _ _ H
    · simp
    · simp

/-- **A signing query is answered alike in both experiments**: with `u₀ = u₁` the two challengers'
reply programs agree. -/
theorem anonChallenger_respond_of_user_eq (keys : Fin n → S.KeyCoins) (Q : ℕ)
    (ω : Fin Q → S.SignCoins) (hist : List (HistoryEntry (AnonRequest S n) S.Sig))
    (c : AnonRequest S n) (hc : c.user₀ = c.user₁) :
    (anonChallenger S n keys false Q).respond ω hist c =
      (anonChallenger S n keys true Q).respond ω hist c := by
  simp only [anonChallenger, AnonRequest.user, Bool.cond_false, Bool.cond_true, hc]

/-- **An invalid challenge gets `⊥` in both experiments.** -/
theorem anonChallenger_respond_of_not_valid (keys : Fin n → S.KeyCoins) (b : Bool) (Q : ℕ)
    (ω : Fin Q → S.SignCoins) (hist : List (HistoryEntry (AnonRequest S n) S.Sig))
    (c : AnonRequest S n) (hc : ¬ c.Valid keys) :
    (anonChallenger S n keys b Q).respond ω hist c = .pure ⟨none, []⟩ := by
  simp [anonChallenger, hc]

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype TS.PK] [Fintype TS.Msg] [DecidableEq TS.Msg] [Fintype TS.Sig]
  [DecidableEq TS.Sig] [Fintype TS.KeyCoins] [Nonempty TS.KeyCoins]

/-- **An adversary of the anonymity game** with `n` honest users and at most `t` queries: on all
users' key coins and the table `V` of the oracle, a `t`-query adversary posing challenges and
outputting a bit (`GameAdversary`). -/
abbrev AnonAdversary (V : OracleView X Y) (t : ℕ) : Type 1 :=
  GameAdversary X Y (AnonRequest S n) S.Sig ((Fin n → S.KeyCoins) × V.Tab) Bool t

variable {S n} {V : OracleView X Y} {t : ℕ}

/-- **The run of experiment `b` of the anonymity game** with `Q` challenges: the users' key coins and
the oracle uniform, the adversary on the key coins and the oracle's table against the challenger of
experiment `b`. -/
noncomputable def anonLaw (A : AnonAdversary S n V t) (Q : ℕ) (b : Bool) :
    PMF (GameRun (Fin n → S.KeyCoins) X Y Bool (AnonRequest S n) S.Sig) :=
  runLaw (fun keys H => A (keys, V.view H)) fun keys => anonChallenger S n keys b Q

/-- The event of the anonymity game: the adversary terminates with output `1`. -/
def anonAccepts : Set (GameRun (Fin n → S.KeyCoins) X Y Bool (AnonRequest S n) S.Sig) :=
  {r | r.Outputs (· = true)}

/-- **The probability that the adversary outputs `1` in experiment `b`.** -/
noncomputable def anonAcceptProb (A : AnonAdversary S n V t) (Q : ℕ) (b : Bool) : ℝ≥0∞ :=
  (anonLaw A Q b).toOuterMeasure anonAccepts

/-- **The anonymity advantage** with `Q` challenges (BKM06 Definition 4, as the distance of the two
experiments' acceptance probabilities; twice the advantage of guessing `b`). -/
noncomputable def anonAdvantage (A : AnonAdversary S n V t) (Q : ℕ) : ℝ :=
  gameAdvantage (anonLaw A Q false) (anonLaw A Q true) anonAccepts

/-- The anonymity advantage is the distance of the two acceptance probabilities. -/
theorem anonAdvantage_eq (A : AnonAdversary S n V t) (Q : ℕ) :
    anonAdvantage A Q = advantage (anonAcceptProb A Q false).toReal (anonAcceptProb A Q true).toReal :=
  rfl

/-- **The anonymity advantage is at most `1`.** -/
theorem anonAdvantage_le_one (A : AnonAdversary S n V t) (Q : ℕ) : anonAdvantage A Q ≤ 1 := by
  rw [anonAdvantage_eq, advantage, abs_sub_le_iff]
  have h₀ : (anonAcceptProb A Q false).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top (prob_runLaw_le_one _ _ _)
  have h₁ : (anonAcceptProb A Q true).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top (prob_runLaw_le_one _ _ _)
  have z₀ := ENNReal.toReal_nonneg (a := anonAcceptProb A Q false)
  have z₁ := ENNReal.toReal_nonneg (a := anonAcceptProb A Q true)
  rw [ENNReal.toReal_one] at h₀ h₁
  exact ⟨by linarith, by linarith⟩

/-- **Equal challengers give advantage `0`**: if for all key coins the two experiments' challengers
are equal, no adversary distinguishes them. -/
theorem anonAdvantage_eq_zero_of_eq
    (h : ∀ (keys : Fin n → S.KeyCoins) (Q : ℕ), anonChallenger S n keys false Q =
      anonChallenger S n keys true Q)
    (A : AnonAdversary S n V t) (Q : ℕ) : anonAdvantage A Q = 0 := by
  rw [anonAdvantage, anonLaw, anonLaw]
  simp only [h, gameAdvantage, advantage_self]

/-- **The trivial scheme is perfectly anonymous** (its signer does not depend on the key), so the
anonymity hypothesis is satisfiable. -/
theorem trivial_anonAdvantage (A : AnonAdversary (RingScheme.trivial X Y N) n V t) (Q : ℕ) :
    anonAdvantage A Q = 0 :=
  anonAdvantage_eq_zero_of_eq (fun _ _ => rfl) A Q

end Challenger

end GordieHowe.RingSignature
