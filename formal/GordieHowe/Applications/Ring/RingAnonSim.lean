-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Anonymity
public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.Quantum.Interactive.ClassicalSim

@[expose] public section

/-!
# Anonymity against quantum adversaries from deterministic classical strategies

The anonymity game of `GordieHowe/Model/RingSignature/Anonymity.lean` is played by interactive
quantum adversaries with classical requests. If, at each key vector `keys`, every family of
deterministic classical strategies (one per oracle, knowing the key coins and the whole oracle) has
advantage at most `ε keys`, then every adversary of the game, for every oracle view `V` and query
bound `t`, has advantage at most `𝔼 ε`.

- `KindAlg.outLaw_composeBothOut_comp`: the output law of a composition whose output is read through
  `g ∘ f` is that read through `f`, mapped by `g`.
- `anonOutLaw`, `anonAcceptProb_eq`: the output law of the anonymity game, the key coins, the oracle
  and the auxiliary input drawn, and the acceptance probability of the game as its probability of
  the output `1`.
- `exists_mem_support_tsum_le`: some point of the support has at least the average of a real
  function bounded by `1`. `sum_toReal_uniform_mul_eq_expect`: a sum weighted by the uniform law is
  the average.
- `AnonDetStrategy S n`, `detAnonWin`: a deterministic classical strategy of the anonymity game (its
  next request or query slot, and its output, as functions of the oracle and the visible history),
  and the probability that a family of them, one per oracle `H` with `m H` rounds, outputs `1`
  against the challenger of experiment `b` at `H`, the oracle uniform.
- `toReal_outLaw_sub_le_of_det`: one direction of the reduction, for any two challenger families.
- `anonAdvantage_le_of_det`: **the reduction**: if for each key vector every family of
  deterministic strategies has advantage at most `ε keys`, every anonymity adversary has advantage
  at most `𝔼 ε`.

The proof is the conditional-sampling simulation of
`GordieHowe/Model/Quantum/Interactive/ClassicalSim.lean` (`AdaptiveIAlg.outLaw_compose_some_eq`) at
each key vector, oracle and auxiliary input, the derandomization of behavioral strategies
(`Interaction.exists_det_winDiff_ge`), and the choice of an auxiliary input at least as good as the
average (`exists_mem_support_tsum_le`). The strategies are chosen per key vector and oracle, so they
may depend on both; the start input `(keys, V.view H)` of the adversary is a function of them.
-/

open scoped ENNReal BigOperators

namespace GordieHowe

namespace Quantum.KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
  (C : Challenger X Y Req Resp)

/-- **Reading the output through `g ∘ f`** maps the output law read through `f` by `g`. -/
theorem outLaw_composeBothOut_comp [Nonempty X] [AddGroup Y] [Nonempty Y] {O' O'' : Type}
    (f : B.CW C → O') (g : O' → O'') (H : X → Y) :
    (B.composeBothOut C (g ∘ f)).outLaw H = ((B.composeBothOut C f).outLaw H).map (Option.map g) := by
  simp only [Alg.outLaw, PMF.map_comp, Option.map_comp_map]
  rfl

end Quantum.KindAlg

/-- **Some point of the support has at least the average** of a real function bounded by `1`. -/
theorem exists_mem_support_tsum_le {α : Type*} (ν : PMF α) (f : α → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    ∃ a ∈ ν.support, ∑' a, (ν a).toReal * f a ≤ f a := by
  by_contra hcon
  push Not at hcon
  set E := ∑' a, (ν a).toReal * f a
  have hs : Summable fun a => (ν a).toReal * f a := pmf_summable_toReal_mul ν hf
  obtain ⟨a₀, ha₀⟩ := ν.support_nonempty
  have hlt : ∑' a, (ν a).toReal * f a < ∑' a, (ν a).toReal * E := by
    refine Summable.tsum_lt_tsum (i := a₀) (fun a => ?_) ?_ hs
      ((pmf_summable_toReal ν).mul_right E)
    · by_cases ha : a ∈ ν.support
      · exact mul_le_mul_of_nonneg_left (hcon a ha).le ENNReal.toReal_nonneg
      · rw [PMF.mem_support_iff, not_not] at ha
        simp [ha]
    · exact mul_lt_mul_of_pos_left (hcon a₀ ha₀)
        (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).1 ha₀) (PMF.apply_ne_top _ _))
  rw [tsum_mul_right, pmf_tsum_toReal, one_mul] at hlt
  exact lt_irrefl _ hlt

/-- **A sum weighted by the uniform law is the average.** -/
theorem sum_toReal_uniform_mul_eq_expect {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∑ x, (PMF.uniformOfFintype α x).toReal * f x = 𝔼 x, f x := by
  simp only [PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card]
  rw [← Finset.mul_sum, div_eq_inv_mul]

namespace RingSignature

open GordieHowe.Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {N n : ℕ} {TS : RingTypes} {S : RingScheme X Y N TS} {V : OracleView X Y} {t : ℕ}

/-- **A deterministic classical strategy of the anonymity game** with `n` honest users: from the
oracle and the visible history, its next move (a challenge, or `none` for a query slot) and its
output. -/
abbrev AnonDetStrategy {TS : RingTypes} (S : RingScheme X Y N TS) (n : ℕ) : Type :=
  Interaction.DetStrategy (X → Y) (Option (AnonRequest S n)) (Option S.Sig × (X → Y)) (Option Bool)

/-- **The probability that a family of deterministic strategies outputs `1`** in experiment `b` at
the users' key coins `keys` with `Q` challenges: the oracle `H` uniform and the strategy `s H`
with `m H` rounds against the challenger of experiment `b` at `H`. -/
noncomputable def detAnonWin (keys : Fin n → S.KeyCoins) (b : Bool) (Q : ℕ) (m : (X → Y) → ℕ)
    (s : (X → Y) → AnonDetStrategy S n) : ℝ :=
  𝔼 H, Interaction.winProb (s H).toStrategy ((anonChallenger S n keys b Q).classicalAt H) (m H)
    {p | p.2 = some true}

/-- **The law of the anonymity game's output**: the key coins, the oracle and the auxiliary input
drawn, the composed algorithm's output law. -/
noncomputable def anonOutLaw (A : AnonAdversary S n V t) (Q : ℕ) (b : Bool) : PMF (Option Bool) :=
  (PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
    (PMF.uniformOfFintype (X → Y)).bind fun H =>
      (A (keys, V.view H)).aux.bind fun a =>
        (((A (keys, V.view H)).alg a).compose (anonChallenger S n keys b Q)).outLaw H

/-- **The acceptance probability of the anonymity game** is that of the output `1` of its output
law. -/
theorem anonAcceptProb_eq (A : AnonAdversary S n V t) (Q : ℕ) (b : Bool) :
    anonAcceptProb A Q b = (anonOutLaw A Q b).toOuterMeasure {some true} := by
  rw [anonAcceptProb, anonLaw, runLaw, anonOutLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun keys => ?_
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine congrArg _ (tsum_congr fun H => ?_)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_bind_apply]
  congr 1
  have h := QueryBoundedAdversary.toOuterMeasure_transcriptLaw_fst (A (keys, V.view H))
    (anonChallenger S n keys b Q) H true
  refine (Eq.trans ?_ h).trans (tsum_congr fun a => ?_)
  · rfl
  · rw [PMF.toOuterMeasure_apply_singleton]

/-- **One direction of the reduction** for two challenger families: if every family of
deterministic strategies wins against `C₀ keys` with at most `ε keys` more probability than against
`C₁ keys`, the output law's probability of `1` is at most `𝔼 ε` more against `C₀` than against
`C₁`. -/
theorem toReal_outLaw_sub_le_of_det (A : AnonAdversary S n V t)
    (C₀ C₁ : (Fin n → S.KeyCoins) → Challenger X Y (AnonRequest S n) S.Sig)
    {ε : (Fin n → S.KeyCoins) → ℝ}
    (hdet : ∀ keys (m : (X → Y) → ℕ) (s : (X → Y) → AnonDetStrategy S n),
      (𝔼 H, Interaction.winProb (s H).toStrategy ((C₀ keys).classicalAt H) (m H)
          {p | p.2 = some true}) -
        (𝔼 H, Interaction.winProb (s H).toStrategy ((C₁ keys).classicalAt H) (m H)
          {p | p.2 = some true}) ≤ ε keys) :
    (((PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
        (PMF.uniformOfFintype (X → Y)).bind fun H => (A (keys, V.view H)).aux.bind fun a =>
          (((A (keys, V.view H)).alg a).compose (C₀ keys)).outLaw H).toOuterMeasure
            {some true}).toReal -
      (((PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
        (PMF.uniformOfFintype (X → Y)).bind fun H => (A (keys, V.view H)).aux.bind fun a =>
          (((A (keys, V.view H)).alg a).compose (C₁ keys)).outLaw H).toOuterMeasure
            {some true}).toReal ≤ 𝔼 keys, ε keys := by
  classical
  -- the win probability of the classical strategy of the adversary on each value
  let w : (keys : Fin n → S.KeyCoins) → (H : X → Y) → Challenger X Y (AnonRequest S n) S.Sig →
      (A (keys, V.view H)).Aux → ℝ := fun keys H C a =>
    (((((A (keys, V.view H)).alg a).compose C).outLaw H).toOuterMeasure {some true}).toReal
  have hw : ∀ keys H C a, w keys H C a = Interaction.winProb
      ((A (keys, V.view H)).alg a).toKindAlg.classicalSim (C.classicalAt H)
      ((A (keys, V.view H)).alg a).slots {p | p.2 = some true} := fun keys H C a => by
    simp only [w, PMF.toOuterMeasure_apply_singleton, AdaptiveIAlg.outLaw_compose_some_eq]
    rfl
  -- at each key vector and oracle, a deterministic strategy at least as good as the adversary
  have hpt : ∀ keys H, ∃ (m : ℕ) (s : AnonDetStrategy S n),
      ∑' a, ((A (keys, V.view H)).aux a).toReal * (w keys H (C₀ keys) a - w keys H (C₁ keys) a) ≤
        Interaction.winProb s.toStrategy ((C₀ keys).classicalAt H) m {p | p.2 = some true} -
          Interaction.winProb s.toStrategy ((C₁ keys).classicalAt H) m {p | p.2 = some true} := by
    intro keys H
    obtain ⟨a, -, ha⟩ := exists_mem_support_tsum_le (A (keys, V.view H)).aux
      (fun a => w keys H (C₀ keys) a - w keys H (C₁ keys) a) fun a => by
        have h0 := toReal_toOuterMeasure_le_one
          ((((A (keys, V.view H)).alg a).compose (C₀ keys)).outLaw H) {some true}
        have h1 := toReal_toOuterMeasure_le_one
          ((((A (keys, V.view H)).alg a).compose (C₁ keys)).outLaw H) {some true}
        have z0 := ENNReal.toReal_nonneg (a := ((((A (keys, V.view H)).alg a).compose
          (C₀ keys)).outLaw H).toOuterMeasure {some true})
        have z1 := ENNReal.toReal_nonneg (a := ((((A (keys, V.view H)).alg a).compose
          (C₁ keys)).outLaw H).toOuterMeasure {some true})
        rw [abs_sub_le_iff]
        constructor <;> simp only [w] <;> linarith
    obtain ⟨s, hs⟩ := Interaction.exists_det_winDiff_ge ((C₀ keys).classicalAt H)
      ((C₁ keys).classicalAt H) {p | p.2 = some true}
      ((A (keys, V.view H)).alg a).toKindAlg.classicalSim ((A (keys, V.view H)).alg a).slots
    refine ⟨((A (keys, V.view H)).alg a).slots, s, ha.trans ?_⟩
    rw [hw, hw]
    exact hs
  choose m s hms using hpt
  -- the difference of the two probabilities as an average
  rw [toReal_bind_sub_eq]
  have hkeys : ∀ keys, (((PMF.uniformOfFintype (X → Y)).bind fun H =>
        (A (keys, V.view H)).aux.bind fun a =>
          (((A (keys, V.view H)).alg a).compose (C₀ keys)).outLaw H).toOuterMeasure
            {some true}).toReal -
      (((PMF.uniformOfFintype (X → Y)).bind fun H =>
        (A (keys, V.view H)).aux.bind fun a =>
          (((A (keys, V.view H)).alg a).compose (C₁ keys)).outLaw H).toOuterMeasure
            {some true}).toReal ≤
      (𝔼 H, Interaction.winProb (s keys H).toStrategy ((C₀ keys).classicalAt H) (m keys H)
          {p | p.2 = some true}) -
        (𝔼 H, Interaction.winProb (s keys H).toStrategy ((C₁ keys).classicalAt H) (m keys H)
          {p | p.2 = some true}) := fun keys => by
    rw [toReal_bind_sub_eq, tsum_fintype (L := SummationFilter.unconditional _),
      ← Finset.expect_sub_distrib, ← sum_toReal_uniform_mul_eq_expect]
    refine Finset.sum_le_sum fun H _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    rw [toReal_bind_sub_eq]
    exact hms keys H
  rw [tsum_fintype (L := SummationFilter.unconditional _), ← sum_toReal_uniform_mul_eq_expect]
  exact Finset.sum_le_sum fun keys _ => mul_le_mul_of_nonneg_left
    ((hkeys keys).trans (hdet keys (m keys) (s keys))) ENNReal.toReal_nonneg

/-- **Anonymity from deterministic classical strategies**: if, at every key vector, every family of
deterministic classical strategies (one per oracle, knowing the key coins and the whole oracle)
distinguishes the two experiments with advantage at most `ε keys`, then every anonymity adversary,
with any oracle view `V` and any query bound `t`, has advantage at most `𝔼 ε` with `Q`
challenges. -/
theorem anonAdvantage_le_of_det (A : AnonAdversary S n V t) (Q : ℕ)
    {ε : (Fin n → S.KeyCoins) → ℝ}
    (hdet : ∀ keys (m : (X → Y) → ℕ) (s : (X → Y) → AnonDetStrategy S n),
      |detAnonWin keys false Q m s - detAnonWin keys true Q m s| ≤ ε keys) :
    anonAdvantage A Q ≤ 𝔼 keys, ε keys := by
  rw [anonAdvantage_eq, anonAcceptProb_eq, anonAcceptProb_eq, advantage, abs_sub_le_iff]
  constructor
  · exact toReal_outLaw_sub_le_of_det A (fun keys => anonChallenger S n keys false Q)
      (fun keys => anonChallenger S n keys true Q) fun keys m s =>
        (le_abs_self _).trans (hdet keys m s)
  · exact toReal_outLaw_sub_le_of_det A (fun keys => anonChallenger S n keys true Q)
      (fun keys => anonChallenger S n keys false Q) fun keys m s =>
        (neg_le_abs _).trans_eq' (by simp only [detAnonWin]; ring) |>.trans (hdet keys m s)

end RingSignature

end GordieHowe
