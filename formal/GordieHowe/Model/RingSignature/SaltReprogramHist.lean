-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.SaltReprogram
public import GordieHowe.Model.Quantum.Interactive.RecordReplies

@[expose] public section

/-!
# Reprogramming at hidden fresh salts for events of the oracle and the history

`GordieHowe/Model/RingSignature/SaltReprogram.lean` bounds, for a salted challenger and its fresh
counterpart (`Challenger.SaltFreshPair`), the change in the probability of an event of the
adversary's output. The games of the library also read the oracle (verification of a forgery) and
the history (the signatures returned). This file carries the bound to events of the start draws,
the oracle, the output and the history that read the oracle only outside the range of the
embedding of the salted inputs.

- `QueryBoundedAdversary.advantage_salt_fresh_le_of_event`: for the uniform oracle, an adversary
  `𝒜 H` and an event `E H` of the output both chosen from the oracle's values outside the range of
  `emb`, the probabilities that the output lies in `E H` against `C₀` and against `C₁` are at most
  `Pr[two salts collide] + 2 t √ε` apart (the proof of `advantage_salt_fresh_le`, conditioning on
  the values outside the range, with the event fixed along with the adversary).
- `RingSignature.RunOutAt`, `RingSignature.RunEventAt`: the events of a game's run of the output,
  and of the output and the history, at the start draws and the oracle.
  `RingSignature.toOuterMeasure_runLaw_apply`: an event of the run as an average over the start
  draws and the oracle.
- `RingSignature.gameAdvantage_runLaw_salt_fresh_le_of_event`: the bound for the run of a game, for
  events of the output read at the start draws and off the range at the oracle.
- `RingSignature.runEventAt_eq_runOutAt_of_isEmpty`: without requests, an event of the output
  and the history is one of the output.
  `RingSignature.toOuterMeasure_runLaw_runEventAt_recordReplies`: an event of the output and the
  history has the probability of an event of the output of the adversary recording its replies
  (`QueryBoundedAdversary.recordReplies`, the history as its first `Q` records).
- `RingSignature.gameAdvantage_runLaw_salt_fresh_le_hist`: the bound for events of the start draws,
  the oracle (read off the range), the output and the history.
  `RingSignature.gameAdvantage_runLaw_salt_fresh_le_hist_of_pi`: for independent salts with point
  probabilities at most `δ`, the bound is `C(K, 2) δ + 2 t √(K δ)`.
-/

namespace GordieHowe

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

variable {S U : Type} [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U] {K : ℕ}
  {emb : S × U → X} {ν : PMF (Fin K → S)}

namespace Quantum.QueryBoundedAdversary

variable {C₀ C₁ : Challenger X Y Req Resp}

/-- **Reprogramming at hidden fresh salts for events read off the salted inputs**: the oracle
uniform, the adversary `𝒜 H` and the event `E H` of its output chosen from the oracle's values
outside the range of the injective embedding `emb`. The output lies in `E H` against the salted
challenger `C₀` and against its fresh counterpart `C₁` (`Challenger.SaltFreshPair`) with
probabilities at most `Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability that
a given point of `S` is a salt. The proof conditions on the oracle's values outside the range
(`advantage_sum_uniform_le`), under which the adversary and the event are fixed and the oracle law
is uniform on the range (`advantage_salt_fresh_le_of_law`). -/
theorem advantage_salt_fresh_le_of_event (𝒜 : (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (h𝒜 : ∀ H H', AgreeOffRange emb H H' → 𝒜 H = 𝒜 H') (P : C₀.SaltFreshPair emb ν C₁)
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : (X → Y) → Set O)
    (hE : ∀ H H', AgreeOffRange emb H H' → E H = E H') :
    GordieHowe.advantage
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((𝒜 H).transcriptLaw C₀ H).toOuterMeasure (OutIn (E H))).toReal)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((𝒜 H).transcriptLaw C₁ H).toOuterMeasure (OutIn (E H))).toReal) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  refine advantage_sum_uniform_le (emb := emb) fun H₀ => ?_
  have hfix : ∀ C : Challenger X Y Req Resp, ∑ H, (offRangeLaw emb H₀ H).toReal *
      (((𝒜 H).transcriptLaw C H).toOuterMeasure (OutIn (E H))).toReal =
      ∑ H, (offRangeLaw emb H₀ H).toReal *
        (((𝒜 H₀).transcriptLaw C H).toOuterMeasure (OutIn (E H₀))).toReal := fun C =>
    Finset.sum_congr rfl fun H _ => by
      by_cases h0 : offRangeLaw emb H₀ H = 0
      · simp [h0]
      · have h := agreeOffRange_of_offRangeLaw_ne_zero h0
        rw [h𝒜 H H₀ h, hE H H₀ h]
  rw [hfix, hfix]
  exact advantage_salt_fresh_le_of_law (𝒜 H₀) P hemb (isUniformOnRange_offRangeLaw H₀) hε (E H₀)

end Quantum.QueryBoundedAdversary

namespace RingSignature

open Quantum.QueryBoundedAdversary

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- A game advantage as the advantage of the two probabilities of the event. -/
theorem gameAdvantage_eq {α : Type} (μ₀ μ₁ : PMF α) (W : Set α) :
    gameAdvantage μ₀ μ₁ W = GordieHowe.advantage (μ₀.toOuterMeasure W).toReal
      (μ₁.toOuterMeasure W).toReal :=
  rfl

/-- **The output events of a game's run at the start draws and the oracle**: the adversary
terminates with an output in `E k H`, at the start draws `k` and the oracle `H` of the run. -/
def RunOutAt {Start : Type} (E : Start → (X → Y) → Set O) :
    Set (Start × (X → Y) × Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x.2.2, p.1 ∈ E x.1 x.2.1}

/-- **The events of a game's run of the output and the history**: the adversary terminates, and
its output with the history lies in `E k H`, at the start draws `k` and the oracle `H` of the
run. -/
def RunEventAt {Start : Type} (E : Start → (X → Y) → Set (O × List (HistoryEntry Req Resp))) :
    Set (Start × (X → Y) × Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x.2.2, p ∈ E x.1 x.2.1}

/-- **An event of a game's run as an average** over the start draws and the oracle of the
probability of its slice under the transcript law. -/
theorem toOuterMeasure_runLaw_apply {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : Start → Challenger X Y Req Resp)
    (W : Set (Start × (X → Y) × Option (O × List (HistoryEntry Req Resp)))) :
    (runLaw A C).toOuterMeasure W =
      ∑' k, PMF.uniformOfFintype Start k * ∑' H, PMF.uniformOfFintype (X → Y) H *
        ((A k H).transcriptLaw (C k) H).toOuterMeasure {o | (k, H, o) ∈ W} := by
  rw [runLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => ?_
  rw [PMF.toOuterMeasure_bind_apply]
  congr 1
  refine tsum_congr fun H => ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- An average of numbers at most `1` is at most `1`. -/
theorem tsum_mul_le_one {α : Type} (μ : PMF α) {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) :
    ∑' a, μ a * f a ≤ 1 :=
  (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hf a) _).trans_eq (by
    simp only [mul_one, PMF.tsum_coe])

omit [DecidableEq Y] [Nonempty X] [AddGroup Y] in
/-- An average over the uniform oracle of numbers at most `1`, as a real sum. -/
theorem toReal_tsum_uniform_mul {f : (X → Y) → ℝ≥0∞} (hf : ∀ H, f H ≤ 1) :
    (∑' H, PMF.uniformOfFintype (X → Y) H * f H).toReal =
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * (f H).toReal := by
  rw [tsum_fintype, ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hf H))]
  simp only [ENNReal.toReal_mul]

/-- **Reprogramming at hidden fresh salts in a game's run, for output events read at the start
draws and off the salted inputs at the oracle**: with start draws `k`, the adversary `A k H` and
the event `E k H` of its output chosen from the start draws and the oracle's values outside the
range of the injective embedding `emb`, and for every `k` a salted challenger `C₀ k` with its fresh
counterpart `C₁ k` (`Challenger.SaltFreshPair`, salts `ρ ← ν`), the probabilities of the event in
the two runs are at most `Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability
that a given point of `S` is a salt. -/
theorem gameAdvantage_runLaw_salt_fresh_le_of_event {Start : Type} [Fintype Start]
    [Nonempty Start] (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H')
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPair emb ν (C₁ k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (E : Start → (X → Y) → Set O)
    (hE : ∀ k H H', AgreeOffRange emb H H' → E k H = E k H') :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunOutAt E) ≤
      (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  rw [gameAdvantage]
  change |((runLaw A C₀).toOuterMeasure (RunOutAt E)).toReal -
    ((runLaw A C₁).toOuterMeasure (RunOutAt E)).toReal| ≤ _
  rw [toOuterMeasure_runLaw_apply, toOuterMeasure_runLaw_apply]
  refine PMF.abs_toReal_tsum_mul_sub_le _
    (fun _ => tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun k => ?_
  rw [toReal_tsum_uniform_mul fun _ => PMF.toOuterMeasure_apply_le_one _ _,
    toReal_tsum_uniform_mul fun _ => PMF.toOuterMeasure_apply_le_one _ _]
  exact advantage_salt_fresh_le_of_event (A k) (hA k) (P k) hemb hε (E k) (hE k)

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- **Without requests every history is empty**, so an event of the output and the history is an
event of the output (with the empty history). -/
theorem runEventAt_eq_runOutAt_of_isEmpty [IsEmpty Req] {Start : Type}
    (E : Start → (X → Y) → Set (O × List (HistoryEntry Req Resp))) :
    RunEventAt E = RunOutAt fun k H => {o | (o, []) ∈ E k H} := by
  have hnil : ∀ l : List (HistoryEntry Req Resp), l = [] := fun l => by
    rcases l with _ | ⟨e, _⟩
    · rfl
    · exact isEmptyElim e.request
  ext x
  constructor
  · rintro ⟨⟨o, l⟩, hp, hE⟩
    refine ⟨(o, l), hp, ?_⟩
    rw [hnil l] at hE
    exact hE
  · rintro ⟨⟨o, l⟩, hp, hE⟩
    refine ⟨(o, l), hp, ?_⟩
    rw [hnil l]
    exact hE

/-- **An event of the output and the history as an event of the recorded output**: the run of the
adversaries `A k H` lies in `RunEventAt E` with the probability that the run of the adversaries
recording their replies (`QueryBoundedAdversary.recordReplies`) ends with an output `(o, l)` such
that `o` with the history of the first `(C k).Q` records of `l` lies in `E k H`
(`QueryBoundedAdversary.prob_transcriptLaw_recordReplies`). -/
theorem toOuterMeasure_runLaw_runEventAt_recordReplies [Inhabited Req] {Start : Type}
    [Fintype Start]
    [Nonempty Start] (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : Start → Challenger X Y Req Resp)
    (E : Start → (X → Y) → Set (O × List (HistoryEntry Req Resp))) :
    (runLaw A C).toOuterMeasure (RunEventAt E) =
      (runLaw (fun k H => (A k H).recordReplies) C).toOuterMeasure
        (RunOutAt fun k H => {q | (q.1, (q.2.take (C k).Q).map HistoryEntry.ofPair) ∈ E k H}) := by
  rw [toOuterMeasure_runLaw_apply, toOuterMeasure_runLaw_apply]
  refine tsum_congr fun k => congrArg _ (tsum_congr fun H => congrArg _ ?_)
  exact (A k H).prob_transcriptLaw_recordReplies (C k) H (· ∈ E k H)

/-- **Reprogramming at hidden fresh salts for events of the oracle, the output and the history**:
with start draws `k`, the adversary `A k H` chosen from the start draws and the oracle's values
outside the range of the injective embedding `emb`, and an event `E k H` of the output and the
history that depends on the oracle only through its values outside the range, for every `k` a
salted challenger `C₀ k` with its fresh counterpart `C₁ k` (`Challenger.SaltFreshPair`, salts
`ρ ← ν`): the probabilities of the event in the two runs are at most
`Pr[two salts collide] + 2 t √ε` apart, for `ε` bounding the probability that a given point of `S`
is a salt. The history becomes part of the output of the adversary recording its replies
(`toOuterMeasure_runLaw_runEventAt_recordReplies`), with the same query bound `t`; without
requests the history is empty (`runEventAt_eq_runOutAt_of_isEmpty`). -/
theorem gameAdvantage_runLaw_salt_fresh_le_hist {Start : Type} [Fintype Start] [Nonempty Start]
    (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H')
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPair emb ν (C₁ k))
    (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε)
    (E : Start → (X → Y) → Set (O × List (HistoryEntry Req Resp)))
    (hE : ∀ k H H', AgreeOffRange emb H H' → E k H = E k H') :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunEventAt E) ≤
      (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * t * √ε := by
  rcases isEmpty_or_nonempty Req with hR | hR
  · rw [runEventAt_eq_runOutAt_of_isEmpty]
    exact gameAdvantage_runLaw_salt_fresh_le_of_event A hA P hemb hε _
      (fun k H H' h => by rw [hE k H H' h])
  let _ : Inhabited Req := ⟨Classical.choice hR⟩
  have hQ : ∀ k, (C₁ k).Q = (C₀ k).Q := fun k => (P k).Q_eq
  have h0 := toOuterMeasure_runLaw_runEventAt_recordReplies A C₀ E
  have h1 := toOuterMeasure_runLaw_runEventAt_recordReplies A C₁ E
  simp only [hQ] at h1
  have key := gameAdvantage_runLaw_salt_fresh_le_of_event (fun k H => (A k H).recordReplies)
    (fun k H H' h => by rw [hA k H H' h]) P hemb hε
    (fun k H => {q | (q.1, (q.2.take (C₀ k).Q).map HistoryEntry.ofPair) ∈ E k H})
    (fun k H H' h => by rw [hE k H H' h])
  rw [gameAdvantage_eq] at key ⊢
  rw [h0, h1]
  exact key

/-- **`gameAdvantage_runLaw_salt_fresh_le_hist` for independent salts of min-entropy `κ`**: for
salts drawn independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the bound is
`C(K, 2) δ + 2 t √(K δ)`. -/
theorem gameAdvantage_runLaw_salt_fresh_le_hist_of_pi {Start : Type} [Fintype Start]
    [Nonempty Start] (A : Start → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (hA : ∀ k H H', AgreeOffRange emb H H' → A k H = A k H') {p : Fin K → PMF S}
    {C₀ C₁ : Start → Challenger X Y Req Resp} (P : ∀ k, (C₀ k).SaltFreshPair emb (PMF.pi p) (C₁ k))
    (hemb : Function.Injective emb) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ)
    (E : Start → (X → Y) → Set (O × List (HistoryEntry Req Resp)))
    (hE : ∀ k H H', AgreeOffRange emb H H' → E k H = E k H') :
    gameAdvantage (runLaw A C₀) (runLaw A C₁) (RunEventAt E) ≤
      K.choose 2 * δ + 2 * t * √(K * δ) :=
  (gameAdvantage_runLaw_salt_fresh_le_hist A hA P hemb (toReal_pi_exists_eq_le p hδ) E hE).trans
    (add_le_add (toReal_pi_not_injective_le p hδ) le_rfl)

end RingSignature

end GordieHowe
