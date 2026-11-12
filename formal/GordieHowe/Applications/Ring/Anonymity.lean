-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.WitnessIndist
public import GordieHowe.Foundations.ToMathlib.PMFCoupling
public import GordieHowe.Headline

@[expose] public section

/-!
# Rounds with public outputs and witness indistinguishability

Rounds in which a signer outputs a public value and a proof compiled by spBCS
(`GordieHowe/SPBCS/Basic.lean`; the proof is the compiled honest proof `GordieHowe.SPBCS.proofLaw`,
`GordieHowe/SPBCS/WitnessIndist.lean`), or refuses, and spBCS witness indistinguishability for
them. The anonymity hypothesis `PubWI` of the ring signatures (`AnonCoupling.lean`) and the
anonymity game of the model (`GordieHowe/Model/RingSignature/Anonymity.lean`) are stated with these
rounds.

- `PubHist`, `roundLaw`, `pubStep`, `pubRun`: the history of public values and proofs, one round,
  and the run of `Q` rounds against a selector of the statements and witnesses.
- `tvDist_pubRun_le`: two runs whose selectors agree except on a bad event are within its
  probability (identical until bad).
- `HistChoices`, `replay`, `map_wiRun_replay`, `gameAdvantage_pubRun_le`: rounds whose choices are
  functions of the history are a run of the witness-indistinguishability game of spBCS
  (`SPBCS.witnessIndistinguishable`), through a recomputed history that discards the proofs of
  refused rounds; the two experiments are within `Q · wiError δ (Q · C)`.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

/-! ### Rounds with public outputs -/

section PubRun

variable {Ω X W Pub Pf : Type} [Fintype Ω] [Nonempty Ω] (law : Ω → X → W → PMF Pf)
  (pubOf : X → Pub) {Q : ℕ}

/-- The history after `j` rounds: the public value and the proof of each round, or `none` (the
refusal `⊥`) for a refused round. -/
abbrev PubHist (Pub Pf : Type) (j : ℕ) : Type := Fin j → Option (Pub × Pf)

/-- **A selector**: in round `j`, from the oracle and the history, the statement and the witness
proved, or `none` when the round is refused. -/
abbrev Selector (Ω X W Pub Pf : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → Ω → PubHist Pub Pf j → Option (X × W)

/-- **The output of a round** at the oracle `h`: for a selected statement and witness, the
statement's public value and a proof from `law`; for a refused round, `none`. -/
noncomputable def roundLaw (h : Ω) : Option (X × W) → PMF (Option (Pub × Pf))
  | none => PMF.pure none
  | some xw => (law h xw.1 xw.2).map fun π => some (pubOf xw.1, π)

variable (sel : Selector Ω X W Pub Pf Q)

/-- Round `j` with the selector `sel`: the output of the round (`roundLaw`) appended to the
history. -/
noncomputable def pubStep (j : Fin Q) (s : Ω × PubHist Pub Pf j) : PMF (Ω × PubHist Pub Pf (j + 1)) :=
  (roundLaw law pubOf s.1 (sel j s.1 s.2)).map fun r =>
    (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 r)

/-- The experiment after `j` rounds: the oracle uniform, then the rounds. -/
noncomputable def pubRun : (j : ℕ) → j ≤ Q → PMF (Ω × PubHist Pub Pf j)
  | 0, _ => (PMF.uniformOfFintype Ω).map fun h => (h, Fin.elim0)
  | j + 1, hj => (pubRun j (by omega)).bind (pubStep law pubOf sel ⟨j, by omega⟩)

variable {law pubOf}

/-- Two selectors that agree before round `j` give the same experiment after `j` rounds. -/
theorem pubRun_congr {sel sel' : Selector Ω X W Pub Pf Q} :
    ∀ j (hj : j ≤ Q), (∀ i : Fin Q, i.1 < j → sel i = sel' i) →
      pubRun law pubOf sel j hj = pubRun law pubOf sel' j hj
  | 0, _, _ => rfl
  | j + 1, hj, h => by
    rw [pubRun, pubRun, pubRun_congr j (by omega) fun i hi => h i (by omega)]
    congr 1
    funext s
    rw [pubStep, pubStep, h ⟨j, by omega⟩ (by simp)]

/-- The probability that two selectors select differently in round `i`, in the experiment of the
first. -/
noncomputable def selectDiffProb (sel sel' : Selector Ω X W Pub Pf Q) (i : Fin Q) : ℝ :=
  ((pubRun law pubOf sel i.1 i.2.le).toOuterMeasure {s | sel i s.1 s.2 ≠ sel' i s.1 s.2}).toReal

/-- **Identical until bad**: two selectors give experiments at most the sum, over the rounds, of
the probability that they select differently in that round apart. -/
theorem tvDist_pubRun_le (sel sel' : Selector Ω X W Pub Pf Q) :
    ∀ j (hj : j ≤ Q), PMF.tvDist (pubRun law pubOf sel j hj) (pubRun law pubOf sel' j hj) ≤
      ∑ i : Fin j, selectDiffProb (law := law) (pubOf := pubOf) sel sel' (Fin.castLE hj i)
  | 0, _ => by simp [pubRun]
  | j + 1, hj => by
    rw [Fin.sum_univ_castSucc]
    have hstep : PMF.tvDist ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel ⟨j, by omega⟩)) ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel' ⟨j, by omega⟩)) ≤
        selectDiffProb (law := law) (pubOf := pubOf) sel sel' ⟨j, by omega⟩ := by
      refine (PMF.tvDist_bind_le_toOuterMeasure_ne _ _ _).trans ?_
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
        (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
      intro s hs he
      exact hs.1 (by simp only [pubStep]; rw [he])
    have hih := tvDist_pubRun_le sel sel' j (by omega)
    have hlast : Fin.castLE hj (Fin.last j) = ⟨j, by omega⟩ := rfl
    have hcast : ∀ i : Fin j, Fin.castLE hj i.castSucc = Fin.castLE (by omega) i := fun _ => rfl
    rw [hlast]
    simp only [hcast]
    rw [pubRun, pubRun]
    refine (PMF.tvDist_triangle _ ((pubRun law pubOf sel j (by omega)).bind
      (pubStep law pubOf sel' ⟨j, by omega⟩)) _).trans ?_
    exact (add_le_add hstep ((PMF.tvDist_bind_right_le _ _ _).trans hih)).trans_eq (add_comm _ _)

end PubRun

/-! ### Selectors from two-witness choices, and witness indistinguishability -/

section ReplayWI

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X W Pub : Type} {M : SPBCS Mg P X k kN kS L e}
  (pubOf : X → Pub) {Q : ℕ}

/-- **Two-witness choices from the history**: in round `j`, from the oracle and the history of
public values and proofs, a statement and two witnesses, or `none` for a refused round. -/
abbrev HistChoices (M : SPBCS Mg P X k kN kS L e) (W Pub : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
    Option (SPBCS.WIChoice X W)

variable (F : HistChoices M W Pub Q)

/-- **The history recomputed from the proofs**: round `i` is refused when the choice of round `i`
from the earlier recomputed history is `none`, and otherwise holds the public value of the chosen
statement with the proof of round `i`. -/
def replay : (j : ℕ) → j ≤ Q → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) →
    PubHist Pub M.NIProof j
  | 0, _, _, _ => Fin.elim0
  | j + 1, hj, h, πs =>
    Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay j (by omega) h (Fin.init πs))
      ((F ⟨j, by omega⟩ h (replay j (by omega) h (Fin.init πs))).map fun c =>
        (pubOf c.stmt, πs (Fin.last j)))

theorem replay_succ_snoc (j : ℕ) (hj : j + 1 ≤ Q) (h : Query k kN kS L → Out k e)
    (πs : Fin j → M.NIProof) (π : M.NIProof) :
    replay pubOf F (j + 1) hj h (Fin.snoc (α := fun _ => M.NIProof) πs π) =
      Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay pubOf F j (by omega) h πs)
        ((F ⟨j, by omega⟩ h (replay pubOf F j (by omega) h πs)).map fun c => (pubOf c.stmt, π)) := by
  rw [replay, Fin.init_snoc, Fin.snoc_last]

/-- **The witness-indistinguishability adversary of two-witness choices from the history**, with
a finite set `S` of admissible choices containing every choice and a choice `c₀ ∈ S` for the
refused rounds, whose proofs the recomputed history discards. -/
def HistChoices.toWIAdversary {rel : Set (X × W)} (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel) {c₀ : SPBCS.WIChoice X W}
    (hc₀ : c₀ ∈ S) (hF : ∀ j h hist c, F j h hist = some c → c ∈ S) : M.WIAdversary rel Q where
  choices := S
  admissible := hS
  choose j h πs := (F j h (replay pubOf F j j.2.le h πs)).getD c₀
  choose_mem j h πs := by
    cases hc : F j h (replay pubOf F j j.2.le h πs) with
    | none => exact hc₀
    | some c => exact hF _ _ _ _ hc

/-- The selector answering round `j` with the second witness when `bs j`, refusing the rounds whose
choice is `none`. -/
def HistChoices.selector (bs : ℕ → Bool) : Selector (Query k kN kS L → Out k e) X W Pub M.NIProof Q :=
  fun j h hist => (F j h hist).map fun c => (c.stmt, if bs j then c.wit₁ else c.wit₀)

variable {F}

/-- **The witness-indistinguishability experiment with its history recomputed** is the experiment
with public outputs of the selector. -/
theorem map_wiRun_replay (law : (Query k kN kS L → Out k e) → X → W → PMF M.NIProof)
    {rel : Set (X × W)} {S : Finset (SPBCS.WIChoice X W)}
    {hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel} {c₀ : SPBCS.WIChoice X W}
    {hc₀ : c₀ ∈ S} {hF : ∀ j h hist c, F j h hist = some c → c ∈ S} (bs : ℕ → Bool) :
    ∀ j (hj : j ≤ Q), (SPBCS.wiRun law (F.toWIAdversary pubOf S hS hc₀ hF) bs j hj).map
        (fun s => (s.1, replay pubOf F j hj s.1 s.2)) =
      pubRun law pubOf (F.selector bs) j hj
  | 0, _ => by
    rw [SPBCS.wiRun, pubRun, PMF.map_comp]
    congr 1
  | j + 1, hj => by
    rw [SPBCS.wiRun, pubRun, ← map_wiRun_replay law (hS := hS) (hc₀ := hc₀) (hF := hF) bs j
      (by omega), PMF.map_bind, PMF.bind_map]
    congr 1
    funext s
    simp only [Function.comp_apply, SPBCS.wiStep, pubStep, PMF.map_comp, HistChoices.selector,
      HistChoices.toWIAdversary]
    simp only [Function.comp_def, replay_succ_snoc]
    cases hc : F ⟨j, by omega⟩ s.1 (replay pubOf F j (by omega) s.1 s.2) with
    | none =>
      simp only [Option.map_none, Option.getD_none, roundLaw, PMF.pure_map]
      exact PMF.map_const _ _
    | some c =>
      simp only [Option.map_some, roundLaw, PMF.map_comp, Function.comp_def]
      rfl

/-- **Witness indistinguishability with public outputs**: for the spBCS compilation `M` whose
honest prover has honest-verifier zero knowledge at error `δ` for `rel` (`h`), and two-witness
choices from the history in a finite admissible set `S` (every choice not `none` is in `S`), the
experiments with public outputs answering every round with the first and with the second witness
are distinguished by any event of the oracle and the history with advantage at most
`Q · wiError δ |S|`. Refused rounds are the same in the two experiments; if `S` is empty every
round is refused and the experiments agree. -/
theorem gameAdvantage_pubRun_le {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {R : Type} [Fintype R] [Nonempty R]
    {honest : W → R → CausalProver P τ X} {rel : Set (X × W)} {PubZ : Type} {pubZ : X → PubZ}
    (Rv : M.Reveal E Qs) {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV rel honest pubZ sim δ) (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel)
    (hF : ∀ j h hist c, F j h hist = some c → c ∈ S)
    (D : (Query k kN kS L → Out k e) → PubHist Pub M.NIProof Q → Prop) :
    GordieHowe.gameAdvantage
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => false) Q le_rfl)
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => true) Q le_rfl)
      {s | D s.1 s.2} ≤ Q * M.wiError δ S.card := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨c₀, hc₀⟩
  · have hnone : ∀ j h hist, F j h hist = none := fun j h hist => by
      cases hc : F j h hist with
      | none => rfl
      | some c => exact absurd (hF j h hist c hc) (by simp [hS0])
    have hsel : F.selector (fun _ => false) = F.selector fun _ => true := by
      funext j h hist
      simp [HistChoices.selector, hnone]
    rw [hsel]
    unfold GordieHowe.gameAdvantage GordieHowe.advantage
    rw [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (SPBCS.wiError_nonneg δ _)
  rw [← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF),
    ← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF)]
  have hadv := SPBCS.witnessIndistinguishable Rv (SPBCS.obsClose_of_causalHVZK Rv h) Q S.card
    (F.toWIAdversary pubOf S hS hc₀ hF) le_rfl (fun h πs => D h (replay pubOf F Q le_rfl h πs))
  unfold SPBCS.wiAdvantage SPBCS.wiAdvantageWith SPBCS.wiGameWith at hadv
  unfold GordieHowe.gameAdvantage at hadv ⊢
  simp only [PMF.toOuterMeasure_map_apply] at ⊢
  exact hadv

end ReplayWI

/-! ### A uniform average -/

/-- A sum weighted by the uniform law is the average. -/
theorem _root_.PMF.sum_toReal_uniformOfFintype_mul {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ∑ x, (PMF.uniformOfFintype α x).toReal * f x = 𝔼 x, f x := by
  simp only [PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card]
  rw [← Finset.mul_sum, div_eq_inv_mul]

end GordieHowe.Ring
