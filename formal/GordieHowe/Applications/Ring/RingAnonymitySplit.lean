-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingAnonymity

@[expose] public section

/-!
# The coupling bound with errors depending on the base signer's part of the oracle

`abs_detAnonWin_split_sub_le` (`GordieHowe/Applications/Ring/RingAnonymity.lean`) bounds the
deterministic classical anonymity game of `ofBase B PS adm` for a base signer reading only the
first part `ω₂` of an oracle split `(X → Y) ≃ Ω₂ × Ω₁`, with one distance bound `ε` for every
value of `ω₂`. Here the bound `ε ω₂` and a good event `Good ω₂` depend on `ω₂`.

- `detAnonWinVia_mem_Icc`: the probability of a family of deterministic strategies, the oracle
  drawn through `ψ`, is in `[0, 1]`.
- `abs_detAnonWin_split_sub_le_expect`: at a key vector, for a base signer reading only the first
  part, with witness indistinguishability `wi` of the proof laws for the ring relation, at most `C`
  valid challenges, the two users' refusal-or-public value laws within `ε ω₂` on a good event
  `Good ω₂` for every valid challenge on a supported ring and every value of the second part, and
  correctness error `εc`, every family of deterministic strategies has
  advantage at most `𝔼_{ω₂} (Q · (ε ω₂ + 2εc) + Q · wi (Q · C) + 1[¬ Good ω₂])`.
- `toOuterMeasure_runLaw_anonAccepts`, `gameAdvantage_runLaw_le_of_det`: for any two challenger
  families on the anonymity game's challenges, the run's acceptance as an output law, and the
  advantage between the two runs from deterministic classical strategies
  (`toReal_outLaw_sub_le_of_det`).
-/

open scoped ENNReal NNReal BigOperators

namespace GordieHowe.RingSignature

open GordieHowe.Quantum GordieHowe.Interaction GordieHowe.Ring

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {N n : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm]
  (keys : Fin n → (ofBase B PS adm).KeyCoins) (Q : ℕ) (m : (X → Y) → ℕ)
  (s : (X → Y) → AnonDetStrategy (ofBase B PS adm) n)

omit [DecidableEq Y] in
/-- **The probability of a family of deterministic strategies, the oracle drawn through `ψ`, is
in `[0, 1]`.** -/
theorem detAnonWinVia_mem_Icc (b : Bool) {Ω₁ : Type} [Fintype Ω₁] [Nonempty Ω₁]
    (ψ : Ω₁ → X → Y) :
    0 ≤ detAnonWinVia keys b Q m s ψ ∧ detAnonWinVia keys b Q m s ψ ≤ 1 := by
  refine ⟨Finset.expect_nonneg fun h₁ _ => ENNReal.toReal_nonneg, ?_⟩
  calc detAnonWinVia keys b Q m s ψ ≤ 𝔼 _h₁ : Ω₁, (1 : ℝ) :=
        Finset.expect_le_expect fun h₁ _ => toReal_toOuterMeasure_le_one _ _
    _ = 1 := Fintype.expect_const _

/-- **The deterministic classical game at a key vector with errors depending on the base signer's
part of the oracle** (`abs_detAnonWinVia_sub_le` at each value `ω₂` of the first part of the split
`e`, on the good event `Good ω₂`, and the trivial bound `1` off it, averaged over `ω₂`): for a base
signer reading the oracle only through the first part (`hB`), with witness indistinguishability at
error `wi` of the proof laws at the oracles of each first part (`hwi`), at most `C` valid challenges
for the keys (`hC`), the two users' refusal-or-public value laws within `ε ω₂` for every valid
challenge on a supported ring and every value `h₁` of the second part when `Good ω₂` holds (`hε`),
and correctness error `εc` (`hcorr`), every family of deterministic strategies has advantage at most
`𝔼_{ω₂} (Q · (ε ω₂ + 2εc) + Q · wi (Q · C) + 1[¬ Good ω₂])`. -/
theorem abs_detAnonWin_split_sub_le_expect {Ω₂ Ω₁ : Type} [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype Ω₁] [Nonempty Ω₁] (e : (X → Y) ≃ Ω₂ × Ω₁) (hB : B.ReadsOnly fun H => (e H).1)
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (e.symm (ω₂, h))) RingStmtOf.pub
      (ringRel B adm (e.symm (ω₂, h₁))) wi) {C : ℕ}
    (hC : (Finset.univ.filter fun c : AnonRequest (ofBase B PS adm) n => c.Valid keys).card ≤ C)
    (Good : Ω₂ → Prop) [DecidablePred Good] (ε : Ω₂ → ℝ) (hε0 : ∀ ω₂, 0 ≤ ε ω₂)
    (hε : ∀ ω₂, Good ω₂ → ∀ h₁ (c : AnonRequest (ofBase B PS adm) n), c.Valid keys →
      adm c.ring → PMF.tvDist (B.refusalPubLaw (e.symm (ω₂, h₁)) (keys c.user₀) c.ring c.msg)
        (B.refusalPubLaw (e.symm (ω₂, h₁)) (keys c.user₁) c.ring c.msg) ≤ ε ω₂)
    {εc : ℝ≥0} (hcorr : B.CorrectWithin εc) :
    |detAnonWin keys false Q m s - detAnonWin keys true Q m s| ≤
      𝔼 ω₂, ((Q : ℝ) * (ε ω₂ + 2 * εc) + Q * wi (Q * C) + if Good ω₂ then 0 else 1) := by
  have hwi0 : 0 ≤ (Q : ℝ) * wi (Q * C) := mul_nonneg (Nat.cast_nonneg _)
    ((hwi (Classical.arbitrary Ω₂) (Classical.arbitrary Ω₁)).wi_nonneg _)
  have hpt : ∀ ω₂, |detAnonWinVia keys false Q m s (fun h₁ => e.symm (ω₂, h₁)) -
      detAnonWinVia keys true Q m s (fun h₁ => e.symm (ω₂, h₁))| ≤
        (Q : ℝ) * (ε ω₂ + 2 * εc) + Q * wi (Q * C) + if Good ω₂ then 0 else 1 := fun ω₂ => by
    have hQ : 0 ≤ (Q : ℝ) * (ε ω₂ + 2 * εc) :=
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hε0 ω₂) (by positivity))
    by_cases hG : Good ω₂
    · simp only [hG, ite_true, add_zero]
      let h₁z : Ω₁ := Classical.arbitrary Ω₁
      exact abs_detAnonWinVia_sub_le keys Q m s (fun h₁ => e.symm (ω₂, h₁)) hB
        (e.symm (ω₂, h₁z)) (fun h₁ => by simp only [Equiv.apply_symm_apply]) (hwi ω₂ h₁z) hC
        (hε0 ω₂) (hε ω₂ hG h₁z) hcorr
    · simp only [hG, ite_false]
      have h0 := detAnonWinVia_mem_Icc keys Q m s false fun h₁ => e.symm (ω₂, h₁)
      have h1 := detAnonWinVia_mem_Icc keys Q m s true fun h₁ => e.symm (ω₂, h₁)
      rw [abs_sub_le_iff]
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have hsplit : ∀ b', detAnonWin keys b' Q m s =
      𝔼 ω₂, detAnonWinVia keys b' Q m s (fun h₁ => e.symm (ω₂, h₁)) := fun b' =>
    expect_eq_expect_split e _
  rw [hsplit false, hsplit true, ← Finset.expect_sub_distrib, abs_le]
  constructor
  · calc -(𝔼 ω₂, ((Q : ℝ) * (ε ω₂ + 2 * εc) + Q * wi (Q * C) + if Good ω₂ then 0 else 1)) =
          𝔼 ω₂, -((Q : ℝ) * (ε ω₂ + 2 * εc) + Q * wi (Q * C) + if Good ω₂ then 0 else 1) :=
          (Finset.expect_neg_distrib _ _).symm
      _ ≤ _ := Finset.expect_le_expect fun ω₂ _ => (abs_le.1 (hpt ω₂)).1
  · exact Finset.expect_le_expect fun ω₂ _ => (abs_le.1 (hpt ω₂)).2

/-! ### Games against any challenger family -/

section Challengers

variable {TS : RingTypes} {S : RingScheme X Y N TS} {V : OracleView X Y} {t : ℕ} [Nonempty X] [AddGroup Y]

/-- **The acceptance probability of a run against any challenger family** is that of the output
`1` of the output law (`anonAcceptProb_eq` for any challengers). -/
theorem toOuterMeasure_runLaw_anonAccepts (A : AnonAdversary S n V t)
    (C : (Fin n → S.KeyCoins) → Quantum.Challenger X Y (AnonRequest S n) S.Sig) :
    (runLaw (fun keys H => A (keys, V.view H)) C).toOuterMeasure anonAccepts =
      ((PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
        (PMF.uniformOfFintype (X → Y)).bind fun H => (A (keys, V.view H)).aux.bind fun a =>
          (((A (keys, V.view H)).alg a).compose (C keys)).outLaw H).toOuterMeasure
            {some true} := by
  rw [runLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun keys => ?_
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine congrArg _ (tsum_congr fun H => ?_)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_bind_apply]
  congr 1
  have h := QueryBoundedAdversary.toOuterMeasure_transcriptLaw_fst (A (keys, V.view H)) (C keys) H
    true
  refine (Eq.trans ?_ h).trans (tsum_congr fun a => ?_)
  · rfl
  · rw [PMF.toOuterMeasure_apply_singleton]

/-- **The game between two challenger families from deterministic classical strategies**: if, at
every key vector, every family of deterministic strategies wins against `C₀ keys` and against
`C₁ keys` with probabilities at most `ε keys` apart, the advantage of every adversary between the
runs against `C₀` and `C₁` is at most `𝔼 ε`. -/
theorem gameAdvantage_runLaw_le_of_det (A : AnonAdversary S n V t)
    (C₀ C₁ : (Fin n → S.KeyCoins) → Quantum.Challenger X Y (AnonRequest S n) S.Sig)
    {ε : (Fin n → S.KeyCoins) → ℝ}
    (hdet : ∀ keys (m : (X → Y) → ℕ) (s : (X → Y) → AnonDetStrategy S n),
      |(𝔼 H, Interaction.winProb (s H).toStrategy ((C₀ keys).classicalAt H) (m H)
          {p | p.2 = some true}) -
        (𝔼 H, Interaction.winProb (s H).toStrategy ((C₁ keys).classicalAt H) (m H)
          {p | p.2 = some true})| ≤ ε keys) :
    gameAdvantage (runLaw (fun keys H => A (keys, V.view H)) C₀)
      (runLaw (fun keys H => A (keys, V.view H)) C₁) anonAccepts ≤ 𝔼 keys, ε keys := by
  unfold gameAdvantage advantage
  change |((runLaw (fun keys H => A (keys, V.view H)) C₀).toOuterMeasure anonAccepts).toReal -
    ((runLaw (fun keys H => A (keys, V.view H)) C₁).toOuterMeasure anonAccepts).toReal| ≤ _
  rw [toOuterMeasure_runLaw_anonAccepts, toOuterMeasure_runLaw_anonAccepts, abs_sub_le_iff]
  constructor
  · exact toReal_outLaw_sub_le_of_det A C₀ C₁ fun keys m s => (le_abs_self _).trans (hdet keys m s)
  · exact toReal_outLaw_sub_le_of_det A C₁ C₀ fun keys m s =>
      (neg_le_abs _).trans_eq' (by ring) |>.trans (hdet keys m s)

end Challengers

end GordieHowe.RingSignature
