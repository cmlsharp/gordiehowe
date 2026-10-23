-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Definition

@[expose] public section

/-!
# GordieHowe: the round errors of a program's proof system

The errors of the soundness IOP (`GordieHowe.RealizedProgram.ProofSystem.soundIOP`) are `GordieHowe.RealizedProgram.ProofSystem.roundError`
(`GordieHowe.RealizedProgram.ProofSystem.error_soundIOP`), by round:

* **a phase's challenge round**: the sum over the phase's challenges of
  `Π_P₀`'s round error at the challenge (`GordieHowe.RealizedProgram.chalError`: `0` at a realization challenge, which
  is no round of `Π_P₀`) and the realization step's error at it
  (`GordieHowe.RealizedProgram.realError`, LogUp's `(N_g + T − 1)/(|F| − tmax)` per group at a table's `α`); the
  per-phase error is `GordieHowe.RealizedProgram.phaseError`, and the lowering's events have probability at most it
  (`GordieHowe.RealizedProgram.ProofSystem.eventBound_lowering`, through `GordieHowe.RealizedProgram.sum_chalPhase_eq`: the challenge rounds of
  `Π_P₀` of phase `k + 1` are the source challenges of the phase);
* **a domain's commit round**: the domain proof's commit-phase
  error;
* **a domain proof's round**: the domain proof's error (its masked row reduction's,
  then its commit-and-prove system's).

The soundness data of the soundness IOP (`GordieHowe.RealizedProgram.ProofSystem.soundIOPSound`) and its state function
(`GordieHowe.RealizedProgram.ProofSystem.stateFn`, not required to be efficient) are defined here.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP IOP.ProtocolSpec
open scoped NNReal

section

variable (ir : RealizedProgram) (I : Interp)

/-! ## The per-phase errors -/

/-- **`Π_P₀`'s round error at challenge `j`**: `ε` at the challenge round of `j`
(`RealizedProgram.chalIdx`), `0` for a challenge that is not a round of `Π_P₀` (a realization challenge,
or a challenge of no phase). -/
def chalError (ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0) (j : ℕ) : ℝ≥0 :=
  if h : ir.IsSourceChal j then ε (chalIdx (I := I) h) else 0

/-- **The error of phase `k + 1`**: the sum over its challenges of `Π_P₀`'s round error at the
challenge and the realization step's error at it. -/
noncomputable def phaseError (ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0) (k : Fin ir.phases) : ℝ≥0 :=
  ∑ jj : ir.ChalAt k, (ir.chalError I ε jj.1 + ir.realError I jj.1)

variable {ir I}

/-- **The phase of the challenge round of source challenge `j`** is `j`'s phase. -/
theorem chalPhase_chalIdx {j : ℕ} (hj : ir.IsSourceChal j) :
    ir.chalPhase I (chalIdx (I := I) hj) = (ir.challenge j).phase := by
  unfold chalPhase
  rw [show ir.rounds.get (chalIdx (I := I) hj).1 = .chal j from ir.get_pos _]

/-- **`Π_P₀`'s round error vanishes off its challenges.** -/
theorem chalError_of_not {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0} {j : ℕ}
    (hj : ¬ ir.IsSourceChal j) : ir.chalError I ε j = 0 :=
  dif_neg hj

/-- **The challenge rounds of `Π_P₀` of phase `k + 1` are the phase's source challenges**: the sum
of `ε` over them is the sum of `chalError ε` over the phase's challenges (`0` at the realization
challenges). -/
theorem sum_chalPhase_eq (ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0) (k : Fin ir.phases) :
    ∑ i ∈ Finset.univ.filter (fun i : (ir.sourceSpec I).ChallengeIdx => ir.chalPhase I i = k + 1),
      ε i = ∑ jj : ir.ChalAt k, ir.chalError I ε jj.1 := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun jj : ir.ChalAt k => ir.IsSourceChal jj.1)
    fun jj _ h => by_contra fun hj => h (chalError_of_not hj)]
  symm
  refine Finset.sum_bij (fun jj hjj => chalIdx (I := I) (Finset.mem_filter.1 hjj).2) ?_ ?_ ?_ ?_
  · intro jj hjj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [chalPhase_chalIdx]
    exact jj.2
  · intro a ha b hb hab
    have hpos : ir.pos (.chal a.1) = ir.pos (.chal b.1) :=
      congrArg (fun i : (ir.sourceSpec I).ChallengeIdx => (i.1 : ℕ)) hab
    have := ir.pos_injective (ir.chal_mem_rounds.2 (Finset.mem_filter.1 ha).2)
      (ir.chal_mem_rounds.2 (Finset.mem_filter.1 hb).2) hpos
    exact Subtype.ext (Fin.ext (Round.chal.inj this))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases chal_or_final i with ⟨j, hget, hj⟩ | hget
    · have hphase : (ir.challenge j).phase = k + 1 := by
        unfold chalPhase at hi
        rw [hget] at hi
        exact hi
      refine ⟨⟨⟨j, hj.1⟩, hphase⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
      refine Subtype.ext (Fin.ext ?_)
      change ir.pos (.chal j) = i.1
      rw [← hget, ir.pos_get]
    · unfold chalPhase at hi
      rw [hget] at hi
      exact absurd hi.symm (Nat.succ_ne_zero _)
  · intro jj hjj
    simp only [chalError, (Finset.mem_filter.1 hjj).2, ↓reduceDIte]

end

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)
  {W : Type} {rel : Set (ir.Valuation I × W)} {proj : ir.Valuation I → ir.Assignment I → W}
  {S : KnowledgeStateFunction (ir.sourceVerifier I)} {ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0}

open Classical in
/-- **The events of the soundness theorem's lowering have the phases' errors** (`phaseError`):
`Π_P₀`'s events at a phase have probability at most the sum of its challenge rounds' errors
(`eventBound_loweringOfRbr`, `sum_chalPhase_eq`), the realization step's the sum of its challenges'
`realError` (`eventBound_realizeSource`), the cells lowering none; errors add along the composite
(`Lowering.eventBound_comp`). -/
theorem eventBound_lowering (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    (B.lowering T ⟨_, h, hend⟩).EventBound (ir.phaseError I ε) := by
  have hc := Lowering.eventBound_comp
    (Lowering.eventBound_comp (B.eventBound_rbrRanged ⟨_, h, hend⟩
        (ir.eventBound_loweringOfRbr I B.source proj S h ⟨_, h, hend⟩))
      B.eventBound_realizeSource)
    (B.eventBound_cellsLowering T)
  rw [B.lowering_eq T ⟨_, h, hend⟩]
  intro k x b r
  refine (hc k x b r).trans (le_of_eq ?_)
  simp only [Pi.add_apply, Pi.zero_apply, add_zero, phaseError, Finset.sum_add_distrib,
    sum_chalPhase_eq]

/-- **The soundness of the soundness IOP**: the domain proofs' soundness `BS`, and the phases' errors
at their challenge rounds (`eventBound_lowering`). -/
noncomputable def soundIOPSound (BS : B.Sound) (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) : (B.soundIOP T h hend).Sound where
  circuitSound := BS
  appε := (ir.layout I).error (ir.phaseError I ε)
  appBound := Phased.eventBound_toAppPhase _
    (Lowering.eventBound_toPhased (Lowering.eventBound_check (B.eventBound_lowering T h hend)))

/-- **The state function of the proof system**: the soundness IOP's (`MultiCircuitIOP.stateFn`), on the
protocol's verifier (`verifier_eq`). Not required to be efficient. -/
noncomputable def stateFn [Inhabited W] (BS : B.Sound) (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) : KnowledgeStateFunction B.verifier :=
  (B.soundIOP T h hend).stateFn (B.soundIOPSound BS T h hend)

/-! ## The round errors -/

/-- **The round errors of the proof system** at the domain proofs' soundness `BS` and `Π_P₀`'s round
errors `ε`: every domain proof's
commit-phase errors at its commit rounds, the phases' errors (`phaseError`) at their challenge
rounds, then every domain proof's errors. -/
noncomputable def roundError (BS : B.Sound) (ε : (ir.sourceSpec I).ChallengeIdx → ℝ≥0) :
    B.spec.ChallengeIdx → ℝ≥0 :=
  B.protocol.app.fullError (fun d => (BS d).toShape) ((ir.layout I).error (ir.phaseError I ε))

/-- **The round errors of the soundness IOP are the proof system's.** -/
theorem error_soundIOP (BS : B.Sound) (T : B.CircuitsEnforce)
    (h : rbrKnowledgeSoundness rel (ir.sourceVerifier I) (ir.sourceExtractor I proj) S ε)
    (hend : ∀ i, ir.rounds.get i.1 = .final → ε i = 0) :
    (B.soundIOP T h hend).error (B.soundIOPSound BS T h hend) = B.roundError BS ε :=
  rfl

end ProofSystem

end GordieHowe.RealizedProgram
