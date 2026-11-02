-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.TPRun

@[expose] public section

/-!
# The aborting completion within the budget at one challenger and oracle

`AdaptiveIAlg.WithinBudget` quantifies over every challenger and every oracle. This file states
the statements of `GordieHowe/Model/Quantum/Interactive/TPRun.lean` that compare an adversary with
its aborting completion (`AdaptiveIAlg.abortAlg`) with the hypothesis at one challenger `C` and
one oracle `H`.

- `AdaptiveIAlg.WithinBudgetAt A C H`: the trace-preserving form ends with probability `0` against
  `C` at `H`. `WithinBudget.withinBudgetAt`: it follows from `WithinBudget`.
  `withinBudgetAt_of_outLaw_none`: it holds when the model's run terminates with probability one
  against `C` at `H`.
- `WithinBudgetAt.final_apply_eq_zero`: the trace-preserving form's final state vanishes on the
  ended branches against `C` at `H`.
- `WithinBudgetAt.final_composeBothOut_eq`: the model's composition and the trace-preserving
  form's have the same final state against `C` at `H`.
- `WithinBudgetAt.run_abortAlg`: the run of the aborting completion's trace-preserving form is
  the adversary's trace-preserving run placed along the lift.
- `WithinBudgetAt.final_composeBothOut_abortAlg`: the aborting completion's composition has the
  adversary's final state placed along the lift of the composed registers (`liftCW`).
- `Alg.toOuterMeasure_outLaw_eq`: an event of an algorithm's output has the sum of the final
  state's diagonal over the basis states whose output lies in it.
- `WithinBudgetAt.toOuterMeasure_outLaw_abortAlg`: an event of the aborting completion's composed
  registers has the probability of its preimage under the lift in the adversary's composition.
-/

open Finset Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace GordieHowe.Quantum

/-- **An event of an algorithm's output** has the sum, over the basis states whose output lies in
it, of the final state's diagonal. -/
theorem Alg.toOuterMeasure_outLaw_eq {X Y O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddGroup Y] (B : Alg X Y O) (H : X → Y) (P : O → Prop) [DecidablePred P] :
    (B.outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ENNReal.ofReal (∑ p, if P (B.out p.1) then (B.final H p p).re else 0) := by
  have hpsd := B.posSemidef_stage H B.depth
  have hd : ∀ p, 0 ≤ (B.final H p p).re := fun p =>
    (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := p))).1
  rw [Alg.outLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, tsum_fintype,
    Fintype.sum_option, ENNReal.ofReal_sum_of_nonneg fun p _ => by
      split_ifs
      · exact hd p
      · exact le_rfl]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_setOf_eq, Option.map_none, Option.mem_def,
    reduceCtorEq, false_and, exists_false, if_false, zero_add, Option.map_some, Option.some.injEq,
    exists_eq_left', basisLaw_some]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rfl
  · simp

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [Nonempty X] [AddGroup Y] [Nonempty Y]
  (C : Challenger X Y Req Resp) (H : X → Y)

/-- **The adversary stays within its budget against `C` at `H`**: its trace-preserving form ends
with probability `0` there (`WithinBudget` at one challenger and oracle). -/
def WithinBudgetAt : Prop :=
  (A.toTPKindAlg.composeBothOut C (A.endedFlag C)).outLaw H (some true) = 0

/-- An adversary within its budget is within its budget at every challenger and oracle. -/
theorem WithinBudget.withinBudgetAt {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} (hB : A.WithinBudget) :
    A.WithinBudgetAt C H :=
  hB C H

variable {A C H}

/-- **Within the budget at `C` and `H`, the trace-preserving form's final state vanishes on ended
branches** (`WithinBudget.final_apply_eq_zero` at one challenger and oracle). -/
theorem WithinBudgetAt.final_apply_eq_zero (hB : A.WithinBudgetAt C H) {O' : Type}
    (f : A.toKindAlg.CW C → O') {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y}
    (hp : p.1.1 ∉ A.aliveC C) : (A.toTPKindAlg.composeBothOut C f).final H p p = 0 := by
  have h := hB
  rw [WithinBudgetAt, Alg.outLaw] at h
  have h' := (map_basisLaw_apply_some _ _ _ _ true).symm.trans h
  rw [Finset.sum_eq_zero_iff] at h'
  have hp' := h' p (Finset.mem_univ _)
  have he : A.endedFlag C p.1.1 = true := by
    simpa [endedFlag, aliveC] using hp
  split_ifs at hp' with hc
  swap
  · exact absurd (congrArg some he.symm) hc
  exact (posSemidef_final C _ _ H).diag_eq_zero_of_re_nonpos (ENNReal.ofReal_eq_zero.1 hp')

/-- **Within the budget at `C` and `H`, the model's composition and the trace-preserving form's
have the same final state** (`WithinBudget.final_composeBothOut_eq` at one challenger and
oracle). -/
theorem WithinBudgetAt.final_composeBothOut_eq (hB : A.WithinBudgetAt C H) {O' : Type}
    (f : A.toKindAlg.CW C → O') :
    (A.toKindAlg.composeBothOut C f).final H = (A.toTPKindAlg.composeBothOut C f).final H := by
  ext p p'
  rw [final_composeBothOut_apply']
  split_ifs with h
  · rfl
  · have hpsd := posSemidef_final C A.toTPKindAlg f H
    rcases not_and_or.1 h with hp | hp
    · exact ((hpsd.apply_eq_zero_of_diag (hB.final_apply_eq_zero f hp) p').2).symm
    · exact ((hpsd.apply_eq_zero_of_diag (hB.final_apply_eq_zero f hp) p).1).symm

variable (A C H) in
/-- **A run that terminates with probability one at `C` and `H` is within the budget there**
(the converse direction of `withinBudget_iff` at one challenger and oracle). -/
theorem withinBudgetAt_of_outLaw_none (h : (A.compose C).outLaw H none = 0) :
    A.WithinBudgetAt C H := by
  classical
  let f : A.toKindAlg.CW C → O := fun v => A.toKindAlg.out v.adv.workspace
  set F := (A.toTPKindAlg.composeBothOut C f).final H
  have hF : F.PosSemidef := posSemidef_final C A.toTPKindAlg f H
  have hd : ∀ p, 0 ≤ (F p p).re := fun p => (Complex.nonneg_iff.1 (hF.diag_nonneg (i := p))).1
  have htr : ∑ p, (F p p).re = 1 := by
    have := (A.stepsTP_toTPKindAlg (freeze := false)).trace_final C f H
    simp only [Matrix.trace, Matrix.diag] at this
    simpa [Complex.re_sum] using congrArg Complex.re this
  have hG : 1 ≤ ∑ p, if p.1.1 ∈ A.aliveC C then (F p p).re else 0 := by
    have h0 := h
    rw [Alg.outLaw_none, ENNReal.ofReal_eq_zero, compose_eq_composeBothOut, Matrix.trace,
      Complex.re_sum] at h0
    have he : ∀ p, ((A.toKindAlg.composeBothOut C fun v => A.toKindAlg.out v.adv.workspace).final
        H p p).re = if p.1.1 ∈ A.aliveC C then (F p p).re else 0 := fun p => by
      rw [final_composeBothOut_apply']
      by_cases hp : p.1.1 ∈ A.aliveC C <;> simp [hp, F, f]
    simp only [Matrix.diag] at h0
    rw [Finset.sum_congr rfl fun p _ => he p] at h0
    linarith
  have hz : ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) = 0 := by
    have hsplit : ∀ p, (F p p).re = (if p.1.1 ∈ A.aliveC C then (F p p).re else 0) +
        (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) := fun p => by split_ifs <;> simp
    have : ∑ p, (F p p).re = ∑ p, (if p.1.1 ∈ A.aliveC C then (F p p).re else 0) +
        ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => hsplit p
    have hnn : 0 ≤ ∑ p, (if p.1.1 ∈ A.aliveC C then 0 else (F p p).re) :=
      Finset.sum_nonneg fun p _ => by split_ifs; exact le_rfl; exact hd p
    linarith
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => by
    split_ifs; exact le_rfl; exact hd p).1 hz
  rw [WithinBudgetAt, Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ true).trans (Finset.sum_eq_zero fun p _ => ?_)
  split_ifs with hc
  · have hp : p.1.1 ∉ A.aliveC C := by
      have : A.endedFlag C p.1.1 = true := (Option.some_inj.1 hc).symm
      simpa [endedFlag, aliveC] using this
    have := hz' p (Finset.mem_univ _)
    rw [if_neg hp] at this
    change ENNReal.ofReal (F p p).re = 0
    rw [this, ENNReal.ofReal_zero]
  · rfl

open ReprogrammedCircuit

/-- **Within the budget at `C` and `H`, the run of the aborting completion's form is the
trace-preserving form's run placed along the lift** (`WithinBudget.run_abortAlg` at one
challenger and oracle). -/
theorem WithinBudgetAt.run_abortAlg (hB : A.WithinBudgetAt C H) :
    (A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat =
      embed (liftQ (A.liftCW C))
        ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) := by
  obtain ⟨-, hT⟩ := (A.sim_fullCircBoth C).run H _ _ (A.invariant_counterInv.cutTo_initSys C)
    (A.cutTo_initSys_lift C)
  set run₁ := (A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat
  set run₂ := (A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat
  have htr₁ : run₁.trace = 1 := by
    rw [(A.stepsTP_toTPKindAlg.allTP_fullCircBoth C).trace_run H,
      (A.toTPKindAlg.initSys C).trace_eq_one]
  have htr₂ : run₂.trace = 1 := by
    rw [(A.abortAlg.stepsTP_toTPKindAlg.allTP_fullCircBoth C).trace_run H,
      (A.abortAlg.toTPKindAlg.initSys C).trace_eq_one]
  have hmodel : (A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat =
      cutTo (workIn (A.aliveC C)) run₁ := by
    rw [(A.intertwined_fullCircBoth C).run H, A.cutTo_initSys C]
    rfl
  have htrm : ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat).trace = 1 := by
    have h := congrArg Matrix.trace
      (hB.final_composeBothOut_eq (fun v => A.toKindAlg.out v.adv.workspace))
    rw [KindAlg.final_composeBothOut, KindAlg.final_composeBothOut, KindAlg.trace_withAnc,
      KindAlg.trace_withAnc] at h
    rw [h]
    exact htr₁
  have h₁ : cutTo (workIn (A.aliveC C)) run₁ = run₁ :=
    cutTo_eq_self_of_trace (posSemidef_run H _ (A.toTPKindAlg.initSys C).posSemidef)
      (by rw [← hmodel, htrm, htr₁])
  have h₁' : cutTo (workIn (A.toTPKindAlg.advIn C A.aliveW)) run₁ = run₁ := h₁
  rw [h₁'] at hT
  have h₂ : cutTo (workIn (A.abortAlg.toTPKindAlg.advIn C A.equalW)) run₂ = run₂ :=
    cutTo_eq_self_of_trace (posSemidef_run H _ (A.abortAlg.toTPKindAlg.initSys C).posSemidef)
      (by rw [hT, re_trace_embed (liftQ_injective (A.liftCW_injective C)), htr₁, htr₂])
  rw [← h₂, hT]

/-- **Within the budget at `C` and `H`, the aborting completion's composition has the adversary's
final state placed along the lift**, for any outputs read from the composed registers. -/
theorem WithinBudgetAt.final_composeBothOut_abortAlg (hB : A.WithinBudgetAt C H) {O' O'' : Type}
    (f : A.toKindAlg.CW C → O') (f' : A.abortAlg.toKindAlg.CW C → O'') :
    (A.abortAlg.toKindAlg.composeBothOut C f').final H =
      embed (liftR (A.liftCW C)) ((A.toKindAlg.composeBothOut C f).final H) := by
  have e₂ : (A.abortAlg.toKindAlg.composeBothOut C f').final H = withAnc KindAlg.x₀
      ((A.abortAlg.toTPKindAlg.fullCircBoth C).run H (A.abortAlg.toTPKindAlg.initSys C).mat) :=
    ((A.withinBudget_abortAlg.withinBudgetAt C H).final_composeBothOut_eq f').trans
      (KindAlg.final_composeBothOut C A.abortAlg.toTPKindAlg f' H)
  have e₁ : (A.toKindAlg.composeBothOut C f).final H = withAnc KindAlg.x₀
      ((A.toTPKindAlg.fullCircBoth C).run H (A.toTPKindAlg.initSys C).mat) :=
    (hB.final_composeBothOut_eq f).trans (KindAlg.final_composeBothOut C A.toTPKindAlg f H)
  rw [e₂, e₁, hB.run_abortAlg, withAnc_embed (A.liftCW_injective C)]

/-- **Within the budget at `C` and `H`, an event of the aborting completion's composed registers
has the probability of its preimage under the lift** in the adversary's composition. -/
theorem WithinBudgetAt.toOuterMeasure_outLaw_abortAlg (hB : A.WithinBudgetAt C H)
    (P : A.abortAlg.toKindAlg.CW C → Prop) [DecidablePred P] :
    ((A.abortAlg.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P (A.liftCW C v)} := by
  classical
  rw [Alg.toOuterMeasure_outLaw_eq, Alg.toOuterMeasure_outLaw_eq,
    hB.final_composeBothOut_abortAlg id id]
  congr 1
  have h := embed_diag_of_injective (liftR_injective (X := X) (Y := Y) (A.liftCW_injective C))
    ((A.toKindAlg.composeBothOut C id).final H) (fun p => if P p.1.1 then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at h
  exact h

end AdaptiveIAlg

end GordieHowe.Quantum
