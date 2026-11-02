-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Basic
public import GordieHowe.Foundations.Probability.Probability

@[expose] public section

/-!
# Lemmas for Unruh's Prove experiment in the oracle-test gap lemma

Model-independent facts used for Unruh's Prove experiment in the oracle-test gap lemma
(`GordieHowe/SPBCS/OracleTest.lean`): two laws on `Option α` that agree on `some` are
equal; with blank logs the challenger's record is empty; an event and its complement have
probabilities summing to `1`.
-/

namespace GordieHowe.Quantum

/-- Two laws on `Option α` that agree on every `some a` are equal. -/
theorem pmf_eq_of_apply_some {α : Type*} [Fintype α] {p p' : PMF (Option α)}
    (h : ∀ a, p (some a) = p' (some a)) : p = p' := by
  have hsum : ∀ r : PMF (Option α), r none + ∑ a, r (some a) = 1 := fun r => by
    have h := r.tsum_coe
    rw [tsum_fintype] at h
    rw [← Fintype.sum_option]
    exact h
  have hfin : ∑ a, p (some a) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => PMF.apply_ne_top p _
  ext o
  cases o with
  | none =>
    have h1 := hsum p
    have h2 := hsum p'
    rw [Finset.sum_congr rfl fun a _ => h a] at h1
    exact (ENNReal.add_left_inj (by rwa [← Finset.sum_congr rfl fun a _ => h a])).1
      (h1.trans h2.symm)
  | some a => exact h a

/-- **With blank logs the challenger's record is empty**: no proof query was answered. -/
theorem Challenger.regState_blank {X Y Req Resp : Type} (C : Challenger X Y Req Resp)
    (ω : C.Coins) {m : ℕ} (ans : Fin m → List Y) :
    ∀ j, C.regState ω (fun _ => none) ans j = ⟨[], []⟩
  | 0 => rfl
  | j + 1 => by
    simp only [Challenger.regState_add_one, regState_blank C ω ans j]
    split_ifs <;> rfl

end GordieHowe.Quantum

namespace GordieHowe.IOP

/-- An event and its complement have probabilities summing to `1`. -/
theorem probUniform_add_not {C : Type*} [Fintype C] [Nonempty C] (E : C → Prop) :
    Pr[c ← C : E c] + Pr[c ← C : ¬ E c] = 1 := by
  rw [probUniform, probUniform, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_add]
  have h : ∀ c, {c | E c}.indicator (PMF.uniformOfFintype C) c +
      {c | ¬ E c}.indicator (PMF.uniformOfFintype C) c = PMF.uniformOfFintype C c := fun c => by
    by_cases hc : E c <;> simp [Set.indicator, hc]
  rw [tsum_congr h, PMF.tsum_coe]

end GordieHowe.IOP

