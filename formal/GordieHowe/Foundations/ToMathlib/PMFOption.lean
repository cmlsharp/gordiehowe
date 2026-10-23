-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Distributions on `Option α`

A distribution on `Option α` is determined by its values at `some a`: the mass at `none` is what
is left (`PMF.ext_of_some`). The statement is about Mathlib objects only and is a candidate for
upstreaming.
-/

open scoped ENNReal

namespace PMF

/-- **Two distributions on `Option α` that agree at every `some a` are equal**: the mass at
`none` is `1` minus the rest. -/
theorem ext_of_some {α : Type*} {p q : PMF (Option α)} (h : ∀ a, p (some a) = q (some a)) :
    p = q := by
  have hrest : (∑' x : Option α, @ite _ (x = none) (Classical.propDecidable _) 0 (p x)) =
      ∑' x : Option α, @ite _ (x = none) (Classical.propDecidable _) 0 (q x) :=
    tsum_congr fun x => by cases x <;> simp [h]
  have hp := p.tsum_coe
  have hq := q.tsum_coe
  rw [ENNReal.tsum_eq_add_tsum_ite none] at hp hq
  have hne : (∑' x : Option α, @ite _ (x = none) (Classical.propDecidable _) 0 (q x)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hq)
  ext x
  cases x with
  | none =>
    rw [hrest] at hp
    exact (ENNReal.add_left_inj hne).1 (hp.trans hq.symm)
  | some a => exact h a

end PMF
