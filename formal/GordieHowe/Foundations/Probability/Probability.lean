-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Probability of an event under a uniform draw

`Pr[c ← C : p c]` is the probability that `p c` holds for `c` drawn uniformly
from the finite nonempty type `C`:
`(PMF.uniformOfFintype C).toOuterMeasure {c | p c}`, valued in `ℝ≥0∞`.

The underlying object is that of VCVio (`eb0f6e4`), without depending on
it; VCVio writes the event as `Pr[ p | $ᵗ C]`. There `$ᵗ α` samples from a
`SampleableType`, whose distribution is
`𝒮[$ᵗ α] = liftM (PMF.uniformOfFintype α)`
(`VCVio/OracleComp/Constructions/SampleableType.lean:196`), and
`probEvent_uniformSample : Pr[ p | $ᵗ α] = #(univ.filter p) / card α` (`:203`)
is our `probUniform_eq_card_div`. In measure form,
`𝒟[$ᵗ C] S = (PMF.uniformOfFintype C).toMeasure S`, which is
`(PMF.uniformOfFintype C).toOuterMeasure S` on measurable sets
(`PMF.toMeasure_apply_eq_toOuterMeasure_apply`); every set is measurable for
the discrete σ-algebra on a finite type.

`card_le_iff_probUniform_le` converts to and from the counting form
`#(univ.filter p) ≤ ε · |C|` in `ℝ≥0` used by the round-by-round proofs.
-/

namespace GordieHowe.IOP

open scoped ENNReal NNReal BigOperators

/-- The probability that `p c` holds for `c` uniform in `C`. -/
noncomputable def probUniform (C : Type*) [Fintype C] [Nonempty C] (p : C → Prop) : ℝ≥0∞ :=
  (PMF.uniformOfFintype C).toOuterMeasure {c | p c}

/-- `Pr[c ← C : E c]`: the probability of the event `E c` for `c` drawn uniformly
from `C`, in the notation of a cryptographic experiment. -/
scoped syntax "Pr[" ident " ← " term " : " term "]" : term

scoped macro_rules
  | `(Pr[$c:ident ← $C : $E]) => `(probUniform $C fun $c => $E)

/-- The unfolding lemma: a uniform probability is a normalized count
(VCVio's `probEvent_uniformSample`). -/
theorem probUniform_eq_card_div (C : Type*) [Fintype C] [Nonempty C] (p : C → Prop)
    [DecidablePred p] :
    Pr[c ← C : p c] = ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card C := by
  rw [probUniform, PMF.toOuterMeasure_uniformOfFintype_apply]
  congr 2
  rw [Fintype.card_ofFinset]
  congr 1

/-- Counting form to and from probability form: at most `ε · |C|` elements
satisfy `p` exactly when `Pr[c ← C : p c] ≤ ε`. -/
theorem card_le_iff_probUniform_le (C : Type*) [Fintype C] [Nonempty C] (p : C → Prop)
    [DecidablePred p] (ε : ℝ≥0) :
    ((Finset.univ.filter p).card : ℝ≥0) ≤ ε * Fintype.card C ↔ Pr[c ← C : p c] ≤ ε := by
  rw [probUniform_eq_card_div, ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.coe_le_coe]
  push_cast
  rfl

/-- **A uniform draw read through a cast** has the law of a uniform draw: an event on the cast of
a uniform element of `α` has the probability of the event on a uniform element of `β`, for `α = β`.
-/
theorem probUniform_cast {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (h : α = β) (p : β → Prop) : Pr[a ← α : p (cast h a)] = Pr[b ← β : p b] := by
  subst h
  simp only [cast_eq]
  congr 1
  exact Subsingleton.elim _ _

/-- A uniform probability in `ℝ` as the uniform average of the indicator. -/
theorem toReal_probUniform {C : Type*} [Fintype C] [Nonempty C] (p : C → Prop) [DecidablePred p] :
    (Pr[c ← C : p c]).toReal = 𝔼 c, if p c then (1 : ℝ) else 0 := by
  rw [probUniform_eq_card_div, ENNReal.toReal_div, Fintype.expect_eq_sum_div_card]
  simp [Finset.sum_boole]

/-- A uniform probability on a product is the average over the first coordinate of the
probability on the second. -/
theorem probUniform_prod_eq_tsum {A C : Type} [Fintype A] [Nonempty A] [Fintype C] [Nonempty C]
    (p : A × C → Prop) :
    Pr[c ← (A × C) : p c] = ∑' a, PMF.uniformOfFintype A a * Pr[c ← C : p (a, c)] := by
  classical
  simp only [probUniform]
  rw [PMF.uniformOfFintype_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- **Products with equal sections**: if at every first coordinate the events on the second
coordinates have the same probability, the events on the products do. -/
theorem probUniform_prod_congr_snd {A C D : Type} [Fintype A] [Nonempty A] [Fintype C]
    [Nonempty C] [Fintype D] [Nonempty D] {p : A × C → Prop} {q : A × D → Prop}
    (h : ∀ a, Pr[c ← C : p (a, c)] = Pr[d ← D : q (a, d)]) :
    Pr[u ← (A × C) : p u] = Pr[u ← (A × D) : q u] := by
  rw [probUniform_prod_eq_tsum, probUniform_prod_eq_tsum]
  exact tsum_congr fun a => by rw [h a]

/-- **A bound averaged over a first coordinate**: if the probability on the second coordinate is
at most `c` at every first coordinate outside the event `bad`, the probability on the product is
at most `c` plus the probability of `bad`. -/
theorem probUniform_prod_le_add {A C : Type} [Fintype A] [Nonempty A] [Fintype C] [Nonempty C]
    (p : A × C → Prop) (bad : A → Prop) {c : ℝ≥0∞}
    (h : ∀ a, ¬ bad a → Pr[x ← C : p (a, x)] ≤ c) :
    Pr[x ← (A × C) : p x] ≤ c + Pr[a ← A : bad a] := by
  classical
  rw [probUniform_prod_eq_tsum]
  change _ ≤ c + (PMF.uniformOfFintype A).toOuterMeasure {a | bad a}
  rw [PMF.toOuterMeasure_apply]
  calc ∑' a, PMF.uniformOfFintype A a * Pr[x ← C : p (a, x)]
      ≤ ∑' a, (PMF.uniformOfFintype A a * c + {a | bad a}.indicator (PMF.uniformOfFintype A) a) :=
        ENNReal.tsum_le_tsum fun a => by
          by_cases ha : bad a
          · rw [Set.indicator_of_mem (show a ∈ {a | bad a} from ha)]
            calc PMF.uniformOfFintype A a * Pr[x ← C : p (a, x)]
                ≤ PMF.uniformOfFintype A a * 1 :=
                  by gcongr; exact PMF.toOuterMeasure_apply_le_one _ _
              _ ≤ _ := by rw [mul_one]; exact le_add_self
          · rw [Set.indicator_of_notMem (show a ∉ {a | bad a} from ha), add_zero]
            gcongr; exact h a ha
    _ = c + ∑' a, {a | bad a}.indicator (PMF.uniformOfFintype A) a := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

variable {C R V : Type} [Fintype C] [Nonempty C] in
/-- **The union bound for two events with bounds**: `Pr[p ∨ q] ≤ a + b` when `Pr[p] ≤ a` and
`Pr[q] ≤ b`. -/
theorem probUniform_or_le_add {p q : C → Prop} {a b : ℝ≥0} (hp : Pr[c ← C : p c] ≤ a)
    (hq : Pr[c ← C : q c] ≤ b) : Pr[c ← C : p c ∨ q c] ≤ ((a + b : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.coe_add]
  exact (MeasureTheory.measure_union_le {c | p c} {c | q c}).trans (add_le_add hp hq)

end GordieHowe.IOP
