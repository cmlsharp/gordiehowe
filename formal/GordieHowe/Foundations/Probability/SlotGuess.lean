-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Guessing a value computed from a coin that is read after the request

A run with law `L c` at a coin `c` drawn from `μ` outputs a request `rq` and a guess `F`. The
value `g r c` is computed from the request `r` and the coin. Assume the law of the request does not
depend on the coin (`h1`: the request is fixed before the coin is read). Also assume that, at a
fixed request `r`, the joint law of the request and the guess depends on the coin only through the
public value `φ r c` (`h2`). Then the guess equals `g rq c` with probability at most the best
guessing probability `⨆ r, ∑ y, ⨆ z, Pr_c[φ r c = y ∧ g r c = some z]`.

- `PMF.sum_toOuterMeasure_le_of_disjoint`: the masses of disjoint subsets of a set sum to at most
  the mass of the set.
- `PMF.toOuterMeasure_le_sum_of_subset`: the mass of a set covered by sets is at most the sum of
  their masses.
- `PMF.tsum_mul_toOuterMeasure_guess_le`: the bound.
-/

namespace PMF

open scoped ENNReal

/-- **The masses of pairwise disjoint subsets of `t` sum to at most the mass of `t`.** -/
theorem sum_toOuterMeasure_le_of_disjoint {Ω ι : Type*} [Fintype ι] (ν : PMF Ω) (s : ι → Set Ω)
    (t : Set Ω) (hd : ∀ ω i j, ω ∈ s i → ω ∈ s j → i = j) (ht : ∀ i, s i ⊆ t) :
    ∑ i, ν.toOuterMeasure (s i) ≤ ν.toOuterMeasure t := by
  simp only [toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ∃ i, ω ∈ s i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i (fun j _ hj => Set.indicator_of_notMem
      (fun hj' => hj (hd ω j i hj' hi)) _) (fun h => absurd (Finset.mem_univ i) h),
      Set.indicator_of_mem hi, Set.indicator_of_mem (ht i hi)]
  · push Not at h
    rw [Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (h i) _]
    exact bot_le

/-- **The mass of a set covered by sets is at most the sum of their masses.** -/
theorem toOuterMeasure_le_sum_of_subset {Ω ι : Type*} [Fintype ι] (ν : PMF Ω) (s : ι → Set Ω)
    (t : Set Ω) (ht : ∀ ω ∈ t, ∃ i, ω ∈ s i) :
    ν.toOuterMeasure t ≤ ∑ i, ν.toOuterMeasure (s i) := by
  classical
  simp only [toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases hω : ω ∈ t
  · obtain ⟨i, hi⟩ := ht ω hω
    rw [Set.indicator_of_mem hω]
    calc ν ω = (s i).indicator ν ω := (Set.indicator_of_mem hi _).symm
      _ ≤ ∑ j, (s j).indicator ν ω :=
        Finset.single_le_sum (f := fun j => (s j).indicator ν ω) (fun _ _ => bot_le)
          (Finset.mem_univ i)
  · rw [Set.indicator_of_notMem hω]
    exact bot_le

variable {C R Pb Z Ω : Type*} [Fintype C] [Fintype R] [Fintype Pb] [DecidableEq Pb] [Fintype Z]
  [DecidableEq Z]

/-- **Guessing a value computed from a coin read after the request** (module docstring): for a law
`μ` of the coin `c`, laws `L c` of the run, a request `rq` whose law does not depend on the coin
(`h1`), and a guess `F` whose joint law with the request `r` depends on the coin only through the
public value `φ r c` (`h2`), the probability that the guess is the value `g r c` at the request
`r` is at most `⨆ r, ∑ y, ⨆ z, Pr_c[φ r c = y ∧ g r c = some z]`. -/
theorem tsum_mul_toOuterMeasure_guess_le (μ : PMF C) (L : C → PMF Ω) (rq : Ω → Option R)
    (F : Ω → Option Z) (φ : R → C → Pb) (g : R → C → Option Z)
    (h1 : ∀ r c c', (L c).toOuterMeasure {ω | rq ω = some r} =
      (L c').toOuterMeasure {ω | rq ω = some r})
    (h2 : ∀ r z c c', φ r c = φ r c' →
      (L c).toOuterMeasure {ω | rq ω = some r ∧ F ω = some z} =
        (L c').toOuterMeasure {ω | rq ω = some r ∧ F ω = some z}) :
    ∑' c, μ c * (L c).toOuterMeasure
        {ω | ∃ r z, rq ω = some r ∧ g r c = some z ∧ F ω = some z} ≤
      ⨆ r, ∑ y, ⨆ z, μ.toOuterMeasure {c | φ r c = y ∧ g r c = some z} := by
  classical
  rcases isEmpty_or_nonempty C with hC | ⟨⟨c₀⟩⟩
  · simp
  -- the joint mass of a request and a guess
  set a : C → R → Z → ℝ≥0∞ := fun c r z =>
    (L c).toOuterMeasure {ω | rq ω = some r ∧ F ω = some z} with ha
  set γ : R → ℝ≥0∞ := fun r => ∑ y, ⨆ z, μ.toOuterMeasure {c | φ r c = y ∧ g r c = some z}
    with hγ
  set p : R → ℝ≥0∞ := fun r => (L c₀).toOuterMeasure {ω | rq ω = some r} with hp
  -- the event of one coin, by the request and the guess
  have hstep : ∀ c, (L c).toOuterMeasure
      {ω | ∃ r z, rq ω = some r ∧ g r c = some z ∧ F ω = some z} ≤
      ∑ r, ∑ z, (if g r c = some z then a c r z else 0) := by
    intro c
    refine (toOuterMeasure_le_sum_of_subset (L c) (fun q : R × Z => if g q.1 c = some q.2 then
        {ω | rq ω = some q.1 ∧ F ω = some q.2} else ∅) _ fun ω hω => ?_).trans (le_of_eq ?_)
    · obtain ⟨r, z, hr, hg, hF⟩ := hω
      refine ⟨(r, z), ?_⟩
      simp only [hg, ite_true]
      exact ⟨hr, hF⟩
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp [ha]
  -- the guesses at one request and one coin sum to at most the request's mass
  have hz : ∀ c r, ∑ z, a c r z ≤ p r := fun c r => by
    refine le_of_le_of_eq ?_ (h1 r c c₀)
    refine sum_toOuterMeasure_le_of_disjoint _ _ _ (fun ω z z' hz hz' => ?_) fun z ω hω => hω.1
    exact Option.some_injective _ (hz.2.symm.trans hz'.2)
  -- one request: the average over the coin by the fibers of the public value
  have hr : ∀ r, ∑ c, μ c * ∑ z, (if g r c = some z then a c r z else 0) ≤ p r * γ r := by
    intro r
    rw [← Finset.sum_fiberwise Finset.univ (φ r), hγ, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hne : ∃ c, φ r c = y
    · obtain ⟨c', hc'⟩ := hne
      have hfib : ∀ c ∈ Finset.univ.filter (fun c => φ r c = y), ∀ z, a c r z = a c' r z :=
        fun c hc z => h2 r z c c' ((Finset.mem_filter.1 hc).2.trans hc'.symm)
      calc ∑ c ∈ Finset.univ.filter (fun c => φ r c = y),
            μ c * ∑ z, (if g r c = some z then a c r z else 0)
          = ∑ z, a c' r z * ∑ c ∈ Finset.univ.filter (fun c => φ r c = y),
              (if g r c = some z then μ c else 0) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun c hc => ?_
            rw [hfib c hc z]
            split_ifs <;> simp [mul_comm]
        _ ≤ ∑ z, a c' r z * ⨆ z, μ.toOuterMeasure {c | φ r c = y ∧ g r c = some z} := by
            refine Finset.sum_le_sum fun z _ => mul_le_mul' le_rfl (le_iSup_of_le z (le_of_eq ?_))
            rw [toOuterMeasure_apply, tsum_fintype, Finset.sum_filter]
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases h1 : φ r c = y <;> by_cases h2 : g r c = some z <;>
              simp [Set.indicator, h1, h2]
        _ = (∑ z, a c' r z) * ⨆ z, μ.toOuterMeasure {c | φ r c = y ∧ g r c = some z} := by
            rw [Finset.sum_mul]
        _ ≤ p r * ⨆ z, μ.toOuterMeasure {c | φ r c = y ∧ g r c = some z} :=
            mul_le_mul' (hz c' r) le_rfl
    · push Not at hne
      rw [Finset.filter_false_of_mem fun c _ => hne c, Finset.sum_empty]
      exact bot_le
  -- the requests' masses sum to at most one
  have hp1 : ∑ r, p r ≤ 1 := by
    refine (sum_toOuterMeasure_le_of_disjoint (L c₀) (fun r => {ω | rq ω = some r}) Set.univ
      (fun ω r r' hr hr' => Option.some_injective _ (hr.symm.trans hr'))
      fun _ => Set.subset_univ _).trans ?_
    rw [toOuterMeasure_apply, Set.indicator_univ, tsum_coe]
  calc ∑' c, μ c * (L c).toOuterMeasure
        {ω | ∃ r z, rq ω = some r ∧ g r c = some z ∧ F ω = some z}
      ≤ ∑ c, μ c * ∑ r, ∑ z, (if g r c = some z then a c r z else 0) := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun c _ => mul_le_mul' le_rfl (hstep c)
    _ = ∑ r, ∑ c, μ c * ∑ z, (if g r c = some z then a c r z else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ r, p r * γ r := Finset.sum_le_sum fun r _ => hr r
    _ ≤ ∑ r, p r * ⨆ r, γ r := Finset.sum_le_sum fun r _ => mul_le_mul' le_rfl (le_iSup γ r)
    _ = (∑ r, p r) * ⨆ r, γ r := by rw [Finset.sum_mul]
    _ ≤ ⨆ r, γ r := by
        calc (∑ r, p r) * ⨆ r, γ r ≤ 1 * ⨆ r, γ r := mul_le_mul' hp1 le_rfl
          _ = ⨆ r, γ r := one_mul _

end PMF
