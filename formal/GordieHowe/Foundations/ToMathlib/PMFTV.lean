-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Total variation distance for PMFs

Mathlib has no total variation distance for `PMF`. We define, on any type,

    tvDist p q = (∑' a, |p a - q a|) / 2

with the values read in `ℝ`, written `p ≈[ε] q` for `tvDist p q ≤ ε` (statistically
`ε`-close). It equals the one-sided excess `∑' a, (p a - q a)` (`tvDist_eq_toReal_tsum_tsub`), the
form the general proofs use; on a finite type it is the finite sum (`tvDist_eq_sum`). The facts the
zero-knowledge and witness-indistinguishability arguments use:

- metric facts: `tvDist_nonneg`, `tvDist_self`, `tvDist_comm`, `tvDist_triangle`,
  `tvDist_le_one`;
- the event form `abs_toOuterMeasure_sub_le_tvDist`: the two probabilities of any event differ by
  at most `tvDist p q`. Events are measured by `PMF.toOuterMeasure`, the form the `Pr[…]`
  notation of `GordieHowe/Foundations/Probability/Probability.lean` unfolds to;
- agreement outside an event: `tvDist_le_of_eq_of_notMem`, the distance is at most the
  average of the two probabilities of the event;
- data processing: `tvDist_map_le` and `tvDist_bind_right_le`;
- mixtures: `tvDist_bind_left_le`, and `tvDist_uniformOfFintype_bind_le` for a uniform mixing
  law, with the average written `𝔼 a, …` (Mathlib's `Finset.expect`);
- products: `PMF.pi`, the product of a family of PMFs over a finite index type, with
  `tvDist_pi_le` (the hybrid over coordinates) and `pi_uniformOfFintype`;
- disintegration: `IsDisintegration p φ k` says `k b` is the conditional law of `a ← p` given
  `φ a = b`; then `(a, φ a)` for `a ← p` and `(a, b)` for `b ← q`, `a ← k b` are at most
  `tvDist (p.map φ) q` apart (`IsDisintegration.tvDist_le`), and disintegrations of coordinates
  give one of the product (`IsDisintegration.pi`);
- mixtures of probabilities: `abs_toReal_tsum_mul_sub_le`, a pointwise bound on the difference
  of two families of probabilities bounds the difference of their averages under any PMF;
- normalized masses: `tvDist_le_sum_abs_sub_div_sum`, two PMFs obtained by normalizing
  nonnegative masses `p` and `s` are at most `∑ a, |p a - s a| / ∑ a, s a` apart;
- the collision bound `tvDist_uniformOfFintype_le`:
  `tvDist p uniform ≤ √(|α| · ∑ a, p a ^ 2 - 1) / 2`, by Cauchy–Schwarz, with
  `one_le_card_mul_sum_sq` for the radicand.

Everything here is about Mathlib objects only and is a candidate for upstreaming.
-/

open Finset
open scoped BigOperators

namespace Real

/-- Jensen's inequality for the square root under a uniform average, proved by Cauchy–Schwarz:
`𝔼 i, √(z i) ≤ √(𝔼 i, z i)` for nonnegative `z`. -/
theorem expect_sqrt_le_sqrt_expect {ι : Type*} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    𝔼 i, √(z i) ≤ √(𝔼 i, z i) := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) fun i => √(z i)
  simp only [one_mul, one_pow, Real.sq_sqrt (hz _)] at h
  refine (le_abs_self _).trans (Real.abs_le_sqrt (h.trans ?_))
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty]
  · rw [Fintype.expect_const, one_mul]

end Real

namespace PMF

variable {α β : Type*}

/-! ### Real values of a PMF -/

section Fintype

variable [Fintype α]

/-- The values of a PMF on a finite type sum to one in `ℝ≥0∞`. -/
theorem sum_coe (p : PMF α) : ∑ a, p a = 1 := by
  rw [← p.tsum_coe, tsum_fintype]

/-- The real values of a PMF on a finite type sum to one. -/
theorem sum_toReal (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun a _ => p.apply_ne_top a, sum_coe, ENNReal.toReal_one]

/-- The probability of an event, in `ℝ`, as a sum over the event. -/
theorem toReal_toOuterMeasure_apply (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    (p.toOuterMeasure s).toReal = ∑ a, if a ∈ s then (p a).toReal else 0 := by
  rw [toOuterMeasure_apply_fintype, ENNReal.toReal_sum fun a _ => ?_]
  · simp only [Set.indicator_apply]
    exact sum_congr rfl fun a _ => by split_ifs <;> simp
  · simp only [Set.indicator_apply]
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top

/-- A value of `p.bind k`, in `ℝ`. -/
theorem toReal_bind_apply (p : PMF α) (k : α → PMF β) (b : β) :
    (p.bind k b).toReal = ∑ a, (p a).toReal * (k a b).toReal := by
  rw [bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)]
  simp only [ENNReal.toReal_mul]

/-- A value of `p.map f`, in `ℝ`: the mass of the preimage. -/
theorem toReal_map_apply (p : PMF α) (f : α → β) [DecidableEq β] (b : β) :
    (p.map f b).toReal = ∑ a, if f a = b then (p a).toReal else 0 := by
  rw [← bind_pure_comp, toReal_bind_apply]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : f a = b
  · simp [h]
  · simp [h, pure_apply, Ne.symm h]

end Fintype

/-- A value of the uniform PMF, in `ℝ`. -/
theorem toReal_uniformOfFintype_apply [Fintype α] [Nonempty α] (a : α) :
    (uniformOfFintype α a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  simp [uniformOfFintype_apply]

/-! ### Total variation distance -/

section TV

/-! ### The distance on any type -/

/-- The probability of an event is at most one. -/
theorem toOuterMeasure_apply_le_one (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 := by
  rw [toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum (Set.indicator_le_self s p)


/-- The total variation distance between two PMFs: `(∑' a, |p a - q a|) / 2`, with the values
read in `ℝ`. It is defined on any type; on a finite type the sum is finite (`tvDist_eq_sum`). -/
noncomputable def tvDist (p q : PMF α) : ℝ :=
  (∑' a, |(p a).toReal - (q a).toReal|) / 2

/-- `μ ≈[ε] ν`: the total variation distance between `μ` and `ν` is at most `ε`. -/
notation:50 μ:51 " ≈[" ε "] " ν:51 => PMF.tvDist μ ν ≤ ε

/-- The one-sided excess `∑' a, (p a - q a)` (truncated subtraction) is at most one. -/
theorem tsum_tsub_le_one (p q : PMF α) : ∑' a, (p a - q a) ≤ 1 :=
  (ENNReal.tsum_le_tsum fun _ => tsub_le_self).trans_eq p.tsum_coe

theorem tsum_tsub_ne_top (p q : PMF α) : ∑' a, (p a - q a) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_tsub_le_one p q)

/-- The two one-sided excesses are equal, since both laws have total mass one. -/
theorem tsum_tsub_comm (p q : PMF α) : ∑' a, (p a - q a) = ∑' a, (q a - p a) := by
  have hp : ∑' a, (p a - q a) + ∑' a, min (p a) (q a) = 1 := by
    rw [← ENNReal.tsum_add, ← p.tsum_coe]
    exact tsum_congr fun a => tsub_add_min
  have hq : ∑' a, (q a - p a) + ∑' a, min (p a) (q a) = 1 := by
    rw [← ENNReal.tsum_add, ← q.tsum_coe]
    exact tsum_congr fun a => by rw [min_comm]; exact tsub_add_min
  have hm : ∑' a, min (p a) (q a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((ENNReal.tsum_le_tsum fun a => min_le_left _ _).trans_eq p.tsum_coe)
  exact (ENNReal.add_left_inj hm).1 (hp.trans hq.symm)

/-- **The distance as a one-sided excess**: `tvDist p q = ∑' a, (p a - q a)`, read in `ℝ`. -/
theorem tvDist_eq_toReal_tsum_tsub (p q : PMF α) : tvDist p q = (∑' a, (p a - q a)).toReal := by
  have hpt : ∀ a, p a ≠ ⊤ := fun a => p.apply_ne_top a
  have hqt : ∀ a, q a ≠ ⊤ := fun a => q.apply_ne_top a
  have hpt' : ∀ a, (p a - q a + (q a - p a)) ≠ ⊤ := fun a =>
    ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top (hpt a) tsub_le_self,
      ne_top_of_le_ne_top (hqt a) tsub_le_self⟩
  have habs : ∀ a, |(p a).toReal - (q a).toReal| = (p a - q a + (q a - p a)).toReal := by
    intro a
    rcases le_total (p a) (q a) with h | h
    · rw [tsub_eq_zero_of_le h, zero_add, ENNReal.toReal_sub_of_le h (hqt a),
        abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (hqt a) h))]
    · rw [tsub_eq_zero_of_le h, add_zero, ENNReal.toReal_sub_of_le h (hpt a),
        abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono (hpt a) h))]
  rw [tvDist, tsum_congr habs, ← ENNReal.tsum_toReal_eq hpt', ENNReal.tsum_add,
    ← tsum_tsub_comm, ← two_mul, ENNReal.toReal_mul]
  simp

theorem tvDist_nonneg (p q : PMF α) : 0 ≤ tvDist p q := by
  rw [tvDist_eq_toReal_tsum_tsub]
  exact ENNReal.toReal_nonneg

@[simp] theorem tvDist_self (p : PMF α) : tvDist p p = 0 := by
  simp [tvDist_eq_toReal_tsum_tsub]

theorem tvDist_comm (p q : PMF α) : tvDist p q = tvDist q p := by
  rw [tvDist_eq_toReal_tsum_tsub, tvDist_eq_toReal_tsum_tsub, tsum_tsub_comm]

theorem tvDist_triangle (p q r : PMF α) : tvDist p r ≤ tvDist p q + tvDist q r := by
  simp only [tvDist_eq_toReal_tsum_tsub]
  rw [← ENNReal.toReal_add (tsum_tsub_ne_top p q) (tsum_tsub_ne_top q r)]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨tsum_tsub_ne_top p q, tsum_tsub_ne_top q r⟩) ?_
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => tsub_le_tsub_add_tsub

theorem tvDist_le_one (p q : PMF α) : tvDist p q ≤ 1 := by
  rw [tvDist_eq_toReal_tsum_tsub]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using tsum_tsub_le_one p q)

/-- The probability of an event under `p` exceeds that under `q` by at most the excess. -/
theorem toOuterMeasure_le_add_tsum_tsub (p q : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ q.toOuterMeasure s + ∑' a, (p a - q a) := by
  rw [toOuterMeasure_apply, toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    exact le_add_tsub
  · simp [Set.indicator_of_notMem ha]

/-- **Event form**: the probabilities of an event under `p` and `q` differ by at most
`tvDist p q`. -/
theorem abs_toOuterMeasure_sub_le_tvDist (p q : PMF α) (s : Set α) :
    |(p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal| ≤ tvDist p q := by
  have hpq := toOuterMeasure_le_add_tsum_tsub p q s
  have hqp := toOuterMeasure_le_add_tsum_tsub q p s
  rw [← tsum_tsub_comm] at hqp
  have hP := ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one p s)
  have hQ := ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one q s)
  have h1 := (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hQ, tsum_tsub_ne_top p q⟩) hpq).trans_eq
    (ENNReal.toReal_add hQ (tsum_tsub_ne_top p q))
  have h2 := (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hP, tsum_tsub_ne_top p q⟩) hqp).trans_eq
    (ENNReal.toReal_add hP (tsum_tsub_ne_top p q))
  rw [tvDist_eq_toReal_tsum_tsub, abs_le]
  constructor <;> linarith

/-- The excess is at most the probability of an event outside which the laws agree. -/
theorem tsum_tsub_le_of_eq_of_notMem (p q : PMF α) (s : Set α) (h : ∀ a ∉ s, p a = q a) :
    ∑' a, (p a - q a) ≤ p.toOuterMeasure s := by
  rw [toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    exact tsub_le_self
  · simp [Set.indicator_of_notMem ha, h a ha]

/-- Two PMFs that agree outside the event `s` are at total variation distance at most the
probability of `s` under the first. -/
theorem tvDist_le_toOuterMeasure_of_eq_of_notMem (p q : PMF α) (s : Set α)
    (h : ∀ a ∉ s, p a = q a) : tvDist p q ≤ (p.toOuterMeasure s).toReal := by
  rw [tvDist_eq_toReal_tsum_tsub]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one p s))
    (tsum_tsub_le_of_eq_of_notMem p q s h)

/-- Two PMFs that agree outside the event `s` are at total variation distance at most the
average of their probabilities of `s`. -/
theorem tvDist_le_of_eq_of_notMem (p q : PMF α) (s : Set α) (h : ∀ a ∉ s, p a = q a) :
    tvDist p q ≤ ((p.toOuterMeasure s).toReal + (q.toOuterMeasure s).toReal) / 2 := by
  have hP := ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one p s)
  have hQ := ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one q s)
  have h1 : tvDist p q ≤ (p.toOuterMeasure s).toReal := by
    rw [tvDist_eq_toReal_tsum_tsub]
    exact ENNReal.toReal_mono hP (tsum_tsub_le_of_eq_of_notMem p q s h)
  have h2 : tvDist p q ≤ (q.toOuterMeasure s).toReal := by
    rw [tvDist_comm, tvDist_eq_toReal_tsum_tsub]
    exact ENNReal.toReal_mono hQ (tsum_tsub_le_of_eq_of_notMem q p s fun a ha => (h a ha).symm)
  linarith

/-- **Data processing** for a kernel: `tvDist (p.bind k) (q.bind k) ≤ tvDist p q`. -/
theorem tvDist_bind_right_le (p q : PMF α) (k : α → PMF β) :
    tvDist (p.bind k) (q.bind k) ≤ tvDist p q := by
  simp only [tvDist_eq_toReal_tsum_tsub]
  refine ENNReal.toReal_mono (tsum_tsub_ne_top p q) ?_
  calc ∑' b, ((p.bind k) b - (q.bind k) b)
      ≤ ∑' b, ∑' a, (p a - q a) * k a b := by
        refine ENNReal.tsum_le_tsum fun b => tsub_le_iff_left.2 ?_
        simp only [bind_apply]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [← add_mul]
        gcongr
        exact le_add_tsub
    _ = ∑' a, (p a - q a) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun a => by rw [ENNReal.tsum_mul_left, (k a).tsum_coe, mul_one]

/-- **Data processing** for a function: `tvDist (p.map f) (q.map f) ≤ tvDist p q`. -/
theorem tvDist_map_le (p q : PMF α) (f : α → β) :
    tvDist (p.map f) (q.map f) ≤ tvDist p q := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact tvDist_bind_right_le p q _

/-- **Mixtures**: mixing two kernels by the same law costs at most the average distance. -/
theorem tvDist_bind_left_le' (p : PMF α) (k₁ k₂ : α → PMF β) :
    tvDist (p.bind k₁) (p.bind k₂) ≤ ∑' a, (p a).toReal * tvDist (k₁ a) (k₂ a) := by
  have hfin : ∀ a, p a * ∑' b, (k₁ a b - k₂ a b) ≠ ⊤ := fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) (tsum_tsub_ne_top _ _)
  simp only [tvDist_eq_toReal_tsum_tsub]
  simp_rw [← ENNReal.toReal_mul]
  rw [← ENNReal.tsum_toReal_eq hfin]
  refine ENNReal.toReal_mono ?_ ?_
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    refine (ENNReal.tsum_le_tsum fun a => mul_le_of_le_one_right' (tsum_tsub_le_one _ _)).trans_eq
      p.tsum_coe
  calc ∑' b, ((p.bind k₁) b - (p.bind k₂) b)
      ≤ ∑' b, ∑' a, p a * (k₁ a b - k₂ a b) := by
        refine ENNReal.tsum_le_tsum fun b => tsub_le_iff_left.2 ?_
        simp only [bind_apply]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [← mul_add]
        gcongr
        exact le_add_tsub
    _ = ∑' a, p a * ∑' b, (k₁ a b - k₂ a b) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun a => ENNReal.tsum_mul_left

/-- **Abstraction** of `abs_tvDist_sub_tvDist_le` and the metric facts: distances to a third law
differ by at most the distance between the two laws. -/
theorem abs_tvDist_sub_tvDist_le (p q r : PMF α) :
    |tvDist p r - tvDist q r| ≤ tvDist p q := by
  rw [abs_le]
  constructor
  · linarith [tvDist_triangle q p r, tvDist_comm p q]
  · linarith [tvDist_triangle p q r]

/-- **An average along a map with a uniform image**: if `p.map φ` is uniform on a finite type,
the `p`-average of `f ∘ φ` is the uniform average of `f`, for `f ≥ 0`. -/
theorem tsum_toReal_mul_comp_eq_expect [Fintype β] [Nonempty β] (p : PMF α) (φ : α → β)
    (hφ : p.map φ = uniformOfFintype β) {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑' a, (p a).toReal * f (φ a) = 𝔼 b, f b := by
  have hterm : ∀ a, (p a).toReal * f (φ a) = (p a * ENNReal.ofReal (f (φ a))).toReal := fun a => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf _)]
  have hfin : ∀ a, p a * ENNReal.ofReal (f (φ a)) ≠ ⊤ := fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ENNReal.ofReal_ne_top
  have hmap' : ∑' a, p a * ENNReal.ofReal (f (φ a)) =
      ∑' b, (p.map φ) b * ENNReal.ofReal (f b) := by
    simp_rw [map_apply, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun a => ?_
    rw [tsum_eq_single (φ a) fun b hb => by simp [hb]]
    simp
  have hmap : ∑' a, p a * ENNReal.ofReal (f (φ a)) =
      ∑ b, uniformOfFintype β b * ENNReal.ofReal (f b) := by
    rw [hmap', hφ, tsum_fintype]
  rw [tsum_congr hterm, ← ENNReal.tsum_toReal_eq hfin, hmap, ENNReal.toReal_sum fun b _ =>
    ENNReal.mul_ne_top (apply_ne_top _ _) ENNReal.ofReal_ne_top, Fintype.expect_eq_sum_div_card,
    sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf b), toReal_uniformOfFintype_apply, inv_mul_eq_div]

/-- Averages under a PMF are monotone, for nonnegative functions bounded by a constant. -/
theorem tsum_toReal_mul_le_tsum_toReal_mul (p : PMF α) {f g : α → ℝ} {C : ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hfg : ∀ a, f a ≤ g a) (hgC : ∀ a, g a ≤ C) :
    ∑' a, (p a).toReal * f a ≤ ∑' a, (p a).toReal * g a := by
  have hp : Summable fun a => (p a).toReal := ENNReal.summable_toReal (by simp [p.tsum_coe])
  have hC : Summable fun a => (p a).toReal * C := hp.mul_right C
  have hg : Summable fun a => (p a).toReal * g a := hC.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg ((hf0 a).trans (hfg a)))
    (fun a => mul_le_mul_of_nonneg_left (hgC a) ENNReal.toReal_nonneg)
  have hf : Summable fun a => (p a).toReal * f a := hg.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (hf0 a))
    (fun a => mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg)
  exact hf.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg) hg

/-! ### Finite types -/

/-- On a finite type the distance is a finite sum. -/
theorem tvDist_eq_sum [Fintype α] (p q : PMF α) :
    tvDist p q = (∑ a, |(p a).toReal - (q a).toReal|) / 2 := by
  rw [tvDist, tsum_fintype]

/-- **Mixtures** over a finite mixing type: at most the average distance. -/
theorem tvDist_bind_left_le [Fintype α] (p : PMF α) (k₁ k₂ : α → PMF β) :
    tvDist (p.bind k₁) (p.bind k₂) ≤ ∑ a, (p a).toReal * tvDist (k₁ a) (k₂ a) :=
  (tvDist_bind_left_le' p k₁ k₂).trans_eq (tsum_fintype _)

variable [Fintype α]

/-- **Mixtures** under a uniform mixing law: at most the uniform average of the distances. -/
theorem tvDist_uniformOfFintype_bind_le [Nonempty α] [Fintype β] (k₁ k₂ : α → PMF β) :
    tvDist ((uniformOfFintype α).bind k₁) ((uniformOfFintype α).bind k₂) ≤
      𝔼 a, tvDist (k₁ a) (k₂ a) := by
  refine (tvDist_bind_left_le _ _ _).trans_eq ?_
  rw [Fintype.expect_eq_sum_div_card, sum_div]
  exact sum_congr rfl fun a _ => by rw [toReal_uniformOfFintype_apply, inv_mul_eq_div]

/-- **Collision bound**, radicand: `1 ≤ |α| · ∑ a, p a ^ 2` (Cauchy–Schwarz). -/
theorem one_le_card_mul_sum_sq (p : PMF α) :
    1 ≤ Fintype.card α * ∑ a, (p a).toReal ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) fun a => (p a).toReal
  simpa [sum_toReal] using h

/-- **Collision bound**: the distance of `p` from uniform is at most
`√(|α| · ∑ a, p a ^ 2 - 1) / 2`, by Cauchy–Schwarz on the deviations `p a - 1 / |α|`. -/
theorem tvDist_uniformOfFintype_le [Nonempty α] (p : PMF α) :
    tvDist p (uniformOfFintype α) ≤
      √(Fintype.card α * ∑ a, (p a).toReal ^ 2 - 1) / 2 := by
  rw [tvDist_eq_sum]
  gcongr ?_ / 2
  simp_rw [toReal_uniformOfFintype_apply]
  set n : ℝ := (Fintype.card α : ℝ) with hn
  have hn0 : n ≠ 0 := by simp [hn]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) fun a => |(p a).toReal - n⁻¹|
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hdev : n * ∑ a, ((p a).toReal - n⁻¹) ^ 2 = n * ∑ a, (p a).toReal ^ 2 - 1 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_toReal,
      sum_const, card_univ, nsmul_eq_mul]
    rw [← hn]
    field_simp
    ring
  rw [← hn, hdev] at hcs
  exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)

/-- **Two maps of one law**: `tvDist (p.map f) (p.map g)` is at most the probability that `f`
and `g` differ. -/
theorem tvDist_map_map_le [Fintype β] [DecidableEq β] (p : PMF α) (f g : α → β) :
    tvDist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  classical
  rw [tvDist_eq_sum, toReal_toOuterMeasure_apply, div_le_iff₀ zero_lt_two]
  calc ∑ b, |((p.map f) b).toReal - ((p.map g) b).toReal|
      = ∑ b, |∑ a, (p a).toReal * ((if f a = b then 1 else 0) - (if g a = b then 1 else 0))| := by
        refine sum_congr rfl fun b _ => ?_
        rw [toReal_map_apply, toReal_map_apply, ← sum_sub_distrib]
        congr 1
        refine sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ b, ∑ a, (p a).toReal *
          |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)| := by
        gcongr with b
        exact (abs_sum_le_sum_abs _ _).trans_eq
          (sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg])
    _ = ∑ a, (p a).toReal *
          ∑ b, |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)| := by
        rw [sum_comm]
        simp_rw [mul_sum]
    _ = ∑ a, (if a ∈ {a | f a ≠ g a} then (p a).toReal else 0) * 2 := by
        refine sum_congr rfl fun a _ => ?_
        by_cases h : f a = g a
        · simp [h]
        · have : ∑ b, |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)| = 2 := by
            rw [← sum_erase_add _ _ (mem_univ (f a)), ← sum_erase_add _ _
              (mem_erase.2 ⟨Ne.symm h, mem_univ (g a)⟩)]
            rw [sum_eq_zero fun b hb => by
              simp [Ne.symm (mem_erase.1 hb).1, Ne.symm (mem_erase.1 (mem_erase.1 hb).2).1]]
            simp [h, Ne.symm h]
            norm_num
          simp [h, this]
    _ = _ := by rw [sum_mul]

end TV

/-- The uniform law on a product: a uniform first component, then a uniform second one. -/
theorem uniformOfFintype_prod_eq_bind {γ : Type*} [Fintype β] [Nonempty β] [Fintype γ]
    [Nonempty γ] :
    uniformOfFintype (β × γ) =
      (uniformOfFintype β).bind fun b => (uniformOfFintype γ).map (Prod.mk b) := by
  classical
  ext ⟨b, c⟩
  rw [bind_apply, tsum_eq_single b fun b' hb' => by
    rw [map_apply, ENNReal.tsum_eq_zero.2 fun c' => by simp [Ne.symm hb'], mul_zero]]
  rw [map_apply, tsum_eq_single c fun c' hc' => by simp [Ne.symm hc']]
  simp [uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv]

/-! ### Products over a finite index type -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- The product of a family of PMFs over a finite index type: the law of independent
coordinates, `pi p f = ∏ i, p i (f i)`. -/
noncomputable def pi (p : ∀ i, PMF (β i)) : PMF (∀ i, β i) :=
  ofFintype (fun f : ∀ i, β i => ∏ i, p i (f i)) (by rw [← Fintype.prod_sum]; simp [sum_coe])

theorem pi_apply (p : ∀ i, PMF (β i)) (f : ∀ i, β i) : pi p f = ∏ i, p i (f i) := rfl

theorem toReal_pi_apply (p : ∀ i, PMF (β i)) (f : ∀ i, β i) :
    (pi p f).toReal = ∏ i, (p i (f i)).toReal := by
  rw [pi_apply, ENNReal.toReal_prod]

/-- The product of uniform laws is the uniform law on the product. -/
theorem pi_uniformOfFintype [∀ i, Nonempty (β i)] :
    pi (fun i => uniformOfFintype (β i)) = uniformOfFintype (∀ i, β i) := by
  ext f
  rw [pi_apply, uniformOfFintype_apply]
  simp only [uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib fun i _ j _ _ => Or.inr (ENNReal.natCast_ne_top _)]

/-- Mapping each coordinate of a product separately gives the product of the mapped laws. -/
theorem pi_map {γ : ι → Type*} [∀ i, Fintype (γ i)] (p : ∀ i, PMF (β i))
    (g : ∀ i, β i → γ i) :
    (pi p).map (fun f i => g i (f i)) = pi fun i => (p i).map (g i) := by
  classical
  ext x
  simp only [map_apply, tsum_fintype, pi_apply]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

/-- **Coordinates a function ignores**: if `F` reads only the coordinates in `S`, and `κ` and
`κ'` agree on `S`, then pushing `pi κ` and `pi κ'` through `F` gives the same law. -/
theorem pi_map_eq_of_eqOn {γ : Type*} [∀ i, Inhabited (β i)] (κ κ' : ∀ i, PMF (β i))
    (S : Finset ι) (hκ : ∀ i ∈ S, κ i = κ' i) (F : (∀ i, β i) → γ)
    (hF : ∀ f f' : ∀ i, β i, (∀ i ∈ S, f i = f' i) → F f = F f') :
    (pi κ).map F = (pi κ').map F := by
  classical
  let g : ∀ i, β i → β i := fun i b => if i ∈ S then b else default
  have hFg : F = F ∘ fun f i => g i (f i) := funext fun f => hF _ _ fun i hi => by simp [g, hi]
  rw [hFg, ← map_comp, ← map_comp, pi_map, pi_map]
  congr 2
  funext i
  by_cases hi : i ∈ S
  · rw [hκ i hi]
  · have : g i = fun _ => default := funext fun b => by simp [g, hi]
    rw [this]
    exact (map_const (κ i) default).trans (map_const (κ' i) default).symm

/-- The hybrid argument over coordinates, for real weights: if every `a i` and `b i` is a
nonnegative family summing to one, then `∑ f, |∏ i, a i (f i) - ∏ i, b i (f i)|` is at most
`∑ i, ∑ x, |a i x - b i x|`. -/
theorem sum_abs_prod_sub_prod_le (a b : ∀ i, β i → ℝ) (ha : ∀ i x, 0 ≤ a i x)
    (hb : ∀ i x, 0 ≤ b i x) (ha1 : ∀ i, ∑ x, a i x = 1) (hb1 : ∀ i, ∑ x, b i x = 1) :
    ∑ f : ∀ i, β i, |∏ i, a i (f i) - ∏ i, b i (f i)| ≤ ∑ i, ∑ x, |a i x - b i x| := by
  let h : Finset ι → (∀ i, β i) → ℝ := fun s f => ∏ i, if i ∈ s then a i (f i) else b i (f i)
  suffices key : ∀ s : Finset ι,
      ∑ f, |h s f - h ∅ f| ≤ ∑ i ∈ s, ∑ x, |a i x - b i x| by
    simpa [h] using key univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    -- one step of the hybrid changes coordinate `j` only
    let c : ∀ i, β i → ℝ := fun i x => if i ∈ s then a i x else b i x
    let g : ∀ i, β i → ℝ := fun i x => if i = j then |a i x - b i x| else c i x
    have hc : ∀ i x, 0 ≤ c i x := fun i x => by
      simp only [c]
      split_ifs
      exacts [ha i x, hb i x]
    have hrest : ∀ f : ∀ i, β i, ∀ i ∈ univ.erase j,
        (if i ∈ insert j s then a i (f i) else b i (f i)) = c i (f i) := fun f i hi => by
      simp [c, ne_of_mem_erase hi]
    have hstep : ∀ f : ∀ i, β i, |h (insert j s) f - h s f| = ∏ i, g i (f i) := fun f => by
      have e1 : h (insert j s) f = a j (f j) * ∏ i ∈ univ.erase j, c i (f i) := by
        simp only [h]
        rw [← mul_prod_erase univ _ (mem_univ j), prod_congr rfl (hrest f)]
        simp
      have e2 : h s f = b j (f j) * ∏ i ∈ univ.erase j, c i (f i) := by
        simp only [h]
        rw [← mul_prod_erase univ _ (mem_univ j)]
        simp [hj, c]
      have e3 : ∏ i, g i (f i) = |a j (f j) - b j (f j)| * ∏ i ∈ univ.erase j, c i (f i) := by
        rw [← mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp [g]
        · exact prod_congr rfl fun i hi => by simp [g, ne_of_mem_erase hi]
      rw [e1, e2, e3, ← sub_mul, abs_mul, abs_of_nonneg (prod_nonneg fun i _ => hc i (f i))]
    have hstep_sum : ∑ f, |h (insert j s) f - h s f| = ∑ x, |a j x - b j x| := by
      simp_rw [hstep]
      rw [← Fintype.prod_sum, ← mul_prod_erase univ _ (mem_univ j)]
      rw [prod_eq_one fun i hi => ?_]
      · simp [g]
      · have hij : i ≠ j := ne_of_mem_erase hi
        simp only [g, hij, ite_false, c]
        split_ifs
        exacts [ha1 i, hb1 i]
    calc ∑ f, |h (insert j s) f - h ∅ f|
        ≤ ∑ f, (|h (insert j s) f - h s f| + |h s f - h ∅ f|) :=
          sum_le_sum fun f _ => abs_sub_le _ _ _
      _ ≤ ∑ i ∈ insert j s, ∑ x, |a i x - b i x| := by
          rw [sum_add_distrib, hstep_sum, sum_insert hj]
          gcongr

/-- **Products**: the distance between two product laws is at most the sum of the coordinate
distances. -/
theorem tvDist_pi_le (p q : ∀ i, PMF (β i)) :
    tvDist (pi p) (pi q) ≤ ∑ i, tvDist (p i) (q i) := by
  simp only [tvDist_eq_sum]
  rw [← sum_div]
  gcongr ?_ / 2
  simp only [toReal_pi_apply]
  exact sum_abs_prod_sub_prod_le (fun i x => (p i x).toReal) (fun i x => (q i x).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => ENNReal.toReal_nonneg) (fun i => sum_toReal _) fun i => sum_toReal _

end Pi

/-! ### Disintegration along a function -/

section Disintegration

variable {γ : Type*}

/-- `k` is a disintegration of `p` along `φ`: for every `b` with `p.map φ b ≠ 0`, `k b` is the
conditional law of `a ← p` given `φ a = b`. Stated without division:
`p.map φ b * k b a` is `p a` when `φ a = b` and `0` otherwise. Where `p.map φ b = 0` the law
`k b` is unconstrained. -/
def IsDisintegration [DecidableEq β] (p : PMF α) (φ : α → β) (k : β → PMF α) : Prop :=
  ∀ b a, p.map φ b * k b a = if φ a = b then p a else 0

/-- Sampling `a ← p` and outputting `(a, φ a)` is the same as sampling `b ← p.map φ`, then
`a ← k b`, and outputting `(a, b)`. -/
theorem IsDisintegration.map_pair_eq [DecidableEq β] {p : PMF α} {φ : α → β} {k : β → PMF α}
    (hk : IsDisintegration p φ k) :
    p.map (fun a => (a, φ a)) = (p.map φ).bind fun b => (k b).map fun a => (a, b) := by
  ext ⟨a, b⟩
  have h1 : p.map (fun a => (a, φ a)) (a, b) = if φ a = b then p a else 0 := by
    rw [map_apply,
      tsum_eq_single a fun a' ha' => ite_eq_right fun h => ha' (congrArg Prod.fst h).symm]
    by_cases h : φ a = b
    · simp [h]
    · simp [h, Prod.ext_iff, Ne.symm h]
  have h2 : ((k b).map fun a' => (a', b)) (a, b) = k b a := by
    rw [map_apply,
      tsum_eq_single a fun a' ha' => ite_eq_right fun h => ha' (congrArg Prod.fst h).symm]
    simp
  rw [bind_apply, tsum_eq_single b fun b' hb' => ?_, h1, h2, hk b a]
  refine mul_eq_zero_of_right _ ?_
  rw [map_apply]
  exact ENNReal.tsum_eq_zero.2 fun a' => ite_eq_right fun h => hb' (congrArg Prod.snd h).symm

/-- **Disintegration and total variation.** If `k` is a disintegration of `p` along `φ`, then
the law of `(a, φ a)` for `a ← p` and the law of `(a, b)` for `b ← q`, `a ← k b` are at most as
far apart as `p.map φ` and `q`: both laws apply the same kernel to their second component. -/
theorem IsDisintegration.tvDist_le [Fintype α] [Fintype β] [DecidableEq β] {p : PMF α}
    {φ : α → β} {k : β → PMF α} (hk : IsDisintegration p φ k) (q : PMF β) :
    tvDist (p.map fun a => (a, φ a)) (q.bind fun b => (k b).map fun a => (a, b)) ≤
      tvDist (p.map φ) q := by
  rw [hk.map_pair_eq]
  exact tvDist_bind_right_le _ _ _

/-- Disintegrations of the coordinates give a disintegration of the product law along the
coordinatewise map. -/
theorem IsDisintegration.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {δ ε : ι → Type*}
    [∀ i, Fintype (δ i)] [∀ i, Fintype (ε i)] [∀ i, DecidableEq (ε i)]
    {p : ∀ i, PMF (δ i)} {φ : ∀ i, δ i → ε i} {k : ∀ i, ε i → PMF (δ i)}
    (hk : ∀ i, IsDisintegration (p i) (φ i) (k i)) :
    IsDisintegration (PMF.pi p) (fun a i => φ i (a i)) fun b => PMF.pi fun i => k i (b i) := by
  intro b a
  simp only [pi_map, pi_apply, ← prod_mul_distrib, funext_iff]
  rw [prod_congr rfl fun i _ => hk i (b i) (a i), Fintype.prod_ite_zero]

end Disintegration

/-! ### Mixtures of probabilities -/


/-- **Mixing preserves a pointwise bound on differences**: if `p a` and `r a` are at most one and
differ by at most `ε` for every `a`, their averages under `μ` differ by at most `ε`. -/
theorem abs_toReal_tsum_mul_sub_le (μ : PMF α) {p r : α → ENNReal} (hp : ∀ a, p a ≤ 1)
    (hr : ∀ a, r a ≤ 1) {ε : ℝ} (h : ∀ a, |(p a).toReal - (r a).toReal| ≤ ε) :
    |(∑' a, μ a * p a).toReal - (∑' a, μ a * r a).toReal| ≤ ε := by
  obtain ⟨a₀, -⟩ := μ.support_nonempty
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h a₀)
  have key : ∀ {p r : α → ENNReal}, (∀ a, p a ≤ 1) → (∀ a, r a ≤ 1) →
      (∀ a, (p a).toReal ≤ (r a).toReal + ε) →
      (∑' a, μ a * p a).toReal ≤ (∑' a, μ a * r a).toReal + ε := by
    intro p r hp hr h
    have hpt : ∀ a, p a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.one_ne_top (hp a)
    have hrt : ∀ a, r a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.one_ne_top (hr a)
    have hpt' : ∀ a, p a ≤ r a + ENNReal.ofReal ε := fun a => by
      rw [← ENNReal.ofReal_toReal (hpt a), ← ENNReal.ofReal_toReal (hrt a),
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε]
      exact ENNReal.ofReal_le_ofReal (h a)
    have hsum : ∑' a, μ a * p a ≤ ∑' a, μ a * r a + ENNReal.ofReal ε := by
      calc ∑' a, μ a * p a ≤ ∑' a, μ a * (r a + ENNReal.ofReal ε) :=
            ENNReal.tsum_le_tsum fun a => by gcongr; exact hpt' a
        _ = ∑' a, μ a * r a + ENNReal.ofReal ε := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    have hfin : ∑' a, μ a * r a ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← μ.tsum_coe]
      exact ENNReal.tsum_le_tsum fun a => (by gcongr; exact hr a : μ a * r a ≤ μ a * 1).trans_eq (mul_one _)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hsum
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε] at this
  rw [abs_sub_le_iff]
  constructor
  · have := key hp hr fun a => by linarith [(abs_sub_le_iff.1 (h a)).1]
    linarith
  · have := key hr hp fun a => by linarith [(abs_sub_le_iff.1 (h a)).2]
    linarith

/-- **Normalized masses.** If `P` and `Q` are the normalizations of nonnegative masses `p` and `s`
on a finite type, with `∑ s > 0`, then `tvDist P Q ≤ ∑ a, |p a - s a| / ∑ a, s a`. The masses
need not sum to one or to each other: the normalization error `|∑ p - ∑ s| / ∑ s` is itself at
most the right side, and the factor `1/2` in `tvDist` absorbs it. -/
theorem tvDist_le_sum_abs_sub_div_sum [Fintype α] (P Q : PMF α) {p s : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hs : 0 < ∑ a, s a)
    (hP : ∀ a, (P a).toReal = p a / ∑ b, p b) (hQ : ∀ a, (Q a).toReal = s a / ∑ b, s b) :
    tvDist P Q ≤ (∑ a, |p a - s a|) / ∑ a, s a := by
  set π := ∑ b, p b with hπdef
  set σ := ∑ b, s b with hσdef
  have hπ1 : π / π = 1 := by
    have h := P.sum_toReal
    simp only [hP] at h
    rwa [← Finset.sum_div] at h
  have hπ : 0 < π := by
    rcases (Finset.sum_nonneg fun a _ => hp a : 0 ≤ π).lt_or_eq with h | h
    · exact h
    · rw [hπdef, ← h, div_zero] at hπ1
      exact absurd hπ1 zero_ne_one
  have key : ∀ a, |p a / π - s a / σ| ≤ p a * |1 / π - 1 / σ| + |p a - s a| / σ := by
    intro a
    have h : p a / π - s a / σ = p a * (1 / π - 1 / σ) + (p a - s a) / σ := by
      field_simp
      ring
    rw [h]
    refine (abs_add_le _ _).trans_eq ?_
    rw [abs_mul, abs_of_nonneg (hp a), abs_div, abs_of_pos hs]
  have h1 : π * |1 / π - 1 / σ| = |σ - π| / σ := by
    rw [show 1 / π - 1 / σ = (σ - π) / (π * σ) by field_simp, abs_div,
      abs_of_pos (mul_pos hπ hs)]
    field_simp
  have h2 : |σ - π| ≤ ∑ a, |p a - s a| := by
    rw [hσdef, hπdef, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    simp only [abs_sub_comm]
  rw [tvDist_eq_sum]
  simp only [hP, hQ]
  calc (∑ a, |p a / π - s a / σ|) / 2
      ≤ (∑ a, (p a * |1 / π - 1 / σ| + |p a - s a| / σ)) / 2 := by
        gcongr with a
        exact key a
    _ = (π * |1 / π - 1 / σ| + (∑ a, |p a - s a|) / σ) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
    _ ≤ (∑ a, |p a - s a|) / σ := by
        rw [h1]
        have := div_le_div_of_nonneg_right h2 hs.le
        linarith

end PMF
