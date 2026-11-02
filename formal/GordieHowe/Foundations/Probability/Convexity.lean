-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.Advantage
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Probability.ProbabilityMassFunction.Monad

@[expose] public section

/-!
# Randomized adversaries are no better than deterministic ones

A randomized adversary is a deterministic adversary run on coins drawn independently of
everything else in the game. Its experiments are mixtures over the coins of the deterministic
adversaries' experiments, `ν.bind μ_b`, and its advantage is at most that of the best coin value:
the advantage is a convex function of the pair of experiments' laws (the absolute value of a
linear function), so its value at a mixture is at most its largest value at the mixed points.
This is the averaging argument (fixing the adversary's coins to their best value) by which
non-uniform adversaries may be taken deterministic (Goldreich, *Foundations of Cryptography* I,
2001). It holds for any game: the experiments `μ₀ ω`, `μ₁ ω` and the winning event are
arbitrary.

- `toReal_toOuterMeasure_bind`: the probability of an event under a mixture is the average of its
  probabilities, in `ℝ`.
- `exists_gameAdvantage_bind_le`: some coin value in the support has at least the advantage of
  the randomized adversary.
- `gameAdvantage_bind_le`, `gameAdvantage_bind_le_iSup`: the bound by a common bound `ε` of the
  deterministic advantages, and by their supremum.
- `exists_gameAdvantage_bind_true_le`: a randomized distinguisher (a test `D : α → PMF Bool`
  of the experiment's outcome) is no better than the best deterministic one, an event `S`.

The multi-round form, for adversaries that draw fresh coins in every round (behavioral
strategies), is `Interaction.exists_det_winDiff_ge`
(`GordieHowe/Foundations/Probability/Interaction.lean`).
-/

open scoped ENNReal

namespace GordieHowe

section Mixture

variable {Ω α : Type*}

/-- `gameAdvantage` with its probabilities written as `toOuterMeasure` of the event. -/
theorem gameAdvantage_eq_toReal (μ₀ μ₁ : PMF α) (win : Set α) :
    gameAdvantage μ₀ μ₁ win =
      advantage (μ₀.toOuterMeasure win).toReal (μ₁.toOuterMeasure win).toReal :=
  rfl

/-- **The probability of an event under a mixture is the average of its probabilities.** -/
theorem toReal_toOuterMeasure_bind (ν : PMF Ω) (μ : Ω → PMF α) (S : Set α) :
    ((ν.bind μ).toOuterMeasure S).toReal =
      ∑' ω, (ν ω).toReal * ((μ ω).toOuterMeasure S).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq fun ω =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _))]
  simp only [ENNReal.toReal_mul]

/-- The weights of a distribution sum to `1` in `ℝ`. -/
theorem pmf_tsum_toReal (ν : PMF Ω) : ∑' ω, (ν ω).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq fun ω => PMF.apply_ne_top _ _, PMF.tsum_coe, ENNReal.toReal_one]

theorem pmf_summable_toReal (ν : PMF Ω) : Summable fun ω => (ν ω).toReal :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

/-- A family bounded by `1` weighted by a distribution is summable. -/
theorem pmf_summable_toReal_mul (ν : PMF Ω) {f : Ω → ℝ} (hf : ∀ ω, |f ω| ≤ 1) :
    Summable fun ω => (ν ω).toReal * f ω :=
  Summable.of_norm_bounded (pmf_summable_toReal ν) fun ω => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hf ω)

theorem toReal_toOuterMeasure_le_one (μ : PMF α) (S : Set α) :
    (μ.toOuterMeasure S).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [ENNReal.ofReal_one]; exact PMF.toOuterMeasure_apply_le_one _ _)

/-- An advantage between two distributions is at most `1`. -/
theorem gameAdvantage_le_one (μ₀ μ₁ : PMF α) (S : Set α) : gameAdvantage μ₀ μ₁ S ≤ 1 := by
  rw [gameAdvantage_eq_toReal, advantage, abs_sub_le_iff]
  have h0 := toReal_toOuterMeasure_le_one μ₀ S
  have h1 := toReal_toOuterMeasure_le_one μ₁ S
  have h0' : 0 ≤ (μ₀.toOuterMeasure S).toReal := ENNReal.toReal_nonneg
  have h1' : 0 ≤ (μ₁.toOuterMeasure S).toReal := ENNReal.toReal_nonneg
  constructor <;> linarith

/-- The difference of the two winning probabilities of a randomized adversary is the average of
the deterministic differences. -/
theorem toReal_bind_sub_eq (ν : PMF Ω) (μ₀ μ₁ : Ω → PMF α) (S : Set α) :
    ((ν.bind μ₀).toOuterMeasure S).toReal - ((ν.bind μ₁).toOuterMeasure S).toReal =
      ∑' ω, (ν ω).toReal *
        (((μ₀ ω).toOuterMeasure S).toReal - ((μ₁ ω).toOuterMeasure S).toReal) := by
  have hb : ∀ (μ : Ω → PMF α) ω, |((μ ω).toOuterMeasure S).toReal| ≤ 1 := fun μ ω => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact toReal_toOuterMeasure_le_one _ _
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind,
    ← (pmf_summable_toReal_mul ν (hb μ₀)).tsum_sub (pmf_summable_toReal_mul ν (hb μ₁))]
  simp only [mul_sub]

/-- **Some coin value is at least as good as the randomized adversary**: for coins `ω ← ν`
drawn independently of the rest of the game and experiments `μ₀ ω`, `μ₁ ω` of the deterministic
adversary with coins `ω`, some `ω` in the support of `ν` has at least the advantage of the
randomized adversary, whose experiments are `ν.bind μ₀` and `ν.bind μ₁`. -/
theorem exists_gameAdvantage_bind_le (ν : PMF Ω) (μ₀ μ₁ : Ω → PMF α) (win : Set α) :
    ∃ ω ∈ ν.support, gameAdvantage (ν.bind μ₀) (ν.bind μ₁) win ≤
      gameAdvantage (μ₀ ω) (μ₁ ω) win := by
  by_contra hcon
  push Not at hcon
  set A := gameAdvantage (ν.bind μ₀) (ν.bind μ₁) win
  set d : Ω → ℝ := fun ω =>
    ((μ₀ ω).toOuterMeasure win).toReal - ((μ₁ ω).toOuterMeasure win).toReal
  have hd1 : ∀ ω, |d ω| ≤ 1 := fun ω => gameAdvantage_le_one (μ₀ ω) (μ₁ ω) win
  have hA : A = |∑' ω, (ν ω).toReal * d ω| := by
    simp only [A, gameAdvantage_eq_toReal, advantage, d, toReal_bind_sub_eq]
  have hs : Summable fun ω => (ν ω).toReal * |d ω| :=
    pmf_summable_toReal_mul ν fun ω => by rw [abs_abs]; exact hd1 ω
  have hn : ∀ ω, ‖(ν ω).toReal * d ω‖ = (ν ω).toReal * |d ω| := fun ω => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hle : A ≤ ∑' ω, (ν ω).toReal * |d ω| := by
    have h := norm_tsum_le_tsum_norm (f := fun ω => (ν ω).toReal * d ω)
      (by simpa only [hn] using hs)
    rw [hA, ← Real.norm_eq_abs]
    simpa only [hn] using h
  obtain ⟨ω₀, hω₀⟩ := ν.support_nonempty
  have hlt : ∑' ω, (ν ω).toReal * |d ω| < ∑' ω, (ν ω).toReal * A := by
    refine Summable.tsum_lt_tsum (i := ω₀) (fun ω => ?_) ?_ hs
      ((pmf_summable_toReal ν).mul_right A)
    · by_cases hω : ω ∈ ν.support
      · exact mul_le_mul_of_nonneg_left (hcon ω hω).le ENNReal.toReal_nonneg
      · rw [PMF.mem_support_iff, not_not] at hω
        simp [hω]
    · refine mul_lt_mul_of_pos_left (hcon ω₀ hω₀) (ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _))
      exact (PMF.mem_support_iff _ _).1 hω₀
  rw [tsum_mul_right, pmf_tsum_toReal, one_mul] at hlt
  linarith

/-- **A randomized adversary's advantage is at most a common bound of the deterministic
ones** on the support of its coins. -/
theorem gameAdvantage_bind_le (ν : PMF Ω) (μ₀ μ₁ : Ω → PMF α) (win : Set α) {ε : ℝ}
    (h : ∀ ω ∈ ν.support, gameAdvantage (μ₀ ω) (μ₁ ω) win ≤ ε) :
    gameAdvantage (ν.bind μ₀) (ν.bind μ₁) win ≤ ε := by
  obtain ⟨ω, hω, hle⟩ := exists_gameAdvantage_bind_le ν μ₀ μ₁ win
  exact hle.trans (h ω hω)

/-- **A randomized adversary's advantage is at most the supremum over its coins of the
deterministic advantages.** -/
theorem gameAdvantage_bind_le_iSup (ν : PMF Ω) (μ₀ μ₁ : Ω → PMF α) (win : Set α) :
    gameAdvantage (ν.bind μ₀) (ν.bind μ₁) win ≤
      ⨆ ω : ν.support, gameAdvantage (μ₀ ω) (μ₁ ω) win := by
  obtain ⟨ω, hω, hle⟩ := exists_gameAdvantage_bind_le ν μ₀ μ₁ win
  exact hle.trans (le_ciSup (f := fun ω : ν.support => gameAdvantage (μ₀ ω) (μ₁ ω) win)
    ⟨1, fun _ ⟨ω', h⟩ => h ▸ gameAdvantage_le_one _ _ _⟩ ⟨ω, hω⟩)

end Mixture

section Distinguisher

variable {α : Type*}

/-- A summable real family times a family in `[0, 1]` is summable. -/
theorem Summable.mul_unit {d f : α → ℝ} (hd : Summable d) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : Summable fun x => d x * f x :=
  Summable.of_norm_bounded hd.abs fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf1 x)

/-- The probability of an event in `ℝ` as a sum of the weights of its points. -/
theorem toReal_toOuterMeasure_eq_tsum (μ : PMF α) (S : Set α) :
    (μ.toOuterMeasure S).toReal = ∑' x, S.indicator (fun x => (μ x).toReal) x := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq fun x => by
    by_cases hx : x ∈ S <;> simp [hx, PMF.apply_ne_top]]
  congr 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx]

/-- **A randomized distinguisher is no better than the best event**: for a test `D` of the
outcome of two experiments, returning a random bit, some event `S` (a deterministic test)
distinguishes the experiments at least as well: the advantage of `D`, the difference of the
probabilities that it returns `true`, is at most that of `S`. One of the events
`{x | μ₁ x ≤ μ₀ x}` and its complement (the outcomes likelier under one experiment) does. -/
theorem exists_gameAdvantage_bind_true_le (μ₀ μ₁ : PMF α) (D : α → PMF Bool) :
    ∃ S : Set α, gameAdvantage (μ₀.bind D) (μ₁.bind D) {true} ≤ gameAdvantage μ₀ μ₁ S := by
  classical
  set f : α → ℝ := fun x => (D x true).toReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hf1 : ∀ x, f x ≤ 1 := fun x => by
    have := toReal_toOuterMeasure_le_one (D x) {true}
    rwa [PMF.toOuterMeasure_apply_singleton] at this
  set d : α → ℝ := fun x => (μ₀ x).toReal - (μ₁ x).toReal
  have hs0 := pmf_summable_toReal μ₀
  have hs1 := pmf_summable_toReal μ₁
  have hsd : Summable d := hs0.sub hs1
  have hP : ∀ μ : PMF α, ((μ.bind D).toOuterMeasure {true}).toReal = ∑' x, (μ x).toReal * f x :=
    fun μ => by
      rw [toReal_toOuterMeasure_bind]
      simp only [PMF.toOuterMeasure_apply_singleton, f]
  have hsf : ∀ μ : PMF α, Summable fun x => (μ x).toReal * f x := fun μ =>
    pmf_summable_toReal_mul μ fun x => by rw [abs_of_nonneg (hf0 x)]; exact hf1 x
  have hdiff : ((μ₀.bind D).toOuterMeasure {true}).toReal -
      ((μ₁.bind D).toOuterMeasure {true}).toReal = ∑' x, d x * f x := by
    rw [hP, hP, ← (hsf μ₀).tsum_sub (hsf μ₁)]
    simp only [d, sub_mul]
  set Sp : Set α := {x | 0 ≤ d x}
  have hSp : ∀ S : Set α, (μ₀.toOuterMeasure S).toReal - (μ₁.toOuterMeasure S).toReal =
      ∑' x, S.indicator d x := fun S => by
    rw [toReal_toOuterMeasure_eq_tsum, toReal_toOuterMeasure_eq_tsum,
      ← (hs0.indicator S).tsum_sub (hs1.indicator S)]
    congr 1
    funext x
    by_cases hx : x ∈ S <;> simp [hx, d]
  have hup : ∑' x, d x * f x ≤ ∑' x, Sp.indicator d x := by
    refine (Summable.mul_unit hsd hf0 hf1).tsum_le_tsum (fun x => ?_) (hsd.indicator Sp)
    by_cases hx : x ∈ Sp
    · rw [Set.indicator_of_mem hx]
      exact mul_le_of_le_one_right hx (hf1 x)
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hx)) (hf0 x)
  have hdown : ∑' x, Spᶜ.indicator d x ≤ ∑' x, d x * f x := by
    refine (hsd.indicator Spᶜ).tsum_le_tsum (fun x => ?_) (Summable.mul_unit hsd hf0 hf1)
    by_cases hx : x ∈ Sp
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      exact mul_nonneg hx (hf0 x)
    · rw [Set.indicator_of_mem (by simpa using hx)]
      have hdx : d x < 0 := not_le.1 hx
      nlinarith [hf1 x, hf0 x]
  by_cases hsign : 0 ≤ ∑' x, d x * f x
  · refine ⟨Sp, ?_⟩
    rw [gameAdvantage_eq_toReal, gameAdvantage_eq_toReal, advantage, advantage, hdiff,
      abs_of_nonneg hsign, hSp]
    exact hup.trans (le_abs_self _)
  · refine ⟨Spᶜ, ?_⟩
    rw [gameAdvantage_eq_toReal, gameAdvantage_eq_toReal, advantage, advantage, hdiff,
      abs_of_neg (not_le.1 hsign), hSp]
    exact (neg_le_neg hdown).trans (neg_le_abs _)

end Distinguisher

end GordieHowe
