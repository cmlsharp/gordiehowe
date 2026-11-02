-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Chi-square divergence for PMFs on finite types

The chi-square divergence of `p` from `q` (Tsybakov, *Introduction to Nonparametric Estimation*,
Springer 2009, Section 2.4; the section is cited from memory, the exact definition and equation
numbers there are unverified) is

    chiSq p q = ∑ a, (p a - q a) ^ 2 / q a,

read in `ℝ`; terms with `q a = 0` are `0` (Lean's division by zero), and the facts below assume
that `p` vanishes wherever `q` does. Its bilinear form, the chi-square correlation

    chiSqCorr p p' q = ∑ a, p a · p' a / q a - 1,

satisfies `chiSq p q = chiSqCorr p p q` (`chiSq_eq_chiSqCorr`). Facts:

- `tvDist_le_sqrt_chiSq`: `tvDist p q ≤ √(chiSq p q) / 2` (Cauchy–Schwarz);
- `one_add_chiSqCorr_pi`: the correlation of products is the product of the correlations, so
  `1 + chiSq (pi p) (pi q) = ∏ i, (1 + chiSq (p i) (q i))` (`one_add_chiSq_pi`) and
  `chiSq (p^⊗Q) (q^⊗Q) = (1 + chiSq p q) ^ Q - 1` (`chiSq_pi_const`);
- mixtures of products (Ingster's second-moment method; cited from memory, unverified):
  `1 + chiSq (E_θ pi (p θ)) (pi q) = E_{θ, θ'} ∏ i, (1 + chiSqCorr (p θ i) (p θ' i) (q i))`
  (`one_add_chiSq_bind_pi`), and `E_{θ, θ'} (1 + ρ θ θ') ^ Q` for `Q` copies of one law
  (`one_add_chiSq_bind_pi_const`).

About Mathlib objects only; a candidate for upstreaming with
`GordieHowe/Foundations/ToMathlib/PMFTV.lean`.
-/

open Finset
open scoped BigOperators

namespace PMF

section ChiSq

variable {α : Type*} [Fintype α]

/-- **The chi-square divergence** of `p` from `q` (Tsybakov 2009, Section 2.4), in `ℝ`. -/
noncomputable def chiSq (p q : PMF α) : ℝ :=
  ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal

/-- **The chi-square correlation** of `p` and `p'` relative to `q`. -/
noncomputable def chiSqCorr (p p' q : PMF α) : ℝ :=
  ∑ a, (p a).toReal * (p' a).toReal / (q a).toReal - 1

/-- With `p` vanishing where `q` does, `1 + chiSq p q = ∑ a, p a ^ 2 / q a`. -/
theorem one_add_chiSq {p q : PMF α} (hpq : ∀ a, q a = 0 → p a = 0) :
    1 + chiSq p q = ∑ a, (p a).toReal ^ 2 / (q a).toReal := by
  have hpt : ∀ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal =
      (p a).toReal ^ 2 / (q a).toReal - 2 * (p a).toReal + (q a).toReal := fun a => by
    rcases eq_or_ne (q a) 0 with h | h
    · simp [h, hpq a h]
    · have hq : (q a).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h, q.apply_ne_top a⟩
      field_simp
      ring
  rw [chiSq, sum_congr rfl fun a _ => hpt a, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_toReal, sum_toReal]
  ring

/-- With `p` vanishing where `q` does, the divergence is the correlation of `p` with itself. -/
theorem chiSq_eq_chiSqCorr {p q : PMF α} (hpq : ∀ a, q a = 0 → p a = 0) :
    chiSq p q = chiSqCorr p p q := by
  have h := one_add_chiSq hpq
  simp only [chiSqCorr, ← sq]
  linarith

/-- `1 + chiSqCorr p p' q` is the sum `∑ a, p a · p' a / q a`. -/
theorem one_add_chiSqCorr (p p' q : PMF α) :
    1 + chiSqCorr p p' q = ∑ a, (p a).toReal * (p' a).toReal / (q a).toReal := by
  rw [chiSqCorr]
  ring

/-- **The chi-square bound on total variation**: `tvDist p q ≤ √(chiSq p q) / 2` when `p`
vanishes where `q` does (Cauchy–Schwarz). -/
theorem tvDist_le_sqrt_chiSq {p q : PMF α} (hpq : ∀ a, q a = 0 → p a = 0) :
    tvDist p q ≤ √(chiSq p q) / 2 := by
  rw [tvDist_eq_sum]
  gcongr
  have hCS := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |(p a).toReal - (q a).toReal| / √((q a).toReal)) fun a => √((q a).toReal)
  have hfg : ∀ a, |(p a).toReal - (q a).toReal| / √((q a).toReal) * √((q a).toReal) =
      |(p a).toReal - (q a).toReal| := fun a => by
    rcases eq_or_ne (q a) 0 with h | h
    · simp [h, hpq a h]
    · have hq : 0 < (q a).toReal := ENNReal.toReal_pos h (q.apply_ne_top a)
      rw [div_mul_cancel₀ _ (Real.sqrt_pos.2 hq).ne']
  have hf : ∀ a, (|(p a).toReal - (q a).toReal| / √((q a).toReal)) ^ 2 =
      ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal := fun a => by
    rw [div_pow, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg]
  simp only [hfg, hf, Real.sq_sqrt ENNReal.toReal_nonneg, sum_toReal, mul_one] at hCS
  exact Real.le_sqrt_of_sq_le hCS

end ChiSq

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- **The chi-square correlation of products** is the product of the correlations. -/
theorem one_add_chiSqCorr_pi (p p' q : ∀ i, PMF (β i)) :
    1 + chiSqCorr (pi p) (pi p') (pi q) = ∏ i, (1 + chiSqCorr (p i) (p' i) (q i)) := by
  simp only [one_add_chiSqCorr, toReal_pi_apply, ← prod_mul_distrib, ← prod_div_distrib]
  exact (Fintype.prod_sum fun i a => (p i a).toReal * (p' i a).toReal / (q i a).toReal).symm

/-- A product vanishes wherever a product of laws that dominate its factors does. -/
theorem pi_apply_eq_zero_of {p q : ∀ i, PMF (β i)} (hpq : ∀ i a, q i a = 0 → p i a = 0)
    (f : ∀ i, β i) (hf : pi q f = 0) : pi p f = 0 := by
  rw [pi_apply, prod_eq_zero_iff] at hf ⊢
  obtain ⟨i, -, hi⟩ := hf
  exact ⟨i, mem_univ i, hpq i (f i) hi⟩

/-- **Chi-square of products**: `1 + chiSq (pi p) (pi q) = ∏ i, (1 + chiSq (p i) (q i))`. -/
theorem one_add_chiSq_pi {p q : ∀ i, PMF (β i)} (hpq : ∀ i a, q i a = 0 → p i a = 0) :
    1 + chiSq (pi p) (pi q) = ∏ i, (1 + chiSq (p i) (q i)) := by
  rw [chiSq_eq_chiSqCorr (pi_apply_eq_zero_of hpq), one_add_chiSqCorr_pi]
  exact prod_congr rfl fun i _ => by rw [chiSq_eq_chiSqCorr (hpq i)]

/-- **Mixtures of products** (Ingster's second-moment identity): for `θ ← μ`, the mixture of the
products `pi (p θ)` satisfies
`1 + chiSq (E_θ pi (p θ)) (pi q) = E_{θ, θ'} ∏ i, (1 + chiSqCorr (p θ i) (p θ' i) (q i))`. -/
theorem one_add_chiSq_bind_pi {Θ : Type*} [Fintype Θ] (μ : PMF Θ) {p : Θ → ∀ i, PMF (β i)}
    {q : ∀ i, PMF (β i)} (hpq : ∀ θ i a, q i a = 0 → p θ i a = 0) :
    1 + chiSq (μ.bind fun θ => pi (p θ)) (pi q) =
      ∑ θ, ∑ θ', (μ θ).toReal * (μ θ').toReal *
        ∏ i, (1 + chiSqCorr (p θ i) (p θ' i) (q i)) := by
  have hM : ∀ f, pi q f = 0 → (μ.bind fun θ => pi (p θ)) f = 0 := fun f hf => by
    rw [bind_apply, ENNReal.tsum_eq_zero]
    exact fun θ => by rw [pi_apply_eq_zero_of (hpq θ) f hf, mul_zero]
  rw [one_add_chiSq hM]
  simp_rw [← one_add_chiSqCorr_pi, one_add_chiSqCorr, mul_sum]
  have hf : ∀ f : ∀ i, β i, ((μ.bind fun θ => pi (p θ)) f).toReal ^ 2 / (pi q f).toReal =
      ∑ θ, ∑ θ', (μ θ).toReal * (μ θ').toReal *
        ((pi (p θ) f).toReal * (pi (p θ') f).toReal / (pi q f).toReal) := fun f => by
    rw [toReal_bind_apply, sq, sum_mul_sum, sum_div]
    refine sum_congr rfl fun θ _ => ?_
    rw [sum_div]
    exact sum_congr rfl fun θ' _ => by ring
  simp_rw [hf]
  rw [sum_comm]
  exact sum_congr rfl fun θ _ => sum_comm

end Pi

section PiConst

variable {α : Type*} [Fintype α]

/-- **Chi-square of `Q` independent copies**: `chiSq (p^⊗Q) (q^⊗Q) = (1 + chiSq p q) ^ Q - 1`. -/
theorem chiSq_pi_const {p q : PMF α} (hpq : ∀ a, q a = 0 → p a = 0) (Q : ℕ) :
    chiSq (pi fun _ : Fin Q => p) (pi fun _ : Fin Q => q) = (1 + chiSq p q) ^ Q - 1 := by
  have h := one_add_chiSq_pi (p := fun _ : Fin Q => p) (q := fun _ => q) fun _ => hpq
  rw [prod_const, card_univ, Fintype.card_fin] at h
  linarith

/-- **Mixtures of `Q` independent copies**: for `θ ← μ`,
`1 + chiSq (E_θ p_θ^⊗Q) (q^⊗Q) = E_{θ, θ'} (1 + chiSqCorr (p θ) (p θ') q) ^ Q`. -/
theorem one_add_chiSq_bind_pi_const {Θ : Type*} [Fintype Θ] (μ : PMF Θ) {p : Θ → PMF α}
    {q : PMF α} (hpq : ∀ θ a, q a = 0 → p θ a = 0) (Q : ℕ) :
    1 + chiSq (μ.bind fun θ => pi fun _ : Fin Q => p θ) (pi fun _ : Fin Q => q) =
      ∑ θ, ∑ θ', (μ θ).toReal * (μ θ').toReal * (1 + chiSqCorr (p θ) (p θ') q) ^ Q := by
  rw [one_add_chiSq_bind_pi μ (p := fun θ _ => p θ) (q := fun _ => q) fun θ _ => hpq θ]
  simp only [prod_const, card_univ, Fintype.card_fin]

end PiConst

end PMF
