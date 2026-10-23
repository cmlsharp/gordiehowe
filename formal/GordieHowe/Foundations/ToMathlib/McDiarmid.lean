-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.Concentration

@[expose] public section

/-!
# McDiarmid's inequality in moment-generating-function form, and the expected maximum

For a function `Z` of `N` independent uniform coordinates with bounded differences `c i`
(changing coordinate `i` moves `Z` by at most `c i`):

    E exp (t (Z - E Z)) ≤ exp (t² (∑ i, c i²) / 8)        (`expect_exp_le_of_boundedDiff`)

so `Z - E Z` is sub-Gaussian with variance proxy `∑ i, c i² / 4`, and for finitely many such
functions `Z m`, each with mean at most `μ` and `∑ i, c m i² ≤ s`,

    E max_m Z m ≤ μ + √(s · log M / 2)                  (`expect_sup'_le_of_boundedDiff`).

This is CY24 Lemma 1.2.5 (McDiarmid's inequality, p. 6) in the sub-Gaussian form its use in
the proof of Claim 3.4.2 (p. 37) needs, followed by Lemma 1.2.7 (p. 7). The proof is the usual
induction over the coordinates: the conditional mean given the first coordinate has range at
most `c 0` (Hoeffding's lemma, `PMF.sum_mul_exp_sub_le_of_mem_Icc`), and the rest is the
induction hypothesis.

The statements are about Mathlib objects only and are candidates for upstreaming.
They give the leaf hiding against an adaptive choice of the columns
(`GordieHowe.SPBCS.expect_sup'_tvDist_digestLaw_le`).
-/

open Finset Real
open scoped BigOperators

namespace PMF

variable {α : Type*} [Fintype α]

/-- **Hoeffding's lemma** on an interval: for a variable with values in `[a, b]`,
`E exp (t (Y - E Y)) ≤ exp (t² (b - a)² / 8)`. Bridged from Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`. -/
theorem sum_mul_exp_sub_le_of_mem_Icc (q : PMF α) {Y : α → ℝ} {a b : ℝ}
    (hY : ∀ x, Y x ∈ Set.Icc a b) (t : ℝ) :
    ∑ x, (q x).toReal * exp (t * (Y x - ∑ y, (q y).toReal * Y y)) ≤
      exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  let _ : MeasurableSpace α := ⊤
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure)
    (Measurable.of_discrete (f := Y)).aemeasurable (Filter.Eventually.of_forall hY)
  have hmgf := hsub.mgf_le t
  simp only [ProbabilityTheory.mgf, integral_eq_sum, smul_eq_mul] at hmgf
  refine hmgf.trans_eq ?_
  congr 1
  push_cast
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  ring

end PMF

section McDiarmid

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- **Hoeffding's lemma, uniform form**: for `Y` with values in `[a, b]` under a uniform
variable, `E exp (t (Y - E Y)) ≤ exp (t² (b - a)² / 8)`. -/
theorem expect_exp_sub_le_of_mem_Icc {Y : Ω → ℝ} {a b : ℝ} (hY : ∀ x, Y x ∈ Set.Icc a b)
    (t : ℝ) : 𝔼 x, exp (t * (Y x - 𝔼 y, Y y)) ≤ exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  have h := PMF.sum_mul_exp_sub_le_of_mem_Icc (PMF.uniformOfFintype Ω) hY t
  simp only [PMF.toReal_uniformOfFintype_apply, ← mul_sum] at h
  rwa [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, div_eq_inv_mul,
    div_eq_inv_mul]

/-- **McDiarmid's inequality** for `Fin N`-indexed coordinates (`expect_exp_le_of_boundedDiff` is
the general form): a function `Z` of `N` uniform coordinates in `Ω` whose value moves by at most
`c i` when coordinate `i` changes has `E exp (t (Z - E Z)) ≤ exp (t² (∑ i, c i²) / 8)`. -/
theorem expect_exp_le_of_boundedDiff_fin :
    ∀ {N : ℕ} (Z : (Fin N → Ω) → ℝ) (c : Fin N → ℝ),
      (∀ f i ω, |Z (Function.update f i ω) - Z f| ≤ c i) → ∀ t : ℝ,
      𝔼 f, exp (t * (Z f - 𝔼 g, Z g)) ≤ exp (t ^ 2 * (∑ i, c i ^ 2) / 8)
  | 0, Z, c, _, t => by
    have hc : ∀ f : Fin 0 → Ω, 𝔼 g, Z g = Z f := fun f => by
      rw [show (fun g => Z g) = fun _ => Z f from funext fun g => congrArg Z (funext (·.elim0))]
      exact Fintype.expect_const _
    simp [hc]
  | N + 1, Z, c, hZ, t => by
    set Zc : Ω → (Fin N → Ω) → ℝ := fun a g => Z (Fin.cons a g) with hZc
    set φ : Ω → ℝ := fun a => 𝔼 g, Zc a g with hφ
    -- splitting off the first coordinate
    have hsplit : ∀ F : (Fin (N + 1) → Ω) → ℝ, 𝔼 f, F f = 𝔼 a, 𝔼 g, F (Fin.cons a g) := by
      intro F
      rw [← Fintype.expect_equiv (Fin.consEquiv fun _ => Ω) (fun x => F (Fin.cons x.1 x.2)) F
        (fun _ => rfl), ← Finset.univ_product_univ]
      exact Finset.expect_product' univ univ fun a g => F (Fin.cons a g)
    have hEZ : 𝔼 g, Z g = 𝔼 a, φ a := hsplit Z
    -- the induction hypothesis on the remaining coordinates
    have hIH : ∀ a, 𝔼 g, exp (t * (Zc a g - φ a)) ≤ exp (t ^ 2 * (∑ i : Fin N, c i.succ ^ 2) / 8) :=
      fun a => expect_exp_le_of_boundedDiff_fin (Zc a) (fun i => c i.succ)
        (fun g i ω => by simpa [hZc, Fin.cons_update] using hZ (Fin.cons a g) i.succ ω) t
    -- the conditional mean has range at most `c 0`
    obtain ⟨a₀, -, ha₀⟩ := Finset.exists_min_image Finset.univ φ Finset.univ_nonempty
    have hrange : ∀ a, φ a ∈ Set.Icc (φ a₀) (φ a₀ + c 0) := fun a => by
      refine ⟨ha₀ a (Finset.mem_univ _), ?_⟩
      have : φ a - φ a₀ = 𝔼 g, (Zc a g - Zc a₀ g) := by
        simp only [hφ, Finset.expect_sub_distrib]
      have hle : 𝔼 g, (Zc a g - Zc a₀ g) ≤ 𝔼 _g : Fin N → Ω, c 0 :=
        Finset.expect_le_expect fun g _ => by
          have h := hZ (Fin.cons a₀ g) 0 a
          rw [Fin.update_cons_zero] at h
          exact (le_abs_self _).trans h
      rw [Fintype.expect_const] at hle
      linarith
    have hhoef := expect_exp_sub_le_of_mem_Icc hrange t
    calc 𝔼 f, exp (t * (Z f - 𝔼 g, Z g))
        = 𝔼 a, exp (t * (φ a - 𝔼 a', φ a')) * 𝔼 g, exp (t * (Zc a g - φ a)) := by
          rw [hsplit, hEZ]
          refine Finset.expect_congr rfl fun a _ => ?_
          rw [Finset.mul_expect]
          refine Finset.expect_congr rfl fun g _ => ?_
          rw [← exp_add]
          congr 1
          ring
      _ ≤ 𝔼 a, exp (t * (φ a - 𝔼 a', φ a')) * exp (t ^ 2 * (∑ i : Fin N, c i.succ ^ 2) / 8) :=
          Finset.expect_le_expect fun a _ =>
            mul_le_mul_of_nonneg_left (hIH a) (exp_pos _).le
      _ = (𝔼 a, exp (t * (φ a - 𝔼 a', φ a'))) * exp (t ^ 2 * (∑ i : Fin N, c i.succ ^ 2) / 8) := by
          rw [Finset.expect_mul]
      _ ≤ exp (t ^ 2 * (φ a₀ + c 0 - φ a₀) ^ 2 / 8) * exp (t ^ 2 * (∑ i : Fin N, c i.succ ^ 2) / 8) :=
          mul_le_mul_of_nonneg_right hhoef (exp_pos _).le
      _ = exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← exp_add, Fin.sum_univ_succ]
          congr 1
          ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **McDiarmid's inequality**, moment-generating-function form: a function `Z` of independent
uniform coordinates `f i ∈ Ω` whose value moves by at most `c i` when coordinate `i` changes has
`E exp (t (Z - E Z)) ≤ exp (t² (∑ i, c i²) / 8)`. -/
theorem expect_exp_le_of_boundedDiff (Z : (ι → Ω) → ℝ) (c : ι → ℝ)
    (hZ : ∀ f i ω, |Z (Function.update f i ω) - Z f| ≤ c i) (t : ℝ) :
    𝔼 f, exp (t * (Z f - 𝔼 g, Z g)) ≤ exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  set e := Fintype.equivFin ι
  set E : (Fin (Fintype.card ι) → Ω) ≃ (ι → Ω) := e.symm.arrowCongr (Equiv.refl Ω)
  have hE : ∀ g : Fin (Fintype.card ι) → Ω, E g = g ∘ e := fun g => rfl
  have hupd : ∀ (g : Fin (Fintype.card ι) → Ω) i ω,
      E (Function.update g i ω) = Function.update (E g) (e.symm i) ω := fun g i ω => by
    funext j
    simp only [hE, Function.comp_apply, Function.update_apply, e.apply_eq_iff_eq_symm_apply]
  have h := expect_exp_le_of_boundedDiff_fin (Z ∘ E) (c ∘ e.symm)
    (fun g i ω => by simpa [hupd] using hZ (E g) (e.symm i) ω) t
  have hmean : 𝔼 g, (Z ∘ E) g = 𝔼 g, Z g := Fintype.expect_equiv E _ _ fun _ => rfl
  rw [hmean, Fintype.expect_equiv E (fun g => exp (t * ((Z ∘ E) g - 𝔼 g, Z g)))
    (fun f => exp (t * (Z f - 𝔼 g, Z g))) fun _ => rfl] at h
  refine h.trans_eq ?_
  rw [Fintype.sum_equiv e.symm (fun i => (c ∘ e.symm) i ^ 2) (fun i => c i ^ 2) fun _ => rfl]

omit [Nonempty Ω] in
/-- Choosing the free parameter, allowing `b = 0`: if `A ≤ a / t + b * t` for every `t > 0`,
with `0 ≤ a` and `0 ≤ b`, then `A ≤ 2 * √(a * b)`. -/
theorem Real.le_two_mul_sqrt_of_forall_le' {A a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t, 0 < t → A ≤ a / t + b * t) : A ≤ 2 * √(a * b) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp only [mul_zero, sqrt_zero, zero_mul, add_zero] at h ⊢
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h ((a + 1) / ε) (by positivity)
    rw [div_div_eq_mul_div] at this
    have : a * ε / (a + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · exact Real.le_two_mul_sqrt_of_forall_le ha hb h

/-- **The expected maximum of functions with bounded differences** (CY24 Lemma 1.2.7, p. 7,
with the variance proxy of McDiarmid's inequality): for `M` functions `Z m` of independent
uniform coordinates, each with mean at most `μ` and bounded differences `c m i` with
`∑ i, c m i² ≤ s`, the expected maximum is at most `μ + √(s · log M / 2)`. -/
theorem expect_sup'_le_of_boundedDiff {M : Type*} [Fintype M] [Nonempty M]
    (Z : M → (ι → Ω) → ℝ) (c : M → ι → ℝ)
    (hZ : ∀ m f i ω, |Z m (Function.update f i ω) - Z m f| ≤ c m i) {μ s : ℝ}
    (hμ : ∀ m, 𝔼 f, Z m f ≤ μ) (hs : ∀ m, ∑ i, c m i ^ 2 ≤ s) :
    𝔼 f, univ.sup' univ_nonempty (fun m => Z m f) ≤ μ + √(s * log (Fintype.card M) / 2) := by
  have hs0 : 0 ≤ s := (sum_nonneg fun i _ => sq_nonneg _).trans (hs (Classical.arbitrary M))
  have hM : 0 ≤ log (Fintype.card M) := log_nonneg (by simp [Nat.one_le_iff_ne_zero])
  have hq : ∀ F : (ι → Ω) → ℝ, ∑ f, ((PMF.uniformOfFintype (ι → Ω)) f).toReal * F f =
      𝔼 f, F f := fun F => by
    simp only [PMF.toReal_uniformOfFintype_apply, ← mul_sum, Fintype.expect_eq_sum_div_card,
      div_eq_inv_mul]
  have key : ∀ t, 0 < t → 𝔼 f, univ.sup' univ_nonempty (fun m => Z m f) - μ ≤
      log (Fintype.card M) / t + s / 8 * t := by
    intro t ht
    have hmax := PMF.sum_mul_sup'_le_log (PMF.uniformOfFintype (ι → Ω)) Z ht
    simp only [hq] at hmax
    have hone : ∀ m, 𝔼 f, exp (t * Z m f) ≤ exp (t * μ + t ^ 2 * s / 8) := by
      intro m
      have hsplit : ∀ f, exp (t * Z m f) = exp (t * 𝔼 g, Z m g) * exp (t * (Z m f - 𝔼 g, Z m g)) :=
        fun f => by rw [← exp_add]; ring_nf
      simp_rw [hsplit, ← Finset.mul_expect]
      calc exp (t * 𝔼 g, Z m g) * 𝔼 f, exp (t * (Z m f - 𝔼 g, Z m g))
          ≤ exp (t * μ) * exp (t ^ 2 * (∑ i, c m i ^ 2) / 8) := by
            gcongr
            · exact hμ m
            · exact expect_exp_le_of_boundedDiff (Z m) (c m) (hZ m) t
        _ ≤ exp (t * μ + t ^ 2 * s / 8) := by
            rw [← exp_add]
            have := mul_le_mul_of_nonneg_left (hs m) (sq_nonneg t)
            exact exp_le_exp.2 (by linarith)
    have hsum : ∑ m, 𝔼 f, exp (t * Z m f) ≤ Fintype.card M * exp (t * μ + t ^ 2 * s / 8) := by
      refine (sum_le_sum fun m _ => hone m).trans_eq ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hpos : 0 < ∑ m, 𝔼 f, exp (t * Z m f) :=
      sum_pos (fun m _ => Finset.expect_pos (fun f _ => exp_pos _) univ_nonempty) univ_nonempty
    have hlog := (log_le_log hpos hsum).trans_eq
      (by rw [log_mul (by simp) (exp_pos _).ne', log_exp])
    have := hmax.trans (div_le_div_of_nonneg_right hlog ht.le)
    rw [add_div] at this
    have e : (t * μ + t ^ 2 * s / 8) / t = μ + s / 8 * t := by
      field_simp
    rw [e] at this
    linarith
  have := Real.le_two_mul_sqrt_of_forall_le' hM (by positivity) key
  have e : 2 * √(log (Fintype.card M) * (s / 8)) = √(s * log (Fintype.card M) / 2) := by
    have h4 : s * log (Fintype.card M) / 2 = 2 ^ 2 * (log (Fintype.card M) * (s / 8)) := by
      ring
    rw [h4, sqrt_mul (sq_nonneg _), sqrt_sq zero_le_two]
  linarith

end McDiarmid
