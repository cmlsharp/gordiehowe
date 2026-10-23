-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The expected maximum of averages of independent bounded variables

For independent coordinates `f s` (`s` in a finite set of size `N`) and, for each `m` in a
finite set of size `M`, variables `Y m s (f s) ∈ [0, 1]` of mean at most `p`:

    E_f [max_m (1/N) ∑ s, Y m s (f s)] ≤ p + √(log M / (2 N)),

with `log` the natural logarithm (`PMF.sum_pi_mul_sup'_le`; for uniform coordinates
`expect_sup'_expect_le`, and for slices of a uniform function `expect_sup'_le_of_slices`).
This is CY24 Lemma 1.2.7 (p. 7): "Let `X_1, …, X_n` be sub-Gaussian random variables with
variance proxy `σ²`. Then `E[max_{i ∈ [n]} X_i] ≤ σ √(2 · log n)`", applied to the centred
averages, whose variance proxy is `1 / (4N)` by Hoeffding's lemma.

The proof is the usual one:
- **Hoeffding's lemma** for a PMF on a finite type (`PMF.sum_mul_exp_le_of_mem_Icc`):
  `E exp (t Y) ≤ exp (t E Y + t² / 8)` for `Y ∈ [0, 1]`. Bridged from Mathlib's measure-theoretic
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` through `PMF.toMeasure` and
  `PMF.integral_eq_sum`.
- **Independence**: under a product law the expectation of a product of functions of the
  separate coordinates is the product of their expectations (`PMF.sum_pi_mul_prod`).
- **The maximal inequality** (`PMF.sum_mul_sup'_le_log`):
  `E max_m Z m ≤ log (∑ m, E exp (t Z m)) / t` for `t > 0`, by Jensen's inequality for `exp`.
- **Choosing `t`** (`Real.le_two_mul_sqrt_of_forall_le`): `A ≤ a / t + b t` for all `t > 0`
  gives `A ≤ 2 √(a b)`.

The bounds are about Mathlib objects only and are candidates for upstreaming. The salt bound of
spBCS (`SPBCS.expect_sup'_fpDist_le`) uses them for the probability of
the bad event under Fiat–Shamir challenges with a per-proof salt.
-/

open Finset Real
open scoped BigOperators

namespace Real

/-- Choosing the free parameter: if `A ≤ a / t + b * t` for every `t > 0`, with `0 ≤ a` and
`0 < b`, then `A ≤ 2 * √(a * b)`. The minimum is at `t = √(a / b)`. -/
theorem le_two_mul_sqrt_of_forall_le {A a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : ∀ t, 0 < t → A ≤ a / t + b * t) : A ≤ 2 * √(a * b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := h (ε / b) (div_pos hε hb)
    rwa [zero_div, zero_add, mul_div_cancel₀ _ hb.ne', ← zero_add ε] at this
  · have ht : 0 < √(a / b) := sqrt_pos.2 (div_pos ha hb)
    refine (h _ ht).trans_eq ?_
    have hab : √(a * b) = b * √(a / b) := by
      rw [← sqrt_sq hb.le, ← sqrt_mul (sq_nonneg b), sqrt_sq hb.le]
      congr 1
      field_simp
    rw [hab]
    field_simp
    rw [sq_sqrt (div_pos ha hb).le]
    field_simp
    ring

end Real

namespace PMF

variable {α : Type*} [Fintype α]

/-- **Hoeffding's lemma** for a PMF on a finite type: a variable with values in `[0, 1]` has
`E exp (t Y) ≤ exp (t E Y + t² / 8)`. Bridged from Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`. -/
theorem sum_mul_exp_le_of_mem_Icc (q : PMF α) {Y : α → ℝ} (hY : ∀ a, Y a ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) :
    ∑ a, (q a).toReal * exp (t * Y a) ≤ exp (t * ∑ a, (q a).toReal * Y a + t ^ 2 / 8) := by
  let _ : MeasurableSpace α := ⊤
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure)
    (Measurable.of_discrete (f := Y)).aemeasurable (Filter.Eventually.of_forall hY)
  have hmgf := hsub.mgf_le t
  simp only [ProbabilityTheory.mgf, integral_eq_sum, smul_eq_mul] at hmgf
  set μY := ∑ a, (q a).toReal * Y a
  have hsplit : ∀ a, exp (t * (Y a - μY)) = exp (t * Y a) * exp (-(t * μY)) := fun a => by
    rw [← exp_add]
    ring_nf
  simp only [hsplit, ← mul_assoc, ← sum_mul] at hmgf
  have hc : (‖(1 : ℝ) - 0‖₊ / 2 : NNReal) ^ 2 = (1 / 4 : NNReal) := by
    ext
    simp
    norm_num
  rw [hc] at hmgf
  rw [← le_div_iff₀ (exp_pos _), div_eq_mul_inv, ← exp_neg] at hmgf
  refine hmgf.trans_eq ?_
  rw [← exp_add]
  congr 1
  push_cast
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ s, Fintype (Ω s)]

/-- **Independence** under a product law: the expectation of a product of functions of the
separate coordinates is the product of their expectations. -/
theorem sum_pi_mul_prod (q : ∀ s, PMF (Ω s)) (φ : ∀ s, Ω s → ℝ) :
    ∑ f, (pi q f).toReal * ∏ s, φ s (f s) = ∏ s, ∑ ω, (q s ω).toReal * φ s ω := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun f _ => ?_
  rw [toReal_pi_apply, ← prod_mul_distrib]

end PMF

namespace PMF

variable {Ω M : Type*} [Fintype Ω] [Fintype M] [Nonempty M]

/-- An expectation of a positive function is positive. -/
theorem sum_mul_exp_pos (q : PMF Ω) (g : Ω → ℝ) : 0 < ∑ ω, (q ω).toReal * exp (g ω) := by
  obtain ⟨ω, hω⟩ : ∃ ω, 0 < (q ω).toReal := by
    by_contra h
    push Not at h
    have h1 := sum_toReal q
    rw [sum_eq_zero fun ω _ => le_antisymm (h ω) ENNReal.toReal_nonneg] at h1
    exact zero_ne_one h1
  exact sum_pos' (fun ω _ => mul_nonneg ENNReal.toReal_nonneg (exp_pos _).le)
    ⟨ω, mem_univ ω, mul_pos hω (exp_pos _)⟩

/-- **The maximal inequality**: for `t > 0`, the expected maximum of finitely many variables is
at most `log (∑ m, E exp (t Z m)) / t`. By Jensen's inequality for `exp` and
`exp (t max_m Z m) ≤ ∑ m, exp (t Z m)`. -/
theorem sum_mul_sup'_le_log (q : PMF Ω) (Z : M → Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    ∑ ω, (q ω).toReal * univ.sup' univ_nonempty (fun m => Z m ω) ≤
      log (∑ m, ∑ ω, (q ω).toReal * exp (t * Z m ω)) / t := by
  rw [le_div_iff₀ ht, le_log_iff_exp_le (sum_pos (fun m _ => sum_mul_exp_pos q _) univ_nonempty)]
  have hjensen := convexOn_exp.map_sum_le (t := univ) (w := fun ω => (q ω).toReal)
    (p := fun ω => t * univ.sup' univ_nonempty (fun m => Z m ω))
    (fun _ _ => ENNReal.toReal_nonneg) (sum_toReal q) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  rw [sum_comm]
  refine le_trans (le_of_eq ?_) (hjensen.trans (sum_le_sum fun ω _ => ?_))
  · congr 1
    rw [sum_mul]
    exact sum_congr rfl fun ω _ => by ring
  · rw [← mul_sum]
    gcongr
    obtain ⟨m, -, hm⟩ := exists_mem_eq_sup' univ_nonempty fun m => Z m ω
    rw [hm]
    exact single_le_sum (f := fun m => exp (t * Z m ω)) (fun _ _ => (exp_pos _).le)
      (mem_univ m)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Ω : ι → Type*}
  [∀ s, Fintype (Ω s)]

/-- **The expected maximum of averages of independent bounded variables.** Coordinates
`f s` independent with laws `q s`, `N = |ι|` of them; for each of the `M = |M|` choices `m`,
variables `Y m s (f s) ∈ [0, 1]` with mean at most `p`. Then the expected maximum over `m` of
the average over `s` is at most `p + √(log M / (2 N))`.

CY24 Lemma 1.2.7 (p. 7) with variance proxy `1 / (4N)` from Hoeffding's lemma. -/
theorem sum_pi_mul_sup'_le (q : ∀ s, PMF (Ω s)) (Y : M → ∀ s, Ω s → ℝ)
    (hY : ∀ m s ω, Y m s ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hp : ∀ m s, ∑ ω, (q s ω).toReal * Y m s ω ≤ p) :
    ∑ f, (pi q f).toReal * univ.sup' univ_nonempty (fun m => 𝔼 s, Y m s (f s)) ≤
      p + √(log (Fintype.card M) / (2 * Fintype.card ι)) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 < N := by simp [hN, Fintype.card_pos]
  have hM : 0 ≤ log (Fintype.card M) := log_nonneg (by simp [Nat.one_le_iff_ne_zero])
  -- for each `t > 0`: `E max ≤ p + log M / t + t / (8 N)`
  have key : ∀ t, 0 < t → ∑ f, (pi q f).toReal * univ.sup' univ_nonempty
      (fun m => 𝔼 s, Y m s (f s)) - p ≤ log (Fintype.card M) / t + (1 / (8 * N)) * t := by
    intro t ht
    have hmax := sum_mul_sup'_le_log (pi q) (fun m f => 𝔼 s, Y m s (f s)) ht
    have hone : ∀ m, ∑ f, (pi q f).toReal * exp (t * 𝔼 s, Y m s (f s)) ≤
        exp (t * p + t ^ 2 / (8 * N)) := by
      intro m
      have hprod : ∀ f : ∀ s, Ω s,
          exp (t * 𝔼 s, Y m s (f s)) = ∏ s, exp (t / N * Y m s (f s)) := fun f => by
        rw [← exp_sum, Fintype.expect_eq_sum_div_card, ← hN]
        congr 1
        rw [mul_div_assoc', mul_sum, sum_div]
        exact sum_congr rfl fun s _ => by ring
      simp_rw [hprod]
      rw [sum_pi_mul_prod q fun s ω => exp (t / N * Y m s ω)]
      calc ∏ s, ∑ ω, (q s ω).toReal * exp (t / N * Y m s ω)
          ≤ ∏ s, exp (t / N * ∑ ω, (q s ω).toReal * Y m s ω + (t / N) ^ 2 / 8) :=
            prod_le_prod₀ (fun s _ => sum_nonneg fun ω _ =>
              mul_nonneg ENNReal.toReal_nonneg (exp_pos _).le)
              fun s _ => sum_mul_exp_le_of_mem_Icc (q s) (hY m s) _
        _ ≤ ∏ _s : ι, exp (t / N * p + (t / N) ^ 2 / 8) :=
            prod_le_prod₀ (fun s _ => (exp_pos _).le) fun s _ => by
              gcongr
              exact hp m s
        _ = exp (t * p + t ^ 2 / (8 * N)) := by
            rw [prod_const, ← exp_nat_mul, card_univ, ← hN]
            congr 1
            field_simp
    have hsum : ∑ m, ∑ f, (pi q f).toReal * exp (t * 𝔼 s, Y m s (f s)) ≤
        Fintype.card M * exp (t * p + t ^ 2 / (8 * N)) := by
      refine (sum_le_sum fun m _ => hone m).trans_eq ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hpos : 0 < ∑ m, ∑ f, (pi q f).toReal * exp (t * 𝔼 s, Y m s (f s)) :=
      sum_pos (fun m _ => sum_mul_exp_pos (pi q) _) univ_nonempty
    have hlog := (log_le_log hpos hsum).trans_eq
      (by rw [log_mul (by simp) (exp_pos _).ne', log_exp])
    have := hmax.trans (div_le_div_of_nonneg_right hlog ht.le)
    rw [add_div] at this
    have e : (t * p + t ^ 2 / (8 * N)) / t = p + 1 / (8 * N) * t := by
      field_simp
    rw [e] at this
    linarith
  have := Real.le_two_mul_sqrt_of_forall_le hM (by positivity) key
  have e : 2 * √(log (Fintype.card M) * (1 / (8 * N))) = √(log (Fintype.card M) / (2 * N)) := by
    have h4 : log (Fintype.card M) / (2 * N) = 2 ^ 2 * (log (Fintype.card M) * (1 / (8 * N))) := by
      field_simp
      ring
    rw [h4, sqrt_mul (sq_nonneg _), sqrt_sq zero_le_two]
  linarith [e ▸ this]

end PMF

/-- **The expected maximum of averages, uniform coordinates.** For `f` uniform on `∀ s, Ω s`
and variables `Y m s (f s) ∈ [0, 1]` with `𝔼 ω, Y m s ω ≤ p`:
`𝔼 f, max_m 𝔼 s, Y m s (f s) ≤ p + √(log M / (2 N))`. -/
theorem expect_sup'_expect_le {ι M : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype M]
    [Nonempty M] {Ω : ι → Type*} [∀ s, Fintype (Ω s)] [∀ s, Nonempty (Ω s)]
    (Y : M → ∀ s, Ω s → ℝ) (hY : ∀ m s ω, Y m s ω ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hp : ∀ m s, 𝔼 ω, Y m s ω ≤ p) :
    𝔼 f : (∀ s, Ω s), univ.sup' univ_nonempty (fun m => 𝔼 s, Y m s (f s)) ≤
      p + √(log (Fintype.card M) / (2 * Fintype.card ι)) := by
  have h := PMF.sum_pi_mul_sup'_le (fun s => PMF.uniformOfFintype (Ω s)) Y hY fun m s => by
    refine le_of_eq_of_le ?_ (hp m s)
    rw [Fintype.expect_eq_sum_div_card, sum_div]
    exact sum_congr rfl fun ω _ => by rw [PMF.toReal_uniformOfFintype_apply, inv_mul_eq_div]
  rw [PMF.pi_uniformOfFintype] at h
  refine le_of_eq_of_le ?_ h
  rw [Fintype.expect_eq_sum_div_card, sum_div]
  exact sum_congr rfl fun f _ => by rw [PMF.toReal_uniformOfFintype_apply, inv_mul_eq_div]

/-- **The salt bound in the form the Fiat–Shamir argument uses**. The
function `f` is uniform, and salt value `s` reads only its slice `f s : Slice s →
Out`; the slices are disjoint, so the coordinates are independent. For each choice `m` of the
distinguisher (statement and two witnesses) and each salt `s`, `Y m s (f s) ∈ [0, 1]` (the
indicator of the bad event of the run with salt `s`) has mean at most `p`. Then the expected
fraction of bad salts, maximized over the choices, is at most `p + √(log M / (2 N))`, with `N`
the number of salts. -/
theorem expect_sup'_le_of_slices {Salt M : Type*} [Fintype Salt] [DecidableEq Salt]
    [Nonempty Salt] [Fintype M] [Nonempty M] {Slice : Salt → Type*} [∀ s, Fintype (Slice s)]
    [∀ s, DecidableEq (Slice s)] {Out : Type*} [Fintype Out] [Nonempty Out]
    (Y : M → ∀ s, (Slice s → Out) → ℝ) (hY : ∀ m s g, Y m s g ∈ Set.Icc (0 : ℝ) 1) {p : ℝ}
    (hp : ∀ m s, 𝔼 g, Y m s g ≤ p) :
    𝔼 f : (∀ s, Slice s → Out), univ.sup' univ_nonempty (fun m => 𝔼 s, Y m s (f s)) ≤
      p + √(log (Fintype.card M) / (2 * Fintype.card Salt)) :=
  expect_sup'_expect_le Y hY hp

section Fibers

variable {A B Ω : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype Ω] [Nonempty Ω] (s : A → Option B)

/-- A function on `A` as its restriction to the points with no label (`s a = none`) and its
restrictions to the fibres of the labels. -/
def fiberEquiv : (A → Ω) ≃ ({a // s a = none} → Ω) × (∀ b, {a // s a = some b} → Ω) where
  toFun f := (fun a => f a, fun _ a => f a)
  invFun g a := match h : s a with
    | none => g.1 ⟨a, h⟩
    | some b => g.2 b ⟨a, h⟩
  left_inv f := by
    funext a
    dsimp only
    split <;> rfl
  right_inv g := by
    obtain ⟨g₁, g₂⟩ := g
    refine Prod.ext (funext fun a => ?_) (funext fun b => funext fun a => ?_)
    · obtain ⟨a, ha⟩ := a
      dsimp only
      split
      · rfl
      · next b h => exact absurd (h.symm.trans ha) (by simp)
    · obtain ⟨a, ha⟩ := a
      dsimp only
      split
      · next h => exact absurd (h.symm.trans ha) (by simp)
      · next b' h =>
        obtain rfl : b' = b := Option.some_injective _ (h.symm.trans ha)
        rfl

omit [Nonempty Ω] in
/-- The uniform expectation over functions on `A` splits into the expectation over the unlabeled
part and the labeled fibres. -/
theorem expect_fiberEquiv [Nonempty Ω] (Φ : (A → Ω) → ℝ) :
    𝔼 f, Φ f = 𝔼 r : {a // s a = none} → Ω, 𝔼 g : ∀ b, {a // s a = some b} → Ω,
      Φ ((fiberEquiv s).symm (r, g)) := by
  rw [← Fintype.expect_equiv (fiberEquiv s).symm (fun p => Φ ((fiberEquiv s).symm p)) Φ
    fun _ => rfl, ← Finset.univ_product_univ]
  exact Finset.expect_product' _ _ fun r g => Φ ((fiberEquiv s).symm (r, g))

omit [Nonempty Ω] in
/-- The restriction of a uniform function to a subtype is uniform. -/
theorem expect_restrict [Nonempty Ω] (p : A → Prop) [DecidablePred p]
    (Ψ : ({a // p a} → Ω) → ℝ) :
    𝔼 g : A → Ω, Ψ (fun a => g a) = 𝔼 g : {a // p a} → Ω, Ψ g := by
  rw [← Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p fun _ => Ω).symm
    (fun q => Ψ q.1) (fun g => Ψ fun a => g a) fun q => by
      congr 1
      funext a
      simp [Equiv.piEquivPiSubtypeProd, a.2], ← Finset.univ_product_univ,
    Finset.expect_product' _ _ fun a _ => Ψ a]
  simp

/-- **The expected maximum of averages over labeled fibres** (the salt bound of
`SPBCS.expect_sup'_fpDist_le`). Points `a` of a uniform function `f : A → Ω` carry an
optional label `s a ∈ B` (the salt a query reads). For each choice `m` and label `b`, the variable
`Y m b f ∈ [0, 1]` reads `f` only at the points labeled `b` and the unlabeled points, and for every
fixed value of `f` off the fibre of `b` its mean over the fibre of `b` is at most `p`. Then
`E_f max_m avg_b Y m b f ≤ p + √(log M / (2 |B|))`: given the unlabeled part, the fibres are
independent (`expect_sup'_le_of_slices`). -/
theorem expect_sup'_le_of_fibers {M : Type*} [Fintype M] [Nonempty M] (Y : M → B → (A → Ω) → ℝ)
    (hY : ∀ m b f, Y m b f ∈ Set.Icc (0 : ℝ) 1)
    (hloc : ∀ m b f f', (∀ a, s a = some b ∨ s a = none → f a = f' a) → Y m b f = Y m b f')
    {p : ℝ} (hp : ∀ m b (f : A → Ω), 𝔼 g : A → Ω, Y m b (fun a => if s a = some b then g a else f a) ≤ p) :
    𝔼 f : A → Ω, univ.sup' univ_nonempty (fun m => 𝔼 b, Y m b f) ≤
      p + √(log (Fintype.card M) / (2 * Fintype.card B)) := by
  classical
  rw [expect_fiberEquiv s]
  refine (Finset.expect_le_expect fun r _ => ?_).trans_eq (Fintype.expect_const _)
  let g₀ : ∀ b, {a // s a = some b} → Ω := fun _ _ => Classical.arbitrary Ω
  let Y' : M → ∀ b, ({a // s a = some b} → Ω) → ℝ := fun m b gb =>
    Y m b ((fiberEquiv s).symm (r, Function.update g₀ b gb))
  have hfib : ∀ (g : ∀ b, {a // s a = some b} → Ω) b a (ha : s a = some b),
      (fiberEquiv s).symm (r, g) a = g b ⟨a, ha⟩ := fun g b a ha => by
    simp only [fiberEquiv, Equiv.coe_fn_symm_mk]
    split
    · next h => exact absurd (h.symm.trans ha) (by simp)
    · next b' h =>
      obtain rfl : b' = b := Option.some_injective _ (h.symm.trans ha)
      rfl
  have hnone : ∀ (g : ∀ b, {a // s a = some b} → Ω) a (ha : s a = none),
      (fiberEquiv s).symm (r, g) a = r ⟨a, ha⟩ := fun g a ha => by
    simp only [fiberEquiv, Equiv.coe_fn_symm_mk]
    split
    · rfl
    · next b' h => exact absurd (h.symm.trans ha) (by simp)
  have hY' : ∀ m b g, Y m b ((fiberEquiv s).symm (r, g)) = Y' m b (g b) := fun m b g =>
    hloc m b _ _ fun a ha => by
      rcases ha with ha | ha
      · rw [hfib _ b a ha, hfib _ b a ha, Function.update_self]
      · rw [hnone _ a ha, hnone _ a ha]
  simp_rw [hY']
  refine expect_sup'_le_of_slices Y' (fun m b g => hY m b _) fun m b => ?_
  have h := hp m b ((fiberEquiv s).symm (r, g₀))
  have heq : ∀ g : A → Ω, (fun a => if s a = some b then g a else (fiberEquiv s).symm (r, g₀) a) =
      (fiberEquiv s).symm (r, Function.update g₀ b fun a => g a) := fun g => by
    funext a
    by_cases ha : s a = some b
    · rw [if_pos ha, hfib _ b a ha, Function.update_self]
    · rw [if_neg ha]
      rcases hs : s a with _ | b'
      · rw [hnone _ a hs, hnone _ a hs]
      · have hb' : b' ≠ b := fun e => ha (hs.trans (congrArg some e))
        rw [hfib _ b' a hs, hfib _ b' a hs, Function.update_of_ne hb']
  simp_rw [heq] at h
  exact (expect_restrict (fun a => s a = some b) (Y' m b)).symm.trans_le h

end Fibers
