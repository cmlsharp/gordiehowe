-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Total variation of causal products

A law on `ι → Y` is a causal product for a rank `rank : ι → ℕ` when its mass at `f` is
`∏ i, p f i (f i)` and each kernel `p f i` reads only the coordinates of `f` of lower rank
(`PMF.RankCausal`). Sampling the coordinates in order of rank, coordinate `i` is drawn from
`p f i` given the coordinates already drawn. This file bounds the distance of two causal products
by the sum of their kernel distances (`PMF.tvDist_le_of_rankCausal`), the hybrid argument over the
coordinates in order of rank. Products of independent coordinates (`PMF.tvDist_pi_le`) are the
case of kernels that read no coordinate.

The proof enumerates the coordinates as `Fin n` in an order compatible with the rank
(`PMF.exists_equiv_fin_monotone`) and goes by induction on `n`, splitting off the first coordinate
(`PMF.sum_abs_prod_sub_prod_causal_fin`).

To upstream: Mathlib has no total variation distance for `PMF`.
-/

open Finset

namespace PMF

variable {Y : Type*} [Fintype Y]

/-! ### Kernels in coordinate order -/

section Fin

/-- A sum over `Fin (n + 1) → Y` splits off the first coordinate. -/
theorem sum_fin_succ_pi {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin (n + 1) → Y) → M) :
    ∑ f, F f = ∑ y, ∑ g : Fin n → Y, F (Fin.cons y g) := by
  rw [← (Fin.consEquiv fun _ => Y).sum_comp, Fintype.sum_prod_type]
  rfl

variable [Nonempty Y]

/-- **A causal product has total mass one**, coordinates in index order: if every kernel
`a f i` is a nonnegative family summing to one that reads only the coordinates of `f` below `i`,
then `∑ f, ∏ i, a f i (f i) = 1`. -/
theorem sum_prod_causal_fin : ∀ {n : ℕ} (a : (Fin n → Y) → Fin n → Y → ℝ),
    (∀ f f' i, (∀ j < i, f j = f' j) → a f i = a f' i) → (∀ f i, ∑ x, a f i x = 1) →
    ∑ f : Fin n → Y, ∏ i, a f i (f i) = 1
  | 0, _, _, _ => by simp
  | n + 1, a, hc, h1 => by
    set f₀ : Fin (n + 1) → Y := fun _ => Classical.arbitrary Y
    have hsplit : ∀ y (g : Fin n → Y),
        ∏ i, a (Fin.cons y g) i ((Fin.cons y g : Fin (n + 1) → Y) i) =
        a f₀ 0 y * ∏ i : Fin n, a (Fin.cons y g) i.succ (g i) := fun y g => by
      rw [Fin.prod_univ_succ, Fin.cons_zero,
        hc _ f₀ 0 fun j hj => absurd hj (Fin.not_lt_zero j)]
      simp only [Fin.cons_succ]
    have htail : ∀ y, ∑ g : Fin n → Y, ∏ i : Fin n, a (Fin.cons y g) i.succ (g i) = 1 :=
      fun y => sum_prod_causal_fin (fun g i x => a (Fin.cons y g) i.succ x)
        (fun g g' i hg => hc _ _ _ fun j hj => by
          cases j using Fin.cases with
          | zero => rfl
          | succ j => simp only [Fin.cons_succ]; exact hg j (Fin.succ_lt_succ_iff.1 hj))
        fun g i => h1 _ _
    rw [sum_fin_succ_pi]
    simp only [hsplit, ← mul_sum, htail, mul_one]
    exact h1 f₀ 0

/-- **The hybrid argument for causal products**, coordinates in index order: if every kernel
`a f i` and `b f i` is a nonnegative family summing to one that reads only the coordinates of
`f` below `i`, and the kernels at every `f` and `i` are within `B` in `ℓ¹`, then the two products
are within `n · B` in `ℓ¹`. -/
theorem sum_abs_prod_sub_prod_causal_fin : ∀ {n : ℕ} (a b : (Fin n → Y) → Fin n → Y → ℝ),
    (∀ f i x, 0 ≤ a f i x) → (∀ f i x, 0 ≤ b f i x) →
    (∀ f i, ∑ x, a f i x = 1) → (∀ f i, ∑ x, b f i x = 1) →
    (∀ f f' i, (∀ j < i, f j = f' j) → a f i = a f' i) →
    (∀ f f' i, (∀ j < i, f j = f' j) → b f i = b f' i) → ∀ B : ℝ,
    (∀ f i, ∑ x, |a f i x - b f i x| ≤ B) →
    ∑ f : Fin n → Y, |∏ i, a f i (f i) - ∏ i, b f i (f i)| ≤ n * B
  | 0, _, _, _, _, _, _, _, _, _, _ => by simp
  | n + 1, a, b, ha0, hb0, ha1, hb1, hca, hcb, B, hB => by
    set f₀ : Fin (n + 1) → Y := fun _ => Classical.arbitrary Y
    have hsplit : ∀ (c : (Fin (n + 1) → Y) → Fin (n + 1) → Y → ℝ),
        (∀ f f' i, (∀ j < i, f j = f' j) → c f i = c f' i) → ∀ y (g : Fin n → Y),
        ∏ i, c (Fin.cons y g) i ((Fin.cons y g : Fin (n + 1) → Y) i) =
          c f₀ 0 y * ∏ i : Fin n, c (Fin.cons y g) i.succ (g i) := fun c hc y g => by
      rw [Fin.prod_univ_succ, Fin.cons_zero,
        hc _ f₀ 0 fun j hj => absurd hj (Fin.not_lt_zero j)]
      simp only [Fin.cons_succ]
    have htail : ∀ (c : (Fin (n + 1) → Y) → Fin (n + 1) → Y → ℝ),
        (∀ f f' i, (∀ j < i, f j = f' j) → c f i = c f' i) → ∀ y,
        ∀ g g' : Fin n → Y, ∀ i : Fin n, (∀ j < i, g j = g' j) →
          c (Fin.cons y g) i.succ = c (Fin.cons y g') i.succ := fun c hc y g g' i hg =>
      hc _ _ _ fun j hj => by
        cases j using Fin.cases with
        | zero => rfl
        | succ j => simp only [Fin.cons_succ]; exact hg j (Fin.succ_lt_succ_iff.1 hj)
    set A : Y → (Fin n → Y) → ℝ := fun y g => ∏ i : Fin n, a (Fin.cons y g) i.succ (g i)
    set Bp : Y → (Fin n → Y) → ℝ := fun y g => ∏ i : Fin n, b (Fin.cons y g) i.succ (g i)
    have hA1 : ∀ y, ∑ g, A y g = 1 := fun y =>
      sum_prod_causal_fin (fun g i x => a (Fin.cons y g) i.succ x) (htail a hca y)
        fun g i => ha1 _ _
    have hAB : ∀ y, ∑ g, |A y g - Bp y g| ≤ n * B := fun y =>
      sum_abs_prod_sub_prod_causal_fin (fun g i x => a (Fin.cons y g) i.succ x)
        (fun g i x => b (Fin.cons y g) i.succ x) (fun _ _ _ => ha0 _ _ _) (fun _ _ _ => hb0 _ _ _)
        (fun g i => ha1 _ _) (fun g i => hb1 _ _) (htail a hca y) (htail b hcb y) B
        fun g i => hB _ _
    have hpt : ∀ y g, |a f₀ 0 y * A y g - b f₀ 0 y * Bp y g| ≤
        |a f₀ 0 y - b f₀ 0 y| * A y g + b f₀ 0 y * |A y g - Bp y g| := fun y g => by
      have hA0 : 0 ≤ A y g := prod_nonneg fun i _ => ha0 _ _ _
      calc |a f₀ 0 y * A y g - b f₀ 0 y * Bp y g|
          = |(a f₀ 0 y - b f₀ 0 y) * A y g + b f₀ 0 y * (A y g - Bp y g)| := by ring_nf
        _ ≤ |(a f₀ 0 y - b f₀ 0 y) * A y g| + |b f₀ 0 y * (A y g - Bp y g)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg (hb0 _ _ _)]
    rw [sum_fin_succ_pi]
    simp only [hsplit a hca, hsplit b hcb]
    calc ∑ y, ∑ g, |a f₀ 0 y * A y g - b f₀ 0 y * Bp y g|
        ≤ ∑ y, ∑ g, (|a f₀ 0 y - b f₀ 0 y| * A y g + b f₀ 0 y * |A y g - Bp y g|) :=
          sum_le_sum fun y _ => sum_le_sum fun g _ => hpt y g
      _ = ∑ y, (|a f₀ 0 y - b f₀ 0 y| + b f₀ 0 y * ∑ g, |A y g - Bp y g|) := by
          refine sum_congr rfl fun y _ => ?_
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, hA1, mul_one]
      _ ≤ ∑ y, (|a f₀ 0 y - b f₀ 0 y| + b f₀ 0 y * (n * B)) :=
          sum_le_sum fun y _ => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hAB y) (hb0 _ _ _))
      _ ≤ B + n * B := by
          rw [sum_add_distrib, ← sum_mul, hb1, one_mul]
          exact add_le_add (hB f₀ 0) le_rfl
      _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

end Fin

/-! ### Kernels in order of rank -/

variable {ι β : Type*} [Fintype ι]

/-- **A family of kernels is causal for a rank**: the kernel `a f i` reads only the coordinates
of `f` whose rank is below the rank of `i`. -/
def RankCausal (rank : ι → ℕ) (a : (ι → Y) → ι → β) : Prop :=
  ∀ ⦃f f' : ι → Y⦄ (i : ι), (∀ j, rank j < rank i → f j = f' j) → a f i = a f' i

omit [Fintype Y] in
/-- **An enumeration compatible with a rank**: the elements of a finite type can be listed as
`Fin (card ι)` with nondecreasing rank. -/
theorem exists_equiv_fin_monotone (rank : ι → ℕ) :
    ∃ σ : Fin (Fintype.card ι) ≃ ι, Monotone (rank ∘ σ) := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (fun i => toLex (rank i, Fintype.equivFin ι i))
    fun i j h => (Fintype.equivFin ι).injective (Prod.ext_iff.1 (toLex.injective h)).2
  refine ⟨(Fintype.orderIsoFinOfCardEq ι rfl).toEquiv, fun a b hab => ?_⟩
  have h : toLex (rank ((Fintype.orderIsoFinOfCardEq ι rfl) a),
      Fintype.equivFin ι ((Fintype.orderIsoFinOfCardEq ι rfl) a)) ≤
      toLex (rank ((Fintype.orderIsoFinOfCardEq ι rfl) b),
        Fintype.equivFin ι ((Fintype.orderIsoFinOfCardEq ι rfl) b)) :=
    (Fintype.orderIsoFinOfCardEq ι rfl).monotone hab
  rcases Prod.Lex.toLex_le_toLex.1 h with h | h
  · exact h.le
  · exact h.1.le

variable [DecidableEq ι] [Nonempty Y]

/-- **The hybrid argument for causal products**: if every kernel `a f i` and `b f i` is a
nonnegative family summing to one that is causal for `rank`, and the kernels at every `f` and `i`
are within `B` in `ℓ¹`, then the two products are within `|ι| · B` in `ℓ¹`. -/
theorem sum_abs_prod_sub_prod_rankCausal_le (rank : ι → ℕ) (a b : (ι → Y) → ι → Y → ℝ)
    (ha0 : ∀ f i x, 0 ≤ a f i x) (hb0 : ∀ f i x, 0 ≤ b f i x) (ha1 : ∀ f i, ∑ x, a f i x = 1)
    (hb1 : ∀ f i, ∑ x, b f i x = 1) (hca : RankCausal rank a) (hcb : RankCausal rank b) {B : ℝ}
    (hB : ∀ f i, ∑ x, |a f i x - b f i x| ≤ B) :
    ∑ f : ι → Y, |∏ i, a f i (f i) - ∏ i, b f i (f i)| ≤ Fintype.card ι * B := by
  obtain ⟨σ, hσ⟩ := exists_equiv_fin_monotone rank
  set τ : (Fin (Fintype.card ι) → Y) ≃ (ι → Y) := σ.arrowCongr (Equiv.refl Y)
  have hτ : ∀ g j, τ g (σ j) = g j := fun g j => by simp [τ, Equiv.arrowCongr_apply]
  have hfin : ∀ c : (ι → Y) → ι → Y → ℝ, RankCausal rank c →
      ∀ g g' : Fin (Fintype.card ι) → Y, ∀ i, (∀ j < i, g j = g' j) →
        c (τ g) (σ i) = c (τ g') (σ i) := fun c hc g g' i hg => hc _ fun k hk => by
    have hk' : σ.symm k < i := by
      by_contra hle
      have := hσ (not_lt.1 hle)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      omega
    rw [← σ.apply_symm_apply k, hτ, hτ]
    exact hg _ hk'
  have hprod : ∀ (c : (ι → Y) → ι → Y → ℝ) g,
      ∏ i, c (τ g) i (τ g i) = ∏ j, c (τ g) (σ j) (g j) := fun c g => by
    rw [← σ.prod_comp]
    simp only [hτ]
  rw [← τ.sum_comp]
  simp only [hprod]
  exact sum_abs_prod_sub_prod_causal_fin (fun g j x => a (τ g) (σ j) x)
    (fun g j x => b (τ g) (σ j) x) (fun _ _ _ => ha0 _ _ _) (fun _ _ _ => hb0 _ _ _)
    (fun _ _ => ha1 _ _) (fun _ _ => hb1 _ _) (hfin a hca) (hfin b hcb) B fun _ _ => hB _ _

/-- **The distance of two causal products** is at most `|ι| · B` when the kernels at every
`f` and `i` are within `B`: the laws `P` and `Q` on `ι → Y` have masses `∏ i, p f i (f i)` and
`∏ i, q f i (f i)` with kernel families `p` and `q` causal for `rank`. -/
theorem tvDist_le_of_rankCausal (rank : ι → ℕ) {P Q : PMF (ι → Y)} (p q : (ι → Y) → ι → PMF Y)
    (hp : RankCausal rank p) (hq : RankCausal rank q) (hP : ∀ f, P f = ∏ i, p f i (f i))
    (hQ : ∀ f, Q f = ∏ i, q f i (f i)) {B : ℝ} (hB : ∀ f i, tvDist (p f i) (q f i) ≤ B) :
    tvDist P Q ≤ Fintype.card ι * B := by
  have hB' : ∀ f i, ∑ x, |(p f i x).toReal - (q f i x).toReal| ≤ 2 * B := fun f i => by
    have := hB f i
    rw [tvDist_eq_sum] at this
    linarith
  have h := sum_abs_prod_sub_prod_rankCausal_le rank (fun f i x => (p f i x).toReal)
    (fun f i x => (q f i x).toReal) (fun _ _ _ => ENNReal.toReal_nonneg)
    (fun _ _ _ => ENNReal.toReal_nonneg) (fun f i => sum_toReal _) (fun f i => sum_toReal _)
    (fun f f' i hf => by simp only [hp i hf]) (fun f f' i hf => by simp only [hq i hf]) hB'
  rw [tvDist_eq_sum]
  simp only [hP, hQ, ENNReal.toReal_prod]
  linarith

end PMF
