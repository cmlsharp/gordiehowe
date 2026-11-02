-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.Determinant
public import GordieHowe.Applications.Params
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.ZMod.ValMinAbs

@[expose] public section

/-!
# Small spectral supports

The small-support bounds of "A shorter proof of the stated HighBits regularity claim"
(10 September 2026, Section 4, equations (9)–(13)), for a kernel `f` on `ZMod q` with
`0 ≤ f ≤ 1` and `f x · |x| ≤ C` for `x ≠ 0`, where `|x|` is the centered absolute value
(`IsKernelBound`). The note uses `C = q / (2L)` (one accepted interval); the hint-split kernel of
the regularity route has `C = q / L`, and the uniform bounds below are stated for every
`C ≤ q / L₀` with `L₀ = 190307`, the smallest accepted cell size of the three parameter sets.

A support `T ⊆ K` is a set of roots of `X^a + 1`; its words are `y_b = Σ_{ρ ∈ T} λ_ρ ρ^b`
(`word`), parametrized by the amplitudes `λ` supported on `T` (`amplitudes`), and

    spectralSum f a s T = Σ_{λ ≠ 0} ∏_{b < a} f (y_b) ^ s,

the note's `δ_{a,s}(T)`. The results:

- `spectralSum_le_of_pow_le`, note (9): at length `a = 2^e` and `|T| ≤ r ≤ a`,
  `δ_{a,s}(T) ≤ q^r / d^s` whenever `(C d)^a · a! ≤ q^(a - r)`, by Lemma 2
  (`pow_le_factorial_mul_pow_of_mem_span`) applied to the centered lift of each nonzero word;
- `spectralSum_two_mul_le_of_forall_neg_notMem`, note (11): with no opposite pair `ρ, -ρ` in
  `T`, `δ_{2a,s}(T) ≤ δ_{a,2s}(T²)`, where `T²` is the image of squaring;
- `spectralSum_two_mul_le`, note (12): in general
  `δ_{2a,s}(T) ≤ 2 δ_{a,s}(P) + δ_{a,s}(P)^2 + δ_{a,s}(T²)^2`, where `P` is the set of squares
  of opposite pairs (`pairedSquares`), with `|P| + |T²| ≤ |T|`
  (`card_pairedSquares_add_card_image_le`). The even and odd coefficients of a word of length
  `2a` are the words of `evenPart λ` and `oddPart λ` at length `a`, and `λ ↦ (evenPart λ,
  oddPart λ)` is injective (the pairing has determinant `-2ρ ≠ 0`);
- the uniform bounds at length `256` and exponent one, `spectralSum_le_one_div_two_pow_617`
  (`|T| ≤ 1`), `…_210` (`|T| ≤ 2`), `…_155` (`|T| ≤ 3`) and `…_52` (`|T| ≤ 4`).

- at cell size at least `523383` (ML-DSA-65 and ML-DSA-87), `C ≤ q / 523383`, the chain
  `cellBound₁ … ₅` gives `δ₁ ≤ 2^-512, δ₂ ≤ 2^-358, δ₃ ≤ 2^-214, δ₄ ≤ 2^-99` and
  `δ₅ ≤ 2^-7` (`spectralSum_cell₁_le … spectralSum_cell₅_le`), with the Hadamard form
  (`spectralSum_le_of_pow_le_hadamard`) at `|T| ≤ 3, 4`.

The uniform bounds use the Leibniz form of Lemma 2 and the stopping lengths `2, 4, 8, 16`
for `|T| ≤ 1, 2, 3, 4`; the bounds `smallSupportBound₁ … ₄` record the recursion.
-/

open Finset

namespace GordieHowe.MLDSA.Regularity

/-! ### Two finite-sum facts -/

/-- A sum over an injective image is at most the sum over any superset of the image, for
nonnegative terms. -/
theorem sum_comp_le_sum_of_injOn {ι κ : Type*} {s : Finset ι} {t : Finset κ} {g : ι → κ}
    {F : κ → ℝ} (hg : Set.InjOn g s) (hmaps : ∀ x ∈ s, g x ∈ t) (hF : ∀ y ∈ t, 0 ≤ F y) :
    ∑ x ∈ s, F (g x) ≤ ∑ y ∈ t, F y := by
  classical
  rw [← Finset.sum_image hg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y hy _ => hF y hy
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  exact hmaps x hx

/-- A product over `range (2a)` pairs the even and odd indices. -/
theorem prod_range_two_mul {M : Type*} [CommMonoid M] (g : ℕ → M) (a : ℕ) :
    ∏ b ∈ range (2 * a), g b = ∏ c ∈ range a, (g (2 * c) * g (2 * c + 1)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring, prod_range_succ (n := 2 * a + 1),
      prod_range_succ (n := 2 * a), ih, prod_range_succ (n := a), mul_assoc]

/-- `2x + x² + y²` is monotone on nonnegative arguments. -/
theorem two_mul_add_sq_add_sq_le {x X y Y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hy0 : 0 ≤ y)
    (hy : y ≤ Y) : 2 * x + x ^ 2 + y ^ 2 ≤ 2 * X + X ^ 2 + Y ^ 2 := by
  nlinarith [mul_le_mul hx hx hx0 (hx0.trans hx), mul_le_mul hy hy hy0 (hy0.trans hy)]

/-! ### Words, weights and the support sum -/

section Field

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The amplitude vectors supported on `T`. -/
def amplitudes (T : Finset K) : Finset (K → K) :=
  univ.filter fun l => ∀ ρ, l ρ ≠ 0 → ρ ∈ T

theorem mem_amplitudes {T : Finset K} {l : K → K} :
    l ∈ amplitudes T ↔ ∀ ρ, l ρ ≠ 0 → ρ ∈ T := by
  simp [amplitudes]

theorem zero_mem_amplitudes (T : Finset K) : (0 : K → K) ∈ amplitudes T :=
  mem_amplitudes.2 fun _ h => absurd rfl h

theorem eq_zero_of_mem_amplitudes {T : Finset K} {l : K → K} (hl : l ∈ amplitudes T) {ρ : K}
    (hρ : ρ ∉ T) : l ρ = 0 :=
  by_contra fun h => hρ (mem_amplitudes.1 hl ρ h)

/-- There are at most `|K|^|T|` amplitude vectors supported on `T`. -/
theorem card_amplitudes_le (T : Finset K) :
    (amplitudes T).card ≤ Fintype.card K ^ T.card := by
  calc (amplitudes T).card ≤ (univ : Finset (T → K)).card := by
        refine card_le_card_of_injOn (fun l (ρ : T) => l ρ) (fun _ _ => mem_univ _) ?_
        intro l hl l' hl' h
        funext ρ
        by_cases hρ : ρ ∈ T
        · exact congrFun h ⟨ρ, hρ⟩
        · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]
    _ = Fintype.card K ^ T.card := by rw [card_univ, Fintype.card_fun, Fintype.card_coe]

/-- **The word** of an amplitude vector: `y_b = Σ_ρ λ_ρ ρ^b`. -/
def word (l : K → K) (b : ℕ) : K := ∑ ρ, l ρ * ρ ^ b

theorem word_eq_sum {T : Finset K} {l : K → K} (hl : l ∈ amplitudes T) (b : ℕ) :
    word l b = ∑ ρ ∈ T, l ρ * ρ ^ b := by
  rw [word]
  symm
  exact Finset.sum_subset (subset_univ T) fun ρ _ hρ => by
    rw [eq_zero_of_mem_amplitudes hl hρ, zero_mul]

/-- A nonzero amplitude vector on at most `a` distinct points has a nonzero coefficient among
the first `a` (Vandermonde). -/
theorem exists_word_ne_zero {T : Finset K} {l : K → K} (hl : l ∈ amplitudes T) (hl0 : l ≠ 0)
    {a : ℕ} (hTa : T.card ≤ a) : ∃ b < a, word l b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hl0
  set e := T.equivFin.symm with he
  have hv : (fun j : Fin T.card => l (e j)) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun j => (e j : K)) ?_ ?_
    · intro i j h
      exact e.injective (Subtype.ext h)
    · intro i
      have h := hcon i (lt_of_lt_of_le i.isLt hTa)
      rw [word_eq_sum hl, ← Finset.sum_coe_sort T] at h
      rw [← h]
      exact e.sum_comp (fun ρ : T => l ρ * (ρ : K) ^ (i : ℕ))
  funext ρ
  by_cases hρ : ρ ∈ T
  · have h := congrFun hv (T.equivFin ⟨ρ, hρ⟩)
    simpa [he] using h
  · exact eq_zero_of_mem_amplitudes hl hρ

/-- The weight `∏_{b < a} f (y_b) ^ s` of an amplitude vector. -/
def weight (f : K → ℝ) (a s : ℕ) (l : K → K) : ℝ := ∏ b ∈ range a, f (word l b) ^ s

/-- **The support sum** `δ_{a,s}(T) = Σ_{λ ≠ 0} ∏_{b < a} f (y_b) ^ s` (note, Section 4). -/
def spectralSum (f : K → ℝ) (a s : ℕ) (T : Finset K) : ℝ :=
  ∑ l ∈ (amplitudes T).erase 0, weight f a s l

variable {f : K → ℝ}

omit [DecidableEq K] in
theorem weight_nonneg (hf0 : ∀ x, 0 ≤ f x) (a s : ℕ) (l : K → K) : 0 ≤ weight f a s l :=
  prod_nonneg fun _ _ => pow_nonneg (hf0 _) s

omit [DecidableEq K] in
theorem weight_le_one (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (a s : ℕ) (l : K → K) :
    weight f a s l ≤ 1 :=
  prod_le_one₀ (fun _ _ => pow_nonneg (hf0 _) s) fun _ _ => pow_le_one₀ (hf0 _) (hf1 _)

theorem spectralSum_nonneg (hf0 : ∀ x, 0 ≤ f x) (a s : ℕ) (T : Finset K) :
    0 ≤ spectralSum f a s T :=
  sum_nonneg fun l _ => weight_nonneg hf0 a s l

omit [DecidableEq K] in
theorem weight_sq (a s : ℕ) (l : K → K) : weight f a s l ^ 2 = weight f a (2 * s) l := by
  rw [weight, weight, ← prod_pow]
  refine prod_congr rfl fun b _ => ?_
  rw [← pow_mul, mul_comm]

/-! ### Halving the length -/

/-- The amplitudes of the even coefficients: `ν ↦ Σ_{ρ² = ν} λ_ρ`. -/
def evenPart (l : K → K) (ν : K) : K := ∑ ρ ∈ univ.filter (fun ρ => ρ ^ 2 = ν), l ρ

/-- The amplitudes of the odd coefficients: `ν ↦ Σ_{ρ² = ν} ρ λ_ρ`. -/
def oddPart (l : K → K) (ν : K) : K := ∑ ρ ∈ univ.filter (fun ρ => ρ ^ 2 = ν), ρ * l ρ

theorem evenPart_zero : evenPart (0 : K → K) = 0 := by
  funext ν
  simp [evenPart]

theorem oddPart_zero : oddPart (0 : K → K) = 0 := by
  funext ν
  simp [oddPart]

/-- The even coefficients of a word are the word of `evenPart`. -/
theorem word_evenPart (l : K → K) (b : ℕ) : word (evenPart l) b = word l (2 * b) := by
  rw [word, word, ← Finset.sum_fiberwise univ (fun ρ : K => ρ ^ 2)
    (fun ρ => l ρ * ρ ^ (2 * b))]
  refine sum_congr rfl fun ν _ => ?_
  rw [evenPart, sum_mul]
  refine sum_congr rfl fun ρ hρ => ?_
  rw [← (mem_filter.1 hρ).2, pow_mul]

/-- The odd coefficients of a word are the word of `oddPart`. -/
theorem word_oddPart (l : K → K) (b : ℕ) : word (oddPart l) b = word l (2 * b + 1) := by
  rw [word, word, ← Finset.sum_fiberwise univ (fun ρ : K => ρ ^ 2)
    (fun ρ => l ρ * ρ ^ (2 * b + 1))]
  refine sum_congr rfl fun ν _ => ?_
  rw [oddPart, sum_mul]
  refine sum_congr rfl fun ρ hρ => ?_
  rw [← (mem_filter.1 hρ).2]
  ring

/-- The weight at length `2a` is the product of the weights of the two halves. -/
theorem weight_two_mul (a s : ℕ) (l : K → K) :
    weight f (2 * a) s l = weight f a s (evenPart l) * weight f a s (oddPart l) := by
  rw [weight, prod_range_two_mul, prod_mul_distrib, weight, weight]
  simp only [word_evenPart, word_oddPart]

omit [Fintype K] [DecidableEq K] in
theorem self_ne_neg_of_ne_zero (h2 : (2 : K) ≠ 0) {ρ : K} (hρ : ρ ≠ 0) : ρ ≠ -ρ := by
  intro h
  have h' : (2 : K) * ρ = 0 := by linear_combination h
  exact mul_ne_zero h2 hρ h'

theorem filter_sq_eq_sq (ρ : K) : univ.filter (fun x : K => x ^ 2 = ρ ^ 2) = {ρ, -ρ} := by
  ext x
  simp [sq_eq_sq_iff_eq_or_eq_neg]

theorem evenPart_sq (h2 : (2 : K) ≠ 0) {ρ : K} (hρ : ρ ≠ 0) (l : K → K) :
    evenPart l (ρ ^ 2) = l ρ + l (-ρ) := by
  rw [evenPart, filter_sq_eq_sq, sum_pair (self_ne_neg_of_ne_zero h2 hρ)]

theorem oddPart_sq (h2 : (2 : K) ≠ 0) {ρ : K} (hρ : ρ ≠ 0) (l : K → K) :
    oddPart l (ρ ^ 2) = ρ * l ρ - ρ * l (-ρ) := by
  rw [oddPart, filter_sq_eq_sq, sum_pair (self_ne_neg_of_ne_zero h2 hρ)]
  ring

theorem evenPart_mem {T : Finset K} {l : K → K} (hl : l ∈ amplitudes T) :
    evenPart l ∈ amplitudes (T.image (· ^ 2)) := by
  refine mem_amplitudes.2 fun ν hν => ?_
  obtain ⟨ρ, hρ, hlρ⟩ := exists_ne_zero_of_sum_ne_zero hν
  exact mem_image.2 ⟨ρ, mem_amplitudes.1 hl ρ hlρ, (mem_filter.1 hρ).2⟩

theorem oddPart_mem {T : Finset K} {l : K → K} (hl : l ∈ amplitudes T) :
    oddPart l ∈ amplitudes (T.image (· ^ 2)) := by
  refine mem_amplitudes.2 fun ν hν => ?_
  obtain ⟨ρ, hρ, hlρ⟩ := exists_ne_zero_of_sum_ne_zero hν
  exact mem_image.2 ⟨ρ, mem_amplitudes.1 hl ρ (right_ne_zero_of_mul hlρ), (mem_filter.1 hρ).2⟩

/-- **The pairing change of variables is invertible**: the two halves determine the amplitudes
(note, after (12): determinant `-2ρ ≠ 0`). -/
theorem eq_of_evenPart_eq_of_oddPart_eq (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T)
    (he : evenPart l = evenPart l') (ho : oddPart l = oddPart l') : l = l' := by
  funext ρ
  by_cases hρ : ρ ∈ T
  · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρ h0
    have h1 := congrFun he (ρ ^ 2)
    have h3 := congrFun ho (ρ ^ 2)
    rw [evenPart_sq h2 hρ0, evenPart_sq h2 hρ0] at h1
    rw [oddPart_sq h2 hρ0, oddPart_sq h2 hρ0] at h3
    have h : (2 * ρ) * l ρ = (2 * ρ) * l' ρ := by linear_combination ρ * h1 + h3
    exact mul_left_cancel₀ (mul_ne_zero h2 hρ0) h
  · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]

/-- Without opposite pairs, the even half alone determines the amplitudes. -/
theorem eq_of_evenPart_eq (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    (hT : ∀ ρ ∈ T, -ρ ∉ T) {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T)
    (he : evenPart l = evenPart l') : l = l' := by
  funext ρ
  by_cases hρ : ρ ∈ T
  · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρ h0
    have h1 := congrFun he (ρ ^ 2)
    rw [evenPart_sq h2 hρ0, evenPart_sq h2 hρ0, eq_zero_of_mem_amplitudes hl (hT ρ hρ),
      eq_zero_of_mem_amplitudes hl' (hT ρ hρ), add_zero, add_zero] at h1
    exact h1
  · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]

/-- Without opposite pairs, the odd half alone determines the amplitudes. -/
theorem eq_of_oddPart_eq (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    (hT : ∀ ρ ∈ T, -ρ ∉ T) {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T)
    (ho : oddPart l = oddPart l') : l = l' := by
  funext ρ
  by_cases hρ : ρ ∈ T
  · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρ h0
    have h1 := congrFun ho (ρ ^ 2)
    rw [oddPart_sq h2 hρ0, oddPart_sq h2 hρ0, eq_zero_of_mem_amplitudes hl (hT ρ hρ),
      eq_zero_of_mem_amplitudes hl' (hT ρ hρ), mul_zero, sub_zero, sub_zero] at h1
    exact mul_left_cancel₀ hρ0 h1
  · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]

/-- **Note (11).** Without opposite pairs in `T`, `δ_{2a,s}(T) ≤ δ_{a,2s}(T²)`: the weight
splits into the two halves, `xy ≤ (x² + y²)/2`, and each half is an injective image. -/
theorem spectralSum_two_mul_le_of_forall_neg_notMem (hf0 : ∀ x, 0 ≤ f x) (h2 : (2 : K) ≠ 0)
    {T : Finset K} (h0 : (0 : K) ∉ T) (hT : ∀ ρ ∈ T, -ρ ∉ T) (a s : ℕ) :
    spectralSum f (2 * a) s T ≤ spectralSum f a (2 * s) (T.image (· ^ 2)) := by
  have hmapE : ∀ l ∈ (amplitudes T).erase 0,
      evenPart l ∈ (amplitudes (T.image (· ^ 2))).erase 0 := by
    intro l hl
    obtain ⟨hl0, hl⟩ := mem_erase.1 hl
    refine mem_erase.2 ⟨fun h => hl0 ?_, evenPart_mem hl⟩
    exact eq_of_evenPart_eq h2 h0 hT hl (zero_mem_amplitudes T) (h.trans evenPart_zero.symm)
  have hmapO : ∀ l ∈ (amplitudes T).erase 0,
      oddPart l ∈ (amplitudes (T.image (· ^ 2))).erase 0 := by
    intro l hl
    obtain ⟨hl0, hl⟩ := mem_erase.1 hl
    refine mem_erase.2 ⟨fun h => hl0 ?_, oddPart_mem hl⟩
    exact eq_of_oddPart_eq h2 h0 hT hl (zero_mem_amplitudes T) (h.trans oddPart_zero.symm)
  have hinjE : Set.InjOn evenPart (((amplitudes T).erase 0 : Finset (K → K)) : Set (K → K)) :=
    fun l hl l' hl' h => eq_of_evenPart_eq h2 h0 hT (mem_erase.1 hl).2 (mem_erase.1 hl').2 h
  have hinjO : Set.InjOn oddPart (((amplitudes T).erase 0 : Finset (K → K)) : Set (K → K)) :=
    fun l hl l' hl' h => eq_of_oddPart_eq h2 h0 hT (mem_erase.1 hl).2 (mem_erase.1 hl').2 h
  calc spectralSum f (2 * a) s T
      = ∑ l ∈ (amplitudes T).erase 0, weight f a s (evenPart l) * weight f a s (oddPart l) :=
        sum_congr rfl fun l _ => weight_two_mul a s l
    _ ≤ ∑ l ∈ (amplitudes T).erase 0,
          (weight f a (2 * s) (evenPart l) + weight f a (2 * s) (oddPart l)) / 2 := by
        refine sum_le_sum fun l _ => ?_
        rw [← weight_sq, ← weight_sq]
        nlinarith [sq_nonneg (weight f a s (evenPart l) - weight f a s (oddPart l))]
    _ = (∑ l ∈ (amplitudes T).erase 0, weight f a (2 * s) (evenPart l) +
          ∑ l ∈ (amplitudes T).erase 0, weight f a (2 * s) (oddPart l)) / 2 := by
        rw [← sum_add_distrib, sum_div]
    _ ≤ (spectralSum f a (2 * s) (T.image (· ^ 2)) +
          spectralSum f a (2 * s) (T.image (· ^ 2))) / 2 := by
        gcongr
        · exact sum_comp_le_sum_of_injOn hinjE hmapE fun _ _ => weight_nonneg hf0 _ _ _
        · exact sum_comp_le_sum_of_injOn hinjO hmapO fun _ _ => weight_nonneg hf0 _ _ _
    _ = spectralSum f a (2 * s) (T.image (· ^ 2)) := by ring

/-- The squares of the opposite pairs `ρ, -ρ` in `T`. -/
def pairedSquares (T : Finset K) : Finset K := (T.filter fun ρ => -ρ ∈ T).image (· ^ 2)

omit [Fintype K] in
theorem pairedSquares_subset (T : Finset K) : pairedSquares T ⊆ T.image (· ^ 2) :=
  image_subset_image (filter_subset _ _)

/-- **Note (12).** `δ_{2a,s}(T) ≤ 2 δ_{a,s}(P) + δ_{a,s}(P)² + δ_{a,s}(T²)²` with `P` the
squares of the opposite pairs. An amplitude vector vanishing at every unpaired root has both
halves supported on `P`; otherwise both halves are nonzero. -/
theorem spectralSum_two_mul_le (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (h2 : (2 : K) ≠ 0)
    {T : Finset K} (h0 : (0 : K) ∉ T) (a s : ℕ) :
    spectralSum f (2 * a) s T ≤ 2 * spectralSum f a s (pairedSquares T) +
      spectralSum f a s (pairedSquares T) ^ 2 + spectralSum f a s (T.image (· ^ 2)) ^ 2 := by
  set AP := amplitudes (pairedSquares T) with hAP
  set A2 := (amplitudes (T.image (· ^ 2))).erase 0 with hA2
  set S0 := (AP ×ˢ AP).erase (0, 0) with hS0
  set S1 := A2 ×ˢ A2 with hS1
  let Φ : (K → K) → (K → K) × (K → K) := fun l => (evenPart l, oddPart l)
  let G : (K → K) × (K → K) → ℝ := fun p => weight f a s p.1 * weight f a s p.2
  have hG : ∀ p, 0 ≤ G p := fun p => mul_nonneg (weight_nonneg hf0 _ _ _) (weight_nonneg hf0 _ _ _)
  have hinj : Set.InjOn Φ (((amplitudes T).erase 0 : Finset (K → K)) : Set (K → K)) :=
    fun l hl l' hl' h => eq_of_evenPart_eq_of_oddPart_eq h2 h0 (mem_erase.1 hl).2
      (mem_erase.1 hl').2 (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hmaps : ∀ l ∈ (amplitudes T).erase 0, Φ l ∈ S0 ∪ S1 := by
    intro l hl
    obtain ⟨hl0, hl⟩ := mem_erase.1 hl
    by_cases hsing : ∀ ρ ∈ T, -ρ ∉ T → l ρ = 0
    · have hEP : evenPart l ∈ AP := by
        refine mem_amplitudes.2 fun ν hν => ?_
        obtain ⟨ρ, hρ, hlρ⟩ := exists_ne_zero_of_sum_ne_zero hν
        have hρT := mem_amplitudes.1 hl ρ hlρ
        have hneg : -ρ ∈ T := by
          by_contra hn
          exact hlρ (hsing ρ hρT hn)
        exact mem_image.2 ⟨ρ, mem_filter.2 ⟨hρT, hneg⟩, (mem_filter.1 hρ).2⟩
      have hOP : oddPart l ∈ AP := by
        refine mem_amplitudes.2 fun ν hν => ?_
        obtain ⟨ρ, hρ, hlρ⟩ := exists_ne_zero_of_sum_ne_zero hν
        have hlρ' := right_ne_zero_of_mul hlρ
        have hρT := mem_amplitudes.1 hl ρ hlρ'
        have hneg : -ρ ∈ T := by
          by_contra hn
          exact hlρ' (hsing ρ hρT hn)
        exact mem_image.2 ⟨ρ, mem_filter.2 ⟨hρT, hneg⟩, (mem_filter.1 hρ).2⟩
      refine mem_union_left _ (mem_erase.2 ⟨fun h => hl0 ?_, mem_product.2 ⟨hEP, hOP⟩⟩)
      exact eq_of_evenPart_eq_of_oddPart_eq h2 h0 hl (zero_mem_amplitudes T)
        ((congrArg Prod.fst h).trans evenPart_zero.symm)
        ((congrArg Prod.snd h).trans oddPart_zero.symm)
    · push Not at hsing
      obtain ⟨ρ, hρT, hnρ, hlρ⟩ := hsing
      have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρT h0
      have hlneg : l (-ρ) = 0 := eq_zero_of_mem_amplitudes hl hnρ
      have hE : evenPart l ∈ A2 := by
        refine mem_erase.2 ⟨fun h => hlρ ?_, evenPart_mem hl⟩
        have h' := congrFun h (ρ ^ 2)
        rwa [evenPart_sq h2 hρ0, hlneg, add_zero] at h'
      have hO : oddPart l ∈ A2 := by
        refine mem_erase.2 ⟨fun h => mul_ne_zero hρ0 hlρ ?_, oddPart_mem hl⟩
        have h' := congrFun h (ρ ^ 2)
        rwa [oddPart_sq h2 hρ0, hlneg, mul_zero, sub_zero] at h'
      exact mem_union_right _ (mem_product.2 ⟨hE, hO⟩)
  have hsum0 : ∑ p ∈ S0, G p = 2 * weight f a s 0 * spectralSum f a s (pairedSquares T) +
      spectralSum f a s (pairedSquares T) ^ 2 := by
    rw [hS0, sum_erase_eq_sub (mem_product.2 ⟨zero_mem_amplitudes _, zero_mem_amplitudes _⟩),
      sum_product]
    simp only [G]
    rw [← sum_mul_sum, spectralSum, ← hAP, ← add_sum_erase AP _ (zero_mem_amplitudes _)]
    ring
  have hsum1 : ∑ p ∈ S1, G p = spectralSum f a s (T.image (· ^ 2)) ^ 2 := by
    rw [hS1, sum_product]
    simp only [G]
    rw [← sum_mul_sum, spectralSum, ← hA2]
    ring
  calc spectralSum f (2 * a) s T = ∑ l ∈ (amplitudes T).erase 0, G (Φ l) :=
        sum_congr rfl fun l _ => weight_two_mul a s l
    _ ≤ ∑ p ∈ S0 ∪ S1, G p := sum_comp_le_sum_of_injOn hinj hmaps fun p _ => hG p
    _ ≤ ∑ p ∈ S0, G p + ∑ p ∈ S1, G p := by
        rw [← sum_union_inter]
        linarith [sum_nonneg fun p (_ : p ∈ S0 ∩ S1) => hG p]
    _ ≤ 2 * spectralSum f a s (pairedSquares T) + spectralSum f a s (pairedSquares T) ^ 2 +
          spectralSum f a s (T.image (· ^ 2)) ^ 2 := by
        rw [hsum0, hsum1]
        have h1 := weight_le_one hf0 hf1 a s 0
        have h3 := spectralSum_nonneg hf0 a s (pairedSquares T)
        nlinarith

omit [Fintype K] in
/-- `|P| + |T²| ≤ |T|`: every square has a nonempty fibre in `T`, and a paired square a fibre of
two points. -/
theorem card_pairedSquares_add_card_image_le (h2 : (2 : K) ≠ 0) {T : Finset K}
    (h0 : (0 : K) ∉ T) : (pairedSquares T).card + (T.image (· ^ 2)).card ≤ T.card := by
  have key : ∀ ν ∈ T.image (· ^ 2),
      (if ν ∈ pairedSquares T then 1 else 0) + 1 ≤ (T.filter fun x => x ^ 2 = ν).card := by
    intro ν hν
    split_ifs with hνP
    · obtain ⟨ρ, hρ, rfl⟩ := mem_image.1 hνP
      obtain ⟨hρT, hnρ⟩ := mem_filter.1 hρ
      have hsub : ({ρ, -ρ} : Finset K) ⊆ T.filter fun x => x ^ 2 = ρ ^ 2 := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨hρT, rfl⟩
        · rw [mem_singleton.1 hx]
          exact mem_filter.2 ⟨hnρ, neg_sq ρ⟩
      have hcard := card_le_card hsub
      rw [card_pair (self_ne_neg_of_ne_zero h2 (ne_of_mem_of_not_mem hρT h0))] at hcard
      omega
    · obtain ⟨ρ, hρT, rfl⟩ := mem_image.1 hν
      have hpos := card_pos.2
        ⟨ρ, (mem_filter.2 ⟨hρT, rfl⟩ : ρ ∈ T.filter fun x => x ^ 2 = ρ ^ 2)⟩
      omega
  have h1 : (pairedSquares T).card =
      ∑ ν ∈ T.image (· ^ 2), if ν ∈ pairedSquares T then 1 else 0 := by
    rw [← card_filter]
    congr 1
    ext ν
    simp only [mem_filter]
    exact ⟨fun h => ⟨pairedSquares_subset T h, h⟩, fun h => h.2⟩
  rw [h1, card_eq_sum_ones (T.image _), ← sum_add_distrib,
    card_eq_sum_card_fiberwise (f := fun x : K => x ^ 2) (t := T.image (· ^ 2))
      (fun x hx => mem_image_of_mem _ hx)]
  exact sum_le_sum key

omit [Fintype K] in
/-- Squares of roots of `X^(2a) + 1` are roots of `X^a + 1`. -/
theorem pow_eq_neg_one_of_mem_image {T : Finset K} {a : ℕ} (hT : ∀ ρ ∈ T, ρ ^ (2 * a) = -1) :
    ∀ ν ∈ T.image (· ^ 2), ν ^ a = -1 := by
  intro ν hν
  obtain ⟨ρ, hρ, rfl⟩ := mem_image.1 hν
  rw [← pow_mul]
  exact hT ρ hρ

omit [Fintype K] [DecidableEq K] in
/-- Roots of `X^a + 1`, `a ≠ 0`, are nonzero. -/
theorem zero_notMem_of_pow_eq_neg_one {T : Finset K} {a : ℕ} (ha : a ≠ 0)
    (hT : ∀ ρ ∈ T, ρ ^ a = -1) : (0 : K) ∉ T := by
  intro h
  have h' := hT 0 h
  rw [zero_pow ha] at h'
  exact one_ne_zero (neg_eq_zero.1 h'.symm)

omit [Fintype K] in
/-- Opposite pairs make `T` at least two points: a set of at most one point has none. -/
theorem forall_neg_notMem_of_card_le_one (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    (hT : T.card ≤ 1) : ∀ ρ ∈ T, -ρ ∉ T := by
  intro ρ hρ hnρ
  have hne := self_ne_neg_of_ne_zero h2 (ne_of_mem_of_not_mem hρ h0)
  have := card_le_card (insert_subset hρ (singleton_subset_iff.2 hnρ))
  rw [card_pair hne] at this
  omega

end Field

/-! ### The determinant step, note (9) -/

section ZMod

variable {q : ℕ}

/-- **The kernel hypotheses**: `0 ≤ f ≤ 1` and `f x · |x| ≤ C` for `x ≠ 0`, with `|x|` the
centered absolute value. The hint-split kernel of the regularity route satisfies this with
`C = q / L` (note (3) with twice the single-interval bound). -/
structure IsKernelBound (C : ℝ) (f : ZMod q → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  mul_abs_valMinAbs_le : ∀ x, x ≠ 0 → f x * |(x.valMinAbs : ℝ)| ≤ C

variable [Fact q.Prime] {C : ℝ} {f : ZMod q → ℝ}

theorem IsKernelBound.nonneg_const (hf : IsKernelBound C f) : 0 ≤ C :=
  (mul_nonneg (hf.nonneg 1) (abs_nonneg _)).trans (hf.mul_abs_valMinAbs_le 1 one_ne_zero)

/-- **Note (9), the counting step.** At length `a = 2^e` and `|T| ≤ r ≤ a`: if every nonzero
integer word whose reduction lies in the span of the root words of `T` has a coefficient of
absolute value at least `C d` (`hlift`), then every nonzero word has weight at most `d^(-s)`, and
there are fewer than `q^r` amplitude vectors. -/
theorem spectralSum_le_of_forall_mul_le_abs (hf : IsKernelBound C f) {e r : ℕ} (s : ℕ)
    {T : Finset (ZMod q)} (hTr : T.card ≤ r) (hra : r ≤ 2 ^ e)
    {d : ℝ} (hd : 0 < d)
    (hlift : ∀ v : Fin (2 ^ e) → ℤ, v ≠ 0 → (fun b => (v b : ZMod q)) ∈ Submodule.span (ZMod q)
      ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T) →
      ∀ B : ℤ, (∀ b, |v b| ≤ B) → C * d ≤ B) :
    spectralSum f (2 ^ e) s T ≤ (q : ℝ) ^ r / d ^ s := by
  have hC := hf.nonneg_const
  have hterm : ∀ l ∈ (amplitudes T).erase 0, weight f (2 ^ e) s l ≤ 1 / d ^ s := by
    intro l hl
    obtain ⟨hl0, hl⟩ := mem_erase.1 hl
    set v : Fin (2 ^ e) → ℤ := fun b => (word l b).valMinAbs with hvdef
    obtain ⟨b1, hb1, hwb1⟩ := exists_word_ne_zero hl hl0 (hTr.trans hra)
    have hv : v ≠ 0 := by
      intro h
      apply hwb1
      have h' := congrFun h ⟨b1, hb1⟩
      simpa [hvdef, ZMod.valMinAbs_eq_zero] using h'
    obtain ⟨b0, -, hb0⟩ := exists_max_image univ (fun b => |v b|) univ_nonempty
    have hspan : (fun b => (v b : ZMod q)) ∈ Submodule.span (ZMod q)
        ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T) := by
      have heq : (fun b => (v b : ZMod q)) =
          ∑ ρ ∈ T, l ρ • (fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) := by
        funext b
        simp [hvdef, ZMod.coe_valMinAbs, word_eq_sum hl, Finset.sum_apply]
      rw [heq]
      exact Submodule.sum_mem _ fun ρ hρ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨ρ, hρ, rfl⟩)
    have hB : C * d ≤ |(v b0 : ℝ)| := by
      have h := hlift v hv hspan |v b0| (fun b => hb0 b (mem_univ b))
      exact_mod_cast h
    have hBpos : 0 < |(v b0 : ℝ)| := by
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hv
      have h1 : 0 < |v b| := abs_pos.2 hb
      have h3 : |v b| ≤ |v b0| := hb0 b (mem_univ b)
      have h4 : 0 < |v b0| := lt_of_lt_of_le h1 h3
      exact_mod_cast h4
    have hx0 : word l b0 ≠ 0 := by
      intro h
      have h' : v b0 = 0 := by simp [hvdef, h]
      rw [h'] at hBpos
      simp at hBpos
    have hfb0 : f (word l b0) ≤ 1 / d := by
      have h := hf.mul_abs_valMinAbs_le _ hx0
      calc f (word l b0) ≤ C / |(v b0 : ℝ)| := (le_div_iff₀ hBpos).2 h
        _ ≤ 1 / d := by
          rw [div_le_div_iff₀ hBpos hd]
          linarith
    rw [weight, ← mul_prod_erase (range (2 ^ e)) _ (mem_range.2 b0.isLt)]
    calc f (word l b0) ^ s * ∏ x ∈ (range (2 ^ e)).erase b0, f (word l x) ^ s
        ≤ f (word l b0) ^ s * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (hf.nonneg _) _)
          exact prod_le_one₀ (fun _ _ => pow_nonneg (hf.nonneg _) _)
            fun _ _ => pow_le_one₀ (hf.nonneg _) (hf.le_one _)
      _ ≤ (1 / d) ^ s := by
          rw [mul_one]
          exact pow_le_pow_left₀ (hf.nonneg _) hfb0 s
      _ = 1 / d ^ s := by rw [one_div_pow]
  have hcard : (((amplitudes T).erase 0).card : ℝ) ≤ (q : ℝ) ^ r := by
    have h1 : ((amplitudes T).erase 0).card ≤ q ^ r :=
      (card_erase_le).trans ((card_amplitudes_le T).trans (by
        rw [ZMod.card]
        exact Nat.pow_le_pow_right (Fact.out : q.Prime).pos hTr))
    exact_mod_cast h1
  calc spectralSum f (2 ^ e) s T ≤ ∑ l ∈ (amplitudes T).erase 0, 1 / d ^ s := sum_le_sum hterm
    _ = ((amplitudes T).erase 0).card * (1 / d ^ s) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) ^ r * (1 / d ^ s) := by gcongr
    _ = (q : ℝ) ^ r / d ^ s := by ring

/-- A bound `|v b| ≤ B` on a word of positive length makes `B` nonnegative. -/
theorem nonneg_of_forall_abs_le {e : ℕ} {v : Fin (2 ^ e) → ℤ} {B : ℤ} (hB : ∀ b, |v b| ≤ B) :
    0 ≤ (B : ℝ) := by
  have h := (abs_nonneg _).trans (hB ⟨0, by positivity⟩)
  exact_mod_cast h

/-- **Note (9), Leibniz form.** `δ_{a,s}(T) ≤ q^r / d^s` at `a = 2^e`, `|T| ≤ r ≤ a`, whenever
`(C d)^a · a! ≤ q^(a - r)`. -/
theorem spectralSum_le_of_pow_le (hf : IsKernelBound C f) {e r : ℕ} (s : ℕ)
    {T : Finset (ZMod q)} (hT : ∀ ρ ∈ T, ρ ^ 2 ^ e = -1) (hTr : T.card ≤ r) (hra : r ≤ 2 ^ e)
    {d : ℝ} (hd : 0 < d)
    (hcheck : (C * d) ^ 2 ^ e * (2 ^ e).factorial ≤ (q : ℝ) ^ (2 ^ e - r)) :
    spectralSum f (2 ^ e) s T ≤ (q : ℝ) ^ r / d ^ s := by
  refine spectralSum_le_of_forall_mul_le_abs hf s hTr hra hd fun v hv hspan B hB => ?_
  have hB0 := nonneg_of_forall_abs_le hB
  have hL2 := pow_le_factorial_mul_pow_of_mem_span hv T hT hTr hspan hB
  have hL2' : (q : ℝ) ^ (2 ^ e - r) ≤ (2 ^ e).factorial * (B : ℝ) ^ 2 ^ e := by
    exact_mod_cast hL2
  have hfac : (0 : ℝ) < (2 ^ e).factorial := by exact_mod_cast Nat.factorial_pos _
  have h1 : (C * d) ^ 2 ^ e ≤ (B : ℝ) ^ 2 ^ e := by
    refine le_of_mul_le_mul_right ?_ hfac
    linarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg hf.nonneg_const hd.le) hB0 (by positivity)).1 h1

/-- **Note (9), Hadamard form.** `δ_{a,s}(T) ≤ q^r / d^s` at `a = 2^e`, `|T| ≤ r ≤ a`, whenever
`(C d)^(2a) · a^a ≤ q^(2(a - r))`. -/
theorem spectralSum_le_of_pow_le_hadamard (hf : IsKernelBound C f) {e r : ℕ} (s : ℕ)
    {T : Finset (ZMod q)} (hT : ∀ ρ ∈ T, ρ ^ 2 ^ e = -1) (hTr : T.card ≤ r) (hra : r ≤ 2 ^ e)
    {d : ℝ} (hd : 0 < d)
    (hcheck : (C * d) ^ (2 * 2 ^ e) * ((2 ^ e : ℕ) : ℝ) ^ 2 ^ e ≤ (q : ℝ) ^ (2 * (2 ^ e - r))) :
    spectralSum f (2 ^ e) s T ≤ (q : ℝ) ^ r / d ^ s := by
  refine spectralSum_le_of_forall_mul_le_abs hf s hTr hra hd fun v hv hspan B hB => ?_
  have hB0 := nonneg_of_forall_abs_le hB
  have hL2 := pow_two_mul_le_pow_mul_pow_of_mem_span hv T hT hTr hspan hB
  have hL2' : (q : ℝ) ^ (2 * (2 ^ e - r)) ≤ ((2 ^ e : ℕ) : ℝ) ^ 2 ^ e * (B : ℝ) ^ (2 * 2 ^ e) := by
    exact_mod_cast hL2
  have hpos : (0 : ℝ) < ((2 ^ e : ℕ) : ℝ) ^ 2 ^ e := by positivity
  have h1 : (C * d) ^ (2 * 2 ^ e) ≤ (B : ℝ) ^ (2 * 2 ^ e) := by
    refine le_of_mul_le_mul_right ?_ hpos
    linarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg hf.nonneg_const hd.le) hB0 (by positivity)).1 h1

end ZMod

/-! ### The uniform bounds at ML-DSA's modulus, note (13) with the hint-split kernel -/

section Uniform

/-- The bound for `|T| ≤ 1` at `m = 2^k s` (length `2^(1+k)`, exponent `s`). -/
noncomputable def smallSupportBound₁ (m : ℕ) : ℝ := 8380417 / 32 ^ m

/-- The bound for `|T| ≤ 2` at `m = 2^k s` (length `2^(2+k)`). -/
noncomputable def smallSupportBound₂ (m : ℕ) : ℝ :=
  max (8380417 ^ 2 / 16 ^ m)
    (2 * smallSupportBound₁ m + smallSupportBound₁ m ^ 2 + smallSupportBound₁ m ^ 2)

/-- The bound for `|T| ≤ 3` at `m = 2^k s` (length `2^(3+k)`). -/
noncomputable def smallSupportBound₃ (m : ℕ) : ℝ :=
  max (8380417 ^ 3 / 128 ^ m)
    (2 * smallSupportBound₁ (2 * m) + smallSupportBound₁ (2 * m) ^ 2 + smallSupportBound₂ m ^ 2)

/-- The bound for `|T| ≤ 4` at `m = 2^k s` (length `2^(4+k)`). -/
noncomputable def smallSupportBound₄ (m : ℕ) : ℝ :=
  max (8380417 ^ 4 / 512 ^ m)
    (2 * smallSupportBound₂ (2 * m) + smallSupportBound₂ (2 * m) ^ 2 + smallSupportBound₃ m ^ 2)

variable {C : ℝ} {f : ZMod 8380417 → ℝ}

theorem two_ne_zero_modulus : (2 : ZMod 8380417) ≠ 0 := by decide

/-- The determinant check at `C ≤ q / L₀`, reduced to `C = q / L₀`. -/
theorem check_of_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) {a n : ℕ} {d : ℝ}
    (hd : 0 ≤ d)
    (h : ((8380417 / 190307 : ℝ) * d) ^ a * a.factorial ≤ (8380417 : ℝ) ^ n) :
    (C * d) ^ a * a.factorial ≤ ((8380417 : ℕ) : ℝ) ^ n := by
  refine le_trans ?_ (by exact_mod_cast h)
  gcongr
  exact mul_nonneg hf.nonneg_const hd

theorem spectralSum_le_smallSupportBound₁ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (1 + k) = -1) → T.card ≤ 1 →
      spectralSum f (2 ^ (1 + k)) s T ≤ smallSupportBound₁ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hT1
    have h := spectralSum_le_of_pow_le hf s hT hT1 (by norm_num) (d := 32) (by norm_num)
      (check_of_le hf hC (by norm_num) (by norm_num [Nat.factorial]))
    simpa [smallSupportBound₁] using h
  | succ k ih =>
    intro s T hT hT1
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (1 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (1 + k) = 2 ^ (1 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (1 + (k + 1)) = 2 * 2 ^ (1 + k) by ring]
    refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
      (forall_neg_notMem_of_card_le_one two_ne_zero_modulus h0 hT1) _ s).trans ?_
    rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
    exact ih (2 * s) _ (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hT1)

/-- `|P| ≥ 1` when `T` has an opposite pair. -/
theorem card_pairedSquares_pos {T : Finset (ZMod 8380417)} (h : ∃ ρ ∈ T, -ρ ∈ T) :
    0 < (pairedSquares T).card := by
  obtain ⟨ρ, hρ, hn⟩ := h
  exact card_pos.2 ⟨ρ ^ 2, mem_image.2 ⟨ρ, mem_filter.2 ⟨hρ, hn⟩, rfl⟩⟩

theorem spectralSum_le_smallSupportBound₂ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (2 + k) = -1) → T.card ≤ 2 →
      spectralSum f (2 ^ (2 + k)) s T ≤ smallSupportBound₂ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le hf s hT hTr (by norm_num) (d := 16) (by norm_num)
      (check_of_le hf hC (by norm_num) (by norm_num [Nat.factorial]))
    refine h.trans ?_
    rw [smallSupportBound₂]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (2 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (2 + k) = 2 ^ (2 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (2 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (2 + (k + 1)) = 2 * 2 ^ (2 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_smallSupportBound₁ hf hC (k + 1) s (pairedSquares T)
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_smallSupportBound₁ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 1) = 2 + k by ring] at hX hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [smallSupportBound₂]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

theorem spectralSum_le_smallSupportBound₃ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (3 + k) = -1) → T.card ≤ 3 →
      spectralSum f (2 ^ (3 + k)) s T ≤ smallSupportBound₃ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le hf s hT hTr (by norm_num) (d := 128) (by norm_num)
      (check_of_le hf hC (by norm_num) (by norm_num [Nat.factorial]))
    refine h.trans ?_
    rw [smallSupportBound₃]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (3 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (3 + k) = 2 ^ (3 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (3 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (3 + (k + 1)) = 2 * 2 ^ (3 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_smallSupportBound₁ hf hC (k + 2) s (pairedSquares T)
        (by rw [show 1 + (k + 2) = 3 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_smallSupportBound₂ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 2 + (k + 1) = 3 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 2) = 3 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
        at hX
      rw [show 2 + (k + 1) = 3 + k by ring] at hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [smallSupportBound₃]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

theorem spectralSum_le_smallSupportBound₄ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (4 + k) = -1) → T.card ≤ 4 →
      spectralSum f (2 ^ (4 + k)) s T ≤ smallSupportBound₄ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le hf s hT hTr (by norm_num) (d := 512) (by norm_num)
      (check_of_le hf hC (by norm_num) (by norm_num [Nat.factorial]))
    refine h.trans ?_
    rw [smallSupportBound₄]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (4 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (4 + k) = 2 ^ (4 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (4 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_smallSupportBound₂ hf hC (k + 2) s (pairedSquares T)
        (by rw [show 2 + (k + 2) = 4 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_smallSupportBound₃ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
      rw [show 2 + (k + 2) = 4 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
        at hX
      rw [show 3 + (k + 1) = 4 + k by ring] at hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [smallSupportBound₄]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

/-! ### Evaluation at length 256 -/

theorem smallSupportBound₁_nonneg (m : ℕ) : 0 ≤ smallSupportBound₁ m := by
  rw [smallSupportBound₁]
  positivity

theorem smallSupportBound₂_nonneg (m : ℕ) : 0 ≤ smallSupportBound₂ m :=
  le_max_of_le_left (by positivity)

theorem smallSupportBound₃_nonneg (m : ℕ) : 0 ≤ smallSupportBound₃ m :=
  le_max_of_le_left (by positivity)

theorem smallSupportBound₂_32_le : smallSupportBound₂ 32 ≤ 1 / 2 ^ 81 :=
  max_le (by norm_num) (by norm_num [smallSupportBound₁])

theorem smallSupportBound₂_16_le : smallSupportBound₂ 16 ≤ 1 / 2 ^ 17 :=
  max_le (by norm_num) (by norm_num [smallSupportBound₁])

theorem smallSupportBound₃_16_le : smallSupportBound₃ 16 ≤ 1 / 2 ^ 33 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (smallSupportBound₁_nonneg _) le_rfl
    (smallSupportBound₂_nonneg _) smallSupportBound₂_16_le).trans ?_
  norm_num [smallSupportBound₁]

/-- **`δ₁` at length 256.** For a support of at most one root of `X^256 + 1` in `ZMod q`,
`δ_{256,1}(T) ≤ 2^(-617)`. -/
theorem spectralSum_le_one_div_two_pow_617 (hf : IsKernelBound C f)
    (hC : C ≤ 8380417 / 190307) {T : Finset (ZMod 8380417)} (hT : ∀ ρ ∈ T, ρ ^ 256 = -1)
    (hTr : T.card ≤ 1) : spectralSum f 256 1 T ≤ 1 / 2 ^ 617 := by
  have h := spectralSum_le_smallSupportBound₁ hf hC 7 1 T hT hTr
  refine h.trans ?_
  have hq : (8380417 : ℝ) ≤ 2 ^ 23 := by norm_num
  rw [smallSupportBound₁, show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_mul,
    show 5 * (2 ^ 7 * 1) = 23 + 617 by norm_num, pow_add, div_le_div_iff₀ (by positivity)
      (by positivity), one_mul]
  exact mul_le_mul_of_nonneg_right hq (by positivity)

/-- **`δ₂` at length 256**: `δ_{256,1}(T) ≤ 2^(-210)` for `|T| ≤ 2`. -/
theorem spectralSum_le_one_div_two_pow_210 (hf : IsKernelBound C f)
    (hC : C ≤ 8380417 / 190307) {T : Finset (ZMod 8380417)} (hT : ∀ ρ ∈ T, ρ ^ 256 = -1)
    (hTr : T.card ≤ 2) : spectralSum f 256 1 T ≤ 1 / 2 ^ 210 := by
  have h := spectralSum_le_smallSupportBound₂ hf hC 6 1 T hT hTr
  refine h.trans ?_
  exact max_le (by norm_num) (by norm_num [smallSupportBound₁])

/-- **`δ₃` at length 256**: `δ_{256,1}(T) ≤ 2^(-155)` for `|T| ≤ 3`. -/
theorem spectralSum_le_one_div_two_pow_155 (hf : IsKernelBound C f)
    (hC : C ≤ 8380417 / 190307) {T : Finset (ZMod 8380417)} (hT : ∀ ρ ∈ T, ρ ^ 256 = -1)
    (hTr : T.card ≤ 3) : spectralSum f 256 1 T ≤ 1 / 2 ^ 155 := by
  have h := spectralSum_le_smallSupportBound₃ hf hC 5 1 T hT hTr
  refine h.trans (max_le (by norm_num) ?_)
  refine (two_mul_add_sq_add_sq_le (smallSupportBound₁_nonneg _) le_rfl
    (smallSupportBound₂_nonneg _) smallSupportBound₂_32_le).trans ?_
  norm_num [smallSupportBound₁]

/-- **`δ₄` at length 256**: `δ_{256,1}(T) ≤ 2^(-52)` for `|T| ≤ 4`. -/
theorem spectralSum_le_one_div_two_pow_52 (hf : IsKernelBound C f)
    (hC : C ≤ 8380417 / 190307) {T : Finset (ZMod 8380417)} (hT : ∀ ρ ∈ T, ρ ^ 256 = -1)
    (hTr : T.card ≤ 4) : spectralSum f 256 1 T ≤ 1 / 2 ^ 52 := by
  have h := spectralSum_le_smallSupportBound₄ hf hC 4 1 T hT hTr
  refine h.trans (max_le (by norm_num) ?_)
  refine (two_mul_add_sq_add_sq_le (smallSupportBound₂_nonneg _) smallSupportBound₂_32_le
    (smallSupportBound₃_nonneg _) smallSupportBound₃_16_le).trans ?_
  norm_num

end Uniform

/-! ### The bounds up to five roots at cell size `523383`, with the Hadamard form

At ML-DSA-65 and ML-DSA-87 every cell has at least `523383` points, so `C ≤ q / 523383`. The
recursion below stops at lengths `2, 4, 8, 8, 16` for `|T| ≤ 1, …, 5`, with the Leibniz form
for `|T| ≤ 1, 2, 5` and the Hadamard form for `|T| ≤ 3, 4`; at `|T| ≤ 4` the larger child
`T²` stops at the same length, so its bound is read at `m / 2`. -/

section Cell

/-- `|T| ≤ 1` at `m = 2^k s` (length `2^(1+k)`). -/
noncomputable def cellBound₁ (m : ℕ) : ℝ := 8380417 / 127 ^ m

/-- `|T| ≤ 2` at `m = 2^k s` (length `2^(2+k)`). -/
noncomputable def cellBound₂ (m : ℕ) : ℝ :=
  max (8380417 ^ 2 / 81 ^ m) (2 * cellBound₁ m + cellBound₁ m ^ 2 + cellBound₁ m ^ 2)

/-- `|T| ≤ 3` at `m = 2^k s` (length `2^(3+k)`). -/
noncomputable def cellBound₃ (m : ℕ) : ℝ :=
  max (8380417 ^ 3 / 468 ^ m) (2 * cellBound₁ (2 * m) + cellBound₁ (2 * m) ^ 2 + cellBound₂ m ^ 2)

/-- `|T| ≤ 4` at `m = 2^k s` (length `2^(3+k)`). -/
noncomputable def cellBound₄ (m : ℕ) : ℝ :=
  max (8380417 ^ 4 / 63 ^ m) (2 * cellBound₂ m + cellBound₂ m ^ 2 + cellBound₃ (m / 2) ^ 2)

/-- `|T| ≤ 5` at `m = 2^k s` (length `2^(4+k)`). -/
noncomputable def cellBound₅ (m : ℕ) : ℝ :=
  max (8380417 ^ 5 / 528 ^ m) (2 * cellBound₂ (2 * m) + cellBound₂ (2 * m) ^ 2 + cellBound₄ m ^ 2)

variable {C : ℝ} {f : ZMod 8380417 → ℝ}

/-- The Leibniz check at `C ≤ q / 523383`, reduced to `C = q / 523383`. -/
theorem check_of_le_cell (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) {a n : ℕ} {d : ℝ}
    (hd : 0 ≤ d)
    (h : ((8380417 / 523383 : ℝ) * d) ^ a * a.factorial ≤ (8380417 : ℝ) ^ n) :
    (C * d) ^ a * a.factorial ≤ ((8380417 : ℕ) : ℝ) ^ n := by
  refine le_trans ?_ (by exact_mod_cast h)
  gcongr
  exact mul_nonneg hf.nonneg_const hd

/-- The Hadamard check at `C ≤ q / 523383`, reduced to `C = q / 523383`. -/
theorem check_hadamard_of_le_cell (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    {a b n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (h : ((8380417 / 523383 : ℝ) * d) ^ a * (b : ℝ) ^ b ≤ (8380417 : ℝ) ^ n) :
    (C * d) ^ a * (b : ℝ) ^ b ≤ ((8380417 : ℕ) : ℝ) ^ n := by
  calc (C * d) ^ a * (b : ℝ) ^ b ≤ ((8380417 / 523383 : ℝ) * d) ^ a * (b : ℝ) ^ b := by
        gcongr
        exact mul_nonneg hf.nonneg_const hd
    _ ≤ _ := by exact_mod_cast h

theorem spectralSum_le_cellBound₁ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (1 + k) = -1) → T.card ≤ 1 →
      spectralSum f (2 ^ (1 + k)) s T ≤ cellBound₁ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hT1
    have h := spectralSum_le_of_pow_le hf s hT hT1 (by norm_num) (d := 127) (by norm_num)
      (check_of_le_cell hf hC (by norm_num) (by norm_num [Nat.factorial]))
    simpa [cellBound₁] using h
  | succ k ih =>
    intro s T hT hT1
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (1 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (1 + k) = 2 ^ (1 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (1 + (k + 1)) = 2 * 2 ^ (1 + k) by ring]
    refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
      (forall_neg_notMem_of_card_le_one two_ne_zero_modulus h0 hT1) _ s).trans ?_
    rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
    exact ih (2 * s) _ (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hT1)

theorem spectralSum_le_cellBound₂ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (2 + k) = -1) → T.card ≤ 2 →
      spectralSum f (2 ^ (2 + k)) s T ≤ cellBound₂ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le hf s hT hTr (by norm_num) (d := 81) (by norm_num)
      (check_of_le_cell hf hC (by norm_num) (by norm_num [Nat.factorial]))
    refine h.trans ?_
    rw [cellBound₂]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (2 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (2 + k) = 2 ^ (2 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (2 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (2 + (k + 1)) = 2 * 2 ^ (2 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₁ hf hC (k + 1) s (pairedSquares T)
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_cellBound₁ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 1) = 2 + k by ring] at hX hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [cellBound₂]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

theorem spectralSum_le_cellBound₃ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (3 + k) = -1) → T.card ≤ 3 →
      spectralSum f (2 ^ (3 + k)) s T ≤ cellBound₃ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le_hadamard hf s hT hTr (by norm_num) (d := 468)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
    refine h.trans ?_
    rw [cellBound₃]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (3 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (3 + k) = 2 ^ (3 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (3 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (3 + (k + 1)) = 2 * 2 ^ (3 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₁ hf hC (k + 2) s (pairedSquares T)
        (by rw [show 1 + (k + 2) = 3 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_cellBound₂ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 2 + (k + 1) = 3 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 2) = 3 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
        at hX
      rw [show 2 + (k + 1) = 3 + k by ring] at hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [cellBound₃]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

theorem spectralSum_le_cellBound₄ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (3 + k) = -1) → T.card ≤ 4 →
      spectralSum f (2 ^ (3 + k)) s T ≤ cellBound₄ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le_hadamard hf s hT hTr (by norm_num) (d := 63)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
    refine h.trans ?_
    rw [cellBound₄]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (3 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (3 + k) = 2 ^ (3 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (3 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (3 + (k + 1)) = 2 * 2 ^ (3 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₂ hf hC (k + 1) s (pairedSquares T)
        (by rw [show 2 + (k + 1) = 3 + k by ring]; exact hP2) (by omega)
      have hY' := spectralSum_le_cellBound₃ hf hC k s (T.image (· ^ 2)) hT2 (by omega)
      rw [show 2 + (k + 1) = 3 + k by ring] at hX
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY').trans ?_
      rw [cellBound₄, show 2 ^ (k + 1) * s / 2 = 2 ^ k * s by
        rw [pow_succ, mul_right_comm, Nat.mul_div_cancel _ two_pos]]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

theorem spectralSum_le_cellBound₅ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), (∀ ρ ∈ T, ρ ^ 2 ^ (4 + k) = -1) → T.card ≤ 5 →
      spectralSum f (2 ^ (4 + k)) s T ≤ cellBound₅ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hT hTr
    have h := spectralSum_le_of_pow_le hf s hT hTr (by norm_num) (d := 528) (by norm_num)
      (check_of_le_cell hf hC (by norm_num) (by norm_num [Nat.factorial]))
    refine h.trans ?_
    rw [cellBound₅]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (4 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (4 + k) = 2 ^ (4 + (k + 1)) by ring]
      exact hT ρ hρ
    have hT2 := pow_eq_neg_one_of_mem_image hT'
    have hP2 : ∀ ν ∈ pairedSquares T, ν ^ 2 ^ (4 + k) = -1 :=
      fun ν hν => hT2 ν (pairedSquares_subset T hν)
    rw [show 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · have hcard := card_pairedSquares_add_card_image_le two_ne_zero_modulus h0
      have hPpos := card_pairedSquares_pos hpair
      have hPsub := card_le_card (pairedSquares_subset T)
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₂ hf hC (k + 2) s (pairedSquares T)
        (by rw [show 2 + (k + 2) = 4 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_cellBound₄ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
      rw [show 2 + (k + 2) = 4 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
        at hX
      rw [show 3 + (k + 1) = 4 + k by ring] at hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [cellBound₅]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ hT2 (card_image_le.trans hTr)

/-! ### Evaluation at length 256 -/

theorem cellBound₁_nonneg (m : ℕ) : 0 ≤ cellBound₁ m := by
  rw [cellBound₁]
  positivity

theorem cellBound₂_nonneg (m : ℕ) : 0 ≤ cellBound₂ m := le_max_of_le_left (by positivity)

theorem cellBound₃_nonneg (m : ℕ) : 0 ≤ cellBound₃ m := le_max_of_le_left (by positivity)

theorem cellBound₄_nonneg (m : ℕ) : 0 ≤ cellBound₄ m := le_max_of_le_left (by positivity)

theorem cellBound₂_8_le : cellBound₂ 8 ≤ 1 / 16 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

theorem cellBound₂_16_le : cellBound₂ 16 ≤ 1 / 2 ^ 55 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

theorem cellBound₂_32_le : cellBound₂ 32 ≤ 1 / 2 ^ 156 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

theorem cellBound₃_8_le : cellBound₃ 8 ≤ 10 / 39 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellBound₂_nonneg _)
    cellBound₂_8_le).trans ?_
  norm_num [cellBound₁]

theorem cellBound₃_16_le : cellBound₃ 16 ≤ 1 / 2 ^ 72 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellBound₂_nonneg _)
    cellBound₂_16_le).trans ?_
  norm_num [cellBound₁]

theorem cellBound₄_16_le : cellBound₄ 16 ≤ 1 / 12 := by
  refine max_le (by norm_num) ?_
  rw [show (16 : ℕ) / 2 = 8 by norm_num]
  refine (two_mul_add_sq_add_sq_le (cellBound₂_nonneg _) cellBound₂_16_le (cellBound₃_nonneg _)
    cellBound₃_8_le).trans ?_
  norm_num

variable {T : Finset (ZMod 8380417)}

/-- `δ₁ ≤ 2^-512` at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cell₁_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 1) :
    spectralSum f 256 1 T ≤ 1 / (2 ^ 256) ^ 2 :=
  (spectralSum_le_cellBound₁ hf hC 7 1 T hT hTr).trans (by norm_num [cellBound₁])

/-- `δ₂ ≤ 2^-358` at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cell₂_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 2) :
    spectralSum f 256 1 T ≤ 1 / (2 ^ 179) ^ 2 :=
  (spectralSum_le_cellBound₂ hf hC 6 1 T hT hTr).trans
    (max_le (by norm_num) (by norm_num [cellBound₁]))

/-- `δ₃ ≤ 2^-214` at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cell₃_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 3) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 214 := by
  refine (spectralSum_le_cellBound₃ hf hC 5 1 T hT hTr).trans (max_le (by norm_num) ?_)
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellBound₂_nonneg _)
    cellBound₂_32_le).trans ?_
  norm_num [cellBound₁]

/-- `δ₄ ≤ 2^-99` at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cell₄_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 4) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 99 := by
  refine (spectralSum_le_cellBound₄ hf hC 5 1 T hT hTr).trans (max_le (by norm_num) ?_)
  rw [show 2 ^ 5 * 1 / 2 = 16 by norm_num]
  refine (two_mul_add_sq_add_sq_le (cellBound₂_nonneg _) cellBound₂_32_le (cellBound₃_nonneg _)
    cellBound₃_16_le).trans ?_
  norm_num

/-- **`δ₅ ≤ 2^-7`** at length 256 for `C ≤ q / 523383` (ML-DSA-65 and ML-DSA-87). -/
theorem spectralSum_cell₅_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 5) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 7 := by
  refine (spectralSum_le_cellBound₅ hf hC 4 1 T hT hTr).trans (max_le (by norm_num) ?_)
  refine (two_mul_add_sq_add_sq_le (cellBound₂_nonneg _) cellBound₂_32_le (cellBound₄_nonneg _)
    cellBound₄_16_le).trans ?_
  norm_num

end Cell

end GordieHowe.MLDSA.Regularity
