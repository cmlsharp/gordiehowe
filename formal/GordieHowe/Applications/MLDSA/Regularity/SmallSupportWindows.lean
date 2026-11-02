-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SmallSupportBridge
public import GordieHowe.Applications.MLDSA.Regularity.KernelMass

@[expose] public section

/-!
# Small spectral supports up to seven roots

Two additions to the spectral recursion of `SmallSupport.lean` (the note "A shorter proof of the
stated HighBits regularity claim", 10 September 2026, Section 4) carry the small-support bounds
at cell size `523383` from five roots to seven.

- `spectralSum_le_two_windows`, a stopping bound that sums over the coefficients of a window: at
  length `a = 2^e`, `|T| ≤ r` and `2r ≤ a`, every block of `r` consecutive coefficients determines
  the amplitudes (`eq_of_word_window_eq`, Vandermonde), so
  `∑_λ ∏_{j < r} g (y_{b+j}) ≤ (∑_x g x)^r` (`sum_prod_window_le`). The largest coefficient of a
  nonzero word avoids one of the two windows `[0, r)` and `[r, 2r)` and has weight at most
  `d^(-s)` (Lemma 2), so `δ_{a,s}(T) ≤ 2 S^r / d^s` whenever `∑_x f(x)^s ≤ S`; this replaces the
  count `q^r` of note (9) by `2 S^r`.
- `spectralSum_two_mul_le_fibre`, a paired halving step:
  `δ_{2a,s}(T) ≤ 2 δ_{a,s}(P) + δ_{a,s}(P)^2 + q^{|P|} δ_{a,2s}(T²)`. Amplitude vectors vanishing
  at every unpaired root are counted as in note (12); for the others both halves are nonzero,
  `xy ≤ (x² + y²)/2`, and the even half together with the odd half on the paired squares
  determines the amplitudes (`eq_of_evenPart_eq_of_oddPart_eqOn`), so each half is hit by at
  most `q^{|P|}` amplitude vectors.

With these, at `C ≤ q / 523383` and with `S = 610` (`sum_le_610`), the bounds
`cellWindowBound₂ … ₄` (two-window stops at lengths `4, 8, 8`, `d = 90, 468, 63`, and the paired
step (12)) give `δ₂ ≤ 2^-394`, `δ₃ ≤ 2^-255`, `δ₄ ≤ 2^-153`, and the bounds
`cellWindowBound₅ … ₇` (two-window stops at length 16, `d = 897, 331, 122`, and the paired step
with fibre counts) give `δ₅ ≤ 2^-75`, `δ₆ ≤ 2^-52`, `δ₇ ≤ 2^-29`, all at length 256
(`spectralSum_cellWindow₂_le … ₇_le`; the values of `d` are the Hadamard form of Lemma 2).
`smallSupportBounds_seven_of_isKernelBound` records `SmallSupportBounds r f 7 cellWindowDelta`.
-/

open Finset

namespace GordieHowe.MLDSA.Regularity

/-! ### Windows of consecutive coefficients -/

section Field

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The amplitudes shifted by `b`, `ρ ↦ λ_ρ ρ^b`: their word is the word of `λ` read from `b`. -/
def shiftAmplitudes (l : K → K) (b : ℕ) : K → K := fun ρ => l ρ * ρ ^ b

omit [DecidableEq K] in
/-- The word of the shifted amplitudes is the word read from `b`. -/
theorem word_shiftAmplitudes (l : K → K) (b c : ℕ) :
    word (shiftAmplitudes l b) c = word l (b + c) := by
  simp only [word, shiftAmplitudes, pow_add, mul_assoc]

omit [DecidableEq K] in
/-- The word is additive in the amplitudes. -/
theorem word_sub (l l' : K → K) (c : ℕ) : word (l - l') c = word l c - word l' c := by
  simp only [word, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **A window of `r` consecutive coefficients is an information set**: for amplitudes on a set
`T ∌ 0` of at most `r` points, the coefficients `b, …, b + r - 1` of the word determine the
amplitudes. -/
theorem eq_of_word_window_eq {T : Finset K} (h0 : (0 : K) ∉ T) {r : ℕ} (hTr : T.card ≤ r)
    {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T) (b : ℕ)
    (h : ∀ j < r, word l (b + j) = word l' (b + j)) : l = l' := by
  by_contra hne
  have hmem : shiftAmplitudes (l - l') b ∈ amplitudes T := by
    refine mem_amplitudes.2 fun ρ hρ => ?_
    by_contra hρT
    apply hρ
    simp [shiftAmplitudes, eq_zero_of_mem_amplitudes hl hρT, eq_zero_of_mem_amplitudes hl' hρT]
  have hne0 : shiftAmplitudes (l - l') b ≠ 0 := by
    intro hz
    apply hne
    funext ρ
    by_cases hρT : ρ ∈ T
    · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρT h0
      have hρ := congrFun hz ρ
      simp only [shiftAmplitudes, Pi.sub_apply, Pi.zero_apply] at hρ
      rcases mul_eq_zero.1 hρ with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 (pow_ne_zero b hρ0)
    · rw [eq_zero_of_mem_amplitudes hl hρT, eq_zero_of_mem_amplitudes hl' hρT]
  obtain ⟨c, hc, hwc⟩ := exists_word_ne_zero hmem hne0 hTr
  apply hwc
  rw [word_shiftAmplitudes, word_sub, h c hc, sub_self]

/-- **The window sum**: for `g ≥ 0`, a window of `r` consecutive coefficients and amplitudes on a
set `T ∌ 0` of at most `r` points, `∑_λ ∏_{j < r} g (y_{b+j}) ≤ (∑_x g x)^r`. -/
theorem sum_prod_window_le {g : K → ℝ} (hg : ∀ x, 0 ≤ g x) {T : Finset K} (h0 : (0 : K) ∉ T)
    {r : ℕ} (hTr : T.card ≤ r) (b : ℕ) {U : Finset (K → K)} (hU : U ⊆ amplitudes T) :
    ∑ l ∈ U, ∏ j ∈ range r, g (word l (b + j)) ≤ (∑ x, g x) ^ r := by
  have hinj : Set.InjOn (fun l (j : Fin r) => word l (b + j)) (U : Set (K → K)) := by
    intro l hl l' hl' h
    refine eq_of_word_window_eq h0 hTr (hU hl) (hU hl') b fun j hj => ?_
    exact congrFun h ⟨j, hj⟩
  have h := sum_comp_le_sum_of_injOn (t := (univ : Finset (Fin r → K)))
    (F := fun x => ∏ j, g (x j)) hinj (fun _ _ => mem_univ _)
    (fun y _ => prod_nonneg fun j _ => hg _)
  calc ∑ l ∈ U, ∏ j ∈ range r, g (word l (b + j))
      = ∑ l ∈ U, ∏ j : Fin r, g (word l (b + j)) := by
        refine sum_congr rfl fun l _ => ?_
        exact (Fin.prod_univ_eq_prod_range (fun j => g (word l (b + j))) r).symm
    _ ≤ ∑ x : Fin r → K, ∏ j, g (x j) := h
    _ = (∑ x, g x) ^ r := (Fintype.sum_pow g r).symm

/-! ### The paired halving step with fibre counts -/

/-- The even half and the odd half on the paired squares determine the amplitudes. -/
theorem eq_of_evenPart_eq_of_oddPart_eqOn (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T)
    (he : evenPart l = evenPart l') (ho : ∀ ν ∈ pairedSquares T, oddPart l ν = oddPart l' ν) :
    l = l' := by
  funext ρ
  by_cases hρ : ρ ∈ T
  · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρ h0
    have h1 := congrFun he (ρ ^ 2)
    rw [evenPart_sq h2 hρ0, evenPart_sq h2 hρ0] at h1
    by_cases hn : -ρ ∈ T
    · have h3 := ho (ρ ^ 2) (mem_image.2 ⟨ρ, mem_filter.2 ⟨hρ, hn⟩, rfl⟩)
      rw [oddPart_sq h2 hρ0, oddPart_sq h2 hρ0] at h3
      have h : (2 * ρ) * l ρ = (2 * ρ) * l' ρ := by linear_combination ρ * h1 + h3
      exact mul_left_cancel₀ (mul_ne_zero h2 hρ0) h
    · rwa [eq_zero_of_mem_amplitudes hl hn, eq_zero_of_mem_amplitudes hl' hn, add_zero,
        add_zero] at h1
  · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]

/-- The odd half and the even half on the paired squares determine the amplitudes. -/
theorem eq_of_oddPart_eq_of_evenPart_eqOn (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T)
    {l l' : K → K} (hl : l ∈ amplitudes T) (hl' : l' ∈ amplitudes T)
    (ho : oddPart l = oddPart l') (he : ∀ ν ∈ pairedSquares T, evenPart l ν = evenPart l' ν) :
    l = l' := by
  funext ρ
  by_cases hρ : ρ ∈ T
  · have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρ h0
    have h3 := congrFun ho (ρ ^ 2)
    rw [oddPart_sq h2 hρ0, oddPart_sq h2 hρ0] at h3
    by_cases hn : -ρ ∈ T
    · have h1 := he (ρ ^ 2) (mem_image.2 ⟨ρ, mem_filter.2 ⟨hρ, hn⟩, rfl⟩)
      rw [evenPart_sq h2 hρ0, evenPart_sq h2 hρ0] at h1
      have h : (2 * ρ) * l ρ = (2 * ρ) * l' ρ := by linear_combination ρ * h1 + h3
      exact mul_left_cancel₀ (mul_ne_zero h2 hρ0) h
    · rw [eq_zero_of_mem_amplitudes hl hn, eq_zero_of_mem_amplitudes hl' hn, mul_zero, sub_zero,
        sub_zero] at h3
      exact mul_left_cancel₀ hρ0 h3
  · rw [eq_zero_of_mem_amplitudes hl hρ, eq_zero_of_mem_amplitudes hl' hρ]

variable {f : K → ℝ}

omit [Field K] in
/-- A sum of `F (h l, v l)` over an injective image in `A ×ˢ univ`, `v l : P → K`, is at most
`q^{|P|} ∑_{e ∈ A} F e`. -/
theorem sum_le_card_pow_mul_of_injOn {U : Finset (K → K)} {A : Finset (K → K)} {P : Finset K}
    {F : (K → K) → ℝ} (hF : ∀ e ∈ A, 0 ≤ F e) (h : (K → K) → K → K) (v : (K → K) → P → K)
    (hinj : Set.InjOn (fun l => (h l, v l)) (U : Set (K → K))) (hmaps : ∀ l ∈ U, h l ∈ A) :
    ∑ l ∈ U, F (h l) ≤ (Fintype.card K : ℝ) ^ P.card * ∑ e ∈ A, F e := by
  have hle := sum_comp_le_sum_of_injOn (t := A ×ˢ (univ : Finset (P → K)))
    (F := fun p => F p.1) hinj (fun l hl => mem_product.2 ⟨hmaps l hl, mem_univ _⟩)
    (fun p hp => hF p.1 (mem_product.1 hp).1)
  refine hle.trans (le_of_eq ?_)
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, nsmul_eq_mul]
  push_cast
  ring

/-- **The paired halving step with fibre counts.**
`δ_{2a,s}(T) ≤ 2 δ_{a,s}(P) + δ_{a,s}(P)² + q^{|P|} δ_{a,2s}(T²)`, with `P` the squares of the
opposite pairs and `q = |K|`. -/
theorem spectralSum_two_mul_le_fibre (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (h2 : (2 : K) ≠ 0) {T : Finset K} (h0 : (0 : K) ∉ T) (a s : ℕ) :
    spectralSum f (2 * a) s T ≤ 2 * spectralSum f a s (pairedSquares T) +
      spectralSum f a s (pairedSquares T) ^ 2 +
      (Fintype.card K : ℝ) ^ (pairedSquares T).card *
        spectralSum f a (2 * s) (T.image (· ^ 2)) := by
  classical
  set AP := amplitudes (pairedSquares T) with hAP
  set A2 := (amplitudes (T.image (· ^ 2))).erase 0 with hA2
  set S0 := (AP ×ˢ AP).erase (0, 0) with hS0
  set A := (amplitudes T).erase 0 with hA
  let sing : (K → K) → Prop := fun l => ∀ ρ ∈ T, -ρ ∉ T → l ρ = 0
  let Φ : (K → K) → (K → K) × (K → K) := fun l => (evenPart l, oddPart l)
  let G : (K → K) × (K → K) → ℝ := fun p => weight f a s p.1 * weight f a s p.2
  have hG : ∀ p, 0 ≤ G p := fun p => mul_nonneg (weight_nonneg hf0 _ _ _) (weight_nonneg hf0 _ _ _)
  -- the amplitude vectors vanishing at every unpaired root: note (12)
  have hpart0 : ∑ l ∈ A.filter sing, weight f (2 * a) s l ≤
      2 * spectralSum f a s (pairedSquares T) + spectralSum f a s (pairedSquares T) ^ 2 := by
    have hinj : Set.InjOn Φ ((A.filter sing : Finset (K → K)) : Set (K → K)) :=
      fun l hl l' hl' h => eq_of_evenPart_eq_of_oddPart_eq h2 h0
        (mem_erase.1 (mem_filter.1 hl).1).2 (mem_erase.1 (mem_filter.1 hl').1).2
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    have hmaps : ∀ l ∈ A.filter sing, Φ l ∈ S0 := by
      intro l hl
      obtain ⟨hlA, hsing⟩ := mem_filter.1 hl
      obtain ⟨hl0, hl⟩ := mem_erase.1 hlA
      have hEP : evenPart l ∈ AP := by
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
      refine mem_erase.2 ⟨fun h => hl0 ?_, mem_product.2 ⟨hEP, hOP⟩⟩
      exact eq_of_evenPart_eq_of_oddPart_eq h2 h0 hl (zero_mem_amplitudes T)
        ((congrArg Prod.fst h).trans evenPart_zero.symm)
        ((congrArg Prod.snd h).trans oddPart_zero.symm)
    have hsum0 : ∑ p ∈ S0, G p = 2 * weight f a s 0 * spectralSum f a s (pairedSquares T) +
        spectralSum f a s (pairedSquares T) ^ 2 := by
      rw [hS0, sum_erase_eq_sub (mem_product.2 ⟨zero_mem_amplitudes _, zero_mem_amplitudes _⟩),
        sum_product]
      simp only [G]
      rw [← sum_mul_sum, spectralSum, ← hAP, ← add_sum_erase AP _ (zero_mem_amplitudes _)]
      ring
    calc ∑ l ∈ A.filter sing, weight f (2 * a) s l = ∑ l ∈ A.filter sing, G (Φ l) :=
          sum_congr rfl fun l _ => weight_two_mul a s l
      _ ≤ ∑ p ∈ S0, G p := sum_comp_le_sum_of_injOn hinj hmaps fun p _ => hG p
      _ ≤ 2 * spectralSum f a s (pairedSquares T) + spectralSum f a s (pairedSquares T) ^ 2 := by
          rw [hsum0]
          have h1 := weight_le_one hf0 hf1 a s 0
          have h3 := spectralSum_nonneg hf0 a s (pairedSquares T)
          nlinarith
  -- the others: both halves are nonzero, and each half is hit at most `q^{|P|}` times
  have hne : ∀ l ∈ A.filter (fun l => ¬ sing l), evenPart l ∈ A2 ∧ oddPart l ∈ A2 := by
    intro l hl
    obtain ⟨hlA, hsing⟩ := mem_filter.1 hl
    have hl := (mem_erase.1 hlA).2
    simp only [sing] at hsing
    push Not at hsing
    obtain ⟨ρ, hρT, hnρ, hlρ⟩ := hsing
    have hρ0 : ρ ≠ 0 := ne_of_mem_of_not_mem hρT h0
    have hlneg : l (-ρ) = 0 := eq_zero_of_mem_amplitudes hl hnρ
    refine ⟨mem_erase.2 ⟨fun h => hlρ ?_, evenPart_mem hl⟩,
      mem_erase.2 ⟨fun h => mul_ne_zero hρ0 hlρ ?_, oddPart_mem hl⟩⟩
    · have h' := congrFun h (ρ ^ 2)
      rwa [evenPart_sq h2 hρ0, hlneg, add_zero] at h'
    · have h' := congrFun h (ρ ^ 2)
      rwa [oddPart_sq h2 hρ0, hlneg, mul_zero, sub_zero] at h'
  have hsubA : A.filter (fun l => ¬ sing l) ⊆ amplitudes T :=
    fun l hl => (mem_erase.1 (mem_filter.1 hl).1).2
  have hW0 : ∀ e ∈ A2, 0 ≤ weight f a (2 * s) e := fun e _ => weight_nonneg hf0 _ _ _
  have hE := sum_le_card_pow_mul_of_injOn (U := A.filter (fun l => ¬ sing l)) (A := A2)
    (P := pairedSquares T) hW0 evenPart (fun l ν => oddPart l ν)
    (fun l hl l' hl' h => eq_of_evenPart_eq_of_oddPart_eqOn h2 h0 (hsubA hl) (hsubA hl')
      (congrArg Prod.fst h) fun ν hν => congrFun (congrArg Prod.snd h) ⟨ν, hν⟩)
    fun l hl => (hne l hl).1
  have hO := sum_le_card_pow_mul_of_injOn (U := A.filter (fun l => ¬ sing l)) (A := A2)
    (P := pairedSquares T) hW0 oddPart (fun l ν => evenPart l ν)
    (fun l hl l' hl' h => eq_of_oddPart_eq_of_evenPart_eqOn h2 h0 (hsubA hl) (hsubA hl')
      (congrArg Prod.fst h) fun ν hν => congrFun (congrArg Prod.snd h) ⟨ν, hν⟩)
    fun l hl => (hne l hl).2
  have hpart1 : ∑ l ∈ A.filter (fun l => ¬ sing l), weight f (2 * a) s l ≤
      (Fintype.card K : ℝ) ^ (pairedSquares T).card *
        spectralSum f a (2 * s) (T.image (· ^ 2)) := by
    calc ∑ l ∈ A.filter (fun l => ¬ sing l), weight f (2 * a) s l
        ≤ ∑ l ∈ A.filter (fun l => ¬ sing l),
            (weight f a (2 * s) (evenPart l) + weight f a (2 * s) (oddPart l)) / 2 := by
          refine sum_le_sum fun l _ => ?_
          rw [weight_two_mul, ← weight_sq, ← weight_sq]
          nlinarith [sq_nonneg (weight f a s (evenPart l) - weight f a s (oddPart l))]
      _ = (∑ l ∈ A.filter (fun l => ¬ sing l), weight f a (2 * s) (evenPart l) +
            ∑ l ∈ A.filter (fun l => ¬ sing l), weight f a (2 * s) (oddPart l)) / 2 := by
          rw [← sum_add_distrib, sum_div]
      _ ≤ ((Fintype.card K : ℝ) ^ (pairedSquares T).card * ∑ e ∈ A2, weight f a (2 * s) e +
            (Fintype.card K : ℝ) ^ (pairedSquares T).card * ∑ e ∈ A2, weight f a (2 * s) e) /
            2 := by
          linarith [hE, hO]
      _ = (Fintype.card K : ℝ) ^ (pairedSquares T).card *
            spectralSum f a (2 * s) (T.image (· ^ 2)) := by
          rw [show spectralSum f a (2 * s) (T.image (· ^ 2)) = ∑ e ∈ A2, weight f a (2 * s) e
            from rfl]
          ring
  rw [show spectralSum f (2 * a) s T = ∑ l ∈ A, weight f (2 * a) s l from rfl,
    ← sum_filter_add_sum_filter_not A sing]
  linarith

end Field

/-! ### The two-window stopping bound -/

section ZMod

variable {q : ℕ} [Fact q.Prime] {C : ℝ} {f : ZMod q → ℝ}

/-- Under the lift hypothesis of note (9) (every nonzero integer word in the span has a
coefficient of absolute value at least `C d`), every nonzero amplitude vector has a coefficient
of weight at most `1 / d`. -/
theorem exists_le_one_div_of_forall_mul_le_abs (hf : IsKernelBound C f) {e : ℕ}
    {T : Finset (ZMod q)} (hTa : T.card ≤ 2 ^ e) {d : ℝ} (hd : 0 < d)
    (hlift : ∀ v : Fin (2 ^ e) → ℤ, v ≠ 0 → (fun b => (v b : ZMod q)) ∈ Submodule.span (ZMod q)
      ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T) →
      ∀ B : ℤ, (∀ b, |v b| ≤ B) → C * d ≤ B)
    {l : ZMod q → ZMod q} (hl : l ∈ amplitudes T) (hl0 : l ≠ 0) :
    ∃ b < 2 ^ e, f (word l b) ≤ 1 / d := by
  set v : Fin (2 ^ e) → ℤ := fun b => (word l b).valMinAbs with hvdef
  obtain ⟨b1, hb1, hwb1⟩ := exists_word_ne_zero hl hl0 hTa
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
  refine ⟨b0, b0.isLt, ?_⟩
  have h := hf.mul_abs_valMinAbs_le _ hx0
  calc f (word l b0) ≤ C / |(v b0 : ℝ)| := (le_div_iff₀ hBpos).2 h
    _ ≤ 1 / d := by
        rw [div_le_div_iff₀ hBpos hd]
        linarith

/-- A word coefficient of weight at most `1 / d` outside a window of `r` coefficients inside the
length bounds the weight by `d^(-s)` times the window product. -/
theorem weight_le_window (hf : IsKernelBound C f) {a r b b₀ : ℕ} (s : ℕ) (hb : b + r ≤ a)
    (hb₀ : b₀ < a) (hb₀w : b₀ ∉ Ico b (b + r)) {d : ℝ} {l : ZMod q → ZMod q}
    (hfb : f (word l b₀) ≤ 1 / d) :
    weight f a s l ≤ (1 / d) ^ s * ∏ j ∈ range r, f (word l (b + j)) ^ s := by
  have hsub : insert b₀ (Ico b (b + r)) ⊆ range a := by
    intro c hc
    rcases mem_insert.1 hc with rfl | hc
    · exact mem_range.2 hb₀
    · exact mem_range.2 (lt_of_lt_of_le (mem_Ico.1 hc).2 hb)
  have hg0 : ∀ c, 0 ≤ f (word l c) ^ s := fun c => pow_nonneg (hf.nonneg _) s
  calc weight f a s l = ∏ c ∈ range a, f (word l c) ^ s := rfl
    _ ≤ ∏ c ∈ insert b₀ (Ico b (b + r)), f (word l c) ^ s :=
        prod_le_prod_of_subset_of_le_one₀ hsub (fun c _ => hg0 c)
          fun c _ _ => pow_le_one₀ (hf.nonneg _) (hf.le_one _)
    _ = f (word l b₀) ^ s * ∏ c ∈ Ico b (b + r), f (word l c) ^ s := prod_insert hb₀w
    _ ≤ (1 / d) ^ s * ∏ c ∈ Ico b (b + r), f (word l c) ^ s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hf.nonneg _) hfb s)
          (prod_nonneg fun c _ => hg0 c)
    _ = (1 / d) ^ s * ∏ j ∈ range r, f (word l (b + j)) ^ s := by
        rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]

/-- **The two-window stopping bound.** At length `a = 2^e`, `|T| ≤ r` with `2r ≤ a` and `0 ∉ T`,
under the lift hypothesis of note (9) and `∑_x f(x)^s ≤ S`: `δ_{a,s}(T) ≤ 2 S^r / d^s`. -/
theorem spectralSum_le_two_windows (hf : IsKernelBound C f) {e r : ℕ} (s : ℕ)
    {T : Finset (ZMod q)} (h0 : (0 : ZMod q) ∉ T) (hTr : T.card ≤ r) (hra : 2 * r ≤ 2 ^ e)
    {d : ℝ} (hd : 0 < d)
    (hlift : ∀ v : Fin (2 ^ e) → ℤ, v ≠ 0 → (fun b => (v b : ZMod q)) ∈ Submodule.span (ZMod q)
      ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T) →
      ∀ B : ℤ, (∀ b, |v b| ≤ B) → C * d ≤ B)
    {S : ℝ} (hS : ∑ x, f x ^ s ≤ S) :
    spectralSum f (2 ^ e) s T ≤ 2 * S ^ r / d ^ s := by
  set W : ℕ → (ZMod q → ZMod q) → ℝ := fun b l => ∏ j ∈ range r, f (word l (b + j)) ^ s
  have hW0 : ∀ b l, 0 ≤ W b l := fun b l => prod_nonneg fun j _ => pow_nonneg (hf.nonneg _) s
  have hterm : ∀ l ∈ (amplitudes T).erase 0,
      weight f (2 ^ e) s l ≤ (1 / d) ^ s * (W 0 l + W r l) := by
    intro l hl
    obtain ⟨hl0, hl⟩ := mem_erase.1 hl
    obtain ⟨b₀, hb₀, hfb⟩ := exists_le_one_div_of_forall_mul_le_abs hf (hTr.trans (by omega)) hd
      hlift hl hl0
    have hd0 : 0 ≤ (1 / d) ^ s := by positivity
    by_cases hw : b₀ ∈ Ico 0 (0 + r)
    · have hw' : b₀ ∉ Ico r (r + r) := by
        intro h
        simp only [mem_Ico] at hw h
        omega
      have h := weight_le_window hf s (by omega) hb₀ hw' hfb
      nlinarith [hW0 0 l]
    · have h := weight_le_window hf s (by omega) hb₀ hw hfb
      nlinarith [hW0 r l]
  have hS0 : 0 ≤ ∑ x, f x ^ s := sum_nonneg fun x _ => pow_nonneg (hf.nonneg x) s
  have hsub : (amplitudes T).erase 0 ⊆ amplitudes T := erase_subset _ _
  have hw1 : ∀ b, ∑ l ∈ (amplitudes T).erase 0, W b l ≤ S ^ r := fun b =>
    (sum_prod_window_le (fun x => pow_nonneg (hf.nonneg x) s) h0 hTr b hsub).trans
      (pow_le_pow_left₀ hS0 hS r)
  calc spectralSum f (2 ^ e) s T
      ≤ ∑ l ∈ (amplitudes T).erase 0, (1 / d) ^ s * (W 0 l + W r l) := sum_le_sum hterm
    _ = (1 / d) ^ s * (∑ l ∈ (amplitudes T).erase 0, W 0 l +
          ∑ l ∈ (amplitudes T).erase 0, W r l) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ (1 / d) ^ s * (S ^ r + S ^ r) := by
        gcongr
        · exact hw1 0
        · exact hw1 r
    _ = 2 * S ^ r / d ^ s := by
        rw [one_div_pow]
        ring

/-- **The two-window stopping bound, Hadamard form.** `δ_{a,s}(T) ≤ 2 S^r / d^s` at `a = 2^e`,
`|T| ≤ r`, `2r ≤ a`, whenever `(C d)^(2a) · a^a ≤ q^(2(a - r))` and `∑_x f(x)^s ≤ S`. -/
theorem spectralSum_le_two_windows_hadamard (hf : IsKernelBound C f) {e r : ℕ} (s : ℕ)
    {T : Finset (ZMod q)} (hT : ∀ ρ ∈ T, ρ ^ 2 ^ e = -1) (hTr : T.card ≤ r)
    (hra : 2 * r ≤ 2 ^ e) {d : ℝ} (hd : 0 < d)
    (hcheck : (C * d) ^ (2 * 2 ^ e) * ((2 ^ e : ℕ) : ℝ) ^ 2 ^ e ≤ (q : ℝ) ^ (2 * (2 ^ e - r)))
    {S : ℝ} (hS : ∑ x, f x ^ s ≤ S) :
    spectralSum f (2 ^ e) s T ≤ 2 * S ^ r / d ^ s := by
  refine spectralSum_le_two_windows hf s (zero_notMem_of_pow_eq_neg_one (by positivity) hT) hTr
    hra hd (fun v hv hspan B hB => ?_) hS
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

/-! ### The bounds up to seven roots at cell size `523383`

The recursion of `SmallSupport.lean` (section `Cell`) with the two-window stopping bound
(Hadamard checks `(C d)^(2a) a^a ≤ q^(2(a - r))` at `C = q / 523383`, `S = 610`).
`cellWindowBound₂ … ₄` keep the paired step (12) of `cellBound₂ … ₄`. `cellWindowBound₅ … ₇`
stop at length `16` and use the paired step with fibre counts: there `|P| ∈ {1, 2}` (five roots)
or `{1, 2, 3}` (six and seven roots), and the term for each value of `|P|` reads `δ(P)` and
`δ(T²)` off the bounds for `|P|` and `|T| - |P|` roots. -/

section CellWindow

/-- `|T| ≤ 5` at `m = 2^k s` (length `2^(4+k)`), with the two-window stop and fibre counts. -/
noncomputable def cellWindowBound₅ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 5 / 897 ^ m)
    (max (2 * cellBound₁ (4 * m) + cellBound₁ (4 * m) ^ 2 + 8380417 * cellBound₄ (2 * m))
      (2 * cellBound₂ (2 * m) + cellBound₂ (2 * m) ^ 2 + 8380417 ^ 2 * cellBound₃ (2 * m)))

/-- `|T| ≤ 6` at `m = 2^k s` (length `2^(4+k)`). -/
noncomputable def cellWindowBound₆ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 6 / 331 ^ m)
    (max (2 * cellBound₁ (4 * m) + cellBound₁ (4 * m) ^ 2 + 8380417 * cellWindowBound₅ m)
      (max (2 * cellBound₂ (2 * m) + cellBound₂ (2 * m) ^ 2 + 8380417 ^ 2 * cellBound₄ (2 * m))
        (2 * cellBound₃ m + cellBound₃ m ^ 2 + 8380417 ^ 3 * cellBound₃ (2 * m))))

/-- `|T| ≤ 7` at `m = 2^k s` (length `2^(4+k)`). -/
noncomputable def cellWindowBound₇ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 7 / 122 ^ m)
    (max (2 * cellBound₁ (4 * m) + cellBound₁ (4 * m) ^ 2 + 8380417 * cellWindowBound₆ m)
      (max (2 * cellBound₂ (2 * m) + cellBound₂ (2 * m) ^ 2 + 8380417 ^ 2 * cellWindowBound₅ m)
        (2 * cellBound₃ m + cellBound₃ m ^ 2 + 8380417 ^ 3 * cellBound₄ (2 * m))))

variable {C : ℝ} {f : ZMod 8380417 → ℝ}

/-- The kernel mass of `f^s`, `s ≥ 1`, at `C ≤ q / 523383`: `∑_x f(x)^s ≤ 610`. -/
theorem sum_pow_le_610 (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) {s : ℕ}
    (hs : 1 ≤ s) : ∑ x, f x ^ s ≤ 610 :=
  (sum_le_sum fun x _ => pow_le_of_le_one (hf.nonneg x) (hf.le_one x) (by omega)).trans
    (sum_le_610 hf.nonneg hf.le_one hf.mul_abs_valMinAbs_le (hC.trans (by norm_num)))

/-- `2x + x² + Ny` is monotone on nonnegative arguments. -/
theorem two_mul_add_sq_add_mul_le {x X y Y N : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hN : 0 ≤ N)
    (hy : y ≤ Y) : 2 * x + x ^ 2 + N * y ≤ 2 * X + X ^ 2 + N * Y := by
  nlinarith [mul_le_mul hx hx hx0 (hx0.trans hx), mul_le_mul_of_nonneg_left hy hN]

/-- The paired data of a support of roots of `X^(2a) + 1`: the squares and the paired squares
are roots of `X^a + 1`, and `|P| + |T²| ≤ |T|`, `1 ≤ |P| ≤ |T²|` when `T` has an opposite pair. -/
theorem pairedData {T : Finset (ZMod 8380417)} {a : ℕ} (hT : ∀ ρ ∈ T, ρ ^ (2 * a) = -1)
    (h0 : (0 : ZMod 8380417) ∉ T) (hpair : ∃ ρ ∈ T, -ρ ∈ T) :
    (∀ ν ∈ T.image (· ^ 2), ν ^ a = -1) ∧ (∀ ν ∈ pairedSquares T, ν ^ a = -1) ∧
      (pairedSquares T).card + (T.image (· ^ 2)).card ≤ T.card ∧
      1 ≤ (pairedSquares T).card ∧ (pairedSquares T).card ≤ (T.image (· ^ 2)).card :=
  have hT2 := pow_eq_neg_one_of_mem_image hT
  ⟨hT2, fun ν hν => hT2 ν (pairedSquares_subset T hν),
    card_pairedSquares_add_card_image_le two_ne_zero_modulus h0, card_pairedSquares_pos hpair,
    card_le_card (pairedSquares_subset T)⟩

/-- `|ZMod q| = q` as a real number. -/
theorem card_zmod_modulus : (Fintype.card (ZMod 8380417) : ℝ) = 8380417 := by
  rw [ZMod.card]
  norm_num

/-- `|T| ≤ 2` at `m = 2^k s` (length `2^(2+k)`), with the two-window stop `d = 90`. -/
noncomputable def cellWindowBound₂ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 2 / 90 ^ m) (2 * cellBound₁ m + cellBound₁ m ^ 2 + cellBound₁ m ^ 2)

/-- `|T| ≤ 3` at `m = 2^k s` (length `2^(3+k)`), with the two-window stop `d = 468`. -/
noncomputable def cellWindowBound₃ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 3 / 468 ^ m)
    (2 * cellBound₁ (2 * m) + cellBound₁ (2 * m) ^ 2 + cellWindowBound₂ m ^ 2)

/-- `|T| ≤ 4` at `m = 2^k s` (length `2^(3+k)`), with the two-window stop `d = 63`; the larger
child `T²` stops at the same length, so its bound is read at `m / 2`. -/
noncomputable def cellWindowBound₄ (m : ℕ) : ℝ :=
  max (2 * 610 ^ 4 / 63 ^ m)
    (2 * cellWindowBound₂ m + cellWindowBound₂ m ^ 2 + cellWindowBound₃ (m / 2) ^ 2)

/-- **Two roots, two-window stop.** For `|T| ≤ 2` at length `2^(2+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₂ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₂ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (2 + k) = -1) → T.card ≤ 2 →
      spectralSum f (2 ^ (2 + k)) s T ≤ cellWindowBound₂ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 90)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₂]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (2 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (2 + k) = 2 ^ (2 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (2 + (k + 1)) = 2 * 2 ^ (2 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₁ hf hC (k + 1) s (pairedSquares T)
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_cellBound₁ hf hC (k + 1) s (T.image (· ^ 2))
        (by rw [show 1 + (k + 1) = 2 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 1) = 2 + k by ring] at hX hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [cellWindowBound₂]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-- The bound `cellWindowBound₂` is nonnegative. -/
theorem cellWindowBound₂_nonneg (m : ℕ) : 0 ≤ cellWindowBound₂ m :=
  le_max_of_le_left (by positivity)

/-- The bound `cellWindowBound₃` is nonnegative. -/
theorem cellWindowBound₃_nonneg (m : ℕ) : 0 ≤ cellWindowBound₃ m :=
  le_max_of_le_left (by positivity)

/-- **Three roots, two-window stop.** For `|T| ≤ 3` at length `2^(3+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₃ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₃ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (3 + k) = -1) → T.card ≤ 3 →
      spectralSum f (2 ^ (3 + k)) s T ≤ cellWindowBound₃ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 468)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₃]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (3 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (3 + k) = 2 ^ (3 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (3 + (k + 1)) = 2 * 2 ^ (3 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellBound₁ hf hC (k + 2) s (pairedSquares T)
        (by rw [show 1 + (k + 2) = 3 + k by ring]; exact hP2) (by omega)
      have hY := spectralSum_le_cellWindowBound₂ hf hC (k + 1) s (T.image (· ^ 2)) hs
        (by rw [show 2 + (k + 1) = 3 + k by ring]; exact hT2) (by omega)
      rw [show 1 + (k + 2) = 3 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
        at hX
      rw [show 2 + (k + 1) = 3 + k by ring] at hY
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY).trans ?_
      rw [cellWindowBound₃]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-- **Four roots, two-window stop.** For `|T| ≤ 4` at length `2^(3+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₄ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₄ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (3 + k) = -1) → T.card ≤ 4 →
      spectralSum f (2 ^ (3 + k)) s T ≤ cellWindowBound₄ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 63)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₄]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (3 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (3 + k) = 2 ^ (3 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (3 + (k + 1)) = 2 * 2 ^ (3 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      have hX := spectralSum_le_cellWindowBound₂ hf hC (k + 1) s (pairedSquares T) hs
        (by rw [show 2 + (k + 1) = 3 + k by ring]; exact hP2) (by omega)
      have hY' := spectralSum_le_cellWindowBound₃ hf hC k s (T.image (· ^ 2)) hs hT2 (by omega)
      rw [show 2 + (k + 1) = 3 + k by ring] at hX
      refine (two_mul_add_sq_add_sq_le (spectralSum_nonneg hf.nonneg _ _ _) hX
        (spectralSum_nonneg hf.nonneg _ _ _) hY').trans ?_
      rw [cellWindowBound₄, show 2 ^ (k + 1) * s / 2 = 2 ^ k * s by
        rw [pow_succ, mul_right_comm, Nat.mul_div_cancel _ two_pos]]
      exact le_max_right _ _
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-- **Five roots.** For `|T| ≤ 5` at length `2^(4+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₅ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₅ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (4 + k) = -1) → T.card ≤ 5 →
      spectralSum f (2 ^ (4 + k)) s T ≤ cellWindowBound₅ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 897)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₅]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (4 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (4 + k) = 2 ^ (4 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le_fibre hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      rw [card_zmod_modulus, cellWindowBound₅]
      refine le_max_of_le_right ?_
      rcases (by omega : (pairedSquares T).card = 1 ∨ (pairedSquares T).card = 2) with hp | hp
      · have hX := spectralSum_le_cellBound₁ hf hC (k + 3) s (pairedSquares T)
          (by rw [show 1 + (k + 3) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellBound₄ hf hC (k + 1) (2 * s) (T.image (· ^ 2))
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
        rw [show 1 + (k + 3) = 4 + k by ring, show 2 ^ (k + 3) * s = 4 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 3 + (k + 1) = 4 + k by ring, show 2 ^ (k + 1) * (2 * s) = 2 * (2 ^ (k + 1) * s)
          by ring] at hY
        rw [hp, pow_one]
        exact le_max_of_le_left (two_mul_add_sq_add_mul_le (spectralSum_nonneg hf.nonneg _ _ _)
          hX (by norm_num) hY)
      · have hX := spectralSum_le_cellBound₂ hf hC (k + 2) s (pairedSquares T)
          (by rw [show 2 + (k + 2) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellBound₃ hf hC (k + 1) (2 * s) (T.image (· ^ 2))
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
        rw [show 2 + (k + 2) = 4 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 3 + (k + 1) = 4 + k by ring, show 2 ^ (k + 1) * (2 * s) = 2 * (2 ^ (k + 1) * s)
          by ring] at hY
        rw [hp]
        exact le_max_of_le_right (two_mul_add_sq_add_mul_le (spectralSum_nonneg hf.nonneg _ _ _)
          hX (by norm_num) hY)
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-- **Six roots.** For `|T| ≤ 6` at length `2^(4+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₆ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₆ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (4 + k) = -1) → T.card ≤ 6 →
      spectralSum f (2 ^ (4 + k)) s T ≤ cellWindowBound₆ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 331)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₆]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (4 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (4 + k) = 2 ^ (4 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le_fibre hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      rw [card_zmod_modulus, cellWindowBound₆]
      refine le_max_of_le_right ?_
      have hm2 : 2 ^ (k + 1) * (2 * s) = 2 * (2 ^ (k + 1) * s) := by ring
      rcases (by omega : (pairedSquares T).card = 1 ∨ (pairedSquares T).card = 2 ∨
          (pairedSquares T).card = 3) with hp | hp | hp
      · have hX := spectralSum_le_cellBound₁ hf hC (k + 3) s (pairedSquares T)
          (by rw [show 1 + (k + 3) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellWindowBound₅ hf hC k (2 * s) (T.image (· ^ 2)) (by omega)
          hT2 (by omega)
        rw [show 1 + (k + 3) = 4 + k by ring, show 2 ^ (k + 3) * s = 4 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 2 ^ k * (2 * s) = 2 ^ (k + 1) * s by ring] at hY
        rw [hp, pow_one]
        exact le_max_of_le_left (two_mul_add_sq_add_mul_le (spectralSum_nonneg hf.nonneg _ _ _)
          hX (by norm_num) hY)
      · have hX := spectralSum_le_cellBound₂ hf hC (k + 2) s (pairedSquares T)
          (by rw [show 2 + (k + 2) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellBound₄ hf hC (k + 1) (2 * s) (T.image (· ^ 2))
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
        rw [show 2 + (k + 2) = 4 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 3 + (k + 1) = 4 + k by ring, hm2] at hY
        rw [hp]
        exact le_max_of_le_right (le_max_of_le_left (two_mul_add_sq_add_mul_le
          (spectralSum_nonneg hf.nonneg _ _ _) hX (by norm_num) hY))
      · have hX := spectralSum_le_cellBound₃ hf hC (k + 1) s (pairedSquares T)
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellBound₃ hf hC (k + 1) (2 * s) (T.image (· ^ 2))
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
        rw [show 3 + (k + 1) = 4 + k by ring] at hX
        rw [show 3 + (k + 1) = 4 + k by ring, hm2] at hY
        rw [hp]
        exact le_max_of_le_right (le_max_of_le_right (two_mul_add_sq_add_mul_le
          (spectralSum_nonneg hf.nonneg _ _ _) hX (by norm_num) hY))
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-- **Seven roots.** For `|T| ≤ 7` at length `2^(4+k)` and exponent `s ≥ 1`,
`δ ≤ cellWindowBound₇ (2^k s)`. -/
theorem spectralSum_le_cellWindowBound₇ (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    ∀ k s (T : Finset (ZMod 8380417)), 1 ≤ s → (∀ ρ ∈ T, ρ ^ 2 ^ (4 + k) = -1) → T.card ≤ 7 →
      spectralSum f (2 ^ (4 + k)) s T ≤ cellWindowBound₇ (2 ^ k * s) := by
  intro k
  induction k with
  | zero =>
    intro s T hs hT hTr
    have h := spectralSum_le_two_windows_hadamard hf s hT hTr (by norm_num) (d := 122)
      (by norm_num) (check_hadamard_of_le_cell hf hC (by norm_num) (by norm_num))
      (sum_pow_le_610 hf hC hs)
    refine h.trans ?_
    rw [cellWindowBound₇]
    exact le_max_of_le_left (by norm_num)
  | succ k ih =>
    intro s T hs hT hTr
    have h0 := zero_notMem_of_pow_eq_neg_one (by positivity) hT
    have hT' : ∀ ρ ∈ T, ρ ^ (2 * 2 ^ (4 + k)) = -1 := by
      intro ρ hρ
      rw [show 2 * 2 ^ (4 + k) = 2 ^ (4 + (k + 1)) by ring]
      exact hT ρ hρ
    rw [show 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) by ring]
    by_cases hpair : ∃ ρ ∈ T, -ρ ∈ T
    · obtain ⟨hT2, hP2, hcard, hP1, hPT⟩ := pairedData hT' h0 hpair
      refine (spectralSum_two_mul_le_fibre hf.nonneg hf.le_one two_ne_zero_modulus h0 _ s).trans ?_
      rw [card_zmod_modulus, cellWindowBound₇]
      refine le_max_of_le_right ?_
      have hm2 : 2 ^ (k + 1) * (2 * s) = 2 * (2 ^ (k + 1) * s) := by ring
      rcases (by omega : (pairedSquares T).card = 1 ∨ (pairedSquares T).card = 2 ∨
          (pairedSquares T).card = 3) with hp | hp | hp
      · have hX := spectralSum_le_cellBound₁ hf hC (k + 3) s (pairedSquares T)
          (by rw [show 1 + (k + 3) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellWindowBound₆ hf hC k (2 * s) (T.image (· ^ 2)) (by omega)
          hT2 (by omega)
        rw [show 1 + (k + 3) = 4 + k by ring, show 2 ^ (k + 3) * s = 4 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 2 ^ k * (2 * s) = 2 ^ (k + 1) * s by ring] at hY
        rw [hp, pow_one]
        exact le_max_of_le_left (two_mul_add_sq_add_mul_le (spectralSum_nonneg hf.nonneg _ _ _)
          hX (by norm_num) hY)
      · have hX := spectralSum_le_cellBound₂ hf hC (k + 2) s (pairedSquares T)
          (by rw [show 2 + (k + 2) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellWindowBound₅ hf hC k (2 * s) (T.image (· ^ 2)) (by omega)
          hT2 (by omega)
        rw [show 2 + (k + 2) = 4 + k by ring, show 2 ^ (k + 2) * s = 2 * (2 ^ (k + 1) * s) by ring]
          at hX
        rw [show 2 ^ k * (2 * s) = 2 ^ (k + 1) * s by ring] at hY
        rw [hp]
        exact le_max_of_le_right (le_max_of_le_left (two_mul_add_sq_add_mul_le
          (spectralSum_nonneg hf.nonneg _ _ _) hX (by norm_num) hY))
      · have hX := spectralSum_le_cellBound₃ hf hC (k + 1) s (pairedSquares T)
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hP2) (by omega)
        have hY := spectralSum_le_cellBound₄ hf hC (k + 1) (2 * s) (T.image (· ^ 2))
          (by rw [show 3 + (k + 1) = 4 + k by ring]; exact hT2) (by omega)
        rw [show 3 + (k + 1) = 4 + k by ring] at hX
        rw [show 3 + (k + 1) = 4 + k by ring, hm2] at hY
        rw [hp]
        exact le_max_of_le_right (le_max_of_le_right (two_mul_add_sq_add_mul_le
          (spectralSum_nonneg hf.nonneg _ _ _) hX (by norm_num) hY))
    · push Not at hpair
      refine (spectralSum_two_mul_le_of_forall_neg_notMem hf.nonneg two_ne_zero_modulus h0
        hpair _ s).trans ?_
      rw [show 2 ^ (k + 1) * s = 2 ^ k * (2 * s) by ring]
      exact ih (2 * s) _ (by omega) (pow_eq_neg_one_of_mem_image hT') (card_image_le.trans hTr)

/-! ### Evaluation at length 256 -/

/-- `cellBound₃ 32 ≤ 2^-214`. -/
theorem cellBound₃_32_le : cellBound₃ 32 ≤ 1 / 2 ^ 214 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellBound₂_nonneg _)
    cellBound₂_32_le).trans ?_
  norm_num [cellBound₁]

/-- `cellBound₄ 32 ≤ 2^-99`. -/
theorem cellBound₄_32_le : cellBound₄ 32 ≤ 1 / 2 ^ 99 := by
  refine max_le (by norm_num) ?_
  rw [show (32 : ℕ) / 2 = 16 by norm_num]
  refine (two_mul_add_sq_add_sq_le (cellBound₂_nonneg _) cellBound₂_32_le (cellBound₃_nonneg _)
    cellBound₃_16_le).trans ?_
  norm_num

/-- `cellWindowBound₂ 16 ≤ 2^-84`. -/
theorem cellWindowBound₂_16_le : cellWindowBound₂ 16 ≤ 1 / 2 ^ 84 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

/-- `cellWindowBound₂ 32 ≤ 2^-188`. -/
theorem cellWindowBound₂_32_le : cellWindowBound₂ 32 ≤ 1 / 2 ^ 188 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

/-- `cellWindowBound₂ 64 ≤ 2^-394`. -/
theorem cellWindowBound₂_64_le : cellWindowBound₂ 64 ≤ 1 / (2 ^ 197) ^ 2 :=
  max_le (by norm_num) (by norm_num [cellBound₁])

/-- `cellWindowBound₃ 16 ≤ 2^-113`. -/
theorem cellWindowBound₃_16_le : cellWindowBound₃ 16 ≤ 1 / 2 ^ 113 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellWindowBound₂_nonneg _)
    cellWindowBound₂_16_le).trans ?_
  norm_num [cellBound₁]

/-- `cellWindowBound₃ 32 ≤ 2^-255`. -/
theorem cellWindowBound₃_32_le : cellWindowBound₃ 32 ≤ 1 / 2 ^ 255 := by
  refine max_le (by norm_num) ?_
  refine (two_mul_add_sq_add_sq_le (cellBound₁_nonneg _) le_rfl (cellWindowBound₂_nonneg _)
    cellWindowBound₂_32_le).trans ?_
  norm_num [cellBound₁]

/-- `cellWindowBound₄ 32 ≤ 2^-153`. -/
theorem cellWindowBound₄_32_le : cellWindowBound₄ 32 ≤ 1 / 2 ^ 153 := by
  refine max_le (by norm_num) ?_
  rw [show (32 : ℕ) / 2 = 16 by norm_num]
  refine (two_mul_add_sq_add_sq_le (cellWindowBound₂_nonneg _) cellWindowBound₂_32_le
    (cellWindowBound₃_nonneg _) cellWindowBound₃_16_le).trans ?_
  norm_num

/-- `cellWindowBound₅ 16 ≤ 2^-75`. -/
theorem cellWindowBound₅_16_le : cellWindowBound₅ 16 ≤ 1 / 2 ^ 75 := by
  refine max_le (by norm_num) (max_le ?_ ?_)
  · refine (two_mul_add_sq_add_mul_le (cellBound₁_nonneg _) le_rfl (by norm_num)
      cellBound₄_32_le).trans ?_
    norm_num [cellBound₁]
  · refine (two_mul_add_sq_add_mul_le (cellBound₂_nonneg _) cellBound₂_32_le (by norm_num)
      cellBound₃_32_le).trans ?_
    norm_num

/-- `cellWindowBound₆ 16 ≤ 2^-52`. -/
theorem cellWindowBound₆_16_le : cellWindowBound₆ 16 ≤ 1 / 2 ^ 52 := by
  refine max_le (by norm_num) (max_le ?_ (max_le ?_ ?_))
  · refine (two_mul_add_sq_add_mul_le (cellBound₁_nonneg _) le_rfl (by norm_num)
      cellWindowBound₅_16_le).trans ?_
    norm_num [cellBound₁]
  · refine (two_mul_add_sq_add_mul_le (cellBound₂_nonneg _) cellBound₂_32_le (by norm_num)
      cellBound₄_32_le).trans ?_
    norm_num
  · refine (two_mul_add_sq_add_mul_le (cellBound₃_nonneg _) cellBound₃_16_le (by norm_num)
      cellBound₃_32_le).trans ?_
    norm_num

/-- `cellWindowBound₇ 16 ≤ 2^-29`. -/
theorem cellWindowBound₇_16_le : cellWindowBound₇ 16 ≤ 1 / 2 ^ 29 := by
  refine max_le (by norm_num) (max_le ?_ (max_le ?_ ?_))
  · refine (two_mul_add_sq_add_mul_le (cellBound₁_nonneg _) le_rfl (by norm_num)
      cellWindowBound₆_16_le).trans ?_
    norm_num [cellBound₁]
  · refine (two_mul_add_sq_add_mul_le (cellBound₂_nonneg _) cellBound₂_32_le (by norm_num)
      cellWindowBound₅_16_le).trans ?_
    norm_num
  · refine (two_mul_add_sq_add_mul_le (cellBound₃_nonneg _) cellBound₃_16_le (by norm_num)
      cellBound₄_32_le).trans ?_
    norm_num

variable {T : Finset (ZMod 8380417)}

/-- **`δ₂ ≤ 2^-394`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₂_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 2) :
    spectralSum f 256 1 T ≤ 1 / (2 ^ 197) ^ 2 :=
  (spectralSum_le_cellWindowBound₂ hf hC 6 1 T le_rfl hT hTr).trans cellWindowBound₂_64_le

/-- **`δ₃ ≤ 2^-255`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₃_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 3) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 255 :=
  (spectralSum_le_cellWindowBound₃ hf hC 5 1 T le_rfl hT hTr).trans cellWindowBound₃_32_le

/-- **`δ₄ ≤ 2^-153`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₄_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 4) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 153 :=
  (spectralSum_le_cellWindowBound₄ hf hC 5 1 T le_rfl hT hTr).trans cellWindowBound₄_32_le

/-- **`δ₅ ≤ 2^-75`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₅_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 5) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 75 :=
  (spectralSum_le_cellWindowBound₅ hf hC 4 1 T le_rfl hT hTr).trans cellWindowBound₅_16_le

/-- **`δ₆ ≤ 2^-52`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₆_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 6) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 52 :=
  (spectralSum_le_cellWindowBound₆ hf hC 4 1 T le_rfl hT hTr).trans cellWindowBound₆_16_le

/-- **`δ₇ ≤ 2^-29`** at length 256 for `C ≤ q / 523383`. -/
theorem spectralSum_cellWindow₇_le (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383)
    (hT : ∀ ρ ∈ T, ρ ^ 256 = -1) (hTr : T.card ≤ 7) :
    spectralSum f 256 1 T ≤ 1 / 2 ^ 29 :=
  (spectralSum_le_cellWindowBound₇ hf hC 4 1 T le_rfl hT hTr).trans cellWindowBound₇_16_le

end CellWindow

/-! ### `SmallSupportBounds` up to seven roots -/

/-- The small-support bounds up to seven roots at cell size at least `523383`. -/
noncomputable def cellWindowDelta (t : ℕ) : ℝ :=
  if t ≤ 1 then 1 / (2 ^ 256) ^ 2 else if t ≤ 2 then 1 / (2 ^ 197) ^ 2
  else if t ≤ 3 then 1 / 2 ^ 255 else if t ≤ 4 then 1 / 2 ^ 153 else if t ≤ 5 then 1 / 2 ^ 75
  else if t ≤ 6 then 1 / 2 ^ 52 else 1 / 2 ^ 29

/-- The values of `cellWindowDelta`. -/
theorem cellWindowDelta_le :
    (∀ t, 0 ≤ cellWindowDelta t) ∧ cellWindowDelta 1 ≤ 1 / (2 ^ 256) ^ 2 ∧
      cellWindowDelta 2 ≤ 1 / (2 ^ 197) ^ 2 ∧ cellWindowDelta 3 ≤ 1 / 2 ^ 255 ∧
      cellWindowDelta 4 ≤ 1 / 2 ^ 153 ∧ cellWindowDelta 5 ≤ 1 / 2 ^ 75 ∧
      cellWindowDelta 6 ≤ 1 / 2 ^ 52 ∧ cellWindowDelta 7 ≤ 1 / 2 ^ 29 := by
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cellWindowDelta; split_ifs <;> positivity
  all_goals simp [cellWindowDelta]

/-- **The small-support bounds up to seven roots at `q = 8380417`.** For distinct roots `r j` of
`X^256 + 1` and a kernel bound `f` with `C ≤ q / 523383`,
`SmallSupportBounds r f 7 cellWindowDelta`. -/
theorem smallSupportBounds_seven_of_isKernelBound {r : Fin 256 → ZMod 8380417}
    (hr : Function.Injective r) (hroot : ∀ j, r j ^ 256 = -1) {C : ℝ}
    {f : ZMod 8380417 → ℝ} (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    SmallSupportBounds r f 7 cellWindowDelta := by
  have hr0 : ∀ j, r j ≠ 0 := fun j h => by
    have := hroot j
    rw [h, zero_pow (by norm_num)] at this
    exact absurd this (by decide)
  refine ⟨fun T _ hT7 => (sum_powerCode_le_spectralSum hr hr0 hf.nonneg T).trans ?_⟩
  have hT' : ∀ ρ ∈ T.image r, ρ ^ 256 = -1 := by
    intro ρ hρ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hρ
    exact hroot j
  have hcard : (T.image r).card = #T := Finset.card_image_of_injective _ hr
  unfold cellWindowDelta
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact spectralSum_cell₁_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₂_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₃_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₄_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₅_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₆_le hf hC hT' (by omega)
  · exact spectralSum_cellWindow₇_le hf hC hT' (by omega)

end GordieHowe.MLDSA.Regularity
