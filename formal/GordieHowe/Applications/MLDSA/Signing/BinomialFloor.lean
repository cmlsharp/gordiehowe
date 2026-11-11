-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Flatten

@[expose] public section

/-!
# The flat vector minimizes the Poisson-binomial CDF

For success probabilities `p_i ∈ [0, 1/2]` with `∑_i p_i² ≤ N x²` (`N = |ι|`, `x ∈ [0, 1]`),
`Pr[Bin(N, x) ≤ ω] ≤ Pr_p[X ≤ ω]` (`binomialCdf_le_poissonBinomialCdf_of_sum_sq_le`).

* `poissonBinomialCdf_comp_equiv`: the CDF is invariant under reindexing.
* `pairCdf`, `poissonBinomialCdf_eq_pair`, `pairCdf_one_zero_le`, `pairCdf_one_one_le`: in two
  coordinates `a ≠ b` the CDF is `C₀₀ - (p_a + p_b) P₀ + p_a p_b (P₀ - P₁)` with `C₀₀`,
  `P₀ = C₀₀ - C₁₀ ≥ 0`, `P₁ = C₁₀ - C₁₁ ≥ 0` the CDFs at the vertices of the pair.
* `poissonBinomialCdf_pair_move_le`: moving a pair along its circle `p_a² + p_b² = r²` to a
  larger sum `s'` with `s + s' ≤ 2` does not raise the CDF.
* `binomialCdf_anti_prob`: the binomial CDF is antitone in the success probability.
* `poissonBinomialCdf_const_le_of_sum_sq_eq`: on the sphere `∑_i p_i² = N y²`, the flat vector
  `y` minimizes the CDF, by finitely many pair moves.
* `binomialCdf_le_one`, `binomialCdf_pos`, `binomialCdfQ`: the binomial CDF is at most `1`,
  positive below `x = 1`, and has a rational form (`cast_binomialCdfQ`).
-/

namespace GordieHowe.MLDSA

open Finset

/-- **The Poisson-binomial CDF is invariant under reindexing**: for an equivalence
`e : κ ≃ ι`, `Pr_{p ∘ e}[X ≤ ω] = Pr_p[X ≤ ω]`. -/
theorem poissonBinomialCdf_comp_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (p : ι → ℝ) (ω : ℕ) :
    poissonBinomialCdf (p ∘ e) ω = poissonBinomialCdf p ω := by
  unfold poissonBinomialCdf
  refine sum_bij' (fun S _ => S.map e.toEmbedding) (fun T _ => T.map e.symm.toEmbedding)
    (fun S hS => by simpa using hS) (fun T hT => by simpa using hT)
    (fun S _ => by simp [map_map]) (fun T _ => by simp [map_map]) (fun S _ => ?_)
  rw [← e.prod_comp]
  simp

/-- Updating `a` below an update of `b ≠ a` overrides an earlier update of `a`. -/
theorem update_update_update_eq {ι : Type*} [DecidableEq ι] (p : ι → ℝ) {a b : ι} (hab : a ≠ b)
    (u u' v : ℝ) :
    Function.update (Function.update (Function.update p a u') b v) a u =
      Function.update (Function.update p a u) b v := by
  rw [Function.update_comm hab.symm, Function.update_idem]

/-- The CDF of `p` with `u` at `a` and `v` at `b`: at `u, v ∈ {0, 1}` the vertices of the pair
`{a, b}`. -/
noncomputable def pairCdf {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (a b : ι)
    (u v : ℝ) (ω : ℕ) : ℝ :=
  poissonBinomialCdf (Function.update (Function.update p a u) b v) ω

/-- `pairCdf` depends on `p` only off `{a, b}`. -/
theorem pairCdf_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {p p' : ι → ℝ} {a b : ι}
    (h : ∀ i, i ≠ a → i ≠ b → p' i = p i) (u v : ℝ) (ω : ℕ) :
    pairCdf p' a b u v ω = pairCdf p a b u v ω := by
  unfold pairCdf
  congr 1
  funext i
  by_cases hb : i = b
  · subst hb; simp
  by_cases ha : i = a
  · subst ha; simp [Function.update_of_ne hb]
  simp [Function.update_of_ne ha, Function.update_of_ne hb, h i ha hb]

/-- The two mixed vertices of a pair have one CDF (`poissonBinomialCdf_comp_equiv` at the swap
of `a` and `b`). -/
theorem pairCdf_zero_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) {a b : ι}
    (hab : a ≠ b) (ω : ℕ) : pairCdf p a b 0 1 ω = pairCdf p a b 1 0 ω := by
  refine Eq.trans ?_ (poissonBinomialCdf_comp_equiv (Equiv.swap a b) _ ω)
  unfold pairCdf
  congr 1
  funext i
  by_cases ha : i = a
  · subst ha; simp [Function.update_of_ne hab]
  by_cases hb : i = b
  · subst hb; simp [Function.update_of_ne hab]
  simp [Function.update_of_ne ha, Function.update_of_ne hb, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- **The two-coordinate form of the CDF**: for `a ≠ b`,
`Pr_p[X ≤ ω] = C₀₀ - (p_a + p_b) P₀ + p_a p_b (P₀ - P₁)` with `C_{uv} = pairCdf p a b u v ω`,
`P₀ = C₀₀ - C₁₀` and `P₁ = C₁₀ - C₁₁` (`poissonBinomialCdf_update_eq_add` at `b` and at `a`,
and `pairCdf_zero_one`). -/
theorem poissonBinomialCdf_eq_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    {a b : ι} (hab : a ≠ b) (ω : ℕ) :
    poissonBinomialCdf p ω = pairCdf p a b 0 0 ω -
      (p a + p b) * (pairCdf p a b 0 0 ω - pairCdf p a b 1 0 ω) +
      p a * p b * ((pairCdf p a b 0 0 ω - pairCdf p a b 1 0 ω) -
        (pairCdf p a b 1 0 ω - pairCdf p a b 1 1 ω)) := by
  have hA : ∀ u v, pairCdf p a b u v ω =
      (1 - v) * pairCdf p a b u 0 ω + v * pairCdf p a b u 1 ω := fun u v =>
    poissonBinomialCdf_update_eq_add _ b v ω
  have hB : ∀ u v, pairCdf p a b u v ω =
      (1 - u) * pairCdf p a b 0 v ω + u * pairCdf p a b 1 v ω := by
    intro u v
    unfold pairCdf
    rw [← update_update_update_eq p hab u 0 v, poissonBinomialCdf_update_eq_add,
      update_update_update_eq p hab, update_update_update_eq p hab]
  have hp : pairCdf p a b (p a) (p b) ω = poissonBinomialCdf p ω := by
    simp [pairCdf]
  rw [← hp, hA (p a) (p b), hB (p a) 0, hB (p a) 1, pairCdf_zero_one p hab]
  ring

/-- The vertex values of `p` with the pair `{a, b}` set to `u, v ∈ [0, 1]` lie in `[0, 1]` when
the other coordinates do. -/
theorem update_update_mem_Icc {ι : Type*} [DecidableEq ι] {p : ι → ℝ} {a b : ι}
    (hp : ∀ i, i ≠ a → i ≠ b → 0 ≤ p i ∧ p i ≤ 1) {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (i : ι) :
    0 ≤ Function.update (Function.update p a u) b v i ∧
      Function.update (Function.update p a u) b v i ≤ 1 := by
  by_cases hb : i = b
  · subst hb; simp [hv0, hv1]
  by_cases ha : i = a
  · subst ha; simp [Function.update_of_ne hb, hu0, hu1]
  simpa [Function.update_of_ne ha, Function.update_of_ne hb] using hp i ha hb

/-- `P₀ ≥ 0`: raising `a` from `0` to `1` lowers the CDF (`poissonBinomialCdf_update_le`). -/
theorem pairCdf_one_zero_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ} {a b : ι}
    (hab : a ≠ b) (hp : ∀ i, i ≠ a → i ≠ b → 0 ≤ p i ∧ p i ≤ 1) (ω : ℕ) :
    pairCdf p a b 1 0 ω ≤ pairCdf p a b 0 0 ω := by
  have h := update_update_mem_Icc hp le_rfl zero_le_one le_rfl zero_le_one
  unfold pairCdf
  rw [← update_update_update_eq p hab 1 0 0]
  exact poissonBinomialCdf_update_le (fun i => (h i).1) (fun i => (h i).2) a
    (by simp [Function.update_of_ne hab]) ω

/-- `P₁ ≥ 0`: raising `b` from `0` to `1` lowers the CDF (`poissonBinomialCdf_update_le`). -/
theorem pairCdf_one_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ} {a b : ι}
    (hp : ∀ i, i ≠ a → i ≠ b → 0 ≤ p i ∧ p i ≤ 1) (ω : ℕ) :
    pairCdf p a b 1 1 ω ≤ pairCdf p a b 1 0 ω := by
  have h := update_update_mem_Icc hp zero_le_one le_rfl le_rfl zero_le_one
  unfold pairCdf
  have e : Function.update (Function.update p a 1) b 1 =
      Function.update (Function.update (Function.update p a 1) b 0) b 1 := by
    rw [Function.update_idem]
  rw [e]
  exact poissonBinomialCdf_update_le (fun i => (h i).1) (fun i => (h i).2) b (by simp) ω

/-- **The pair move**: if `p'` agrees with `p` off `{a, b}`, the other coordinates lie in
`[0, 1]`, `p'_a² + p'_b² = p_a² + p_b²`, the four values are nonnegative, `s = p_a + p_b ≤
s' = p'_a + p'_b` and `s + s' ≤ 2`, then `Pr_{p'}[X ≤ ω] ≤ Pr_p[X ≤ ω]`: the difference is
`-(s' - s)((1 - σ) P₀ + σ P₁)` with `σ = (s + s')/2` (`poissonBinomialCdf_eq_pair`). -/
theorem poissonBinomialCdf_pair_move_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p p' : ι → ℝ}
    {a b : ι} (hab : a ≠ b) (hagree : ∀ i, i ≠ a → i ≠ b → p' i = p i)
    (hp : ∀ i, i ≠ a → i ≠ b → 0 ≤ p i ∧ p i ≤ 1) (ha : 0 ≤ p a) (hb : 0 ≤ p b)
    (ha' : 0 ≤ p' a) (hb' : 0 ≤ p' b) (hsq : p' a ^ 2 + p' b ^ 2 = p a ^ 2 + p b ^ 2)
    (hs : p a + p b ≤ p' a + p' b) (hs2 : p a + p b + p' a + p' b ≤ 2) (ω : ℕ) :
    poissonBinomialCdf p' ω ≤ poissonBinomialCdf p ω := by
  rw [poissonBinomialCdf_eq_pair p hab, poissonBinomialCdf_eq_pair p' hab,
    pairCdf_congr hagree, pairCdf_congr hagree, pairCdf_congr hagree]
  have hP0 := pairCdf_one_zero_le hab hp ω
  have hP1 := pairCdf_one_one_le hp ω
  set P0 := pairCdf p a b 0 0 ω - pairCdf p a b 1 0 ω
  set P1 := pairCdf p a b 1 0 ω - pairCdf p a b 1 1 ω
  set s := p a + p b
  set s' := p' a + p' b
  have hmid : 0 ≤ (1 - (s + s') / 2) * P0 + (s + s') / 2 * P1 := by
    have : 0 ≤ s + s' := by simp only [s, s']; linarith
    have : 0 ≤ P0 := by simp only [P0]; linarith
    have : 0 ≤ P1 := by simp only [P1]; linarith
    have : 0 ≤ 1 - (s + s') / 2 := by simp only [s, s']; linarith
    positivity
  have key := mul_nonneg (sub_nonneg.2 hs) hmid
  nlinarith [key]

/-- **The binomial CDF is antitone in the success probability**: for `0 ≤ x ≤ y ≤ 1`,
`Pr[Bin(N, y) ≤ ω] ≤ Pr[Bin(N, x) ≤ ω]` (`poissonBinomialCdf_anti` at the flat vectors of
`poissonBinomialCdf_indicator_eq`). -/
theorem binomialCdf_anti_prob {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) (N ω : ℕ) :
    binomialCdf y N ω ≤ binomialCdf x N ω := by
  have ex := poissonBinomialCdf_indicator_eq (univ : Finset (Fin N)) x ω
  have ey := poissonBinomialCdf_indicator_eq (univ : Finset (Fin N)) y ω
  simp only [mem_univ, ite_true, card_univ, Fintype.card_fin] at ex ey
  rw [← ex, ← ey]
  exact poissonBinomialCdf_anti (fun _ => hx0) (fun _ => hxy) (fun _ => hy1) ω

/-- The Poisson-binomial CDF of the flat vector `y` is the binomial CDF
(`poissonBinomialCdf_indicator_eq` at `T = univ`). -/
theorem poissonBinomialCdf_const {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ℝ) (ω : ℕ) :
    poissonBinomialCdf (fun _ : ι => y) ω = binomialCdf y (Fintype.card ι) ω := by
  have e := poissonBinomialCdf_indicator_eq (univ : Finset ι) y ω
  simpa only [mem_univ, ite_true, card_univ] using e

/-- **The flat vector minimizes the CDF on the sphere**: for `p_i ∈ [0, 1/2]` and `y ≥ 0` with
`∑_i p_i² = N y²`, `Pr_y[X ≤ ω] ≤ Pr_p[X ≤ ω]`. By strong induction on the number of
coordinates different from `y`: a coordinate `a` below `y` and one `b` above move to `y` and
`z = √(p_a² + p_b² - y²)`, a pair move (`poissonBinomialCdf_pair_move_le`). -/
theorem poissonBinomialCdf_const_le_of_sum_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h2 : ∀ i, p i ≤ 1 / 2) {y : ℝ} (hy : 0 ≤ y)
    (hsq : ∑ i, p i ^ 2 = Fintype.card ι * y ^ 2) (ω : ℕ) :
    poissonBinomialCdf (fun _ : ι => y) ω ≤ poissonBinomialCdf p ω := by
  suffices h : ∀ n, ∀ p : ι → ℝ, (univ.filter fun i => p i ≠ y).card = n → (∀ i, 0 ≤ p i) →
      (∀ i, p i ≤ 1 / 2) → ∑ i, p i ^ 2 = Fintype.card ι * y ^ 2 →
      poissonBinomialCdf (fun _ : ι => y) ω ≤ poissonBinomialCdf p ω from h _ _ rfl h0 h2 hsq
  clear h0 h2 hsq p
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn h0 h2 hsq
  have hsum : ∑ i, p i ^ 2 = ∑ _i : ι, y ^ 2 := by
    rw [hsq, sum_const, card_univ, nsmul_eq_mul]
  by_cases hflat : ∀ i, p i = y
  · exact le_of_eq (congrArg (poissonBinomialCdf · ω) (funext fun i => (hflat i).symm))
  push Not at hflat
  obtain ⟨i₀, hi₀⟩ := hflat
  -- a coordinate below `y` and one above, else the sum of squares would differ from `N y²`
  have hlow : ∃ a, p a < y := by
    by_contra hc
    push Not at hc
    have := (sum_eq_sum_iff_of_le fun i _ => pow_le_pow_left₀ hy (hc i) 2).1 hsum.symm i₀
      (mem_univ _)
    exact hi₀ ((pow_left_inj₀ (h0 i₀) hy two_ne_zero).1 this.symm)
  have hhigh : ∃ b, y < p b := by
    by_contra hc
    push Not at hc
    have := (sum_eq_sum_iff_of_le fun i _ => pow_le_pow_left₀ (h0 i) (hc i) 2).1 hsum i₀
      (mem_univ _)
    exact hi₀ ((pow_left_inj₀ (h0 i₀) hy two_ne_zero).1 this)
  obtain ⟨a, ha⟩ := hlow
  obtain ⟨b, hb⟩ := hhigh
  have hab : a ≠ b := fun h => by subst h; linarith
  have ha0 := h0 a
  have hb2 := h2 b
  set z := Real.sqrt (p a ^ 2 + p b ^ 2 - y ^ 2) with hz
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = p a ^ 2 + p b ^ 2 - y ^ 2 := Real.sq_sqrt (by nlinarith)
  have hz2 : z ≤ 1 / 2 := by nlinarith
  set p' := Function.update (Function.update p a y) b z with hp'
  have hp'a : p' a = y := by simp [p', Function.update_of_ne hab]
  have hp'b : p' b = z := by simp [p']
  have hagree : ∀ i, i ≠ a → i ≠ b → p' i = p i := fun i hia hib => by
    simp [p', Function.update_of_ne hia, Function.update_of_ne hib]
  have hsq' : ∑ i, p' i ^ 2 = ∑ i, p i ^ 2 := by
    rw [← sub_eq_zero, ← sum_sub_distrib,
      Fintype.sum_eq_add a b hab fun i hi => by rw [hagree i hi.1 hi.2, sub_self], hp'a, hp'b]
    linarith
  -- the moved pair has the larger sum: `y z ≥ p_a p_b`
  have hyz : p a * p b ≤ y * z := by
    have hd : 0 ≤ (y ^ 2 - p a ^ 2) * (p b ^ 2 - y ^ 2) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    have h1 : (p a * p b) ^ 2 ≤ (y * z) ^ 2 := by
      rw [mul_pow, mul_pow, hzsq]; nlinarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg ha0 (h0 b)) (mul_nonneg hy hz0) two_ne_zero).1 h1
  have hs : p a + p b ≤ y + z := by
    have h1 : (p a + p b) ^ 2 ≤ (y + z) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (add_nonneg ha0 (h0 b)) (add_nonneg hy hz0) two_ne_zero).1 h1
  have hlt : (univ.filter fun i => p' i ≠ y).card < n := by
    rw [← hn]
    refine (card_le_card fun i hi => ?_).trans_lt
      (card_erase_lt_of_mem (s := univ.filter fun i => p i ≠ y) (a := a) (by simp; linarith))
    simp only [mem_filter, mem_univ, true_and] at hi
    have hia : i ≠ a := fun h => hi (h ▸ hp'a)
    refine mem_erase.2 ⟨hia, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    by_cases hib : i = b
    · subst hib; linarith
    · rwa [← hagree i hia hib]
  have h0' : ∀ i, 0 ≤ p' i := fun i => by
    by_cases hib : i = b
    · subst hib; rw [hp'b]; exact hz0
    by_cases hia : i = a
    · subst hia; rw [hp'a]; exact hy
    rw [hagree i hia hib]; exact h0 i
  have h2' : ∀ i, p' i ≤ 1 / 2 := fun i => by
    by_cases hib : i = b
    · subst hib; rw [hp'b]; exact hz2
    by_cases hia : i = a
    · subst hia; rw [hp'a]; linarith [h2 i]
    rw [hagree i hia hib]; exact h2 i
  refine (ih _ hlt p' rfl h0' h2' (hsq'.trans hsq)).trans ?_
  refine poissonBinomialCdf_pair_move_le hab hagree
    (fun i _ _ => ⟨h0 i, by linarith [h2 i]⟩) ha0 (h0 b) (h0' a) (h0' b) ?_ ?_ ?_ ω
  · rw [hp'a, hp'b, hzsq]; ring
  · rw [hp'a, hp'b]; exact hs
  · linarith [h2 a, h2' a, h2' b]

/-- **The flat vector minimizes the CDF**: for success probabilities in `[0, 1/2]` whose squares
sum to at most `N · x²`, the probability of at most `ω` successes is at least the binomial one at
`x`. -/
theorem binomialCdf_le_poissonBinomialCdf_of_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h2 : ∀ i, p i ≤ 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hsq : ∑ i, p i ^ 2 ≤ Fintype.card ι * x ^ 2) (ω : ℕ) :
    binomialCdf x (Fintype.card ι) ω ≤ poissonBinomialCdf p ω := by
  set N := Fintype.card ι with hN
  set y := Real.sqrt ((∑ i, p i ^ 2) / N) with hy
  have hS0 : 0 ≤ ∑ i, p i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hysq : y ^ 2 = (∑ i, p i ^ 2) / N := Real.sq_sqrt (div_nonneg hS0 (Nat.cast_nonneg _))
  have hS : (∑ i, p i ^ 2) / N ≤ x ^ 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h, sq_nonneg]
    · rw [div_le_iff₀ (Nat.cast_pos.2 h)]; linarith
  have hsq' : ∑ i, p i ^ 2 = N * y ^ 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h
      simp [h]
    · rw [hysq]; field_simp
  have hyx : y ≤ x := by
    rw [hy, Real.sqrt_le_left hx0]
    exact hS
  calc binomialCdf x N ω ≤ binomialCdf y N ω := binomialCdf_anti_prob hy0 hyx hx1 N ω
    _ = poissonBinomialCdf (fun _ => y) ω := (poissonBinomialCdf_const y ω).symm
    _ ≤ poissonBinomialCdf p ω := poissonBinomialCdf_const_le_of_sum_sq_eq h0 h2 hy0 hsq' ω

/-! ### Bounds on the binomial CDF and its rational form -/

/-- The binomial CDF is at most `1` for `x ∈ [0, 1]`. -/
theorem binomialCdf_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (N ω : ℕ) :
    binomialCdf x N ω ≤ 1 := by
  rcases le_or_gt ω N with h | h
  · have ht := binomialCdf_add_tail x h
    have : 0 ≤ 1 - x := by linarith
    have : 0 ≤ ∑ j ∈ Ico (ω + 1) (N + 1), (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j) :=
      sum_nonneg fun j _ => by positivity
    linarith
  · rw [binomialCdf, ← sum_range_add_sum_Ico _ (show N + 1 ≤ ω + 1 by omega),
      sum_eq_zero (s := Ico (N + 1) (ω + 1)) fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (by have := (mem_Ico.1 hj).1; omega)]; simp,
      add_zero]
    exact (sum_range_choose_mul_pow_mul_pow x N).le

/-- The binomial CDF is positive for `x ∈ [0, 1)`: its term `j = 0` is `(1 - x)^N > 0`. -/
theorem binomialCdf_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N ω : ℕ) :
    0 < binomialCdf x N ω := by
  refine lt_of_lt_of_le ?_ (choose_mul_pow_mul_pow_le_binomialCdf h0 h1.le (Nat.zero_le ω) N)
  have : 0 < 1 - x := by linarith
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero]
  positivity

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- The binomial CDF at a rational probability. -/
@[irreducible] def binomialCdfQ (x : ℚ) (N ω : ℕ) : ℚ :=
  ∑ j ∈ range (ω + 1), (N.choose j : ℚ) * x ^ j * (1 - x) ^ (N - j)

@[simp, norm_cast] theorem cast_binomialCdfQ (x : ℚ) (N ω : ℕ) :
    (binomialCdfQ x N ω : ℝ) = binomialCdf (x : ℝ) N ω := by
  simp only [binomialCdfQ, binomialCdf, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_one, Rat.cast_natCast]

/-- The rational binomial CDF is at most `1` for `x ∈ [0, 1]`. -/
theorem binomialCdfQ_le_one {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (N ω : ℕ) :
    binomialCdfQ x N ω ≤ 1 := by
  have := binomialCdf_le_one (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1) N ω
  rw [← cast_binomialCdfQ] at this
  exact_mod_cast this

/-- The rational binomial CDF is positive for `x ∈ [0, 1)`. -/
theorem binomialCdfQ_pos {x : ℚ} (h0 : 0 ≤ x) (h1 : x < 1) (N ω : ℕ) :
    0 < binomialCdfQ x N ω := by
  have := binomialCdf_pos (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1) N ω
  rw [← cast_binomialCdfQ] at this
  exact_mod_cast this

/-- The rational binomial CDF is antitone in the success probability on `[0, 1]`. -/
theorem binomialCdfQ_anti_prob {x y : ℚ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) (N ω : ℕ) :
    binomialCdfQ y N ω ≤ binomialCdfQ x N ω := by
  have := binomialCdf_anti_prob (x := (x : ℝ)) (y := (y : ℝ)) (by exact_mod_cast hx0)
    (by exact_mod_cast hxy) (by exact_mod_cast hy1) N ω
  rw [← cast_binomialCdfQ, ← cast_binomialCdfQ] at this
  exact_mod_cast this

end GordieHowe.MLDSA
