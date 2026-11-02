-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.Convexity

@[expose] public section

/-!
# Classical interactions: randomized strategies against classical challengers

A classical interaction of `Q` rounds between an adversary and a challenger. The challenger
draws its coins `ω` up front (`Challenger.coins`), gives the adversary an input `input ω` (keys,
whole oracle tables), and answers the adversary's move `m` in a round with a reply drawn from
`reply ω h m`, which may read the coins and the history `h` of earlier moves and replies (so it
may also draw fresh coins in each round). The adversary is a **behavioral strategy** in the
sense of game theory (Kuhn, *Extensive games and the problem of information*, 1953): in each
round it draws its move
from a law `next i h` that depends on its input and the history, with fresh randomness, and after
the last round its output from `out i h`. Histories are lists of any length over any types, so a
strategy is a function on an infinite set of histories and need not be a finite object.

The experiment (`exper`) is the law of the history and the output; `winProb` is the
probability of an event. Deterministic strategies (`DetStrategy`) choose their moves and output
as functions of the input and the history.

## Results

`exists_det_winDiff_ge`: for two challengers and any event, some deterministic strategy has at least
the difference of winning probabilities of a given randomized strategy. So `abs_winDiff_le_of_det`:
a bound on the advantage of every deterministic strategy bounds that of every randomized one. This
is the multi-round form of `exists_gameAdvantage_bind_le`
(`GordieHowe/Foundations/Probability/Convexity.lean`), for strategies that randomize in every round
rather than up front. Its proof is backward induction: the difference of the two winning
probabilities is linear in the strategy's law at each history (each run passes through one history
of each length), so at each history, from the last round back, a move of largest continuation value
does at least as well as the strategy's law. The moves, replies and outputs range over finite types
(`Fintype M`, `R`, `O`), as for measured registers; the inputs, the coins and the histories do not.
No finite table of deterministic strategies is formed.

`tsum_mul_tsum_mul_comm` (at the `GordieHowe` level): two averages commute.
-/

open scoped ENNReal BigOperators

namespace GordieHowe

/-- **Two averages commute.** -/
theorem tsum_mul_tsum_mul_comm {α β : Type*} (μ : α → ℝ≥0∞) (ν : β → ℝ≥0∞)
    (f : α → β → ℝ≥0∞) :
    ∑' x, μ x * ∑' y, ν y * f x y = ∑' y, ν y * ∑' x, μ x * f x y := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun y => tsum_congr fun x => mul_left_comm _ _ _

end GordieHowe

namespace GordieHowe.Interaction

/-- **A history**: the moves and replies of the rounds so far, in order. -/
abbrev Hist (M R : Type*) := List (M × R)

/-- **A randomized (behavioral) strategy** with inputs `I`, moves `M`, replies `R` and outputs
`O`: the law of the next move given the input and the history, drawn with fresh randomness in
each round, and the law of the output after the last round. -/
structure Strategy (I M R O : Type*) where
  /-- The law of the next move. -/
  next : I → Hist M R → PMF M
  /-- The law of the output. -/
  out : I → Hist M R → PMF O

/-- **A deterministic strategy**: the next move and the output as functions of the input and the
history. -/
structure DetStrategy (I M R O : Type*) where
  /-- The next move. -/
  next : I → Hist M R → M
  /-- The output. -/
  out : I → Hist M R → O

/-- A deterministic strategy as a randomized one, with point-mass laws. -/
noncomputable def DetStrategy.toStrategy {I M R O : Type*} (s : DetStrategy I M R O) :
    Strategy I M R O where
  next i h := PMF.pure (s.next i h)
  out i h := PMF.pure (s.out i h)

/-- **A classical challenger** with coins in `Ω`: coins drawn up front from `coins`, the
adversary's input `input ω`, and the law `reply ω h m` of the reply to the move `m` after the
history `h`. -/
structure Challenger (Ω I M R : Type*) where
  /-- The law of the coins. -/
  coins : PMF Ω
  /-- The adversary's input. -/
  input : Ω → I
  /-- The law of the reply. -/
  reply : Ω → Hist M R → M → PMF R

variable {Ω I M R O : Type*}

/-- **The continuation of the interaction** from the history `h` with `k` rounds left, at the
challenger's coins `ω`: the law of the final history and the output. -/
noncomputable def cont (σ : Strategy I M R O) (χ : Challenger Ω I M R) (ω : Ω) :
    Hist M R → ℕ → PMF (Hist M R × O)
  | h, 0 => (σ.out (χ.input ω) h).map fun o => (h, o)
  | h, k + 1 => (σ.next (χ.input ω) h).bind fun m =>
      (χ.reply ω h m).bind fun r => cont σ χ ω (h ++ [(m, r)]) k

/-- **The experiment** of `Q` rounds: the coins, then the interaction from the empty history; the
law of the history and the output. -/
noncomputable def exper (σ : Strategy I M R O) (χ : Challenger Ω I M R) (Q : ℕ) :
    PMF (Hist M R × O) :=
  χ.coins.bind fun ω => cont σ χ ω [] Q

/-- The probability of the event `W` of the history and output in the experiment of `Q`
rounds. -/
noncomputable def winProb (σ : Strategy I M R O) (χ : Challenger Ω I M R) (Q : ℕ)
    (W : Set (Hist M R × O)) : ℝ :=
  ((exper σ χ Q).toOuterMeasure W).toReal

/-! ### Relabelled outputs -/

section MapOut

variable {O' : Type*}

/-- **The strategy with its output relabelled by `g`.** -/
noncomputable def Strategy.mapOut (σ : Strategy I M R O) (g : O → O') : Strategy I M R O' where
  next := σ.next
  out i h := (σ.out i h).map g

theorem cont_mapOut (σ : Strategy I M R O) (g : O → O') (χ : Challenger Ω I M R) (ω : Ω) :
    ∀ (k : ℕ) (h : Hist M R),
      cont (σ.mapOut g) χ ω h k = (cont σ χ ω h k).map (Prod.map id g)
  | 0, h => by
    simp only [cont, Strategy.mapOut, PMF.map_comp]
    rfl
  | k + 1, h => by
    simp only [cont, PMF.map_bind]
    refine congrArg _ (funext fun m => congrArg _ (funext fun r => ?_))
    exact cont_mapOut σ g χ ω k _

theorem winProb_mapOut (σ : Strategy I M R O) (g : O → O') (χ : Challenger Ω I M R) (Q : ℕ)
    (W : Set (Hist M R × O')) :
    winProb (σ.mapOut g) χ Q W = winProb σ χ Q (Prod.map id g ⁻¹' W) := by
  simp only [winProb, exper, cont_mapOut, ← PMF.map_bind, PMF.toOuterMeasure_map_apply]

end MapOut

/-! ### The weight of a history -/

section Weight

variable (χ : Challenger Ω I M R)

open Classical in
/-- **The challenger's weight of a history at its coins `ω` and the input `i`**: the probability
of `ω`, if its input is `i`, times the probabilities of the replies of the history given its
moves. -/
noncomputable def wt (i : I) (ω : Ω) (h : Hist M R) : ℝ≥0∞ :=
  (h.foldl (fun (a : ℝ≥0∞ × Hist M R) x => (a.1 * χ.reply ω a.2 x.1 x.2, a.2 ++ [x]))
    (χ.coins ω * (if χ.input ω = i then 1 else 0), [])).1

private theorem foldl_snd (ω : Ω) (h : Hist M R) (a : ℝ≥0∞) (l : Hist M R) :
    (h.foldl (fun (a : ℝ≥0∞ × Hist M R) x => (a.1 * χ.reply ω a.2 x.1 x.2, a.2 ++ [x]))
      (a, l)).2 = l ++ h := by
  induction h generalizing a l with
  | nil => simp
  | cons x h ih => simp [List.foldl_cons, ih]

open Classical in
theorem wt_nil (i : I) (ω : Ω) :
    wt χ i ω [] = χ.coins ω * (if χ.input ω = i then 1 else 0) :=
  rfl

theorem wt_append_singleton (i : I) (ω : Ω) (h : Hist M R) (m : M) (r : R) :
    wt χ i ω (h ++ [(m, r)]) = wt χ i ω h * χ.reply ω h m r := by
  unfold wt
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  congr 2
  rw [foldl_snd, List.nil_append]

theorem wt_eq_zero_of_ne {i : I} {ω : Ω} (hi : χ.input ω ≠ i) (h : Hist M R) :
    wt χ i ω h = 0 := by
  induction h using List.reverseRecOn with
  | nil => simp [wt_nil, hi]
  | append_singleton h x ih =>
    obtain ⟨m, r⟩ := x
    rw [wt_append_singleton, ih, zero_mul]

theorem wt_le_coins (i : I) (ω : Ω) (h : Hist M R) : wt χ i ω h ≤ χ.coins ω := by
  induction h using List.reverseRecOn with
  | nil =>
    rw [wt_nil]
    split_ifs <;> simp
  | append_singleton h x ih =>
    obtain ⟨m, r⟩ := x
    rw [wt_append_singleton]
    exact (mul_le_of_le_one_right' (PMF.coe_le_one _ _)).trans ih

/-- A function of the input weighted by the weight at input `i` reads the input as `i`. -/
theorem wt_mul_input {β : Type*} (f : I → β → ℝ≥0∞) (i : I) (ω : Ω) (h : Hist M R) (b : β) :
    wt χ i ω h * f (χ.input ω) b = wt χ i ω h * f i b := by
  by_cases hi : χ.input ω = i
  · rw [hi]
  · rw [wt_eq_zero_of_ne χ hi, zero_mul, zero_mul]

end Weight

/-! ### The weighted continuation -/

section Weighted

variable (σ : Strategy I M R O) (χ : Challenger Ω I M R) (W : Set (Hist M R × O))

/-- **The weighted winning probability from a history**: the sum over the coins of the weight of
the history times the probability that the continuation from it wins. -/
noncomputable def G (i : I) (h : Hist M R) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω, wt χ i ω h * (cont σ χ ω h k).toOuterMeasure W

theorem G_le (i : I) (h : Hist M R) (k : ℕ) : G σ χ W i h k ≤ ∑' ω, wt χ i ω h :=
  ENNReal.tsum_le_tsum fun _ => mul_le_of_le_one_right' (PMF.toOuterMeasure_apply_le_one _ _)

theorem tsum_wt_le_one (i : I) (h : Hist M R) : ∑' ω, wt χ i ω h ≤ 1 :=
  (ENNReal.tsum_le_tsum fun ω => wt_le_coins χ i ω h).trans_eq χ.coins.tsum_coe

theorem G_ne_top (i : I) (h : Hist M R) (k : ℕ) : G σ χ W i h k ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((G_le σ χ W i h k).trans (tsum_wt_le_one χ i h))

theorem G_succ (i : I) (h : Hist M R) (k : ℕ) :
    G σ χ W i h (k + 1) =
      ∑' m, σ.next i h m * ∑' r, G σ χ W i (h ++ [(m, r)]) k := by
  have hω : ∀ ω, wt χ i ω h * (cont σ χ ω h (k + 1)).toOuterMeasure W =
      ∑' m, σ.next i h m * ∑' r, wt χ i ω (h ++ [(m, r)]) *
        (cont σ χ ω (h ++ [(m, r)]) k).toOuterMeasure W := fun ω => by
    simp only [cont, PMF.toOuterMeasure_bind_apply]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m => ?_
    have h1 := wt_mul_input χ (fun i' m' => σ.next i' h m') i ω h m
    rw [← mul_assoc, h1, mul_assoc, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [wt_append_singleton]
    ring
  simp only [G, hω]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]

open Classical in
theorem G_zero (i : I) (h : Hist M R) :
    G σ χ W i h 0 =
      ∑' o, σ.out i h o * (if (h, o) ∈ W then ∑' ω, wt χ i ω h else 0) := by
  have hω : ∀ ω, wt χ i ω h * (cont σ χ ω h 0).toOuterMeasure W =
      ∑' o, σ.out i h o * (if (h, o) ∈ W then wt χ i ω h else 0) := fun ω => by
    simp only [cont]
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun o => ?_
    have h1 := wt_mul_input χ (fun i' o' => σ.out i' h o') i ω h o
    by_cases ho : (h, o) ∈ W
    · simp only [Set.indicator_of_mem (show o ∈ (fun o => (h, o)) ⁻¹' W from ho), if_pos ho]
      rw [h1, mul_comm]
    · simp only [Set.indicator_of_notMem (show o ∉ (fun o => (h, o)) ⁻¹' W from ho), if_neg ho,
        mul_zero]
  simp only [G, hω]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  rw [ENNReal.tsum_mul_left]
  split_ifs <;> simp

open Classical in
/-- The winning probability as the sum over the inputs of the weighted winning probability
from the empty history. -/
theorem toOuterMeasure_exper (Q : ℕ) :
    (exper σ χ Q).toOuterMeasure W = ∑' i, G σ χ W i [] Q := by
  simp only [exper, PMF.toOuterMeasure_bind_apply, G, wt_nil]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  simp only [mul_assoc, ENNReal.tsum_mul_left]
  congr 1
  simp_rw [ite_mul, one_mul, zero_mul, @eq_comm _ (χ.input ω)]
  rw [tsum_ite_eq]

theorem winProb_eq_tsum (Q : ℕ) :
    winProb σ χ Q W = ∑' i, (G σ χ W i [] Q).toReal := by
  rw [winProb, toOuterMeasure_exper, ENNReal.tsum_toReal_eq fun i => G_ne_top σ χ W i [] Q]

theorem summable_G_toReal (Q : ℕ) : Summable fun i => (G σ χ W i [] Q).toReal :=
  ENNReal.summable_toReal (by
    rw [← toOuterMeasure_exper]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _))

end Weighted

/-! ### Backward induction -/

section Backward

variable [Fintype M] [Fintype R] [Fintype O] {Ω₀ Ω₁ : Type*}
  (χ₀ : Challenger Ω₀ I M R) (χ₁ : Challenger Ω₁ I M R) (W : Set (Hist M R × O))

/-- **The signed weighted continuation**: the difference of the weighted winning probabilities
against the two challengers. -/
noncomputable def D (σ : Strategy I M R O) (i : I) (h : Hist M R) (k : ℕ) : ℝ :=
  (G σ χ₀ W i h k).toReal - (G σ χ₁ W i h k).toReal

open Classical in
/-- The value of output `o` at the history `h`: the signed weight of the history if `(h, o)`
wins. -/
noncomputable def c (i : I) (h : Hist M R) (o : O) : ℝ :=
  if (h, o) ∈ W then (∑' ω, wt χ₀ i ω h).toReal - (∑' ω, wt χ₁ i ω h).toReal else 0

theorem toReal_tsum_fintype_mul {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ≥0∞)
    (hf : ∀ a, f a ≠ ⊤) : (∑' a, p a * f a).toReal = ∑ a, (p a).toReal * (f a).toReal := by
  rw [tsum_fintype, ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hf a)]
  simp only [ENNReal.toReal_mul]

omit [Fintype O] in
theorem toReal_G_succ {Ω' : Type*} (χ : Challenger Ω' I M R) (σ : Strategy I M R O) (i : I)
    (h : Hist M R) (k : ℕ) : (G σ χ W i h (k + 1)).toReal =
      ∑ m, (σ.next i h m).toReal * ∑ r, (G σ χ W i (h ++ [(m, r)]) k).toReal := by
  rw [G_succ, toReal_tsum_fintype_mul _ _ fun m => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [tsum_fintype, ENNReal.toReal_sum fun r _ => G_ne_top σ χ W i _ k]
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 fun r _ => G_ne_top σ χ W i _ k

omit [Fintype M] [Fintype R] in
open Classical in
theorem toReal_G_zero {Ω' : Type*} (χ : Challenger Ω' I M R) (σ : Strategy I M R O) (i : I)
    (h : Hist M R) : (G σ χ W i h 0).toReal =
      ∑ o, (σ.out i h o).toReal * (if (h, o) ∈ W then (∑' ω, wt χ i ω h).toReal else 0) := by
  rw [G_zero, toReal_tsum_fintype_mul _ _ fun o => ?_]
  · refine Finset.sum_congr rfl fun o _ => ?_
    split_ifs <;> simp
  · split_ifs
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_wt_le_one χ i h)
    · exact ENNReal.zero_ne_top

omit [Fintype O] in
theorem D_succ (σ : Strategy I M R O) (i : I) (h : Hist M R) (k : ℕ) :
    D χ₀ χ₁ W σ i h (k + 1) =
      ∑ m, (σ.next i h m).toReal * ∑ r, D χ₀ χ₁ W σ i (h ++ [(m, r)]) k := by
  rw [D, toReal_G_succ, toReal_G_succ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rfl

omit [Fintype M] [Fintype R] in
theorem D_zero (σ : Strategy I M R O) (i : I) (h : Hist M R) :
    D χ₀ χ₁ W σ i h 0 = ∑ o, (σ.out i h o).toReal * c χ₀ χ₁ W i h o := by
  classical
  rw [D, toReal_G_zero, toReal_G_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← mul_sub, c]
  split_ifs <;> simp

/-- An average under a point mass is the value at the point. -/
theorem sum_pure_toReal_mul {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    ∑ x, ((PMF.pure a) x).toReal * f x = f a := by
  classical
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [PMF.pure_apply, hx])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [PMF.pure_apply]

variable [Nonempty M] [Nonempty O]

/-- **The value of a history** with `k` rounds left: the largest signed weighted continuation a
strategy can reach from it (`D_le_V`), reached by a greedy deterministic strategy
(`D_greedy_eq_V`). -/
noncomputable def V (i : I) : Hist M R → ℕ → ℝ
  | h, 0 => Finset.univ.sup' Finset.univ_nonempty (c χ₀ χ₁ W i h)
  | h, k + 1 => Finset.univ.sup' Finset.univ_nonempty fun m => ∑ r, V i (h ++ [(m, r)]) k

/-- An average under a law on a finite type is at most the largest value. -/
theorem sum_toReal_mul_le_sup' {α : Type*} [Fintype α] [Nonempty α] (p : PMF α) (f : α → ℝ) :
    ∑ a, (p a).toReal * f a ≤ Finset.univ.sup' Finset.univ_nonempty f := by
  calc ∑ a, (p a).toReal * f a ≤ ∑ a, (p a).toReal * Finset.univ.sup' Finset.univ_nonempty f :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (Finset.le_sup' f (Finset.mem_univ a)) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

/-- **No strategy exceeds the value.** -/
theorem D_le_V (σ : Strategy I M R O) (i : I) (k : ℕ) (h : Hist M R) :
    D χ₀ χ₁ W σ i h k ≤ V χ₀ χ₁ W i h k := by
  induction k generalizing h with
  | zero =>
    rw [D_zero, V]
    exact sum_toReal_mul_le_sup' _ _
  | succ k ih =>
    rw [D_succ, V]
    refine (Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun r _ => ih (h ++ [(m, r)])) ENNReal.toReal_nonneg).trans ?_
    exact sum_toReal_mul_le_sup' _ _

/-- A point where a function on a nonempty finite type is largest. -/
noncomputable def argmax {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : α :=
  Classical.choose (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)

theorem argmax_spec {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    f (argmax f) = Finset.univ.sup' Finset.univ_nonempty f :=
  le_antisymm (Finset.le_sup' f (Finset.mem_univ _))
    (Finset.sup'_le _ _ fun a _ =>
      (Classical.choose_spec (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)).2 a
        (Finset.mem_univ a))

/-- **The greedy deterministic strategy** for `Q` rounds: at each history, the move of largest
value with the remaining rounds, and the output of largest value. -/
noncomputable def greedy (Q : ℕ) : DetStrategy I M R O where
  next i h := argmax fun m => ∑ r, V χ₀ χ₁ W i (h ++ [(m, r)]) (Q - h.length - 1)
  out i h := argmax (c χ₀ χ₁ W i h)

/-- **The greedy strategy reaches the value.** -/
theorem D_greedy_eq_V (Q : ℕ) (i : I) (k : ℕ) (h : Hist M R) (hk : h.length + k = Q) :
    D χ₀ χ₁ W (greedy χ₀ χ₁ W Q).toStrategy i h k = V χ₀ χ₁ W i h k := by
  induction k generalizing h with
  | zero =>
    rw [D_zero, V]
    exact (sum_pure_toReal_mul _ _).trans (argmax_spec (c χ₀ χ₁ W i h))
  | succ k ih =>
    rw [D_succ, V]
    refine (sum_pure_toReal_mul ((greedy χ₀ χ₁ W Q).next i h) _).trans ?_
    rw [Finset.sum_congr rfl fun r _ => ih (h ++ [((greedy χ₀ χ₁ W Q).next i h, r)])
      (by simp; omega)]
    have hQ : Q - h.length - 1 = k := by omega
    have hn : (greedy χ₀ χ₁ W Q).next i h =
        argmax fun m => ∑ r, V χ₀ χ₁ W i (h ++ [(m, r)]) k := by
      simp only [greedy, hQ]
    rw [hn]
    exact argmax_spec fun m => ∑ r, V χ₀ χ₁ W i (h ++ [(m, r)]) k

/-- **Some deterministic strategy does at least as well as a randomized one**: for two
challengers and an event `W`, the greedy deterministic strategy has at least the difference of
the winning probabilities of the randomized strategy `σ`. -/
theorem exists_det_winDiff_ge (σ : Strategy I M R O) (Q : ℕ) :
    ∃ s : DetStrategy I M R O, winProb σ χ₀ Q W - winProb σ χ₁ Q W ≤
      winProb s.toStrategy χ₀ Q W - winProb s.toStrategy χ₁ Q W := by
  refine ⟨greedy χ₀ χ₁ W Q, ?_⟩
  have hdiff : ∀ τ : Strategy I M R O,
      winProb τ χ₀ Q W - winProb τ χ₁ Q W = ∑' i, D χ₀ χ₁ W τ i [] Q := fun τ => by
    rw [winProb_eq_tsum, winProb_eq_tsum,
      ← (summable_G_toReal τ χ₀ W Q).tsum_sub (summable_G_toReal τ χ₁ W Q)]
    rfl
  have hs : ∀ τ : Strategy I M R O, Summable fun i => D χ₀ χ₁ W τ i [] Q := fun τ =>
    (summable_G_toReal τ χ₀ W Q).sub (summable_G_toReal τ χ₁ W Q)
  rw [hdiff, hdiff]
  refine (hs σ).tsum_le_tsum (fun i => ?_) (hs _)
  rw [D_greedy_eq_V χ₀ χ₁ W Q i Q [] (by simp)]
  exact D_le_V χ₀ χ₁ W σ i Q []

/-- **A bound for every deterministic strategy bounds every randomized strategy**: if every
deterministic strategy's winning probabilities against the two challengers differ by at most
`ε`, so do those of every randomized strategy. -/
theorem abs_winDiff_le_of_det (σ : Strategy I M R O) (Q : ℕ) {ε : ℝ}
    (hdet : ∀ s : DetStrategy I M R O,
      |winProb s.toStrategy χ₀ Q W - winProb s.toStrategy χ₁ Q W| ≤ ε) :
    |winProb σ χ₀ Q W - winProb σ χ₁ Q W| ≤ ε := by
  rw [abs_sub_le_iff]
  obtain ⟨s, hs⟩ := exists_det_winDiff_ge χ₀ χ₁ W σ Q
  obtain ⟨s', hs'⟩ := exists_det_winDiff_ge χ₁ χ₀ W σ Q
  exact ⟨hs.trans ((le_abs_self _).trans (hdet s)),
    hs'.trans ((le_abs_self _).trans (abs_sub_comm (winProb s'.toStrategy χ₀ Q W) _ ▸ hdet s'))⟩

/-- **`abs_winDiff_le_of_det` as a game advantage** of the two experiments. -/
theorem gameAdvantage_exper_le_of_det (σ : Strategy I M R O) (Q : ℕ) {ε : ℝ}
    (hdet : ∀ s : DetStrategy I M R O,
      gameAdvantage (exper s.toStrategy χ₀ Q) (exper s.toStrategy χ₁ Q) W ≤ ε) :
    gameAdvantage (exper σ χ₀ Q) (exper σ χ₁ Q) W ≤ ε :=
  abs_winDiff_le_of_det χ₀ χ₁ W σ Q hdet

end Backward

end GordieHowe.Interaction
