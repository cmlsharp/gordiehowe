-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

public section

/-!
# The sorted-sum bound

For weights `w ≥ 0` and values `P` whose every sum over `m` indices is at most `E m`,
`∑ j, w j · P j ≤ ∑ m < n, (a m − a (m + 1)) · E (m + 1)`, where `a` lists the weights in antitone
order and `a n = 0` (`sum_mul_le_sortedSumBound`). The proof is Abel summation
(`sum_range_mul_eq_sum_sub_mul`): the partial sums of `P` along the order are sums over sets of
`m + 1` indices.

* `Fin.extendZero`: a vector `Fin n → ℝ` read on `ℕ`, zero from `n` on.
* `Tuple.antitoneSort`: a permutation listing a vector in antitone order.
* `sortedSumBound w E`: the bound at the order `Tuple.antitoneSort w`.
* `ConcaveTable E n`: `E 0 = 0` with antitone increments on `0..n`. Under it,
  `sortedSumBound w E ≤ A · E M + (∑ j, w j − A · M) · (E (M + 1) − E M)` for `0 ≤ w ≤ A` and
  every `M < n` (`sortedSumBound_le_fill`).
* `incrementTable l`: the table of a list of natural increments, concave when the list passes
  the antitone check `List.antitoneB` (`concaveTable_incrementTable`).
* `sortedSumBound_mono`: under a concave table with nonnegative increments, the bound is
  monotone in the weights `w ≥ 0`.
* `List.sortDesc`, `Finset.sum_le_sum_take_sortDesc`: a list of naturals in antitone order, and
  the sum over any `m` positions is at most the sum of its first `m` entries.
* `envelopeCheck l s u`, `sortedDot l u`: computable forms of the conditions "every sum of `m`
  values of `u / s` is at most `incrementTable l m`" (`sum_le_incrementTable_of_envelopeCheck`)
  and of an upper bound on `s · sortedSumBound w (incrementTable l)` for `0 ≤ w ≤ u / s`
  (`mul_sortedSumBound_le_sortedDot`).
-/

open Finset

/-- A vector `Fin n → ℝ` read on `ℕ`, zero from `n` on. -/
noncomputable def Fin.extendZero {n : ℕ} (v : Fin n → ℝ) (m : ℕ) : ℝ :=
  if h : m < n then v ⟨m, h⟩ else 0

/-- Below `n` the extension reads the vector. -/
theorem Fin.extendZero_of_lt {n : ℕ} (v : Fin n → ℝ) {m : ℕ} (h : m < n) :
    Fin.extendZero v m = v ⟨m, h⟩ := by
  simp [Fin.extendZero, h]

/-- The extension is zero at `n`. -/
theorem Fin.extendZero_self {n : ℕ} (v : Fin n → ℝ) : Fin.extendZero v n = 0 := by
  simp [Fin.extendZero]

/-- A sum over the indices up to `b` is the sum of the extended vector over `range (b + 1)`. -/
theorem Fin.sum_Iic_eq_sum_range_extendZero {n : ℕ} (v : Fin n → ℝ) (b : Fin n) :
    ∑ m ∈ Iic b, v m = ∑ i ∈ range (b + 1), Fin.extendZero v i := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  exact Finset.sum_congr rfl fun m _ => (Fin.extendZero_of_lt v m.isLt).symm

/-- **Abel summation on `range n`**: `∑ i < n, a i Q i = ∑ l < n, (a l − a (l + 1)) S (l + 1) +
a n S n` with `S m = ∑ i < m, Q i`. -/
theorem sum_range_mul_eq_sum_sub_mul (a Q : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, a i * Q i =
      ∑ l ∈ range n, (a l - a (l + 1)) * ∑ i ∈ range (l + 1), Q i +
        a n * ∑ i ∈ range n, Q i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun l => (a l - a (l + 1)) * _),
      sum_range_succ Q n]
    ring

/-- A permutation listing `w` in antitone order. -/
noncomputable def Tuple.antitoneSort {n : ℕ} (w : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (-w)

/-- `w` is antitone along `Tuple.antitoneSort w`. -/
theorem Tuple.antitone_antitoneSort {n : ℕ} (w : Fin n → ℝ) :
    Antitone (w ∘ Tuple.antitoneSort w) := fun i j hij => by
  have h := Tuple.monotone_sort (-w) hij
  simp only [Function.comp_apply, Pi.neg_apply, neg_le_neg_iff] at h
  exact h

/-- **The sorted-sum bound**: if every sum of `m` values of `P` is at most `E m` and `w ≥ 0` is
antitone along `e`, then `∑ j, w j * P j ≤ ∑ m, (a m - a (m + 1)) * E (m + 1)` with
`a m = w (e m)` and `a n = 0`. -/
theorem sum_mul_le_sum_sub_mul_of_antitone {n : ℕ} {w P : Fin n → ℝ} {E : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hP : ∀ T : Finset (Fin n), ∑ j ∈ T, P j ≤ E T.card)
    (e : Equiv.Perm (Fin n)) (he : Antitone (w ∘ e)) :
    ∑ j, w j * P j ≤
      ∑ m ∈ range n, (Fin.extendZero (w ∘ e) m - Fin.extendZero (w ∘ e) (m + 1)) * E (m + 1) := by
  set a := Fin.extendZero (w ∘ e) with ha
  have hsum : ∑ j, w j * P j = ∑ i ∈ range n, a i * Fin.extendZero (P ∘ e) i := by
    rw [← Equiv.sum_comp e, ← Fin.sum_univ_eq_sum_range (fun i => a i * Fin.extendZero (P ∘ e) i)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ha, Fin.extendZero_of_lt _ m.isLt, Fin.extendZero_of_lt _ m.isLt]
    rfl
  rw [hsum, sum_range_mul_eq_sum_sub_mul, show a n = 0 from Fin.extendZero_self _, zero_mul,
    add_zero]
  refine Finset.sum_le_sum fun l hl => ?_
  have hl : l < n := Finset.mem_range.1 hl
  have hd : 0 ≤ a l - a (l + 1) := by
    rw [sub_nonneg, ha, Fin.extendZero_of_lt _ hl]
    by_cases hl1 : l + 1 < n
    · rw [Fin.extendZero_of_lt _ hl1]
      exact he (Fin.mk_le_mk.2 (Nat.le_succ l))
    · rw [show Fin.extendZero (w ∘ e) (l + 1) = 0 by simp [Fin.extendZero, hl1]]
      exact hw _
  refine mul_le_mul_of_nonneg_left ?_ hd
  have hT := hP ((Iic (⟨l, hl⟩ : Fin n)).map e.toEmbedding)
  rw [Finset.sum_map, Finset.card_map, Fin.card_Iic] at hT
  rw [← show ∑ m ∈ Iic (⟨l, hl⟩ : Fin n), (P ∘ e) m = _ from
    Fin.sum_Iic_eq_sum_range_extendZero (P ∘ e) ⟨l, hl⟩]
  exact hT

/-- **The sorted-sum bound at the antitone order of `w`**:
`∑ m < n, (a m − a (m + 1)) · E (m + 1)` with `a` the values of `w` in antitone order and
`a n = 0`. -/
noncomputable def sortedSumBound {n : ℕ} (w : Fin n → ℝ) (E : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range n, (Fin.extendZero (w ∘ Tuple.antitoneSort w) m -
    Fin.extendZero (w ∘ Tuple.antitoneSort w) (m + 1)) * E (m + 1)

/-- **The sorted-sum bound**: for `w ≥ 0` and `P` with every sum of `m` values at most `E m`,
`∑ j, w j · P j ≤ sortedSumBound w E`. -/
theorem sum_mul_le_sortedSumBound {n : ℕ} {w P : Fin n → ℝ} {E : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hP : ∀ T : Finset (Fin n), ∑ j ∈ T, P j ≤ E T.card) :
    ∑ j, w j * P j ≤ sortedSumBound w E :=
  sum_mul_le_sum_sub_mul_of_antitone hw hP _ (Tuple.antitone_antitoneSort w)

/-! ### The sorted-sum bound under a concave table -/

/-- **A concave table**: `E 0 = 0` and the increments `E (m + 1) - E m` are antitone on `0..n`. -/
structure ConcaveTable (E : ℕ → ℝ) (n : ℕ) : Prop where
  zero : E 0 = 0
  sub_anti : ∀ m, m + 1 < n → E (m + 2) - E (m + 1) ≤ E (m + 1) - E m

/-- The increments of a concave table are antitone on the indices below `n`. -/
theorem ConcaveTable.sub_anti_of_le {E : ℕ → ℝ} {n : ℕ} (hE : ConcaveTable E n) {i j : ℕ}
    (hij : i ≤ j) (hj : j < n) : E (j + 1) - E j ≤ E (i + 1) - E i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hE.sub_anti j hj).trans (ih (by omega))

/-- **Abel summation back**: for `a n = 0` and `E 0 = 0`,
`∑ m < n, (a m − a (m + 1)) · E (m + 1) = ∑ m < n, a m · (E (m + 1) − E m)`. -/
theorem sum_range_sub_mul_eq_sum_mul_sub {a E : ℕ → ℝ} {n : ℕ} (ha : a n = 0) (hE : E 0 = 0) :
    ∑ m ∈ range n, (a m - a (m + 1)) * E (m + 1) =
      ∑ m ∈ range n, a m * (E (m + 1) - E m) := by
  have key : ∀ n, ∑ m ∈ range n, (a m - a (m + 1)) * E (m + 1) =
      ∑ m ∈ range n, a m * (E (m + 1) - E m) - a n * E n := fun n => by
    induction n with
    | zero => simp [hE]
    | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring
  rw [key, ha, zero_mul, sub_zero]

/-- **The fill bound**: for `0 ≤ a m ≤ A` and `ε` antitone on the indices below `n`, and `M < n`,
`∑ m < n, a m ε m ≤ A ∑ m < M, ε m + (∑ m < n, a m − A M) ε M`. -/
theorem sum_range_mul_le_fill {a ε : ℕ → ℝ} {A : ℝ} {n M : ℕ}
    (ha0 : ∀ m < n, 0 ≤ a m) (haA : ∀ m < n, a m ≤ A)
    (hε : ∀ i j, i ≤ j → j < n → ε j ≤ ε i) (hM : M < n) :
    ∑ m ∈ range n, a m * ε m ≤
      A * ∑ m ∈ range M, ε m + (∑ m ∈ range n, a m - A * M) * ε M := by
  have hsplit : ∑ m ∈ range n, a m * ε m =
      ∑ m ∈ range n, a m * (ε m - ε M) + (∑ m ∈ range n, a m) * ε M := by
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hlo : ∑ m ∈ range M, a m * (ε m - ε M) ≤ ∑ m ∈ range M, A * (ε m - ε M) :=
    sum_le_sum fun m hm => by
      have hm := mem_range.1 hm
      exact mul_le_mul_of_nonneg_right (haA m (by omega))
        (sub_nonneg.2 (hε m M hm.le hM))
  have hhi : ∑ m ∈ Ico M n, a m * (ε m - ε M) ≤ 0 :=
    sum_nonpos fun m hm => by
      have hm := mem_Ico.1 hm
      exact mul_nonpos_of_nonneg_of_nonpos (ha0 m hm.2)
        (sub_nonpos.2 (hε M m hm.1 hm.2))
  rw [hsplit, ← sum_range_add_sum_Ico _ hM.le]
  have hA : ∑ m ∈ range M, A * (ε m - ε M) = A * ∑ m ∈ range M, ε m - A * M * ε M := by
    rw [← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
  linarith

/-- **The sorted-sum bound under a concave table**: for `0 ≤ w j ≤ A` and every `M < n`,
`sortedSumBound w E ≤ A · E M + (∑ j, w j − A · M) · (E (M + 1) − E M)`. -/
theorem sortedSumBound_le_fill {n : ℕ} {w : Fin n → ℝ} {E : ℕ → ℝ} {A : ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hwA : ∀ j, w j ≤ A) (hE : ConcaveTable E n) {M : ℕ} (hM : M < n) :
    sortedSumBound w E ≤ A * E M + (∑ j, w j - A * M) * (E (M + 1) - E M) := by
  have hsum : ∑ m ∈ range n, Fin.extendZero (w ∘ Tuple.antitoneSort w) m = ∑ j, w j := by
    rw [← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp (Tuple.antitoneSort w) w]
    exact sum_congr rfl fun m _ => Fin.extendZero_of_lt _ m.isLt
  have htel : ∑ m ∈ range M, (E (m + 1) - E m) = E M := by
    rw [sum_range_sub, hE.zero, sub_zero]
  rw [sortedSumBound, sum_range_sub_mul_eq_sum_mul_sub (Fin.extendZero_self _) hE.zero]
  refine (sum_range_mul_le_fill (A := A) (fun m hm => ?_) (fun m hm => ?_)
    (fun i j hij hj => hE.sub_anti_of_le hij hj) hM).trans_eq ?_
  · rw [Fin.extendZero_of_lt _ hm]; exact hw0 _
  · rw [Fin.extendZero_of_lt _ hm]; exact hwA _
  · rw [htel, hsum]

/-! ### The table of a list of increments -/

/-- **Antitone as a check**: every entry of the list is at least the next one. -/
@[expose] def List.antitoneB : List ℕ → Bool
  | a :: b :: t => decide (b ≤ a) && List.antitoneB (b :: t)
  | _ => true

/-- Under the check, the entries read with default `0` are antitone in the index. -/
theorem List.getD_succ_le_of_antitoneB :
    ∀ {l : List ℕ}, l.antitoneB = true → ∀ m, l.getD (m + 1) 0 ≤ l.getD m 0
  | [], _, m => by simp
  | [a], _, m => by cases m <;> simp
  | a :: b :: t, h, m => by
    simp only [List.antitoneB, Bool.and_eq_true, decide_eq_true_eq] at h
    cases m with
    | zero => simpa using h.1
    | succ m => simpa using List.getD_succ_le_of_antitoneB h.2 m

/-- The sum of the first `m + 1` entries is the sum of the first `m` plus entry `m`
(default `0`). -/
theorem List.sum_take_succ_getD :
    ∀ (l : List ℕ) (m : ℕ), (l.take (m + 1)).sum = (l.take m).sum + l.getD m 0
  | [], m => by simp
  | a :: l, 0 => by simp
  | a :: l, m + 1 => by
    simp only [List.take_succ_cons, List.sum_cons, List.getD_cons_succ,
      List.sum_take_succ_getD l m]
    omega

/-- **The table of a list of natural increments**: `E m` is the sum of the first `m` entries. -/
noncomputable def incrementTable (l : List ℕ) (m : ℕ) : ℝ := ((l.take m).sum : ℕ)

/-- The table at `m` is the cast of a natural sum; the kernel evaluates it at a numeral `m`. -/
theorem incrementTable_eq {l : List ℕ} {m s : ℕ} (h : (l.take m).sum = s) :
    incrementTable l m = s := by
  rw [incrementTable, h]

/-- The increment of the table at `m` is entry `m` (default `0`). -/
theorem incrementTable_succ_sub (l : List ℕ) (m : ℕ) :
    incrementTable l (m + 1) - incrementTable l m = l.getD m 0 := by
  rw [incrementTable, incrementTable, List.sum_take_succ_getD, Nat.cast_add, add_sub_cancel_left]

/-- The table is monotone in one step. -/
theorem incrementTable_le_succ (l : List ℕ) (m : ℕ) :
    incrementTable l m ≤ incrementTable l (m + 1) := by
  have := incrementTable_succ_sub l m
  have h0 : (0 : ℝ) ≤ l.getD m 0 := Nat.cast_nonneg _
  linarith

/-- **The table of an antitone list is concave** at every `n`. -/
theorem concaveTable_incrementTable {l : List ℕ} (h : l.antitoneB = true) (n : ℕ) :
    ConcaveTable (incrementTable l) n where
  zero := by simp [incrementTable]
  sub_anti m _ := by
    rw [incrementTable_succ_sub, incrementTable_succ_sub]
    exact_mod_cast List.getD_succ_le_of_antitoneB h m

/-! ### Sums over a threshold -/

/-- **The threshold bound**: if `B ⊆ A` holds the values of `f` at least `t` and the rest of `A`
holds values at most `t`, then every `T ⊆ A` with `|T| = |B|` has `∑_T f ≤ ∑_B f`. -/
theorem Finset.sum_le_sum_of_threshold {ι : Type*} [DecidableEq ι] {A B T : Finset ι}
    {f : ι → ℝ} {t : ℝ} (hT : T ⊆ A) (hB : B ⊆ A) (hc : T.card = B.card)
    (hBt : ∀ i ∈ B, t ≤ f i) (hAt : ∀ i ∈ A, i ∉ B → f i ≤ t) :
    ∑ i ∈ T, f i ≤ ∑ i ∈ B, f i := by
  have h1 : ∑ i ∈ T, f i = ∑ i ∈ T, (f i - t) + T.card * t := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ i ∈ T, (f i - t) ≤ ∑ i ∈ T, max (f i - t) 0 :=
    sum_le_sum fun i _ => le_max_left _ _
  have h3 : ∑ i ∈ T, max (f i - t) 0 ≤ ∑ i ∈ A, max (f i - t) 0 :=
    sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => le_max_right _ _
  have h4 : ∑ i ∈ B, max (f i - t) 0 = ∑ i ∈ A, max (f i - t) 0 :=
    sum_subset hB fun i hiA hiB => max_eq_right (by linarith [hAt i hiA hiB])
  have h5 : ∑ i ∈ B, max (f i - t) 0 = ∑ i ∈ B, (f i - t) :=
    sum_congr rfl fun i hi => max_eq_left (by linarith [hBt i hi])
  have h6 : ∑ i ∈ B, (f i - t) = ∑ i ∈ B, f i - B.card * t := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hc' : (T.card : ℝ) = B.card := by exact_mod_cast hc
  rw [hc'] at h1
  linarith

/-- **Distinct increments of a concave table**: any `k` distinct increments `E (i + 1) − E i`,
`i < n`, sum to at most `E k`. -/
theorem ConcaveTable.sum_sub_le {E : ℕ → ℝ} {n : ℕ} (hE : ConcaveTable E n)
    (T : Finset (Fin n)) : ∑ i ∈ T, (E (i + 1) - E i) ≤ E T.card := by
  set k := T.card with hk
  have hkn : k ≤ n := by simpa using T.card_le_univ
  set B : Finset (Fin n) := univ.filter fun i => (i : ℕ) < k with hBdef
  have hBmap : B.map Fin.valEmbedding = range k := by
    ext m
    simp only [B, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  have hBsum : ∑ i ∈ B, (E (i + 1) - E i) = E k := by
    rw [← show ∑ m ∈ B.map Fin.valEmbedding, (E (m + 1) - E m) = ∑ i ∈ B, (E (i + 1) - E i)
      from Finset.sum_map _ _ _, hBmap, sum_range_sub (fun m => E m) k, hE.zero, sub_zero]
  have hBcard : B.card = k := by rw [← card_map Fin.valEmbedding, hBmap, card_range]
  rw [← hBsum]
  rcases lt_or_eq_of_le hkn with hlt | heq
  · refine sum_le_sum_of_threshold (A := univ) (t := E (k + 1) - E k) (subset_univ _)
      (subset_univ _) hBcard.symm (fun i hi => ?_) (fun i _ hi => ?_)
    · have hi : (i : ℕ) < k := (mem_filter.1 hi).2
      exact hE.sub_anti_of_le hi.le hlt
    · have hi : k ≤ (i : ℕ) := by simpa [B] using hi
      exact hE.sub_anti_of_le hi i.isLt
  · have hT : T = univ := eq_univ_of_card T (by simp [← hk, heq])
    have hB : B = univ := filter_true_of_mem fun i _ => by rw [heq]; exact i.isLt
    rw [hT, hB]

/-- **The sorted-sum bound is monotone in the weights**: for `0 ≤ w ≤ w'` and a concave table
with `E m ≤ E (m + 1)` below `n`, `sortedSumBound w E ≤ sortedSumBound w' E`. -/
theorem sortedSumBound_mono {n : ℕ} {w w' : Fin n → ℝ} {E : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hww : ∀ j, w j ≤ w' j) (hE : ConcaveTable E n) (hinc : ∀ m < n, E m ≤ E (m + 1)) :
    sortedSumBound w E ≤ sortedSumBound w' E := by
  set σ := Tuple.antitoneSort w
  -- the increments of `E` placed in the antitone order of `w`
  set Pw : Fin n → ℝ := fun j => E (σ.symm j + 1) - E (σ.symm j)
  have hP0 : ∀ j, 0 ≤ Pw j := fun j => sub_nonneg.2 (hinc _ (σ.symm j).isLt)
  have hPT : ∀ T : Finset (Fin n), ∑ j ∈ T, Pw j ≤ E T.card := fun T => by
    have h := hE.sum_sub_le (T.map σ.symm.toEmbedding)
    rw [Finset.sum_map, Finset.card_map] at h
    exact h
  have heq : ∑ j, w j * Pw j = sortedSumBound w E := by
    rw [sortedSumBound, sum_range_sub_mul_eq_sum_mul_sub (Fin.extendZero_self _) hE.zero,
      ← Fin.sum_univ_eq_sum_range (fun m => Fin.extendZero (w ∘ σ) m * (E (m + 1) - E m)),
      ← Equiv.sum_comp σ (fun j => w j * Pw j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.extendZero_of_lt _ i.isLt]
    simp [Pw]
  rw [← heq]
  calc ∑ j, w j * Pw j ≤ ∑ j, w' j * Pw j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hww j) (hP0 j)
    _ ≤ sortedSumBound w' E := sum_mul_le_sortedSumBound (fun j => (hw j).trans (hww j)) hPT

/-- **The sorted-sum bound from a sorted list of the weights**: for `L` antitone and a
permutation of the values of `w`, and `E 0 = 0`,
`sortedSumBound w E = ∑ m < n, L m · (E (m + 1) − E m)`. -/
theorem sortedSumBound_eq_of_perm {n : ℕ} {w : Fin n → ℝ} {E : ℕ → ℝ} {L : List ℝ}
    (hL : L.Pairwise (· ≥ ·)) (hp : L.Perm (List.ofFn w)) (hE0 : E 0 = 0) :
    sortedSumBound w E = ∑ m ∈ range n, L.getD m 0 * (E (m + 1) - E m) := by
  have hs : (List.ofFn (w ∘ Tuple.antitoneSort w)).Pairwise (· ≥ ·) :=
    List.pairwise_ofFn.2 fun i j hij => Tuple.antitone_antitoneSort w hij.le
  have heq : List.ofFn (w ∘ Tuple.antitoneSort w) = L :=
    List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hba hab) hs hL
      (((Tuple.antitoneSort w).ofFn_comp_perm w).trans hp.symm)
  rw [sortedSumBound, sum_range_sub_mul_eq_sum_mul_sub (Fin.extendZero_self _) hE0]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm := Finset.mem_range.1 hm
  rw [Fin.extendZero_of_lt _ hm, ← heq]
  simp [List.getD_eq_getElem?_getD, hm]

/-! ### Computable forms -/

/-- A list of naturals sorted in antitone order. -/
def List.sortDesc (u : List ℕ) : List ℕ := u.mergeSort fun a b => decide (b ≤ a)

/-- The sorted list is a permutation of the list. -/
theorem List.sortDesc_perm (u : List ℕ) : u.sortDesc.Perm u := List.mergeSort_perm _ _

/-- The sorted list is antitone. -/
theorem List.pairwise_sortDesc (u : List ℕ) : u.sortDesc.Pairwise (· ≥ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : ℕ => decide (b ≤ a))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simpa using Nat.le_total b a) u
  exact h.imp fun h => by simpa using h

/-- Above a threshold `t`, `∑ (x − t) + |M| t = ∑ x`. -/
theorem List.sum_map_sub_add_length_mul {t : ℕ} :
    ∀ {M : List ℕ}, (∀ x ∈ M, t ≤ x) → (M.map (· - t)).sum + M.length * t = M.sum
  | [], _ => by simp
  | x :: M, h => by
    have ih := List.sum_map_sub_add_length_mul (M := M) fun y hy => h y (by simp [hy])
    have hx := h x (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    generalize M.length * t = c at ih ⊢
    omega

/-- Below a threshold `t`, `∑ (x − t) = 0`. -/
theorem List.sum_map_sub_eq_zero {t : ℕ} :
    ∀ {M : List ℕ}, (∀ x ∈ M, x ≤ t) → (M.map (· - t)).sum = 0
  | [], _ => rfl
  | x :: M, h => by
    simp only [List.map_cons, List.sum_cons, Nat.sub_eq_zero_of_le (h x (by simp)),
      List.sum_map_sub_eq_zero (M := M) fun y hy => h y (by simp [hy])]

/-- **The sorted-list bound**: the sum of `u` over any set `T` of positions is at most the sum of
the first `|T|` entries of the sorted list. -/
theorem Finset.sum_le_sum_take_sortDesc {n : ℕ} (u : Fin n → ℕ) (T : Finset (Fin n)) :
    ∑ j ∈ T, u j ≤ (((List.ofFn u).sortDesc).take T.card).sum := by
  set L := (List.ofFn u).sortDesc
  set k := T.card
  set t := (L.drop k).headD 0
  have hp : L.Perm (List.ofFn u) := List.sortDesc_perm _
  have hs : L.Pairwise (· ≥ ·) := List.pairwise_sortDesc _
  have hsplit := hs
  rw [← List.take_append_drop k L, List.pairwise_append] at hsplit
  obtain ⟨-, hdrop, hcross⟩ := hsplit
  have htake : ∀ x ∈ L.take k, t ≤ x := by
    intro x hx
    cases hd : L.drop k with
    | nil => simp [t, hd]
    | cons y ys =>
      have ht : t = y := by simp [t, hd]
      rw [ht]
      exact hcross x hx y (by simp [hd])
  have hdrop' : ∀ y ∈ L.drop k, y ≤ t := by
    cases hd : L.drop k with
    | nil => simp
    | cons y ys =>
      intro z hz
      have ht : t = y := by simp [t, hd]
      rw [hd] at hdrop
      rw [ht]
      rcases List.mem_cons.1 hz with rfl | hz
      · exact le_rfl
      · exact (List.pairwise_cons.1 hdrop).1 z hz
  have hlen : (L.take k).length = k := by
    rw [List.length_take, hp.length_eq, List.length_ofFn]
    exact min_eq_left (by simpa using T.card_le_univ)
  have hfin := List.sum_map_sub_add_length_mul htake
  rw [hlen] at hfin
  calc ∑ j ∈ T, u j ≤ ∑ j ∈ T, ((u j - t) + t) := Finset.sum_le_sum fun j _ => by omega
    _ = ∑ j ∈ T, (u j - t) + k * t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ j, (u j - t) + k * t :=
        Nat.add_le_add_right (Finset.sum_le_sum_of_subset (Finset.subset_univ T)) _
    _ = ((List.ofFn u).map (· - t)).sum + k * t := by rw [List.map_ofFn, List.sum_ofFn]; rfl
    _ = (L.map (· - t)).sum + k * t := by rw [(hp.map _).sum_eq]
    _ = (L.take k).sum := by
        conv_lhs => rw [← List.take_append_drop k L]
        rw [List.map_append, List.sum_append, List.sum_map_sub_eq_zero hdrop', add_zero]
        exact hfin

/-- **The envelope check**: for every `m ≤ |u|`, the sum of the `m` largest entries of `u` is at
most `s` times the sum of the first `m` entries of `l`. -/
def envelopeCheck (l : List ℕ) (s : ℕ) (u : List ℕ) : Bool :=
  (List.range (u.length + 1)).all fun m => decide ((u.sortDesc.take m).sum ≤ s * (l.take m).sum)

/-- **The envelope check is sound**: if `P j ≤ u j / s` and the check holds, every sum of `m`
values of `P` is at most `incrementTable l m`. -/
theorem sum_le_incrementTable_of_envelopeCheck {n s : ℕ} {l : List ℕ} {u : Fin n → ℕ}
    (hc : envelopeCheck l s (List.ofFn u) = true) {P : Fin n → ℝ}
    (hP : ∀ j, P j ≤ u j / s) (T : Finset (Fin n)) :
    ∑ j ∈ T, P j ≤ incrementTable l T.card := by
  have hE0 : (0 : ℝ) ≤ incrementTable l T.card := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine (Finset.sum_le_sum fun j _ => hP j).trans ?_
    simpa using hE0
  have hm : ((List.ofFn u).sortDesc.take T.card).sum ≤ s * (l.take T.card).sum := by
    have h := List.all_eq_true.1 hc T.card
      (List.mem_range.2 (by simpa using Nat.lt_succ_of_le T.card_le_univ))
    simpa using h
  have hT := Finset.sum_le_sum_take_sortDesc u T
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : ((∑ j ∈ T, u j : ℕ) : ℝ) ≤ s * ((l.take T.card).sum : ℕ) := by
    exact_mod_cast hT.trans hm
  calc ∑ j ∈ T, P j ≤ ∑ j ∈ T, (u j : ℝ) / s := Finset.sum_le_sum fun j _ => hP j
    _ = ((∑ j ∈ T, u j : ℕ) : ℝ) / s := by
        rw [Nat.cast_sum]; simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ incrementTable l T.card := by
        rw [div_le_iff₀ hs', incrementTable]
        linarith

/-- **The sorted dot product**: the entries of `u` in antitone order against the entries of
`l`, `∑ m, u↓ m · l m`. -/
def sortedDot (l u : List ℕ) : ℕ := (List.zipWith (· * ·) u.sortDesc l).sum

/-- The sum of an entrywise product, as a sum over the positions of the first list. -/
theorem List.sum_zipWith_mul_eq :
    ∀ (L l : List ℕ), (List.zipWith (· * ·) L l).sum =
      ∑ m ∈ Finset.range L.length, L.getD m 0 * l.getD m 0
  | [], l => by simp
  | a :: L, [] => by simp
  | a :: L, b :: l => by
    rw [List.zipWith_cons_cons, List.sum_cons, List.sum_zipWith_mul_eq L l, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

/-- Reading a mapped list with default `0` maps the entry, for a map fixing `0`. -/
theorem List.getD_map_of_zero {α β : Type*} [Zero α] [Zero β] {g : α → β} (hg : g 0 = 0)
    (L : List α) (m : ℕ) : (L.map g).getD m 0 = g (L.getD m 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[m]? <;> simp [hg]

/-- **The sorted dot product is sound**: if `0 ≤ w j ≤ u j / s` and `l` passes the antitone
check, `s · sortedSumBound w (incrementTable l) ≤ sortedDot l u`. -/
theorem mul_sortedSumBound_le_sortedDot {n s : ℕ} {l : List ℕ} (hl : l.antitoneB = true)
    {u : Fin n → ℕ} {w : Fin n → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hwu : ∀ j, w j ≤ u j / s) :
    s * sortedSumBound w (incrementTable l) ≤ sortedDot l (List.ofFn u) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set L := (List.ofFn u).sortDesc
  have hmono := sortedSumBound_mono hw0 hwu (concaveTable_incrementTable hl n)
    (fun m _ => incrementTable_le_succ l m)
  have hL : (L.map fun x : ℕ => (x : ℝ) / s).Pairwise (· ≥ ·) :=
    List.pairwise_map.2 ((List.pairwise_sortDesc _).imp fun h =>
      div_le_div_of_nonneg_right (by exact_mod_cast h) hs'.le)
  have hp : (L.map fun x : ℕ => (x : ℝ) / s).Perm (List.ofFn fun j => (u j : ℝ) / s) := by
    rw [show (List.ofFn fun j => (u j : ℝ) / s) = (List.ofFn u).map fun x : ℕ => (x : ℝ) / s by
      rw [List.map_ofFn]; rfl]
    exact (List.sortDesc_perm _).map _
  rw [sortedSumBound_eq_of_perm hL hp (by simp [incrementTable])] at hmono
  have hlen : L.length = n := by rw [(List.sortDesc_perm _).length_eq, List.length_ofFn]
  rw [sortedDot, List.sum_zipWith_mul_eq, hlen]
  push_cast
  refine (mul_le_mul_of_nonneg_left hmono hs'.le).trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [incrementTable_succ_sub, List.getD_map_of_zero (g := fun x : ℕ => (x : ℝ) / s) (by simp)]
  field_simp
  ring
