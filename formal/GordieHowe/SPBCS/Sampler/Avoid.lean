-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.ChallengeReader

@[expose] public section

/-!
# Rejection sampling of a challenge off a public set

The C++ loop `do { a = elt(); } while (a in U)` draws a challenge outside a public finite set `U`:
each attempt is a whole draw of the field `sample` (`RandomEngine`, `third_party/longfellow/lib/random/random.h`), and
the loop repeats the draw while its value lies in `U`.

`Reader.retry R g t` is that loop at attempt bound `t` for a general reader `R` and a partial map
`g` (the value is kept when `g` is defined on it). For a uniform `R` whose map `g` has fibres of
equal size, the result is uniform (`Reader.Uniform.retry`). Its Chernoff data come from the
weighting of a uniform reader: `R` returns each of its `|α|` values with the same weight, so the
generating function of `R.bind k` is that of `R` times the average of the continuations'
(`Reader.Uniform.pgf_bind_mul_card`, `Reader.Uniform.pfail_bind_mul_card`). Hence `pgf_retry_le` (a geometric
number of attempts, each dominated by the inner generating function) and `pfail_retry_le`.

`CReader.avoid r U` is the loop with `elt` the challenge reader `r`, uniform on the complement of
`U` on success, when `U` is a small enough fraction of the challenge space.
-/

namespace GordieHowe.SPBCS

/-- A fact about a Mathlib object (powers in an ordered field), kept here until upstreamed:
`x ^ (n + 1) - 1 ≤ (n + 1) · x ^ n · (x - 1)` for `x ≥ 1`. -/
theorem pow_succ_sub_one_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    x ^ (n + 1) - 1 ≤ (n + 1) * x ^ n * (x - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ x ^ n := one_le_pow₀ hx
    have h2 : x ^ n ≤ x ^ (n + 1) := pow_le_pow_right₀ hx (Nat.le_succ n)
    have e1 : x ^ (n + 1 + 1) - 1 = x * (x ^ (n + 1) - 1) + (x - 1) := by ring
    rw [e1]
    push_cast
    have hx1 : 0 ≤ x - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ x),
      mul_le_mul_of_nonneg_right h2 hx1, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ n + 1)
        (by linarith : (0 : ℝ) ≤ x ^ (n + 1) - x ^ n)) hx1]

namespace Reader

variable {α β : Type}

/-! ### The weighted generating function -/

/-- **The weighted generating function** at `z` with weight `v`: over a uniform unbounded byte
stream, the expected value of `z ^ (bytes read) · v (value returned)` on the runs that return. -/
noncomputable def wpgf (z : ℝ) (v : α → ℝ) : Reader α → ℝ
  | done a => v a
  | fail => 0
  | read f => z / 256 * ∑ x, wpgf z v (f x)

/-- The generating function is the weighted one at the constant weight `1`. -/
theorem pgf_eq_wpgf (z : ℝ) : ∀ R : Reader α, R.pgf z = R.wpgf z (fun _ => 1)
  | done _ => rfl
  | fail => rfl
  | read f => by simp only [pgf, wpgf, pgf_eq_wpgf z (f _)]

/-- Sequencing: the generating function of `R.bind k` weights `R`'s values by the continuations'
generating functions. -/
theorem pgf_bind (z : ℝ) (k : α → Reader β) : ∀ R : Reader α,
    (R.bind k).pgf z = R.wpgf z (fun a => (k a).pgf z)
  | done _ => rfl
  | fail => rfl
  | read f => by simp only [bind, pgf, wpgf, pgf_bind z k (f _)]

/-- Sequencing: `R.bind k` fails when `R` fails, or when the continuation fails, weighted by
`R`'s values at `z = 1`. -/
theorem pfail_bind (k : α → Reader β) : ∀ R : Reader α,
    (R.bind k).pfail = R.pfail + R.wpgf 1 (fun a => (k a).pfail)
  | done _ => by simp [bind, pfail, wpgf]
  | fail => by simp [bind, pfail, wpgf]
  | read f => by
    simp only [bind, pfail, wpgf, pfail_bind k (f _), Finset.sum_add_distrib]
    ring

/-- At `z = 1` returning and failing have total probability one. -/
theorem pgf_one_add_pfail : ∀ R : Reader α, R.pgf 1 + R.pfail = 1
  | done _ => by simp [pgf, pfail]
  | fail => by simp [pgf, pfail]
  | read f => by
    simp only [pgf, pfail]
    have h : ∑ x, ((f x).pgf 1 + (f x).pfail) = 256 := by
      simp [pgf_one_add_pfail (f _)]
    rw [Finset.sum_add_distrib] at h
    linarith

theorem pfail_le_one (R : Reader α) : R.pfail ≤ 1 := by
  have := pgf_one_add_pfail R
  have := pgf_nonneg (zero_le_one) R
  linarith

/-- The weighted generating function is linear in the weight: scaling. -/
theorem wpgf_mul (z c : ℝ) (v : α → ℝ) : ∀ R : Reader α,
    R.wpgf z (fun a => c * v a) = c * R.wpgf z v
  | done _ => rfl
  | fail => by simp [wpgf]
  | read f => by
    simp only [wpgf, wpgf_mul z c v (f _), ← Finset.mul_sum]
    ring

/-- The weighted generating function is linear in the weight: sums. -/
theorem wpgf_add (z : ℝ) (v w : α → ℝ) : ∀ R : Reader α,
    R.wpgf z (fun a => v a + w a) = R.wpgf z v + R.wpgf z w
  | done _ => rfl
  | fail => by simp [wpgf]
  | read f => by
    simp only [wpgf, wpgf_add z v w (f _), Finset.sum_add_distrib]
    ring

/-- The weighted generating function is monotone in a nonnegative weight at `z ≥ 0`. -/
theorem wpgf_mono {z : ℝ} (hz : 0 ≤ z) {v w : α → ℝ} (h : ∀ a, v a ≤ w a) : ∀ R : Reader α,
    R.wpgf z v ≤ R.wpgf z w
  | done a => h a
  | fail => le_rfl
  | read f => by
    simp only [wpgf]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => wpgf_mono hz h (f x))
      (by positivity)

/-- The depth of the tree: the most bytes a run reads. -/
def depth : Reader α → ℕ
  | done _ => 0
  | fail => 0
  | read f => (Finset.univ.sup fun x => depth (f x)) + 1

section ExactFormula

variable [Fintype α] [DecidableEq α]

/-- **The weighted generating function through `exact`**: for `D` at least the depth, the sum over
the bytes read `j ≤ D` and the values `a` of `exact R j a · (z/256)^j · v a`. -/
theorem wpgf_eq_sum_exact (z : ℝ) (v : α → ℝ) :
    ∀ (R : Reader α) (D : ℕ), R.depth ≤ D →
      R.wpgf z v = ∑ j ∈ Finset.range (D + 1), (z / 256) ^ j * ∑ a, (R.exact j a : ℝ) * v a
  | done a', D, _ => by
    rw [Finset.sum_range_succ']
    simp only [exact, wpgf, pow_zero, one_mul]
    rw [Finset.sum_eq_zero fun j _ => by simp]
    simp [Finset.sum_ite_eq]
  | fail, D, _ => by simp [wpgf, exact]
  | read f, D, hD => by
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by simp [depth] at hD; omega⟩
    have hf : ∀ x, (f x).depth ≤ D := fun x =>
      (Finset.le_sup (f := fun x => depth (f x)) (Finset.mem_univ x)).trans
        (by simp only [depth] at hD; omega)
    rw [Finset.sum_range_succ']
    simp only [wpgf, exact, Nat.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
      wpgf_eq_sum_exact z v (f _) D (hf _), Finset.mul_sum, Nat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
    ring

/-- A reader of an empty type never returns. -/
theorem wpgf_of_isEmpty [IsEmpty α] (z : ℝ) (v : α → ℝ) (R : Reader α) : R.wpgf z v = 0 := by
  rw [wpgf_eq_sum_exact z v R _ le_rfl]
  simp

/-- **The weighting of a uniform reader**: each of the `|α|` values carries the same weight, so the
weighted generating function is the generating function times the average weight. -/
theorem Uniform.wpgf_mul_card {R : Reader α} (hR : R.Uniform) (z : ℝ) (v : α → ℝ) :
    R.wpgf z v * Fintype.card α = R.pgf z * ∑ a, v a := by
  rw [pgf_eq_wpgf, wpgf_eq_sum_exact z v R _ le_rfl, wpgf_eq_sum_exact z _ R _ le_rfl,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, mul_assoc]
  congr 1
  have hc : (Fintype.card α : ℝ) = ∑ _b : α, (1 : ℝ) := by simp
  rw [hc, Finset.sum_mul, Finset.sum_mul]
  simp only [mul_one, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hR j a b]

/-- **Sequencing after a uniform reader**: the generating function is that of `R` times the
average of the continuations'. -/
theorem Uniform.pgf_bind_mul_card {R : Reader α} (hR : R.Uniform) (k : α → Reader β) (z : ℝ) :
    (R.bind k).pgf z * Fintype.card α = R.pgf z * ∑ a, (k a).pgf z := by
  rw [pgf_bind, hR.wpgf_mul_card]

/-- **Sequencing after a uniform reader**: beyond `R`'s own failure, the reader fails when a
continuation does, each value returned with probability `(1 - R.pfail) / |α|`. -/
theorem Uniform.pfail_bind_mul_card {R : Reader α} (hR : R.Uniform) (k : α → Reader β) :
    ((R.bind k).pfail - R.pfail) * Fintype.card α = (1 - R.pfail) * ∑ a, (k a).pfail := by
  have h := pgf_one_add_pfail R
  rw [pfail_bind, add_sub_cancel_left, hR.wpgf_mul_card, show 1 - R.pfail = R.pgf 1 by linarith]

end ExactFormula

/-! ### Retrying a draw -/

/-- At most `t` attempts: run `R`, return `g` of its value when defined, else try again. -/
def retry (R : Reader α) (g : α → Option β) : ℕ → Reader β
  | 0 => fail
  | t + 1 => R.bind fun a => (g a).elim (retry R g t) done

section RetryExact

variable [Fintype α] [DecidableEq β]

/-- The `exact` counts of one attempt's continuation, summed over the attempt's values: the
rejected values continue with `X`, the others return. -/
theorem sum_exact_elim_fintype (g : α → Option β) (X : Reader β) (m : ℕ) (c : β) :
    ∑ a, ((g a).elim X done).exact m c =
      (Finset.univ.filter fun a => g a = none).card * X.exact m c +
        if m = 0 then (Finset.univ.filter fun a => g a = some c).card else 0 := by
  have hpt : ∀ a, ((g a).elim X done).exact m c =
      (if g a = none then X.exact m c else 0) +
        if m = 0 then (if g a = some c then 1 else 0) else 0 := by
    intro a
    cases g a with
    | none => simp
    | some a' => cases m <;> simp [exact]
  simp only [hpt, Finset.sum_add_distrib, Finset.card_filter, Finset.sum_mul, ite_mul,
    one_mul, zero_mul]
  split_ifs <;> simp

variable [DecidableEq α]

theorem Uniform.retry {R : Reader α} (hR : R.Uniform) {g : α → Option β}
    (hg : ∀ b b', (Finset.univ.filter fun a => g a = some b).card =
      (Finset.univ.filter fun a => g a = some b').card) (t : ℕ) : (R.retry g t).Uniform := by
  induction t with
  | zero => intro j a a'; simp [Reader.retry, exact]
  | succ t ih =>
    intro j c c'
    rw [Reader.retry, exact_bind, exact_bind]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hα : Nonempty α
    · obtain ⟨a₀⟩ := hα
      simp only [hR i _ a₀, ← Finset.mul_sum, sum_exact_elim_fintype, ih (j - i) c c', hg c c']
    · rw [not_nonempty_iff] at hα
      simp

end RetryExact

section RetryBounds

variable [Fintype α]

/-- The generating functions of one attempt's continuations, summed over the attempt's values:
the rejected values continue with `X`, the others return. -/
theorem sum_pgf_elim (g : α → Option β) (X : Reader β) (z : ℝ) :
    ∑ a, ((g a).elim X done).pgf z =
      (Finset.univ.filter fun a => g a = none).card * X.pgf z +
        (Fintype.card α - (Finset.univ.filter fun a => g a = none).card) := by
  have h1 : ∑ a, ((g a).elim X done).pgf z = ∑ a, (if g a = none then X.pgf z else 1) :=
    Finset.sum_congr rfl fun a _ => by cases g a <;> simp [pgf]
  rw [h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : α => g a = none)
  rw [Finset.card_univ] at htot
  have : ((Finset.univ.filter fun a => ¬ g a = none).card : ℝ) =
      Fintype.card α - (Finset.univ.filter fun a => g a = none).card := by
    rw [← htot]; push_cast; ring
  rw [this]

/-- The failure probabilities of one attempt's continuations, summed over the attempt's values. -/
theorem sum_pfail_elim (g : α → Option β) (X : Reader β) :
    ∑ a, ((g a).elim X done).pfail = (Finset.univ.filter fun a => g a = none).card * X.pfail := by
  rw [show ∑ a, ((g a).elim X done).pfail = ∑ a, (if g a = none then X.pfail else 0) from
      Finset.sum_congr rfl fun a _ => by cases g a <;> simp [pfail],
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]

variable [DecidableEq α]

/-- **The generating function of retrying a uniform draw**: if `R`'s generating function is at most
`H ≥ 1` and the rejected values are at most a fraction `ρ` of `R`'s values with `ρ H < 1`, then the
retried reader's is at most `(1 - ρ) H / (1 - ρ H)`, which solves `Y = H (1 + ρ (Y - 1))`. -/
theorem pgf_retry_le {R : Reader α} (hR : R.Uniform) (g : α → Option β) {z : ℝ} (hz : 1 ≤ z)
    {H ρ : ℝ} (hG : R.pgf z ≤ H) (hH : 1 ≤ H)
    (hρ : ((Finset.univ.filter fun a => g a = none).card : ℝ) ≤ ρ * Fintype.card α)
    (hρH : ρ * H < 1) (t : ℕ) : (R.retry g t).pgf z ≤ (1 - ρ) * H / (1 - ρ * H) := by
  set Y := (1 - ρ) * H / (1 - ρ * H) with hYdef
  have hpos : 0 < 1 - ρ * H := by linarith
  have hY : Y * (1 - ρ * H) = (1 - ρ) * H := div_mul_cancel₀ _ hpos.ne'
  have hY1 : 1 ≤ Y := by
    rw [hYdef, le_div_iff₀ hpos]; nlinarith
  induction t with
  | zero => simp only [retry, pgf]; linarith
  | succ t ih =>
    set n : ℝ := (Fintype.card α : ℝ)
    set N0 : ℝ := ((Finset.univ.filter fun a => g a = none).card : ℝ)
    rcases (Nat.eq_zero_or_pos (Fintype.card α)) with hn | hn
    · have : IsEmpty α := Fintype.card_eq_zero_iff.1 hn
      rw [retry, pgf_bind, wpgf_of_isEmpty]
      linarith
    have hn' : (0 : ℝ) < n := by simp only [n]; exact_mod_cast hn
    have hX0 : 0 ≤ (R.retry g t).pgf z := pgf_nonneg (by linarith) _
    have hN0 : 0 ≤ N0 := Nat.cast_nonneg _
    have hρ0 : 0 ≤ ρ := by
      by_contra h
      push Not at h
      have : ρ * n < 0 := mul_neg_of_neg_of_pos h hn'
      linarith
    have hG0 : 0 ≤ R.pgf z := pgf_nonneg (by linarith) _
    have hmul := hR.pgf_bind_mul_card (fun a => (g a).elim (R.retry g t) done) z
    rw [sum_pgf_elim] at hmul
    rw [retry, ← mul_le_mul_iff_of_pos_right hn', hmul]
    have e : Y * n = H * (n + ρ * n * (Y - 1)) := by
      have : Y = H * (1 + ρ * (Y - 1)) := by nlinarith
      linear_combination n * this
    rw [e]
    calc R.pgf z * (N0 * (R.retry g t).pgf z + (n - N0))
        = R.pgf z * (n + N0 * ((R.retry g t).pgf z - 1)) := by ring
      _ ≤ R.pgf z * (n + N0 * (Y - 1)) := by gcongr
      _ ≤ R.pgf z * (n + ρ * n * (Y - 1)) := by
          gcongr
      _ ≤ H * (n + ρ * n * (Y - 1)) := by
          gcongr

/-- **The failure probability of retrying a uniform draw**: if `R` fails with probability at most
`ε` and the rejected values are at most a fraction `ρ < 1` of `R`'s values, then `t` attempts fail
with probability at most `ε / (1 - ρ) + ρ ^ t` (from `P_(t+1) ≤ R.pfail + ρ P_t`). -/
theorem pfail_retry_le {R : Reader α} (hR : R.Uniform) (g : α → Option β) {ε ρ : ℝ}
    (hε : R.pfail ≤ ε)
    (hρ : ((Finset.univ.filter fun a => g a = none).card : ℝ) ≤ ρ * Fintype.card α)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (t : ℕ) : (R.retry g t).pfail ≤ ε / (1 - ρ) + ρ ^ t := by
  have hε0 : 0 ≤ ε := (pfail_nonneg R).trans hε
  have hpos : 0 < 1 - ρ := by linarith
  have hq : ε / (1 - ρ) * (1 - ρ) = ε := div_mul_cancel₀ _ hpos.ne'
  have hq0 : 0 ≤ ε / (1 - ρ) := div_nonneg hε0 hpos.le
  induction t with
  | zero => simp only [retry, pfail, pow_zero]; linarith
  | succ t ih =>
    have hρt : 0 ≤ ρ ^ (t + 1) := pow_nonneg hρ0 _
    rcases (Nat.eq_zero_or_pos (Fintype.card α)) with hn | hn
    · have : IsEmpty α := Fintype.card_eq_zero_iff.1 hn
      rw [retry, pfail_bind, wpgf_of_isEmpty]
      nlinarith
    have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
    have hmul := hR.pfail_bind_mul_card (fun a => (g a).elim (R.retry g t) done)
    rw [sum_pfail_elim] at hmul
    have hP0 : 0 ≤ (R.retry g t).pfail := pfail_nonneg _
    have hp1 : 0 ≤ 1 - R.pfail := by linarith [pfail_le_one R]
    have hp0 := pfail_nonneg R
    rw [retry]
    set P' := (R.bind fun a => (g a).elim (R.retry g t) done).pfail
    set P := (R.retry g t).pfail
    set n : ℝ := (Fintype.card α : ℝ)
    set N0 : ℝ := ((Finset.univ.filter fun a => g a = none).card : ℝ)
    -- `P' n = p n + (1 - p) N0 P ≤ ε n + ρ n P`
    have hstep : P' * n ≤ (ε + ρ * P) * n := by
      have h1 : (1 - R.pfail) * (N0 * P) ≤ N0 * P :=
        mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hP0) (by linarith)
      have h2 : N0 * P ≤ ρ * n * P := mul_le_mul_of_nonneg_right hρ hP0
      nlinarith
    have hP' : P' ≤ ε + ρ * P := le_of_mul_le_mul_right hstep hn'
    calc P' ≤ ε + ρ * (ε / (1 - ρ) + ρ ^ t) := hP'.trans (by gcongr)
      _ = ε / (1 - ρ) + ρ ^ (t + 1) := by
          rw [pow_succ]
          nlinarith

end RetryBounds

/-! ### Unranking the retried draw -/

/-- **A computable listing of a finite set**: a list without duplicates whose members are the
elements of the set. -/
structure _root_.Finset.Listing {γ : Type} (U : Finset γ) where
  /-- The list. -/
  list : List γ
  nodup : list.Nodup
  mem_iff : ∀ x, x ∈ list ↔ x ∈ U

/-- **The data of an unranking of `retry R g`**: a list of the values `g` rejects, and for every
kept value `c` the `nAcc` values that `g` sends to `c`. -/
structure RetryData [Fintype α] (g : α → Option β) where
  /-- The rejected values. -/
  rejList : List α
  rejList_nodup : rejList.Nodup
  mem_rejList : ∀ a, a ∈ rejList ↔ g a = none
  /-- The number of values kept as each value. -/
  nAcc : ℕ
  /-- The `i`-th value kept as `c`. -/
  accVal : β → ℕ → α
  acc_some : ∀ c i, i < nAcc → g (accVal c i) = some c
  acc_inj : ∀ c i i', i < nAcc → i' < nAcc → accVal c i = accVal c i' → i = i'
  card_acc : ∀ [DecidableEq β] c, (Finset.univ.filter fun a => g a = some c).card = nAcc

namespace Unrank

variable [Fintype α] {R : Reader α} (U : R.Unrank) {g : α → Option β} (D : RetryData g)

/-- The number of exact paths of length `j` of `retry R g t`. -/
def retryCnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, j => ((List.range (j + 1)).map fun i =>
      D.rejList.length * U.cnt i * retryCnt t (j - i)).sum + D.nAcc * U.cnt j

/-- The block sizes of `retryCnt (t + 1) j`: the first draw reads `i` bytes and is rejected. -/
def retryBlock (t j i : ℕ) : ℕ := D.rejList.length * U.cnt i * retryCnt U D t (j - i)

theorem retryCnt_succ (t j : ℕ) : retryCnt U D (t + 1) j =
    ((List.range (j + 1)).map (retryBlock U D t j)).sum + D.nAcc * U.cnt j := rfl

/-- The `idx`-th exact path of length `j` of `retry R g t` returning `c`: a rejected draw and a
path of `retry R g (t - 1)`, or a kept draw. -/
def retryPath : ℕ → ℕ → β → ℕ → List QROM.Byte
  | 0, _, _, _ => []
  | t + 1, j, c, idx =>
    if idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum then
      let p := pick (retryBlock U D t j) (List.range (j + 1)) idx
      let r1 := p.2 / retryCnt U D t (j - p.1)
      U.path p.1 (D.rejList.getD (r1 % D.rejList.length) (D.accVal c 0)) (r1 / D.rejList.length) ++
        retryPath t (j - p.1) c (p.2 % retryCnt U D t (j - p.1))
    else
      U.path j (D.accVal c ((idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j))
        ((idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum) % U.cnt j)

/-- The bounds of the rejected branch. -/
theorem retry_rej_spec {t j idx : ℕ}
    (h : idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum) :
    let p := pick (retryBlock U D t j) (List.range (j + 1)) idx
    let K := retryCnt U D t (j - p.1)
    p.1 ≤ j ∧ (p.2 / K) % D.rejList.length < D.rejList.length ∧
      (p.2 / K) / D.rejList.length < U.cnt p.1 ∧ p.2 % K < K := by
  intro p K
  obtain ⟨h1, h2⟩ := pick_mem _ _ idx h
  simp only [retryBlock] at h2
  have hK : 0 < K := Nat.pos_of_ne_zero fun h0 => by
    simp only [K] at h0
    rw [h0, mul_zero] at h2; omega
  have hr1 : p.2 / K < D.rejList.length * U.cnt p.1 :=
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
  have hn : 0 < D.rejList.length := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hr1
    exact Nat.not_lt_zero _ hr1
  exact ⟨Nat.lt_succ_iff.1 (List.mem_range.1 h1), Nat.mod_lt _ hn, Nat.div_lt_of_lt_mul hr1,
    Nat.mod_lt _ hK⟩

/-- The bounds of the kept branch. -/
theorem retry_acc_spec {t j idx : ℕ} (h : idx < retryCnt U D (t + 1) j)
    (hi : ¬ idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum) :
    let r := idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum
    r / U.cnt j < D.nAcc ∧ r % U.cnt j < U.cnt j := by
  intro r
  rw [retryCnt_succ] at h
  have hr : r < D.nAcc * U.cnt j := by simp only [r]; omega
  have hpos : 0 < U.cnt j := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hr; omega
  exact ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hr), Nat.mod_lt _ hpos⟩

theorem retryPath_rej {t j idx : ℕ} {c : β}
    (h : idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum) :
    retryPath U D (t + 1) j c idx =
      U.path (pick (retryBlock U D t j) (List.range (j + 1)) idx).1
        (D.rejList.getD (((pick (retryBlock U D t j) (List.range (j + 1)) idx).2 /
          retryCnt U D t (j - (pick (retryBlock U D t j) (List.range (j + 1)) idx).1)) %
            D.rejList.length) (D.accVal c 0))
        (((pick (retryBlock U D t j) (List.range (j + 1)) idx).2 /
          retryCnt U D t (j - (pick (retryBlock U D t j) (List.range (j + 1)) idx).1)) /
            D.rejList.length) ++
      retryPath U D t (j - (pick (retryBlock U D t j) (List.range (j + 1)) idx).1) c
        ((pick (retryBlock U D t j) (List.range (j + 1)) idx).2 %
          retryCnt U D t (j - (pick (retryBlock U D t j) (List.range (j + 1)) idx).1)) := by
  simp only [retryPath, if_pos h]

theorem getD_mem_rejList {k : ℕ} (hk : k < D.rejList.length) (d : α) :
    g (D.rejList.getD k d) = none := by
  rw [List.getD_eq_getElem _ _ hk]
  exact (D.mem_rejList _).1 (List.getElem_mem hk)

theorem getD_rejList_inj {k k' : ℕ} (hk : k < D.rejList.length) (hk' : k' < D.rejList.length)
    (d d' : α) (h : D.rejList.getD k d = D.rejList.getD k' d') : k = k' := by
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at h
  exact (List.Nodup.getElem_inj_iff D.rejList_nodup).1 h

theorem retryPath_acc {t j idx : ℕ} {c : β}
    (hi : ¬ idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum) :
    retryPath U D (t + 1) j c idx =
      U.path j (D.accVal c ((idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j))
        ((idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum) % U.cnt j) := by
  simp only [retryPath, if_neg hi]

theorem length_retryPath : ∀ (t j : ℕ) (c : β) (idx : ℕ), idx < retryCnt U D t j →
    (retryPath U D t j c idx).length = j
  | 0, _, _, _, h => by simp [retryCnt] at h
  | t + 1, j, c, idx, h => by
    by_cases hi : idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum
    · obtain ⟨hj, hk, hq, hK⟩ := retry_rej_spec U D hi
      rw [retryPath_rej U D hi, List.length_append, U.length_path _ _ _ hq, length_retryPath t _ c _ hK]
      omega
    · obtain ⟨hq, hr⟩ := retry_acc_spec U D h hi
      rw [retryPath_acc U D hi, U.length_path _ _ _ hr]

theorem run_retryPath : ∀ (t j : ℕ) (c : β) (idx : ℕ) (rest : List QROM.Byte),
    idx < retryCnt U D t j → (R.retry g t).run (retryPath U D t j c idx ++ rest) = some (c, rest)
  | 0, _, _, _, _, h => by simp [retryCnt] at h
  | t + 1, j, c, idx, rest, h => by
    by_cases hi : idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum
    · obtain ⟨hj, hk, hq, hK⟩ := retry_rej_spec U D hi
      rw [retryPath_rej U D hi, Reader.retry, run_bind, List.append_assoc, U.run_path _ _ _ _ hq,
        Option.bind_some, getD_mem_rejList D hk]
      exact run_retryPath t _ c _ rest hK
    · obtain ⟨hq, hr⟩ := retry_acc_spec U D h hi
      rw [retryPath_acc U D hi, Reader.retry, run_bind, U.run_path _ _ _ _ hr, Option.bind_some,
        D.acc_some _ _ hq]
      rfl

theorem retryPath_inj : ∀ (t j : ℕ) (c : β) (idx idx' : ℕ), idx < retryCnt U D t j →
    idx' < retryCnt U D t j → retryPath U D t j c idx = retryPath U D t j c idx' → idx = idx'
  | 0, _, _, _, _, h, _, _ => by simp [retryCnt] at h
  | t + 1, j, c, idx, idx', h, h', he => by
    by_cases hi : idx < ((List.range (j + 1)).map (retryBlock U D t j)).sum <;>
      by_cases hi' : idx' < ((List.range (j + 1)).map (retryBlock U D t j)).sum
    · obtain ⟨hj, hk, hq, hK⟩ := retry_rej_spec U D hi
      obtain ⟨hj', hk2, hq', hK'⟩ := retry_rej_spec U D hi'
      rw [retryPath_rej U D hi, retryPath_rej U D hi'] at he
      refine pick_injective _ _ List.nodup_range hi hi' ?_
      generalize pick (retryBlock U D t j) (List.range (j + 1)) idx = P at he hj hk hq hK ⊢
      generalize pick (retryBlock U D t j) (List.range (j + 1)) idx' = P' at he hj' hk2 hq' hK' ⊢
      obtain ⟨i, r⟩ := P
      obtain ⟨i', r'⟩ := P'
      dsimp only at he hj hk hq hK hj' hk2 hq' hK' ⊢
      have hr1 := U.run_path i (D.rejList.getD (r / retryCnt U D t (j - i) % D.rejList.length)
        (D.accVal c 0)) _ (retryPath U D t (j - i) c (r % retryCnt U D t (j - i))) hq
      have hr2 := U.run_path i' (D.rejList.getD (r' / retryCnt U D t (j - i') % D.rejList.length)
        (D.accVal c 0)) _ (retryPath U D t (j - i') c (r' % retryCnt U D t (j - i'))) hq'
      rw [he, hr2] at hr1
      obtain ⟨hu, hX⟩ := Prod.mk.inj (Option.some_inj.1 hr1)
      have hii : i = i' := by
        have := congrArg List.length hX
        rw [length_retryPath U D t _ c _ hK, length_retryPath U D t _ c _ hK'] at this
        omega
      subst hii
      have hpth := List.append_inj_left he (by rw [U.length_path _ _ _ hq, U.length_path _ _ _ hq'])
      rw [hu] at hpth
      have hq2 := U.path_inj _ _ _ _ hq hq' hpth
      have hkk := getD_rejList_inj D hk hk2 _ _ hu.symm
      have hm := retryPath_inj t _ c _ _ hK' hK hX
      have hr1' : r / retryCnt U D t (j - i) = r' / retryCnt U D t (j - i) := by
        rw [← Nat.div_add_mod (r / retryCnt U D t (j - i)) D.rejList.length,
          ← Nat.div_add_mod (r' / retryCnt U D t (j - i)) D.rejList.length, hkk, hq2]
      rw [← Nat.div_add_mod r (retryCnt U D t (j - i)), ← Nat.div_add_mod r' (retryCnt U D t (j - i)),
        hr1', hm]
    · obtain ⟨hj, hk, hq, hK⟩ := retry_rej_spec U D hi
      obtain ⟨hq', hr'⟩ := retry_acc_spec U D h' hi'
      rw [retryPath_rej U D hi, retryPath_acc U D hi'] at he
      have hr1 := congrArg R.run he
      rw [U.run_path _ _ _ _ hq] at hr1
      have hr2 := U.run_path j (D.accVal c ((idx' - ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j)) _ [] hr'
      rw [List.append_nil] at hr2
      rw [hr2] at hr1
      have hu := (Prod.mk.inj (Option.some_inj.1 hr1)).1
      have h1 := getD_mem_rejList D hk (D.accVal c 0)
      rw [hu, D.acc_some _ _ hq'] at h1
      exact absurd h1 (by simp)
    · obtain ⟨hj, hk, hq, hK⟩ := retry_rej_spec U D hi'
      obtain ⟨hq', hr'⟩ := retry_acc_spec U D h hi
      rw [retryPath_rej U D hi', retryPath_acc U D hi] at he
      have hr1 := congrArg R.run he.symm
      rw [U.run_path _ _ _ _ hq] at hr1
      have hr2 := U.run_path j (D.accVal c ((idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j)) _ [] hr'
      rw [List.append_nil] at hr2
      rw [hr2] at hr1
      have hu := (Prod.mk.inj (Option.some_inj.1 hr1)).1
      have h1 := getD_mem_rejList D hk (D.accVal c 0)
      rw [hu, D.acc_some _ _ hq'] at h1
      exact absurd h1 (by simp)
    · obtain ⟨hq, hr⟩ := retry_acc_spec U D h hi
      obtain ⟨hq', hr'⟩ := retry_acc_spec U D h' hi'
      rw [retryPath_acc U D hi, retryPath_acc U D hi'] at he
      have hr1 := congrArg R.run he
      have hr2 := U.run_path j (D.accVal c ((idx -
        ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j)) _ [] hr
      have hr3 := U.run_path j (D.accVal c ((idx' -
        ((List.range (j + 1)).map (retryBlock U D t j)).sum) / U.cnt j)) _ [] hr'
      rw [List.append_nil] at hr2 hr3
      rw [hr2, hr3] at hr1
      have hu := (Prod.mk.inj (Option.some_inj.1 hr1)).1
      have ha := D.acc_inj c _ _ hq hq' hu
      rw [hu] at he
      have hm := U.path_inj _ _ _ _ hr hr' he
      have hs : idx - ((List.range (j + 1)).map (retryBlock U D t j)).sum =
          idx' - ((List.range (j + 1)).map (retryBlock U D t j)).sum := by
        rw [← Nat.div_add_mod (idx - _) (U.cnt j), ← Nat.div_add_mod (idx' - _) (U.cnt j), ha, hm]
      omega

theorem exact_retry [DecidableEq β] : ∀ (t j : ℕ) (c : β),
    (R.retry g t).exact j c = retryCnt U D t j
  | 0, j, c => by simp [Reader.retry, exact, retryCnt]
  | t + 1, j, c => by
    classical
    rw [Reader.retry, exact_bind, retryCnt_succ, sum_map_range]
    have hrej : (Finset.univ.filter fun a => g a = none).card = D.rejList.length := by
      rw [← List.toFinset_card_of_nodup D.rejList_nodup]
      congr 1
      ext a
      simp [D.mem_rejList]
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ∑ a, R.exact i a * ((g a).elim (R.retry g t) Reader.done).exact (j - i) c =
          retryBlock U D t j i + if i = j then D.nAcc * U.cnt j else 0 := by
      intro i hi
      simp only [U.exact_eq, ← Finset.mul_sum, sum_exact_elim_fintype, hrej, D.card_acc,
        exact_retry t, retryBlock]
      have : (j - i = 0) ↔ i = j := by
        simp only [Finset.mem_range] at hi
        omega
      simp only [this]
      split_ifs with hij
      · subst hij
        simp only [Nat.sub_self]
        ring
      · ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp

/-- **The retried draw** with an unranking of the inner reader and of `g`. -/
def retry (t : ℕ) : (R.retry g t).Unrank where
  cnt := retryCnt U D t
  path := retryPath U D t
  length_path := length_retryPath U D t
  run_path := run_retryPath U D t
  path_inj := retryPath_inj U D t
  exact_eq j c := exact_retry U D t j c

end Unrank

end Reader

namespace CReader

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The partial map of `avoid`: a value outside `U` is kept, a value in `U` is rejected. -/
def avoidMap (U : Finset C) (a : C) : Option {x : C // x ∉ U} :=
  if h : a ∈ U then none else some ⟨a, h⟩

omit [Fintype C] in
theorem avoidMap_eq_none_iff (U : Finset C) (a : C) : avoidMap U a = none ↔ a ∈ U := by
  unfold avoidMap; split_ifs with h <;> simp [h]

omit [Fintype C] in
theorem avoidMap_eq_some_iff (U : Finset C) (a : C) (b : {x : C // x ∉ U}) :
    avoidMap U a = some b ↔ a = b.1 := by
  unfold avoidMap
  split_ifs with h
  · simp only [false_iff]
    rintro rfl; exact b.2 h
  · simp [Subtype.ext_iff]

theorem card_avoidMap_none (U : Finset C) :
    (Finset.univ.filter fun a => avoidMap U a = none).card = U.card := by
  simp only [avoidMap_eq_none_iff, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem card_avoidMap_some (U : Finset C) (b : {x : C // x ∉ U}) :
    (Finset.univ.filter fun a => avoidMap U a = some b).card = 1 := by
  simp only [avoidMap_eq_some_iff, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.card_singleton]

/-- The arithmetic of `avoid`'s generating function: with `g = geomPgf z b`, `w = z ^ b`, `w² < 2`,
`H ≤ g ^ D` and `ρ ≤ 1 / (2 (D + 1) 3 ^ D)`, the bound of `Reader.pgf_retry_le` is at most
`g ^ (D + 1)`. -/
theorem avoid_pgf_arith {g H ρ : ℝ} {D : ℕ} (hg1 : 1 ≤ g) (hg3 : g < 3) (hH1 : 1 ≤ H)
    (hH : H = g ^ D) (hρ0 : 0 ≤ ρ) (hρ : ρ * (2 * (D + 1) * 3 ^ D) ≤ 1) (hρH : ρ * H < 1) :
    (1 - ρ) * H / (1 - ρ * H) ≤ g ^ (D + 1) := by
  have hpos : 0 < 1 - ρ * H := by linarith
  rw [div_le_iff₀ hpos]
  have hgD : g ^ D ≤ 3 ^ D := pow_le_pow_left₀ (by linarith) hg3.le D
  have hk := pow_succ_sub_one_le hg1 D
  -- `ρ (g H - 1) ≤ g - 1`
  have hgH : g ^ (D + 1) = g * H := by rw [hH, pow_succ, mul_comm]
  have h3 : ((D : ℝ) + 1) * g ^ D * (g - 1) ≤ ((D : ℝ) + 1) * 3 ^ D * (g - 1) := by
    gcongr
  have h4 : ρ * (g * H - 1) ≤ g - 1 := by
    have : ρ * (((D : ℝ) + 1) * 3 ^ D * (g - 1)) ≤ (g - 1) / 2 := by
      have hg0 : 0 ≤ g - 1 := by linarith
      nlinarith
    have hgH1 : 0 ≤ g * H - 1 := by nlinarith
    calc ρ * (g * H - 1) ≤ ρ * (((D : ℝ) + 1) * 3 ^ D * (g - 1)) := by
          gcongr; rw [← hgH]; linarith
      _ ≤ (g - 1) / 2 := this
      _ ≤ g - 1 := by linarith
  rw [hgH]
  nlinarith

/-- **The data of an unranking of the loop of `avoid`** (`Reader.RetryData`): the rejected values
are the listed elements of `U`, each kept value `c` is kept from one value, `c` itself. -/
def avoidRetryData (U : Finset C) (Ul : U.Listing) : Reader.RetryData (avoidMap U) where
  rejList := Ul.list
  rejList_nodup := Ul.nodup
  mem_rejList a := by rw [Ul.mem_iff, avoidMap_eq_none_iff]
  nAcc := 1
  accVal c _ := c.1
  acc_some c _ _ := (avoidMap_eq_some_iff U c.1 c).2 rfl
  acc_inj _ i i' hi hi' _ := by omega
  card_acc c := by convert card_avoidMap_some U c

/-- **Rejection sampling off `U`**: `r`'s draw repeated until its value is outside `U`, at most
`t` attempts at attempt bound `t` (the C++ loop `do { a = elt(); } while (a in U)`). The value is
uniform on the complement of `U` on success.

The load: write `D` and `b` for `r`'s draws and bytes, `g = geomPgf z b`. On `z ^ (2 b) < 2` one
has `z ^ b < 3/2`, so `g < 3`, the inner reader's generating function `H = g ^ D < 3 ^ D`, and with
`ρ = |U| / |C| ≤ 1 / (2 (D + 1) 3 ^ D)`: `(1 - ρ) H / (1 - ρ H) ≤ g ^ (D + 1) ≤
geomPgf z (2 b) ^ (D + 2)` (because `ρ (g H - 1) ≤ g - 1`, from
`g ^ (D + 1) - 1 ≤ (D + 1) g ^ D (g - 1)`); and the failure probability is at most
`D 2^-t / (1 - ρ) + ρ ^ t ≤ (D + 2) 2^-t`. The load is thus `⟨D + 2, 2 b⟩`.

An attempt bound `t` at least the stream length is never reached when each draw reads at least one
byte: every attempt then consumes a byte. -/
def avoid (r : CReader C) (U : Finset C)
    (hU : 2 * (r.load.draws + 1) * 3 ^ r.load.draws * U.card ≤ Fintype.card C) (Ul : U.Listing)
    (d : {x : C // x ∉ U}) : CReader {x : C // x ∉ U} where
  R t := (r.R t).retry (avoidMap U) t
  uniform t := by
    classical
    exact uniform_classical ((r.uniform' t).retry (fun b b' => by
      rw [card_avoidMap_some, card_avoidMap_some]) t)
  load := ⟨r.load.draws + 2, 2 * r.load.bytes⟩
  pgf_le {z} hz hzb t := by
    set D := r.load.draws
    set b := r.load.bytes
    have hw1 : 1 ≤ z ^ b := one_le_pow₀ hz
    have hw2 : (z ^ b) ^ 2 < 2 := by rw [← pow_mul, mul_comm]; exact hzb
    have hw : z ^ b < 3 / 2 := by nlinarith
    have hzb' : z ^ b < 2 := by linarith
    have hg1 := one_le_geomPgf hz hzb'
    have hg3 : geomPgf z b < 3 := by
      unfold geomPgf; rw [div_lt_iff₀ (by linarith)]; linarith
    set g := geomPgf z b
    have hH1 : 1 ≤ g ^ D := one_le_pow₀ hg1
    have hK : (0 : ℝ) < 2 * (D + 1) * 3 ^ D := by positivity
    set ρ : ℝ := 1 / (2 * (D + 1) * 3 ^ D)
    have hρ0 : 0 ≤ ρ := by positivity
    have hρK : ρ * (2 * (D + 1) * 3 ^ D) = 1 := by simp only [ρ]; field_simp
    have hgD : g ^ D < 3 ^ D ∨ D = 0 := by
      rcases Nat.eq_zero_or_pos D with h | h
      · exact Or.inr h
      · exact Or.inl (pow_lt_pow_left₀ hg3 (by linarith) h.ne')
    have hρH : ρ * g ^ D < 1 := by
      have h3 : g ^ D ≤ 3 ^ D := pow_le_pow_left₀ (by linarith) hg3.le D
      have h3' : (1 : ℝ) ≤ 3 ^ D := one_le_pow₀ (by norm_num)
      have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      nlinarith
    have hρ : ((Finset.univ.filter fun a => avoidMap U a = none).card : ℝ) ≤
        ρ * Fintype.card C := by
      rw [card_avoidMap_none]
      have hU' : (2 * (D + 1) * 3 ^ D * U.card : ℝ) ≤ Fintype.card C := by exact_mod_cast hU
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK]
      linarith
    refine (Reader.pgf_retry_le (r.uniform' t) _ hz (r.pgf_le hz hzb' t) hH1 hρ hρH t).trans ?_
    refine (avoid_pgf_arith hg1 hg3 hH1 rfl hρ0 hρK.le hρH).trans ?_
    have hm : g ≤ geomPgf z (2 * b) := geomPgf_mono hz (by omega) hzb
    calc g ^ (D + 1) ≤ geomPgf z (2 * b) ^ (D + 1) := pow_le_pow_left₀ (by linarith) hm _
      _ ≤ geomPgf z (2 * b) ^ (D + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  pfail_le t := by
    set D := r.load.draws
    have hK : (0 : ℝ) < 2 * (D + 1) * 3 ^ D := by positivity
    set ρ : ℝ := 1 / (2 * (D + 1) * 3 ^ D)
    have hρ0 : 0 ≤ ρ := by positivity
    have hρK : ρ * (2 * (D + 1) * 3 ^ D) = 1 := by simp only [ρ]; field_simp
    have h3' : (1 : ℝ) ≤ 3 ^ D := one_le_pow₀ (by norm_num)
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have hρh : ρ ≤ 1 / 2 := by nlinarith
    have hρD : ρ * (D + 1) ≤ 1 / 2 := by nlinarith
    have hρ : ((Finset.univ.filter fun a => avoidMap U a = none).card : ℝ) ≤
        ρ * Fintype.card C := by
      rw [card_avoidMap_none]
      have hU' : (2 * (D + 1) * 3 ^ D * U.card : ℝ) ≤ Fintype.card C := by exact_mod_cast hU
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK]
      linarith
    refine (Reader.pfail_retry_le (r.uniform' t) _ (r.pfail_le t) hρ hρ0 (by linarith) t).trans ?_
    have hh : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
    have hpow : ρ ^ t ≤ (1 / 2) ^ t := pow_le_pow_left₀ hρ0 hρh t
    have hdiv : (D : ℝ) * (1 / 2) ^ t / (1 - ρ) ≤ (D + 1) * (1 / 2) ^ t := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    push_cast
    nlinarith
  unrank t := (r.unrank t).retry (avoidRetryData U Ul) t
  default := d
  grant := r.grant

@[simp] theorem avoid_load (r : CReader C) (U : Finset C) (hU) (Ul : U.Listing) (d) :
    (r.avoid U hU Ul d).load = ⟨r.load.draws + 2, 2 * r.load.bytes⟩ := rfl

@[simp] theorem avoid_grant (r : CReader C) (U : Finset C) (hU) (Ul : U.Listing) (d) :
    (r.avoid U hU Ul d).grant = r.grant := rfl

end CReader

end GordieHowe.SPBCS
