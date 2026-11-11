-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleSide
public import GordieHowe.Foundations.ToMathlib.UniformFunction
public import GordieHowe.Foundations.ToMathlib.McDiarmid
public import GordieHowe.Foundations.ToMathlib.NNRatENNReal

@[expose] public section

/-!
# Weighted rejection loops against a fixed random function

A ring of members `N` reads one random function `H : N × V → C`; member `j` weighs a column `v`
with value `c` by `wt j (v, c) ∈ [0, 1]` (`RingWeights`, the cast of a rational weight `wtQ`;
`otherWeight` and `ringWeight` are rational, `coe_otherWeight`, `coe_ringWeight`). The signer `i`
repeats attempts (`weightedAttempt`): draw `y`, read its own value `H (i, w1 y)`, reject unless
`acc` accepts, and keep `w1 y` with probability `κ (w1 y, H (i, w1 y))` times the other members'
weights `∏_{j ≠ i} wt j (w1 y, H (j, w1 y))` (`otherWeight`).

The signer's attempt is the core attempt of `PMFOracleSide.lean` (`quenchedAttempt`) with side data
the other members' values, read through the column split (`columnSplit`), and keep factor the other
members' factor (`RingWeights.otherFactor`): `weightedAttempt_eq_quenchedAttempt`,
`weightedDev_eq_quenchedDev`. The column deviation, column error, mean weight and relative column
error (`colDev`, `colError`, `RingWeights.meanWeight`, `relColError`) are the core's with the
signer's weight. At a fixed oracle `H`:

- `tvDist_untilSome_untilSome_le_weight`: two unbounded loops whose accepted masses are close to
  `β₀ · g` and `β₁ · g` for one nonnegative `g` are within their normalized deviations;
- `weightedDev`, `weightedDev_eq`, `expect_weightedDev`, `RingWeights.expect_weightMass`: the
  deviation of the signer's attempt from `β` times the ring weight `∏_j wt j (v, H (j, v))`
  (`ringWeight`) is a sum of column terms, with explicit means against a uniform oracle
  (`quenchedDev_eq`, `expect_quenchedDev_of_eq`);
- `ringOf`, `abs_weightedDev_update_le`, `abs_weightMass_update_le`: bounded differences when the
  ring sits inside a larger oracle (`abs_quenchedDev_update_le` for the deviation);
- `RingPair`, `familyBound`, `tvDist_le_familyBound`, `one_le_familyBound_of_never`,
  `expect_familyBound_le`: the expected largest distance over many rings, by McDiarmid
  (`expect_sup'_le_of_boundedDiff`);
- `RingPair.countVar_le`, `RingPair.devVar_le`, `RingWeights.mul_card_le_mass`: the variance
  proxies of a ring with at most `N` members and mass at least `m |V|`, the deviation proxy
  through the collision probabilities `∑_v Pr[w1 = v]²` of the two signers' commitments
  (`sum_sq_toReal_map_uniformOfFintype` for a uniform proposal);
- `RingWeights.massRatio`, `RingPair.error_le_of_massRatio_le`: when the column masses
  `∏_j 𝔼_c wt j (v, c)` are positive with ratio at most `κ`, the ring error is at most `κ / θ`
  times the signers' relative column errors (`relColError`);
- `Finset.one_sub_sum_le_prod`, `RingWeights.one_sub_le_colMass`,
  `RingWeights.massRatio_le_inv_one_sub`: when member `j`'s mean weights are at least `1 - δ_j`
  in every column and `∑_j δ_j ≤ σ < 1`, every column mass is in `[1 - σ, 1]` and the mass ratio
  is at most `1 / (1 - σ)` (the Weierstrass product inequality);
- `weightedAttemptWith`, `map_weightedAttemptWith`, `exists_of_mem_support_weightedAttemptWith`,
  `untilSome_map_optionMap`: the attempt with its output.

About Mathlib objects only.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

section Normalize

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The unbounded loop over `A`, at an accepted value, in `ℝ`. -/
theorem toReal_untilSome_apply_some (A : PMF (Option α)) (a : α) :
    (untilSome A (some a)).toReal = (A (some a)).toReal / (1 - A none).toReal := by
  rw [untilSome_apply_some, ENNReal.toReal_div]

omit [DecidableEq α] in
/-- **Normalizing two nonnegative functions**: `∑ |f / ∑ f - g / ∑ g| ≤ 2 ∑ |f - g| / ∑ g`. -/
theorem sum_abs_div_sub_div_le {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hF : 0 < ∑ a, f a)
    (hG : 0 < ∑ a, g a) :
    ∑ a, |f a / ∑ b, f b - g a / ∑ b, g b| ≤ 2 * (∑ a, |f a - g a|) / ∑ a, g a := by
  set F := ∑ b, f b
  set G := ∑ b, g b
  have hF0 : F ≠ 0 := hF.ne'
  have hG0 : G ≠ 0 := hG.ne'
  have h1 : ∀ a, |f a / F - g a / G| ≤ f a * |1 / F - 1 / G| + |f a - g a| / G := fun a => by
    calc |f a / F - g a / G| = |f a * (1 / F - 1 / G) + (f a - g a) / G| := by
          congr 1; field_simp; ring
      _ ≤ |f a * (1 / F - 1 / G)| + |(f a - g a) / G| := abs_add_le _ _
      _ = f a * |1 / F - 1 / G| + |f a - g a| / G := by
          rw [abs_mul, abs_of_nonneg (hf a), abs_div, abs_of_pos hG]
  have h2 : F * |1 / F - 1 / G| ≤ (∑ a, |f a - g a|) / G := by
    calc F * |1 / F - 1 / G| = |G - F| / G := by
          rw [show 1 / F - 1 / G = (G - F) / (F * G) by field_simp, abs_div,
            abs_of_pos (mul_pos hF hG)]
          field_simp
      _ = |∑ a, (g a - f a)| / G := by rw [Finset.sum_sub_distrib]
      _ ≤ (∑ a, |f a - g a|) / G := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun a _ => ?_)
          exact abs_sub_comm _ _
  calc ∑ a, |f a / F - g a / G|
      ≤ ∑ a, (f a * |1 / F - 1 / G| + |f a - g a| / G) := Finset.sum_le_sum fun a _ => h1 a
    _ = F * |1 / F - 1 / G| + (∑ a, |f a - g a|) / G := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_div]
    _ ≤ 2 * (∑ a, |f a - g a|) / G := by rw [mul_div_assoc]; linarith

omit [DecidableEq α] in
/-- The unbounded loop over an attempt that never accepts. -/
theorem untilSome_of_apply_none_eq_one {A : PMF (Option α)} (h : A none = 1) :
    untilSome A = pure none := by
  unfold untilSome; rw [dif_pos h]

omit [DecidableEq α] in
/-- The unbounded loop over an attempt that accepts never outputs `none`. -/
theorem untilSome_apply_none {A : PMF (Option α)} (h : A none ≠ 1) : untilSome A none = 0 := by
  unfold untilSome; rw [dif_neg h, map_apply]; exact ENNReal.tsum_eq_zero.2 fun a => by simp

omit [DecidableEq α] in
/-- The accepted mass of an attempt, in `ℝ`. -/
theorem sum_toReal_apply_some (A : PMF (Option α)) :
    ∑ a, (A (some a)).toReal = (1 - A none).toReal := by
  rw [← ENNReal.toReal_sum fun a _ => A.apply_ne_top _, sum_apply_some]

omit [DecidableEq α] in
/-- An attempt that never accepts has no accepted mass. -/
theorem apply_some_eq_zero_of_apply_none_eq_one {A : PMF (Option α)} (h : A none = 1) (a : α) :
    A (some a) = 0 := by
  have hs := sum_apply_some A
  rw [h, tsub_self] at hs
  exact (Finset.sum_eq_zero_iff.1 hs) a (mem_univ _)

omit [DecidableEq α] in
/-- **The distance of two unbounded loops that accept**, as the distance of the normalized
accepted masses. -/
theorem tvDist_untilSome_eq_sum {A₀ A₁ : PMF (Option α)} (h₀ : A₀ none ≠ 1) (h₁ : A₁ none ≠ 1) :
    tvDist (untilSome A₀) (untilSome A₁) =
      (∑ a, |(A₀ (some a)).toReal / ∑ b, (A₀ (some b)).toReal -
        (A₁ (some a)).toReal / ∑ b, (A₁ (some b)).toReal|) / 2 := by
  classical
  rw [tvDist_eq_sum, Fintype.sum_option, untilSome_apply_none h₀, untilSome_apply_none h₁]
  simp only [ENNReal.toReal_zero, sub_zero, abs_zero, zero_add, toReal_untilSome_apply_some,
    sum_toReal_apply_some]

omit [DecidableEq α] in
/-- **Two unbounded loops close to one weight**: for a nonnegative weight `g`, levels `β₀, β₁ > 0`
and a threshold `s₀ > 0` on the total weight, the two loops are within their deviations
`∑ |A_b (some a) - β_b · g a|`, each normalized by `β_b · s₀`, or the total weight is below
`s₀`. -/
theorem tvDist_untilSome_untilSome_le_weight (A₀ A₁ : PMF (Option α)) {g : α → ℝ}
    (hg : ∀ a, 0 ≤ g a) {β₀ β₁ s₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 < β₁) (hs₀ : 0 < s₀) :
    tvDist (untilSome A₀) (untilSome A₁) ≤
      (∑ a, |(A₀ (some a)).toReal - β₀ * g a|) / (β₀ * s₀) +
        (∑ a, |(A₁ (some a)).toReal - β₁ * g a|) / (β₁ * s₀) +
        (if ∑ a, g a < s₀ then 1 else 0) := by
  have hd : ∀ (A : PMF (Option α)) (β : ℝ), 0 < β →
      0 ≤ (∑ a, |(A (some a)).toReal - β * g a|) / (β * s₀) := fun A β hβ =>
    div_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _) (mul_pos hβ hs₀).le
  have h0 := hd A₀ β₀ hβ₀
  have h1 := hd A₁ β₁ hβ₁
  have htv := tvDist_le_one (untilSome A₀) (untilSome A₁)
  by_cases hS : ∑ a, g a < s₀
  · rw [if_pos hS]; linarith
  rw [if_neg hS, add_zero]
  rw [not_lt] at hS
  set G := ∑ a, g a with hGdef
  have hG : 0 < G := hs₀.trans_le hS
  -- a loop that never accepts has deviation `β · G`
  have hnever : ∀ (A : PMF (Option α)) (β : ℝ), 0 < β → A none = 1 →
      1 ≤ (∑ a, |(A (some a)).toReal - β * g a|) / (β * s₀) := fun A β hβ hA => by
    rw [one_le_div (mul_pos hβ hs₀)]
    have : ∑ a, |(A (some a)).toReal - β * g a| = β * G := by
      simp only [apply_some_eq_zero_of_apply_none_eq_one hA, ENNReal.toReal_zero, zero_sub,
        abs_neg]
      rw [Finset.sum_congr rfl fun a _ => abs_of_nonneg (mul_nonneg hβ.le (hg a)),
        ← Finset.mul_sum]
    rw [this]; exact mul_le_mul_of_nonneg_left hS hβ.le
  by_cases hA₀ : A₀ none = 1
  · linarith [hnever A₀ β₀ hβ₀ hA₀]
  by_cases hA₁ : A₁ none = 1
  · linarith [hnever A₁ β₁ hβ₁ hA₁]
  -- both loops accept: normalize against `g / G`
  have hone : ∀ (A : PMF (Option α)) (β : ℝ), 0 < β → A none ≠ 1 →
      ∑ a, |(A (some a)).toReal / ∑ b, (A (some b)).toReal - g a / G| ≤
        2 * ((∑ a, |(A (some a)).toReal - β * g a|) / (β * s₀)) := fun A β hβ hA => by
    have hF : 0 < ∑ b, (A (some b)).toReal := by
      rw [sum_toReal_apply_some]
      exact ENNReal.toReal_pos (one_sub_apply_none_ne_zero hA)
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    have hβG : 0 < ∑ a, β * g a := by rw [← Finset.mul_sum]; exact mul_pos hβ hG
    have key := sum_abs_div_sub_div_le (fun a => ENNReal.toReal_nonneg) hF hβG
    have hnorm : ∀ a, β * g a / ∑ b, β * g b = g a / G := fun a => by
      rw [← Finset.mul_sum, mul_div_mul_left _ _ hβ.ne']
    simp only [hnorm] at key
    refine key.trans ?_
    rw [← Finset.mul_sum, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun a _ => abs_nonneg _) (mul_pos hβ hs₀)
      (mul_le_mul_of_nonneg_left hS hβ.le)
  rw [tvDist_untilSome_eq_sum hA₀ hA₁]
  have htri : ∑ a, |(A₀ (some a)).toReal / ∑ b, (A₀ (some b)).toReal -
        (A₁ (some a)).toReal / ∑ b, (A₁ (some b)).toReal| ≤
      ∑ a, |(A₀ (some a)).toReal / ∑ b, (A₀ (some b)).toReal - g a / G| +
        ∑ a, |(A₁ (some a)).toReal / ∑ b, (A₁ (some b)).toReal - g a / G| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [abs_sub_comm ((A₁ (some a)).toReal / _) _]
    exact abs_sub_le _ _ _
  linarith [hone A₀ β₀ hβ₀ hA₀, hone A₁ β₁ hβ₁ hA₁]

end Normalize

/-! ### The weighted ring attempt against a fixed oracle -/

/-- **Column weights of a ring**: member `j` weighs the column `v` with its value `c` by a
rational `wtQ j (v, c) ∈ [0, 1]` (rational, so that a signer comparing weights computes them),
`wt j (v, c)` in `ℝ≥0∞`. -/
structure RingWeights (N V C : Type*) where
  /-- The weight of member `j` at column `v` with value `c`. -/
  wtQ : N → V × C → ℚ≥0
  /-- Every weight is a probability. -/
  wtQ_le_one : ∀ j a, wtQ j a ≤ 1

/-- The weight of member `j` at column `v` with value `c`, in `ℝ≥0∞`. -/
noncomputable def RingWeights.wt {N V C : Type*} (s : RingWeights N V C) (j : N) (a : V × C) :
    ℝ≥0∞ :=
  (s.wtQ j a : ℝ≥0∞)

/-- Every weight is a probability. -/
theorem RingWeights.wt_le_one {N V C : Type*} (s : RingWeights N V C) (j : N) (a : V × C) :
    s.wt j a ≤ 1 :=
  ENNReal.nnratCast_le_one.2 (s.wtQ_le_one j a)


section Weighted

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]

namespace RingWeights

variable (s : RingWeights N V C)

/-- **The other members' weight** of column `v` at the oracle `H`, for the signer `i`:
`∏_{j ≠ i} wt j (v, H (j, v))`, a rational. -/
def otherWeight (i : N) (H : N × V → C) (v : V) : ℚ≥0 :=
  ∏ j ∈ univ.erase i, s.wtQ j (v, H (j, v))

/-- **The ring weight** of column `v` at the oracle `H`: `∏_j wt j (v, H (j, v))`, a rational. -/
def ringWeight (H : N × V → C) (v : V) : ℚ≥0 :=
  ∏ j, s.wtQ j (v, H (j, v))

/-- The other members' weight in `ℝ≥0∞` is the product of their weights. -/
theorem coe_otherWeight (i : N) (H : N × V → C) (v : V) :
    (s.otherWeight i H v : ℝ≥0∞) = ∏ j ∈ univ.erase i, s.wt j (v, H (j, v)) :=
  ENNReal.nnratCast_prod _ _

/-- The ring weight in `ℝ≥0∞` is the product of the weights. -/
theorem coe_ringWeight (H : N × V → C) (v : V) :
    (s.ringWeight H v : ℝ≥0∞) = ∏ j, s.wt j (v, H (j, v)) :=
  ENNReal.nnratCast_prod _ _

/-- The total ring weight at the oracle `H`: `∑_v ∏_j wt j (v, H (j, v))`. -/
noncomputable def weightMass (H : N × V → C) : ℝ :=
  ∑ v, (s.ringWeight H v : ℝ≥0∞).toReal

theorem otherWeight_le_one (i : N) (H : N × V → C) (v : V) :
    (s.otherWeight i H v : ℝ≥0∞) ≤ 1 := by
  rw [coe_otherWeight]
  exact Finset.prod_le_one' fun j _ => s.wt_le_one j _

theorem ringWeight_le_one (H : N × V → C) (v : V) : (s.ringWeight H v : ℝ≥0∞) ≤ 1 := by
  rw [coe_ringWeight]
  exact Finset.prod_le_one' fun j _ => s.wt_le_one j _

/-- The ring weight is the signer's weight times the other members' weight. -/
theorem ringWeight_eq_mul (i : N) (H : N × V → C) (v : V) :
    (s.ringWeight H v : ℝ≥0∞) = s.wt i (v, H (i, v)) * (s.otherWeight i H v : ℝ≥0∞) := by
  rw [coe_ringWeight, coe_otherWeight]
  exact (Finset.mul_prod_erase univ (fun j => s.wt j (v, H (j, v))) (mem_univ i)).symm

/-- **The other members' factor** for the signer `i` at a column whose other members' values are
`z`: `∏_{j ≠ i} wt j (v, z j)`. It is the keep factor of the ring signer as a core attempt
(`weightedAttempt_eq_quenchedAttempt`), and does not read the signer's value `c`. -/
noncomputable def otherFactor (i : N) (a : V × C × ({j // j ≠ i} → C)) : ℝ≥0∞ :=
  ∏ j : {j // j ≠ i}, s.wt j (a.1, a.2.2 j)

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
theorem otherFactor_le_one (i : N) (a : V × C × ({j // j ≠ i} → C)) : s.otherFactor i a ≤ 1 :=
  Finset.prod_le_one' fun j _ => s.wt_le_one j _

/-- At the other members' values of a column of `H`, the factor is the other members' weight. -/
theorem otherFactor_mk (i : N) (H : N × V → C) (v : V) (c : C) :
    s.otherFactor i (v, c, fun j => H (j.1, v)) = s.otherWeight i H v := by
  rw [coe_otherWeight, otherFactor]
  exact (Finset.prod_subtype (univ.erase i) (fun j => by simp)
    (fun j => s.wt j (v, H (j, v)))).symm

variable [Nonempty C]

/-- **The mean weight** of member `j` at column `v`: `𝔼_c wt j (v, c)`. -/
noncomputable def meanWeight (j : N) (v : V) : ℝ := quenchedMeanWeight (s.wt j) v

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [DecidableEq C] [Nonempty C] in
theorem meanWeight_eq (j : N) (v : V) : s.meanWeight j v = 𝔼 c : C, (s.wt j (v, c)).toReal :=
  rfl

/-- **The column mass** `∏_j 𝔼_c wt j (v, c)`: the mean ring weight of column `v` against a
uniform oracle. -/
noncomputable def colMass (v : V) : ℝ := ∏ j, s.meanWeight j v

/-- **The ring mass** `∑_v ∏_j 𝔼_c wt j (v, c)`: the mean total ring weight. -/
noncomputable def mass : ℝ := ∑ v, s.colMass v

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [DecidableEq C] [Nonempty C] in
theorem meanWeight_nonneg (j : N) (v : V) : 0 ≤ s.meanWeight j v :=
  quenchedMeanWeight_nonneg _ v

theorem colMass_nonneg (v : V) : 0 ≤ s.colMass v :=
  Finset.prod_nonneg fun j _ => s.meanWeight_nonneg j v

end RingWeights

variable (s : RingWeights N V C) (i : N) {Y : Type*} [Fintype Y] (P : PMF Y) (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

include hκ in
/-- The keep probability of the weighted attempt is a probability. -/
theorem keepWeight_le_one (H : N × V → C) (v : V) : κ (v, H (i, v)) * s.otherWeight i H v ≤ 1 :=
  mul_le_one' (hκ _) (s.otherWeight_le_one i H v)

/-- **The signer's weighted ring attempt** at the oracle `H`: `y ← P`; reject unless
`acc y (H (i, w1 y))`; keep `w1 y` with probability `κ (w1 y, H (i, w1 y))` times the other
members' weight of the column `w1 y`. -/
noncomputable def weightedAttempt (H : N × V → C) : PMF (Option V) :=
  P.bind fun y =>
    if acc y (H (i, w1 y)) = true then
      keepOrReject (w1 y) (κ (w1 y, H (i, w1 y)) * s.otherWeight i H (w1 y))
        (keepWeight_le_one s i κ hκ H (w1 y))
    else pure none

omit [Fintype Y] in
/-- **The weighted ring attempt is the core attempt** (`quenchedAttempt`) with the other members'
factor, read through the column split. -/
theorem weightedAttempt_eq_quenchedAttempt (H : N × V → C) :
    weightedAttempt s i P w1 acc κ hκ H =
      quenchedAttempt P w1 acc κ hκ (s.otherFactor i) (s.otherFactor_le_one i)
        (columnSplit i H) := by
  unfold weightedAttempt quenchedAttempt
  refine congrArg P.bind (funext fun y => ?_)
  simp only [columnSplit_apply, s.otherFactor_mk]

/-- The weighted attempt keeps `v` with probability
`signerMass v (H (i, v)) · κ (v, H (i, v)) · otherWeight v`. -/
theorem weightedAttempt_apply_some (H : N × V → C) (v : V) :
    weightedAttempt s i P w1 acc κ hκ H (some v) =
      signerMass P w1 acc v (H (i, v)) * κ (v, H (i, v)) * s.otherWeight i H v := by
  rw [weightedAttempt_eq_quenchedAttempt, quenchedAttempt_apply_some, columnSplit_apply,
    s.otherFactor_mk]

/-- **The column deviation** of the signer at column `v` with its value `c`:
`|signerMass v c · κ (v, c) - β · wt i (v, c)|`, the core's column deviation with the signer's
weight. -/
noncomputable def colDev (β : ℝ) (v : V) (c : C) : ℝ :=
  quenchedColDev P w1 acc κ (s.wt i) β v c

omit [Fintype N] [DecidableEq N] [Fintype V] [Fintype C] [DecidableEq C] in
theorem colDev_eq (β : ℝ) (v : V) (c : C) :
    colDev s i P w1 acc κ β v c =
      |(signerMass P w1 acc v c * κ (v, c)).toReal - β * (s.wt i (v, c)).toReal| :=
  rfl

/-- **The deviation of the signer's weighted attempt at the oracle `H`** from `β` times the ring
weight: `∑_v |A_H (some v) - β · ringWeight H v|`. -/
noncomputable def weightedDev (β : ℝ) (H : N × V → C) : ℝ :=
  ∑ v, |(weightedAttempt s i P w1 acc κ hκ H (some v)).toReal -
    β * (s.ringWeight H v : ℝ≥0∞).toReal|

/-- **The deviation is the core deviation** (`quenchedDev`) with the other members' factor and the
signer's weight, read through the column split. -/
theorem weightedDev_eq_quenchedDev (β : ℝ) (H : N × V → C) :
    weightedDev s i P w1 acc κ hκ β H =
      quenchedDev P w1 acc κ hκ (s.otherFactor i) (s.otherFactor_le_one i) (s.wt i) β
        (columnSplit i H) := by
  unfold weightedDev quenchedDev
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [weightedAttempt_eq_quenchedAttempt, s.ringWeight_eq_mul i, columnSplit_apply,
    s.otherFactor_mk]

/-- **The deviation is a sum of column terms**: the other members' weight times the column
deviation (`quenchedDev_eq`). -/
theorem weightedDev_eq (β : ℝ) (H : N × V → C) :
    weightedDev s i P w1 acc κ hκ β H =
      ∑ v, (s.otherWeight i H v : ℝ≥0∞).toReal * colDev s i P w1 acc κ β v (H (i, v)) := by
  rw [weightedDev_eq_quenchedDev, quenchedDev_eq]
  simp only [columnSplit_apply, s.otherFactor_mk]
  rfl

omit [Fintype N] [DecidableEq N] [Fintype V] [Fintype C] [DecidableEq C] in
include hκ in
/-- The column deviation is at most `Pr[w1 = v] + β` (`quenchedColDev_le`). -/
theorem colDev_le {β : ℝ} (hβ : 0 ≤ β) (v : V) (c : C) :
    colDev s i P w1 acc κ β v c ≤ (P.map w1 v).toReal + β :=
  quenchedColDev_le P w1 acc κ hκ (s.wt i) (s.wt_le_one i) hβ v c

variable [Nonempty C]

/-- **The signer's column error** at column `v`:
`𝔼_c |signerMass v c · κ (v, c) - β · wt i (v, c)|`, the core's column error with the signer's
weight. -/
noncomputable def colError (β : ℝ) (v : V) : ℝ := quenchedColError P w1 acc κ (s.wt i) β v

/-- **The signer's relative column error**: `∑_v colError v / 𝔼_c wt i (v, c)`, over `β · |V|`,
the core's relative column error with the signer's weight. It compares the signer's kept mass at
each column with `β` times its own weight, relative to its mean weight. -/
noncomputable def relColError (β : ℝ) : ℝ := quenchedRelColError P w1 acc κ (s.wt i) β

omit [Fintype N] [DecidableEq N] [DecidableEq C] [Nonempty C] in
/-- The relative column error in terms of the ring's column error and mean weight. -/
theorem relColError_eq (β : ℝ) :
    relColError s i P w1 acc κ β =
      (∑ v, colError s i P w1 acc κ β v / s.meanWeight i v) / (β * Fintype.card V) :=
  rfl

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq C] [Nonempty C] in
theorem colError_nonneg (β : ℝ) (v : V) : 0 ≤ colError s i P w1 acc κ β v :=
  quenchedColError_nonneg P w1 acc κ (s.wt i) β v

end Weighted

/-! ### Means against a uniform oracle -/

section WeightedMean

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Nonempty C] (s : RingWeights N V C)

/-- **The mean total ring weight against a uniform oracle** is the ring mass. -/
theorem RingWeights.expect_weightMass : 𝔼 H : N × V → C, s.weightMass H = s.mass := by
  simp only [RingWeights.weightMass, RingWeights.coe_ringWeight, ENNReal.toReal_prod]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [expect_column (N := N) (C := C) v fun col => ∏ j, (s.wt j (v, col j)).toReal,
    expect_prod_apply (fun j y => (s.wt j (v, y)).toReal)]
  rfl

variable (i : N) {Y : Type*} [Fintype Y] (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool)
  (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

/-- **The mean deviation against a uniform oracle**: at each column, the other members' mean
weights times the signer's column error. -/
theorem expect_weightedDev (β : ℝ) :
    𝔼 H : N × V → C, weightedDev s i P w1 acc κ hκ β H =
      ∑ v, (∏ j ∈ univ.erase i, s.meanWeight j v) * colError s i P w1 acc κ β v := by
  simp only [weightedDev_eq_quenchedDev]
  rw [expect_comp_equiv (columnSplit i) fun F => quenchedDev P w1 acc κ hκ (s.otherFactor i)
      (s.otherFactor_le_one i) (s.wt i) β F,
    expect_quenchedDev_of_eq P w1 acc κ hκ _ _ (s.wt i)
      (fun a : V × ({j // j ≠ i} → C) => ∏ j : {j // j ≠ i}, s.wt j (a.1, a.2 j))
      (fun _ _ _ => rfl) β]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  simp only [ENNReal.toReal_prod]
  rw [expect_prod_apply (fun (j : {j // j ≠ i}) y => (s.wt j (v, y)).toReal)]
  exact (Finset.prod_subtype (univ.erase i) (fun j => by simp) (fun j => s.meanWeight j v)).symm

end WeightedMean

/-! ### A ring inside a larger oracle: bounded differences -/

section Embedded

variable {N V C K : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] (pt : N → K)

/-- **The ring's oracle inside a larger oracle** `G : K × V → C`: member `j` reads `G` at the
point `pt j`. -/
def ringOf (G : K × V → C) : N × V → C := fun x => G (pt x.1, x.2)

/-- The ring's oracle inside a uniform oracle is uniform, for distinct points. -/
theorem expect_ringOf [Nonempty C] (hpt : Function.Injective pt) (Φ : (N × V → C) → ℝ) :
    𝔼 G : K × V → C, Φ (ringOf pt G) = 𝔼 H : N × V → C, Φ H :=
  expect_comp_embedding ⟨fun x => (pt x.1, x.2), fun x y h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (hpt h1) h2⟩ Φ

/-- Changing the larger oracle at `(k, v)` changes the ring's oracle only at column `v`, and not
at all unless `k` is a member's point. -/
theorem ringOf_update_apply (G : K × V → C) (k : K) (v : V) (c : C) (x : N × V)
    (hx : x.2 ≠ v ∨ k ∉ Set.range pt) :
    ringOf pt (Function.update G (k, v) c) x = ringOf pt G x := by
  unfold ringOf
  rw [Function.update_of_ne]
  intro h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rcases hx with hx | hx
  · exact hx h2
  · exact hx ⟨x.1, h1⟩

/-- **Bounded differences of a sum of column terms**: a sum over the columns of terms with
values in `[0, b v]`, each reading its column of the ring's oracle, moves by at most `b v` when
the larger oracle changes at `(k, v)`, and not at all unless `k` is a member's point. -/
theorem abs_sum_column_update_le (T : V → (N → C) → ℝ) {b : V → ℝ}
    (hT : ∀ v col, T v col ∈ Set.Icc 0 (b v)) (G : K × V → C) (k : K) (v : V) (c : C) :
    |∑ v', T v' (fun j => ringOf pt (Function.update G (k, v) c) (j, v')) -
        ∑ v', T v' (fun j => ringOf pt G (j, v'))| ≤
      if k ∈ Set.range pt then b v else 0 := by
  classical
  have hcol : ∀ v', v' ≠ v ∨ k ∉ Set.range pt →
      (fun j => ringOf pt (Function.update G (k, v) c) (j, v')) = fun j => ringOf pt G (j, v') :=
    fun v' h => funext fun j => ringOf_update_apply pt G k v c (j, v') h
  split_ifs with hk
  · rw [← Finset.sum_sub_distrib, Finset.sum_eq_single v (fun v' _ hv' => by
      rw [hcol v' (Or.inl hv'), sub_self]) (by simp)]
    have h1 := hT v (fun j => ringOf pt (Function.update G (k, v) c) (j, v))
    have h2 := hT v (fun j => ringOf pt G (j, v))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · rw [Finset.sum_congr rfl fun v' _ => by rw [hcol v' (Or.inr hk)], sub_self, abs_zero]

variable (s : RingWeights N V C)

/-- **Bounded differences of the total ring weight.** -/
theorem abs_weightMass_update_le (G : K × V → C) (k : K) (v : V) (c : C) :
    |s.weightMass (ringOf pt (Function.update G (k, v) c)) - s.weightMass (ringOf pt G)| ≤
      if k ∈ Set.range pt then 1 else 0 := by
  simp only [RingWeights.weightMass, RingWeights.coe_ringWeight]
  exact abs_sum_column_update_le pt (fun v col => (∏ j, s.wt j (v, col j)).toReal)
    (b := fun _ => 1) (fun v col => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_one_of_le_one
      (Finset.prod_le_one' fun j _ => s.wt_le_one j _)⟩) G k v c

variable (i : N) {Y : Type*} [Fintype Y] (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool)
  (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

/-- **Bounded differences of the deviation**: changing the larger oracle at `(k, v)` moves the
deviation of the ring's oracle by at most `Pr[w1 = v] + β`, and not at all unless `k` is a
member's point. -/
theorem abs_weightedDev_update_le {β : ℝ} (hβ : 0 ≤ β) (G : K × V → C) (k : K) (v : V) (c : C) :
    |weightedDev s i P w1 acc κ hκ β (ringOf pt (Function.update G (k, v) c)) -
        weightedDev s i P w1 acc κ hκ β (ringOf pt G)| ≤
      if k ∈ Set.range pt then (P.map w1 v).toReal + β else 0 := by
  by_cases hk : k ∈ Set.range pt
  · rw [if_pos hk, weightedDev_eq_quenchedDev, weightedDev_eq_quenchedDev]
    have hsplit : columnSplit i (ringOf pt (Function.update G (k, v) c)) =
        Function.update (columnSplit i (ringOf pt G)) v
          (columnSplit i (ringOf pt (Function.update G (k, v) c)) v) := by
      funext v'
      by_cases hv : v' = v
      · subst hv
        rw [Function.update_self]
      · rw [Function.update_of_ne hv, columnSplit_apply, columnSplit_apply]
        exact Prod.ext (ringOf_update_apply pt G k v c (i, v') (Or.inl hv))
          (funext fun j => ringOf_update_apply pt G k v c (j.1, v') (Or.inl hv))
    rw [hsplit]
    exact abs_quenchedDev_update_le P w1 acc κ hκ _ _ (s.wt i) (s.wt_le_one i) hβ _ v _
  · rw [if_neg hk, show ringOf pt (Function.update G (k, v) c) = ringOf pt G from
      funext fun x => ringOf_update_apply pt G k v c x (Or.inr hk), sub_self, abs_zero]

end Embedded

/-! ### Many rings inside one oracle: the expected largest distance -/

section Family

/-- **A signer of a ring attempt**: a proposal `P`, its commitment `w1`, the acceptance `acc`, the
keep coin `κ`, and a level `β > 0` of its flattened kept mass. -/
structure LoopSigner (V C : Type) where
  /-- The proposals. -/
  Y : Type
  /-- The proposal law. -/
  P : PMF Y
  /-- The commitment of a proposal. -/
  w1 : Y → V
  /-- The acceptance of a proposal and a challenge. -/
  acc : Y → C → Bool
  /-- The keep coin. -/
  κ : V × C → ℝ≥0∞
  /-- The keep coin is a probability. -/
  hκ : ∀ a, κ a ≤ 1
  /-- The level of the flattened kept mass. -/
  β : ℝ
  /-- The level is positive. -/
  hβ : 0 < β

/-- **Two signers of one ring inside a larger oracle** `K × V → C`: the members' distinct points
`pt`, their column weights `wts`, and the two signers' positions and attempts. -/
structure RingPair (K V C : Type) where
  /-- The members. -/
  Mem : Type
  /-- The members' points. -/
  pt : Mem ↪ K
  /-- The members' column weights. -/
  wts : RingWeights Mem V C
  /-- The positions of the two signers. -/
  pos : Bool → Mem
  /-- The two signers. -/
  signer : Bool → LoopSigner V C

variable {V C K : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype K] [DecidableEq K]

namespace RingPair

variable (R : RingPair K V C) [Fintype R.Mem] [DecidableEq R.Mem] [∀ b, Fintype (R.signer b).Y]

/-- The attempt of signer `b` against the larger oracle `G`. -/
noncomputable def attempt (b : Bool) (G : K × V → C) : PMF (Option V) :=
  weightedAttempt R.wts (R.pos b) (R.signer b).P (R.signer b).w1 (R.signer b).acc (R.signer b).κ
    (R.signer b).hκ (ringOf R.pt G)

/-- The deviation of signer `b` against the larger oracle `G`. -/
noncomputable def dev (b : Bool) (G : K × V → C) : ℝ :=
  weightedDev R.wts (R.pos b) (R.signer b).P (R.signer b).w1 (R.signer b).acc (R.signer b).κ
    (R.signer b).hκ (R.signer b).β (ringOf R.pt G)

/-- The total ring weight against the larger oracle `G`. -/
noncomputable def massAt (G : K × V → C) : ℝ := R.wts.weightMass (ringOf R.pt G)

/-- **The error of the ring at the threshold fraction `θ`**: the two signers' mean deviations,
each over its level times `θ` times the ring mass. -/
noncomputable def error (θ : ℝ) : ℝ :=
  ∑ b : Bool, (∑ v, (∏ j ∈ univ.erase (R.pos b), R.wts.meanWeight j v) *
    colError R.wts (R.pos b) (R.signer b).P (R.signer b).w1 (R.signer b).acc (R.signer b).κ
      (R.signer b).β v) / ((R.signer b).β * (θ * R.wts.mass))

/-- The variance proxy of the deviations at the threshold fraction `θ`. -/
noncomputable def devVar (θ : ℝ) : ℝ :=
  Fintype.card R.Mem * ∑ v, (∑ b : Bool, (((R.signer b).P.map (R.signer b).w1 v).toReal +
    (R.signer b).β) / ((R.signer b).β * (θ * R.wts.mass))) ^ 2

/-- The variance proxy of the total ring weight at the threshold fraction `θ`. -/
noncomputable def countVar (θ : ℝ) : ℝ :=
  Fintype.card R.Mem * Fintype.card V / ((1 - θ) * R.wts.mass) ^ 2

omit [∀ b, Fintype (R.signer b).Y] in
/-- **The distance of the two signers' loops at one oracle**, at most the normalized deviations
and the indicator of too little total ring weight. -/
theorem tvDist_untilSome_le (θ : ℝ) (hθ : 0 < θ) (hμ : 0 < R.wts.mass) (G : K × V → C) :
    tvDist (untilSome (R.attempt false G)) (untilSome (R.attempt true G)) ≤
      R.dev false G / ((R.signer false).β * (θ * R.wts.mass)) +
        R.dev true G / ((R.signer true).β * (θ * R.wts.mass)) +
        (if R.massAt G < θ * R.wts.mass then 1 else 0) :=
  tvDist_untilSome_untilSome_le_weight _ _ (fun _ => ENNReal.toReal_nonneg) (R.signer false).hβ
    (R.signer true).hβ (mul_pos hθ hμ)

omit [DecidableEq R.Mem] [(b : Bool) → Fintype (R.signer b).Y] in
/-- Too little total ring weight: the indicator is at most the normalized shortfall, or zero. -/
theorem ite_massAt_lt_le (θ : ℝ) (hθ : θ < 1) (hμ : 0 < R.wts.mass) (G : K × V → C) :
    (if R.massAt G < θ * R.wts.mass then (1 : ℝ) else 0) ≤
      max 0 ((R.wts.mass - R.massAt G) / ((1 - θ) * R.wts.mass)) := by
  split_ifs with h
  · refine le_max_of_le_right ?_
    rw [le_div_iff₀ (mul_pos (by linarith) hμ)]
    linarith
  · exact le_max_left _ _

omit [DecidableEq R.Mem] [(b : Bool) → Fintype (R.signer b).Y] in
/-- The number of points of the ring. -/
theorem sum_ite_mem_range (a : ℝ) :
    ∑ k : K, (if k ∈ Set.range R.pt then a else 0) = Fintype.card R.Mem * a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun k => k ∈ Set.range R.pt) = Finset.univ.map R.pt := by
    ext k; simp
  rw [this, Finset.card_map, Finset.card_univ]

omit [DecidableEq R.Mem] [(b : Bool) → Fintype (R.signer b).Y] in
/-- The squared bounded differences of a family on the ring's points. -/
theorem sum_sq_ite_mem_range (a : V → ℝ) :
    ∑ x : K × V, (if x.1 ∈ Set.range R.pt then a x.2 else 0) ^ 2 =
      Fintype.card R.Mem * ∑ v, a v ^ 2 := by
  rw [Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← R.sum_ite_mem_range (a v ^ 2)]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

omit [DecidableEq V] [DecidableEq C] [Nonempty C] [Fintype K] [DecidableEq K]
  [DecidableEq R.Mem] [∀ b, Fintype (R.signer b).Y] in
/-- **The weight variance proxy from a lower bound on the mass**: with at most `N` members and
ring mass at least `m · |V|`, `m > 0`, `countVar θ ≤ N / ((1 - θ)² m² |V|)` for `θ < 1`. -/
theorem countVar_le [Nonempty V] {N : ℕ} {θ m : ℝ} (hcard : Fintype.card R.Mem ≤ N)
    (hθ : θ < 1) (hm : 0 < m) (hmass : m * Fintype.card V ≤ R.wts.mass) :
    R.countVar θ ≤ N / ((1 - θ) ^ 2 * m ^ 2 * Fintype.card V) := by
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ha : 0 < 1 - θ := by linarith
  have hN : (Fintype.card R.Mem : ℝ) ≤ N := by exact_mod_cast hcard
  have hden : ((1 - θ) * (m * Fintype.card V)) ^ 2 ≤ ((1 - θ) * R.wts.mass) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hmass ha.le) 2
  unfold countVar
  calc (Fintype.card R.Mem : ℝ) * Fintype.card V / ((1 - θ) * R.wts.mass) ^ 2
      ≤ N * Fintype.card V / ((1 - θ) * (m * Fintype.card V)) ^ 2 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hN hV.le) (by positivity) hden
    _ = N / ((1 - θ) ^ 2 * m ^ 2 * Fintype.card V) := by
        field_simp

omit [DecidableEq V] [DecidableEq C] [Nonempty C] [Fintype K] [DecidableEq K]
  [DecidableEq R.Mem] [∀ b, Fintype (R.signer b).Y] in
/-- **The deviation variance proxy from a lower bound on the mass**: with at most `N` members,
ring mass at least `m · |V|`, `m > 0`, and both signers at the level `β`,
`devVar θ ≤ 4N / (θ m)² · ∑_b (∑_v Pr[w1_b = v]² / (β |V|)² + 1 / |V|)` for `θ > 0`, from
`(x₀ + x₁ + 2β)² ≤ 4 (x₀² + x₁² + 2β²)`. -/
theorem devVar_le [Nonempty V] {N : ℕ} {θ m β : ℝ} (hcard : Fintype.card R.Mem ≤ N)
    (hθ : 0 < θ) (hm : 0 < m) (hmass : m * Fintype.card V ≤ R.wts.mass)
    (hβ : ∀ b, (R.signer b).β = β) :
    R.devVar θ ≤ 4 * N / (θ * m) ^ 2 * ∑ b : Bool,
      ((∑ v, ((R.signer b).P.map (R.signer b).w1 v).toReal ^ 2) / (β * Fintype.card V) ^ 2 +
        1 / Fintype.card V) := by
  have hβ0 : 0 < β := hβ false ▸ (R.signer false).hβ
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hN : (Fintype.card R.Mem : ℝ) ≤ N := by exact_mod_cast hcard
  set P : Bool → V → ℝ := fun b v => ((R.signer b).P.map (R.signer b).w1 v).toReal
  set D := β * (θ * R.wts.mass)
  have hD0 : β * (θ * (m * Fintype.card V)) ≤ D :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hθ.le) hβ0.le
  have hDm : 0 < β * (θ * (m * Fintype.card V)) := by positivity
  have hterm : ∀ v, (∑ b : Bool, (P b v + (R.signer b).β) /
      ((R.signer b).β * (θ * R.wts.mass))) ^ 2 ≤
        4 * ∑ b : Bool, (P b v ^ 2 + β ^ 2) / (β * (θ * (m * Fintype.card V))) ^ 2 := by
    intro v
    simp only [hβ, Fintype.sum_bool]
    rw [← add_div, div_pow, ← add_div, ← mul_div_assoc]
    have hnum : (P true v + β + (P false v + β)) ^ 2 ≤
        4 * (P true v ^ 2 + β ^ 2 + (P false v ^ 2 + β ^ 2)) := by
      nlinarith [sq_nonneg (P true v - P false v), sq_nonneg (P true v - β),
        sq_nonneg (P false v - β)]
    exact div_le_div₀ (by positivity) hnum (by positivity)
      (pow_le_pow_left₀ hDm.le hD0 2)
  unfold devVar
  calc (Fintype.card R.Mem : ℝ) * ∑ v, (∑ b : Bool, (P b v + (R.signer b).β) /
        ((R.signer b).β * (θ * R.wts.mass))) ^ 2
      ≤ N * ∑ v, 4 * ∑ b : Bool, (P b v ^ 2 + β ^ 2) / (β * (θ * (m * Fintype.card V))) ^ 2 :=
        mul_le_mul hN (Finset.sum_le_sum fun v _ => hterm v)
          (Finset.sum_nonneg fun v _ => sq_nonneg _) (Nat.cast_nonneg _)
    _ = 4 * N / (θ * m) ^ 2 * ∑ b : Bool,
          ((∑ v, P b v ^ 2) / (β * Fintype.card V) ^ 2 + 1 / Fintype.card V) := by
        simp only [Fintype.sum_bool, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end RingPair

variable {M : Type} [Fintype M] [Nonempty M] (R : M → RingPair K V C) [∀ m, Fintype (R m).Mem]
  [∀ m, DecidableEq (R m).Mem] [∀ m b, Fintype ((R m).signer b).Y] (θ : ℝ)

/-- The normalizing constant of signer `b` of ring `m`: its level times `θ` times the ring mass. -/
noncomputable def famDen (m : M) (b : Bool) : ℝ := ((R m).signer b).β * (θ * (R m).wts.mass)

/-- The normalized deviations of ring `m` at the oracle `G`. -/
noncomputable def famDev (m : M) (G : K × V → C) : ℝ := ∑ b : Bool, (R m).dev b G / famDen R θ m b

/-- The normalized shortfall of total ring weight of ring `m` at the oracle `G`; zero for
`none`. -/
noncomputable def famShort (o : Option M) (G : K × V → C) : ℝ := o.elim 0 fun m =>
  ((R m).wts.mass - (R m).massAt G) / ((1 - θ) * (R m).wts.mass)

/-- **The bound of the rings at the oracle `G`**: the largest normalized deviations plus the
largest normalized shortfall of total ring weight (or zero). -/
noncomputable def familyBound (G : K × V → C) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun m => famDev R θ m G) +
    Finset.univ.sup' Finset.univ_nonempty (fun o => famShort R θ o G)

variable {R θ}

omit [(m : M) → (b : Bool) → Fintype ((R m).signer b).Y] in
/-- **The distance of the two signers' loops of every ring is at most the bound.** -/
theorem tvDist_le_familyBound (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : ∀ m, 0 < (R m).wts.mass)
    (m : M) (G : K × V → C) :
    tvDist (untilSome ((R m).attempt false G)) (untilSome ((R m).attempt true G)) ≤
      familyBound R θ G := by
  refine ((R m).tvDist_untilSome_le θ hθ0 (hμ m) G).trans ?_
  have h1 : (R m).dev false G / famDen R θ m false + (R m).dev true G / famDen R θ m true ≤
      Finset.univ.sup' Finset.univ_nonempty (fun m => famDev R θ m G) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun m => famDev R θ m G) (Finset.mem_univ m))
    simp only [famDev, Fintype.sum_bool]
    ring
  have h2 : (if (R m).massAt G < θ * (R m).wts.mass then (1 : ℝ) else 0) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun o => famShort R θ o G) := by
    refine ((R m).ite_massAt_lt_le θ hθ1 (hμ m) G).trans (max_le ?_ ?_)
    · exact le_trans (le_of_eq rfl)
        (Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ none))
    · exact Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ (some m))
  unfold famDen at h1
  unfold familyBound
  linarith

omit [∀ m b, Fintype ((R m).signer b).Y] in
/-- **A signer that never keeps makes the bound at least one**: its deviation is `β` times the
total ring weight. -/
theorem one_le_familyBound_of_never (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : ∀ m, 0 < (R m).wts.mass)
    (m : M) (b : Bool) (G : K × V → C) (hb : (R m).attempt b G none = 1) :
    1 ≤ familyBound R θ G := by
  have hden : ∀ b, 0 < famDen R θ m b := fun b =>
    mul_pos ((R m).signer b).hβ (mul_pos hθ0 (hμ m))
  have hdev0 : ∀ b, 0 ≤ (R m).dev b G := fun b =>
    Finset.sum_nonneg fun v _ => abs_nonneg _
  have hdev : (R m).dev b G = ((R m).signer b).β * (R m).massAt G := by
    have hz := apply_some_eq_zero_of_apply_none_eq_one hb
    unfold RingPair.attempt at hz
    unfold RingPair.dev weightedDev RingPair.massAt RingWeights.weightMass
    simp only [hz, ENNReal.toReal_zero, zero_sub, abs_neg]
    rw [Finset.sum_congr rfl fun v _ => abs_of_nonneg (mul_nonneg ((R m).signer b).hβ.le
      ENNReal.toReal_nonneg), Finset.mul_sum]
  have hDev : (R m).dev b G / famDen R θ m b ≤ famDev R θ m G := by
    unfold famDev
    exact Finset.single_le_sum (f := fun b => (R m).dev b G / famDen R θ m b)
      (fun b _ => div_nonneg (hdev0 b) (hden b).le) (Finset.mem_univ b)
  have hsupD := Finset.le_sup' (fun m => famDev R θ m G) (Finset.mem_univ m)
  have hsupS0 : famShort R θ none G ≤ _ :=
    Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ none)
  have hsupS : famShort R θ (some m) G ≤ _ :=
    Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ (some m))
  have e0 : famShort R θ none G = 0 := rfl
  have e1 : famShort R θ (some m) G =
      ((R m).wts.mass - (R m).massAt G) / ((1 - θ) * (R m).wts.mass) := rfl
  rw [e0] at hsupS0
  rw [e1] at hsupS
  unfold familyBound
  by_cases hS : θ * (R m).wts.mass ≤ (R m).massAt G
  · -- enough total weight: the deviation term is at least one
    have : 1 ≤ (R m).dev b G / famDen R θ m b := by
      rw [one_le_div (hden b), hdev, famDen]
      exact mul_le_mul_of_nonneg_left hS ((R m).signer b).hβ.le
    linarith
  · -- too little: the shortfall term is at least one
    rw [not_le] at hS
    have hpos : 0 < (1 - θ) * (R m).wts.mass := mul_pos (by linarith) (hμ m)
    have : 1 ≤ ((R m).wts.mass - (R m).massAt G) / ((1 - θ) * (R m).wts.mass) := by
      rw [one_le_div hpos]; linarith
    have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun m => famDev R θ m G) :=
      le_trans (div_nonneg (hdev0 b) (hden b).le) (hDev.trans hsupD)
    linarith

omit [∀ m b, Fintype ((R m).signer b).Y] in
/-- **The bound is nonnegative.** -/
theorem familyBound_nonneg (hθ0 : 0 < θ) (hμ : ∀ m, 0 < (R m).wts.mass) (G : K × V → C) :
    0 ≤ familyBound R θ G := by
  have hdev : 0 ≤ famDev R θ (Classical.arbitrary M) G :=
    Finset.sum_nonneg fun b _ => div_nonneg (Finset.sum_nonneg fun v _ => abs_nonneg _)
      (mul_pos ((R _).signer b).hβ (mul_pos hθ0 (hμ _))).le
  have h1 := Finset.le_sup' (fun m => famDev R θ m G) (Finset.mem_univ (Classical.arbitrary M))
  have h2 := Finset.le_sup' (fun o => famShort R θ o G) (Finset.mem_univ none)
  have e0 : famShort R θ none G = 0 := rfl
  simp only [e0] at h2
  unfold familyBound
  linarith

/-- **The expected bound over many rings inside one uniform oracle**: for rings `R m` with
positive ring masses, errors at most `e`, and variance proxies at most `sd` and `sc` at the
threshold fraction `θ ∈ (0, 1)`, the oracle-average of the bound is at most
`e + √(sd · log |M| / 2) + √(sc · log (|M| + 1) / 2)` (McDiarmid's inequality for the deviations
and the total ring weights, `expect_sup'_le_of_boundedDiff`). -/
theorem expect_familyBound_le (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : ∀ m, 0 < (R m).wts.mass)
    {e sd sc : ℝ} (he : ∀ m, (R m).error θ ≤ e) (hsd : ∀ m, (R m).devVar θ ≤ sd)
    (hsc : ∀ m, (R m).countVar θ ≤ sc) :
    𝔼 G : K × V → C, familyBound R θ G ≤
      e + √(sd * Real.log (Fintype.card M) / 2) + √(sc * Real.log (Fintype.card M + 1) / 2) := by
  classical
  set den : M → Bool → ℝ := famDen R θ
  have hden : ∀ m b, 0 < den m b := fun m b => mul_pos ((R m).signer b).hβ (mul_pos hθ0 (hμ m))
  set Z : M → (K × V → C) → ℝ := famDev R θ
  set W : Option M → (K × V → C) → ℝ := famShort R θ
  unfold familyBound
  rw [Finset.expect_add_distrib]
  refine add_le_add ?_ ?_
  -- the deviations
  · refine expect_sup'_le_of_boundedDiff Z
      (fun m x => if x.1 ∈ Set.range (R m).pt then
        ∑ b : Bool, ((((R m).signer b).P.map ((R m).signer b).w1 x.2).toReal +
          ((R m).signer b).β) / den m b else 0) ?_ ?_ ?_
    · rintro m G ⟨k, v⟩ ω
      simp only [Z, famDev]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ b : Bool, |(R m).dev b (Function.update G (k, v) ω) / den m b -
          (R m).dev b G / den m b| ≤ if k ∈ Set.range (R m).pt then
            ((((R m).signer b).P.map ((R m).signer b).w1 v).toReal + ((R m).signer b).β) / den m b
            else 0 := fun b => by
        rw [← sub_div, abs_div, abs_of_pos (hden m b)]
        have := abs_weightedDev_update_le (R m).pt (R m).wts ((R m).pos b) ((R m).signer b).P
          ((R m).signer b).w1 ((R m).signer b).acc ((R m).signer b).κ ((R m).signer b).hκ
          ((R m).signer b).hβ.le G k v ω
        split_ifs at this ⊢ with hk
        · exact div_le_div_of_nonneg_right this (hden m b).le
        · rw [div_le_iff₀ (hden m b), zero_mul]; exact this
      refine (Finset.sum_le_sum fun b _ => hb b).trans_eq ?_
      split_ifs <;> simp
    · intro m
      simp only [Z, famDev]
      rw [Finset.expect_sum_comm]
      refine le_of_eq_of_le ?_ (he m)
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.expect_div]
      simp only [RingPair.dev]
      rw [expect_ringOf (R m).pt (R m).pt.injective (fun H => weightedDev (R m).wts ((R m).pos b)
        ((R m).signer b).P ((R m).signer b).w1 ((R m).signer b).acc ((R m).signer b).κ
        ((R m).signer b).hκ ((R m).signer b).β H), expect_weightedDev]
      rfl
    · intro m
      refine le_of_eq_of_le ?_ (hsd m)
      rw [(R m).sum_sq_ite_mem_range (fun v => ∑ b : Bool, ((((R m).signer b).P.map
        ((R m).signer b).w1 v).toReal + ((R m).signer b).β) / den m b)]
      rfl
  -- the total ring weights
  · have hW := expect_sup'_le_of_boundedDiff W
      (fun o x => o.elim 0 fun m => if x.1 ∈ Set.range (R m).pt then
        1 / ((1 - θ) * (R m).wts.mass) else 0) (μ := 0) (s := sc) ?_ ?_ ?_
    · rw [zero_add, Fintype.card_option] at hW
      push_cast at hW
      exact hW
    · rintro (_ | m) G ⟨k, v⟩ ω
      · simp [W, famShort]
      · simp only [W, famShort, Option.elim]
        have hc := abs_weightMass_update_le (R m).pt (R m).wts G k v ω
        have hpos : 0 < (1 - θ) * (R m).wts.mass := mul_pos (by linarith) (hμ m)
        rw [← sub_div, abs_div, abs_of_pos hpos]
        have : (R m).wts.mass - (R m).massAt (Function.update G (k, v) ω) -
            ((R m).wts.mass - (R m).massAt G) =
            -((R m).massAt (Function.update G (k, v) ω) - (R m).massAt G) := by ring
        rw [this, abs_neg]
        split_ifs at hc ⊢
        · rw [div_le_div_iff_of_pos_right hpos]; exact hc
        · rw [div_le_iff₀ hpos, zero_mul]; exact hc
    · rintro (_ | m)
      · simp [W, famShort]
      · simp only [W, famShort, Option.elim]
        rw [← Finset.expect_div, Finset.expect_sub_distrib, Fintype.expect_const]
        simp only [RingPair.massAt]
        rw [expect_ringOf (R m).pt (R m).pt.injective (fun H => (R m).wts.weightMass H),
          RingWeights.expect_weightMass]
        simp
    · rintro (_ | m)
      · simp only [Option.elim]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, Finset.sum_const_zero]
        exact le_trans (by
          unfold RingPair.countVar
          positivity) (hsc (Classical.arbitrary M))
      · refine le_of_eq_of_le ?_ (hsc m)
        simp only [Option.elim]
        rw [(R m).sum_sq_ite_mem_range (fun _ => 1 / ((1 - θ) * (R m).wts.mass)),
          RingPair.countVar, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **The expected largest distance between the two signers' loops over many rings inside one
uniform oracle** (`tvDist_le_familyBound`, `expect_familyBound_le`). -/
theorem expect_sup'_tvDist_untilSome_le (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hμ : ∀ m, 0 < (R m).wts.mass)
    {e sd sc : ℝ} (he : ∀ m, (R m).error θ ≤ e) (hsd : ∀ m, (R m).devVar θ ≤ sd)
    (hsc : ∀ m, (R m).countVar θ ≤ sc) :
    𝔼 G : K × V → C, Finset.univ.sup' Finset.univ_nonempty (fun m =>
        tvDist (untilSome ((R m).attempt false G)) (untilSome ((R m).attempt true G))) ≤
      e + √(sd * Real.log (Fintype.card M) / 2) + √(sc * Real.log (Fintype.card M + 1) / 2) :=
  (Finset.expect_le_expect fun G _ => Finset.sup'_le _ _ fun m _ =>
    tvDist_le_familyBound hθ0 hθ1 hμ m G).trans (expect_familyBound_le hθ0 hθ1 hμ he hsd hsc)

end Family

/-! ### Admissible rings -/

section Admissible

/-- **The Weierstrass product inequality**: for `m_j ∈ [0, 1]`,
`1 - ∑_j (1 - m_j) ≤ ∏_j m_j`. -/
theorem _root_.Finset.one_sub_sum_le_prod {ι : Type*} (t : Finset ι) {m : ι → ℝ}
    (h0 : ∀ j ∈ t, 0 ≤ m j) (h1 : ∀ j ∈ t, m j ≤ 1) :
    1 - ∑ j ∈ t, (1 - m j) ≤ ∏ j ∈ t, m j := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    have hP1 : ∏ j ∈ t, m j ≤ 1 := Finset.prod_le_one₀ (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    have ha0 := h0 a (Finset.mem_insert_self a t)
    have ha1 := h1 a (Finset.mem_insert_self a t)
    nlinarith

namespace RingWeights

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype C] [DecidableEq C] [Nonempty C] (s : RingWeights N V C)

/-- **The mass ratio** of a ring, `max_v colMass v / min_v colMass v`: how far the mean ring
weights of the columns are from flat. A ring is admissible at `κ` when every column mass is
positive and the ratio is at most `κ`. -/
noncomputable def massRatio : ℝ :=
  univ.sup' univ_nonempty s.colMass / univ.inf' univ_nonempty s.colMass

/-- **The other members' mean weights against the column masses**: for a ring with positive
column masses and mass ratio at most `κ`, `∑_v (∏_{j ≠ i} 𝔼 wt j) · d v` is at most
`κ · (mass / |V|) · ∑_v d v / 𝔼 wt i`, for every nonnegative `d`. -/
theorem sum_prod_erase_mul_le (i : N) (hpos : ∀ v, 0 < s.colMass v) {κ : ℝ}
    (hκ : s.massRatio ≤ κ) (d : V → ℝ) (hd : ∀ v, 0 ≤ d v) :
    ∑ v, (∏ j ∈ univ.erase i, s.meanWeight j v) * d v ≤
      κ * (s.mass / Fintype.card V) * ∑ v, d v / s.meanWeight i v := by
  set Mx := univ.sup' univ_nonempty s.colMass
  set mn := univ.inf' univ_nonempty s.colMass
  have hmn : 0 < mn := by
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_inf' univ_nonempty s.colMass
    have hv' : mn = s.colMass v := hv
    rw [hv']; exact hpos v
  have hai : ∀ v, 0 < s.meanWeight i v := fun v => by
    refine lt_of_le_of_ne (s.meanWeight_nonneg i v) fun h => ?_
    have := hpos v
    rw [colMass, ← Finset.mul_prod_erase univ _ (mem_univ i), ← h, zero_mul] at this
    exact lt_irrefl _ this
  have hterm : ∀ v, (∏ j ∈ univ.erase i, s.meanWeight j v) * d v =
      s.colMass v * (d v / s.meanWeight i v) := fun v => by
    rw [colMass, ← Finset.mul_prod_erase univ _ (mem_univ i)]
    field_simp [(hai v).ne']
  have hMx : Mx ≤ κ * mn := by
    have : Mx = s.massRatio * mn := by rw [massRatio, div_mul_cancel₀ _ hmn.ne']
    rw [this]; exact mul_le_mul_of_nonneg_right hκ hmn.le
  have hmn_avg : mn ≤ s.mass / Fintype.card V := by
    have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    rw [le_div_iff₀ hc, mass, mul_comm]
    have := Finset.card_nsmul_le_sum univ s.colMass mn fun v _ => Finset.inf'_le _ (mem_univ v)
    simpa [Finset.card_univ, nsmul_eq_mul] using this
  have hκ0 : 0 ≤ κ := by
    have hr : 0 ≤ s.massRatio :=
      div_nonneg ((s.colMass_nonneg _).trans (Finset.le_sup' s.colMass (mem_univ
        (Classical.arbitrary V)))) hmn.le
    linarith
  simp only [hterm]
  calc ∑ v, s.colMass v * (d v / s.meanWeight i v)
      ≤ ∑ v, Mx * (d v / s.meanWeight i v) := Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_right (Finset.le_sup' s.colMass (mem_univ v))
          (div_nonneg (hd v) (hai v).le)
    _ = Mx * ∑ v, d v / s.meanWeight i v := by rw [Finset.mul_sum]
    _ ≤ κ * (s.mass / Fintype.card V) * ∑ v, d v / s.meanWeight i v := by
        refine mul_le_mul_of_nonneg_right (hMx.trans
          (mul_le_mul_of_nonneg_left hmn_avg hκ0)) ?_
        exact Finset.sum_nonneg fun v _ => div_nonneg (hd v) (hai v).le

/-- A ring with positive column masses has positive mass. -/
theorem mass_pos (hpos : ∀ v, 0 < s.colMass v) : 0 < s.mass :=
  Finset.sum_pos (fun v _ => hpos v) univ_nonempty

omit [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq C] in
/-- A mean weight is at most one. -/
theorem meanWeight_le_one (j : N) (v : V) : s.meanWeight j v ≤ 1 :=
  (Finset.expect_le_expect fun _ _ => ENNReal.toReal_le_one_of_le_one (s.wt_le_one j _)).trans_eq
    (Finset.expect_const univ_nonempty 1)

/-- A column mass is at most one. -/
theorem colMass_le_one (v : V) : s.colMass v ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => s.meanWeight_nonneg j v) fun j _ => s.meanWeight_le_one j v

/-- **The column masses from the members' defects**: if member `j`'s mean weight is at least
`1 - δ_j` in every column and `∑_j δ_j ≤ σ`, every column mass is at least `1 - σ`
(`Finset.one_sub_sum_le_prod`). -/
theorem one_sub_le_colMass {δ : N → ℝ} {σ : ℝ} (hδ : ∀ j v, 1 - δ j ≤ s.meanWeight j v)
    (hσ : ∑ j, δ j ≤ σ) (v : V) : 1 - σ ≤ s.colMass v := by
  have h : ∑ j, (1 - s.meanWeight j v) ≤ ∑ j, δ j :=
    Finset.sum_le_sum fun j _ => by linarith [hδ j v]
  have hW := Finset.one_sub_sum_le_prod univ (m := fun j => s.meanWeight j v)
    (fun j _ => s.meanWeight_nonneg j v) fun j _ => s.meanWeight_le_one j v
  unfold colMass
  linarith

/-- **The mass from a lower bound on the column masses**: if every column mass is at least `m`,
the mass is at least `m · |V|`. -/
theorem mul_card_le_mass {m : ℝ} (h : ∀ v, m ≤ s.colMass v) : m * Fintype.card V ≤ s.mass := by
  have := Finset.card_nsmul_le_sum univ s.colMass m fun v _ => h v
  rw [Finset.card_univ, nsmul_eq_mul] at this
  rw [mass, mul_comm]
  exact this

/-- **The mass ratio from the members' defects**: under `one_sub_le_colMass` with `σ < 1`,
the mass ratio is at most `1 / (1 - σ)`. -/
theorem massRatio_le_inv_one_sub {δ : N → ℝ} {σ : ℝ} (hδ : ∀ j v, 1 - δ j ≤ s.meanWeight j v)
    (hσ : ∑ j, δ j ≤ σ) (hσ1 : σ < 1) : s.massRatio ≤ (1 - σ)⁻¹ := by
  rw [massRatio, ← one_div]
  exact div_le_div₀ zero_le_one (Finset.sup'_le _ _ fun v _ => s.colMass_le_one v)
    (by linarith) (Finset.le_inf' _ _ fun v _ => s.one_sub_le_colMass hδ hσ v)

end RingWeights

/-- **The error of an admissible ring**: with positive column masses and mass ratio at most `κ`,
the ring error at the threshold fraction `θ` is at most `κ / θ` times the sum of the two signers'
relative column errors. -/
theorem RingPair.error_le_of_massRatio_le {K V C : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype C] [DecidableEq C] [Nonempty C] (R : RingPair K V C) [Fintype R.Mem]
    [DecidableEq R.Mem] [∀ b, Fintype (R.signer b).Y] {θ : ℝ}
    (hθ : 0 < θ) (hpos : ∀ v, 0 < R.wts.colMass v) {κ : ℝ} (hκ : R.wts.massRatio ≤ κ) :
    R.error θ ≤ κ / θ * ∑ b : Bool, relColError R.wts (R.pos b) (R.signer b).P
      (R.signer b).w1 (R.signer b).acc (R.signer b).κ (R.signer b).β := by
  unfold RingPair.error
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have hμ := R.wts.mass_pos hpos
  have hβ := (R.signer b).hβ
  have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have h := R.wts.sum_prod_erase_mul_le (R.pos b) hpos hκ _ fun v => colError_nonneg R.wts
    (R.pos b) (R.signer b).P (R.signer b).w1 (R.signer b).acc (R.signer b).κ (R.signer b).β v
  rw [div_le_iff₀ (mul_pos hβ (mul_pos hθ hμ))]
  refine h.trans (le_of_eq ?_)
  rw [relColError_eq]
  field_simp

end Admissible

/-! ### The loop with its output -/

section Output

/-- An accepted value of the unbounded loop is an accepted value of one attempt. -/
theorem apply_some_ne_zero_of_untilSome {α : Type*} [Fintype α] {A : PMF (Option α)} {a : α}
    (h : untilSome A (some a) ≠ 0) : A (some a) ≠ 0 := by
  rw [untilSome_apply_some] at h
  intro h0; apply h; rw [h0, ENNReal.zero_div]

/-- An output of the unbounded loop is an output of one attempt. -/
theorem mem_support_of_mem_support_untilSome {α : Type*} [Fintype α] {A : PMF (Option α)}
    {a : α} (h : some a ∈ (untilSome A).support) : some a ∈ A.support :=
  (mem_support_iff _ _).2 (apply_some_ne_zero_of_untilSome ((mem_support_iff _ _).1 h))

/-- **Relabelling the accepted values commutes with the unbounded loop.** -/
theorem untilSome_map_optionMap {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : PMF (Option α)) (f : α → β) :
    (untilSome A).map (Option.map f) = untilSome (A.map (Option.map f)) := by
  classical
  have hnone : A.map (Option.map f) none = A none := by
    rw [map_apply, tsum_fintype, Fintype.sum_option]
    simp
  by_cases hA : A none = 1
  · have hA' : A.map (Option.map f) none = 1 := hnone.trans hA
    unfold untilSome
    rw [dif_pos hA, dif_pos hA', pure_map]
    rfl
  · ext o
    cases o with
    | none =>
      have h1 : (untilSome A).map (Option.map f) none = 0 := by
        rw [map_apply]
        refine ENNReal.tsum_eq_zero.2 fun o => ?_
        cases o with
        | none =>
          unfold untilSome; rw [dif_neg hA, map_apply]
          simp
        | some a => simp
      have h2 : untilSome (A.map (Option.map f)) none = 0 := by
        unfold untilSome; rw [dif_neg (hnone ▸ hA), map_apply]; simp
      rw [h1, h2]
    | some b =>
      rw [untilSome_apply_some, hnone, map_apply, map_apply, tsum_fintype, tsum_fintype,
        Fintype.sum_option, Fintype.sum_option]
      simp only [Option.map_none, reduceCtorEq, if_false, zero_add, Option.map_some,
        Option.some.injEq]
      rw [ENNReal.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp [untilSome_apply_some]

variable {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype C]
  [DecidableEq C] (s : RingWeights N V C) (i : N) {Y : Type*} [Fintype Y] (P : PMF Y)
  (w1 : Y → V) (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞)
  (hκ : ∀ a, κ a ≤ 1) {S : Type*} (out : Y → C → S)

/-- **The weighted attempt with its output**: as `weightedAttempt`, outputting with the kept
`w1 y` the value `out y c` of the proposal and the signer's value `c = H (i, w1 y)`. -/
noncomputable def weightedAttemptWith (H : N × V → C) : PMF (Option (V × S)) :=
  P.bind fun y =>
    if acc y (H (i, w1 y)) = true then
      (keepOrReject (w1 y) (κ (w1 y, H (i, w1 y)) * s.otherWeight i H (w1 y))
        (keepWeight_le_one s i κ hκ H (w1 y))).map (Option.map fun v => (v, out y (H (i, w1 y))))
    else pure none

/-- Forgetting the output gives the weighted attempt. -/
theorem map_weightedAttemptWith (H : N × V → C) :
    (weightedAttemptWith s i P w1 acc κ hκ out H).map (Option.map Prod.fst) =
      weightedAttempt s i P w1 acc κ hκ H := by
  rw [weightedAttemptWith, weightedAttempt, map_bind]
  congr 1
  funext y
  split_ifs
  · rw [map_comp]
    have : (Option.map Prod.fst ∘ Option.map fun v : V => (v, out y (H (i, w1 y)))) = id := by
      funext o; cases o <;> rfl
    rw [this, map_id]
  · rw [pure_map]; rfl

/-- **Every output of the weighted attempt with its output** is the output of an accepted
proposal. -/
theorem exists_of_mem_support_weightedAttemptWith (H : N × V → C) {v : V} {σ : S}
    (h : some (v, σ) ∈ (weightedAttemptWith s i P w1 acc κ hκ out H).support) :
    ∃ y, w1 y = v ∧ acc y (H (i, v)) = true ∧ σ = out y (H (i, v)) := by
  rw [weightedAttemptWith, mem_support_bind_iff] at h
  obtain ⟨y, -, hy⟩ := h
  split_ifs at hy with hacc
  · rw [mem_support_map_iff] at hy
    obtain ⟨o, ho, hoe⟩ := hy
    cases o with
    | none => simp at hoe
    | some v' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoe
      obtain ⟨rfl, rfl⟩ := hoe
      have hv : v' = w1 y := by
        rw [mem_support_iff, keepOrReject_apply_some] at ho
        by_contra hne; exact ho (if_neg hne)
      subst hv
      exact ⟨y, rfl, hacc, rfl⟩
  · simp at hy

end Output

end PMF
