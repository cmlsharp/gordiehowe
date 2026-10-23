-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.CircuitPad
public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.Model.Quantum.O2H.CountOn
public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Model.QROM.QueryBoundedRun
public import GordieHowe.Model.ROM.AdaptiveCompleteness

@[expose] public section

/-!
# Adaptive completeness of a salted argument in the quantum random-oracle model

Unruh 2017 (ePrint 2017/398), Definition 5, p. 14: "for any polynomial-time oracle algorithm `A`
there is a negligible `µ` such that `Pr[(x, w) ∈ R ∧ V^H(1^η, x, π) = 0 : H ←$ Fun,
(x, w) ← A^H(1^η), π ← P^H(1^η, x, w)] ≤ µ(η)`". The adversary chooses the statement and witness
after querying the oracle; here it is a query-bounded adversary of the paper's
`def:adversary` (`Quantum.QueryBoundedAdversary`) without proof queries, with at most `t` queries
on every branch.

The argument is salted: `saltOf x` is the salt in the slot of the oracle input `x` (or `none`),
and the honest prover draws uniform coins `r` and a uniform salt `σ` after the adversary. The
one-proof hypothesis is the **fresh-slice bound** of `GordieHowe/Model/ROM/AdaptiveCompleteness.lean`: for
every salt `σ`, oracle `g` and output `o`, the event `Bad r σ H o` (`o` is a pair in the relation
and the honest proof with coins `r` and salt `σ` is rejected with the oracle `H`) has probability
at most `δ` over uniform coins `r` when the inputs of salt `σ` are answered by a fresh uniform
function and all other inputs by `g`.

**The theorem** (`QueryBoundedAdversary.adaptiveCompleteness_coins`): over the auxiliary input,
uniform coins, a uniform salt and a uniform oracle, the adversary outputs `o` with `Bad r σ H o`
with probability at most `δ + 2 t / √|Sd|`.

**The argument** (our statement; O2H for a fresh secret with a per-branch count, AHU19 Theorem 3
and Lemma 8, pp. 11–12 and 26–27). Draw a fresh function `F` besides `σ` and `H`, and let
`H' = replaceSlice saltOf σ H F`.
1. (O2H, `2 t / √|Sd|`) The adversary's runs against `H` and against `H'` differ, at each query
   step, only on the branches that query an input of salt `σ` and are not padded. The pure form
   of the adversary counts its unpadded queries on every branch (`AdaptiveIAlg.tpQueryCount`), and
   its padded queries act as the identity against every oracle (`AdaptiveIAlg.tpRealPad`), so the
   hybrid with a per-branch count (`OracleAlg.StepCountOn.norm_final_sub_le`) bounds the distance
   of the final states by `2 √t √(∑ i, Pr[query i unpadded and of salt σ])`. The run against `H`
   does not read `σ`, so averaging over `σ` gives at most `t / |Sd|` under the root
   (`sum_abs_prob_sub_le`).
2. (exact) The exchange of the slices of `σ` of `H` and `F` (`ROM.sliceSwap`) preserves the
   uniform law; after it, the adversary runs against `H` and the event is evaluated at `H` with
   the slice of `σ` answered by the fresh `F`, where the fresh-slice bound applies.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

open GordieHowe.Quantum GordieHowe.IOP GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B)

/-! ### The output law of a pure algorithm as a Born probability -/

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] [AddGroup Y] {t : ℕ} (A : GordieHowe.Quantum.QueryAlg X Y t O)

/-- **The probability of an output event** is the Born probability of its preimage in the final
state. -/
theorem toOuterMeasure_outLaw (f : X → Y) (E : Set O) :
    (A.outLaw f).toOuterMeasure E = ENNReal.ofReal (prob {r | A.out r.1 ∈ E} (A.final f)) := by
  classical
  rw [GordieHowe.Quantum.QueryAlg.outLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply,
    tsum_fintype, prob, norm_mask_sq, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : A.out r.1 ∈ E
  · simp [h, Set.indicator, born, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  · simp [h, Set.indicator]

end QueryAlg

/-! ### The per-branch count on the run's supports -/

namespace QueryCount

variable {W O : Type} {t b : ℕ} {A : GordieHowe.Quantum.QueryAlg (Bits m) (BitStr I J) t O}

/-- **A per-branch query count is a count on the run's supports** (`OracleAlg.StepCountOn`): the
records and supports of the count, read on the work register. -/
theorem stepCountOn (qc : QueryCount e A b) :
    (A.toOracleAlg ∅).StepCountOn () (fun k => {r | r.1 ∈ qc.G k}) (fun i => {r | r.1 ∈ qc.C i})
      b where
  init := qc.init
  stepG k hk v hv := qc.stepG k hk v hv
  stepC i k hik hk v hv := qc.stepC i k hik hk v hv
  stepCc i k hik hk v hv := qc.stepCc i k hik hk v hv
  count r hr := by
    classical
    have h := qc.count t le_rfl r.1 hr
    rw [min_eq_right (Nat.le_succ t)] at h
    unfold countBelow at h
    convert h using 3
    exact Iff.rfl

end QueryCount

/-! ### O2H for a fresh salt with a per-branch count -/

section FreshSalt

variable {Sd : Type} [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] (saltOf : Bits m → Option Sd)

/-- The inputs whose salt slot holds `σ`. -/
def saltSet (σ : Sd) : Set (Bits m) := {x | saltOf x = some σ}

omit [DecidableEq Sd] in
/-- **A tuple of query inputs carries a uniform salt with probability at most `1 / |Sd|`.** -/
theorem toReal_uniform_saltSet_le (q : Fin 1 → Bits m) :
    ((PMF.uniformOfFintype Sd).toOuterMeasure {σ | ∃ j, q j ∈ saltSet saltOf σ}).toReal ≤
      (Fintype.card Sd : ℝ)⁻¹ := by
  classical
  have hle : (PMF.uniformOfFintype Sd).toOuterMeasure {σ | ∃ j, q j ∈ saltSet saltOf σ} ≤
      ((saltOf (q 0)).toFinset.card : ℝ≥0∞) / Fintype.card Sd :=
    probUniform_le_card_div (Y := Sd) ((saltOf (q 0)).toFinset) fun σ ⟨j, hj⟩ => by
      rw [Subsingleton.elim j 0] at hj
      simp only [saltSet, Set.mem_ofPred_eq] at hj
      simp [hj]
  have hcard : ((saltOf (q 0)).toFinset.card : ℝ≥0∞) ≤ 1 := by
    cases saltOf (q 0) <;> simp
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hle.trans ?_)
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast,
    ENNReal.div_eq_inv_mul]
  calc (Fintype.card Sd : ℝ≥0∞)⁻¹ * ((saltOf (q 0)).toFinset.card : ℝ≥0∞)
      ≤ (Fintype.card Sd : ℝ≥0∞)⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

variable {O : Type} {t b : ℕ} (A : GordieHowe.Quantum.QueryAlg (Bits m) (BitStr I J) t O)

/-- **The run against `H` and against `H` with the slice of `σ` replaced are close on average
over `σ`** (module docstring, step 1): for a pure algorithm with a per-branch count `qc` whose
padded queries act as the identity in its real runs (`hpad`), and every output event `E`, the
`σ`-average of the difference of the probabilities of `E` is at most `2 b / √|Sd|`. -/
theorem sum_abs_prob_sub_le (qc : QueryCount e A b)
    (hpad : ∀ (H H' : Bits m → BitStr I J) (k : ℕ), k < t →
      permOp (queryPerm H') (mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k)) =
        mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k))
    (H F : Bits m → BitStr I J) (E : Sd → Set O) :
    ∑ σ, (Fintype.card Sd : ℝ)⁻¹ * |prob {r | A.out r.1 ∈ E σ} (A.final H) -
        prob {r | A.out r.1 ∈ E σ} (A.final (replaceSlice saltOf σ H F))| ≤
      2 * b / √(Fintype.card Sd : ℝ) := by
  classical
  set u : ℝ := (Fintype.card Sd : ℝ)
  have hu : 0 < u := by simp only [u]; exact_mod_cast Fintype.card_pos
  set G : ℕ → Set (QueryReg A.W 1 (Bits m) (BitStr I J)) := fun k => {r | r.1 ∈ qc.G k}
  set C : ℕ → Set (QueryReg A.W 1 (Bits m) (BitStr I J)) := fun i => {r | r.1 ∈ qc.C i}
  have hsc := qc.stepCountOn e
  have hresp : ∀ K : Bits m → BitStr I J, OracleAlg.Respects (queryPerm (n := 1) K) G C := fun K => by
    have := respects_queryPermOf (n := 1) (fun _ : A.W => K) qc.G qc.C
    rwa [queryPermOf_const] at this
  set ψ : Fin t → QState (QueryReg A.W 1 (Bits m) (BitStr I J)) := fun i =>
    mask (C i) ((A.toOracleAlg ∅).pre (queryPerm H) () i)
  -- the distance at one salt
  have hpoint : ∀ σ, |prob {r | A.out r.1 ∈ E σ} (A.final H) -
      prob {r | A.out r.1 ∈ E σ} (A.final (replaceSlice saltOf σ H F))| ≤
      2 * √b * √(∑ i : Fin t, prob (queried (saltSet saltOf σ)) (ψ i)) := by
    intro σ
    refine (abs_prob_sub_le _ (A.norm_final _) (A.norm_final _)).trans ?_
    refine hsc.norm_final_sub_le (hresp H) (hresp _) (B := queried (saltSet saltOf σ))
      (fun r hr => ?_) (fun k hk => ?_)
    · rw [queryPerm_apply, queryPerm_apply]
      congr 1
      funext j
      have hj : (r.2 j).1 ∉ saltSet saltOf σ := fun h => hr ⟨j, h⟩
      have hj' : ¬ saltOf (r.2 j).1 = some σ := hj
      simp only [replaceSlice, hj', ite_false]
    · rw [hpad H H k hk, hpad H _ k hk]
  have hw : ∀ σ : Sd, 0 ≤ ((PMF.uniformOfFintype Sd) σ).toReal := fun _ => ENNReal.toReal_nonneg
  have hw1 : ∑ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal = 1 := (PMF.uniformOfFintype Sd).sum_toReal
  have hwu : ∀ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal = u⁻¹ := fun σ => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  -- the average over the salt of the queried probabilities
  have havg : ∑ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal *
      ∑ i : Fin t, prob (queried (saltSet saltOf σ)) (ψ i) ≤ u⁻¹ * b := by
    simp_rw [mul_sum]
    rw [sum_comm]
    calc ∑ i : Fin t, ∑ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal *
          prob (queried (saltSet saltOf σ)) (ψ i)
        ≤ ∑ i : Fin t, u⁻¹ * ‖ψ i‖ ^ 2 := sum_le_sum fun i _ =>
          sum_mul_prob_queried_le_mul_norm_sq (PMF.uniformOfFintype Sd) (saltSet saltOf) (ψ i)
            (toReal_uniform_saltSet_le saltOf)
      _ = u⁻¹ * ∑ i : Fin t, prob (C i) ((A.toOracleAlg ∅).pre (queryPerm H) () i) := by
          rw [mul_sum]
          rfl
      _ ≤ u⁻¹ * b := by
          gcongr
          exact hsc.sum_prob_pre_le (hresp H)
  have hg0 : ∀ σ : Sd, 0 ≤ ∑ i : Fin t, prob (queried (saltSet saltOf σ)) (ψ i) :=
    fun _ => sum_nonneg fun _ _ => prob_nonneg _ _
  calc ∑ σ, u⁻¹ * |prob {r | A.out r.1 ∈ E σ} (A.final H) -
          prob {r | A.out r.1 ∈ E σ} (A.final (replaceSlice saltOf σ H F))|
      ≤ ∑ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal *
          (2 * √b * √(∑ i : Fin t, prob (queried (saltSet saltOf σ)) (ψ i))) :=
        sum_le_sum fun σ _ => by
          rw [hwu]
          exact mul_le_mul_of_nonneg_left (hpoint σ) (by positivity)
    _ = 2 * √b * ∑ σ : Sd, ((PMF.uniformOfFintype Sd) σ).toReal *
          √(∑ i : Fin t, prob (queried (saltSet saltOf σ)) (ψ i)) := by
        rw [mul_sum]
        exact sum_congr rfl fun σ _ => by ring
    _ ≤ 2 * √b * √(u⁻¹ * b) := by
        gcongr
        exact (Real.sum_mul_sqrt_le_sqrt_sum_mul hw hw1 hg0).trans (Real.sqrt_le_sqrt havg)
    _ = 2 * b / √u := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_inv, mul_comm (√u)⁻¹, ← mul_assoc,
          mul_assoc 2 (√(b : ℝ)) (√(b : ℝ)), Real.mul_self_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]

/-- **An average of the probabilities of a family of events under one law**: if every outcome `o`
lies in the event `S F` with probability at most `δ` over a uniform `F`, then the `F`-average of
`μ (S F)` is at most `δ`. -/
theorem sum_inv_mul_toOuterMeasure_le {T O : Type} [Fintype T] [Nonempty T] (μ : PMF O)
    (S : T → Set O) {δ : ℝ≥0∞} (hS : ∀ o, Pr[F ← T : o ∈ S F] ≤ δ) :
    ∑ F, (Fintype.card T : ℝ≥0∞)⁻¹ * μ.toOuterMeasure (S F) ≤ δ := by
  classical
  have hpr : ∀ o, ∑ F, (Fintype.card T : ℝ≥0∞)⁻¹ * (S F).indicator μ o =
      μ o * Pr[F ← T : o ∈ S F] := fun o => by
    rw [probUniform_eq_card_div, ENNReal.div_eq_inv_mul, ← Finset.sum_boole, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h : o ∈ S F <;> simp [h, mul_comm]
  calc ∑ F, (Fintype.card T : ℝ≥0∞)⁻¹ * μ.toOuterMeasure (S F)
      = ∑ F, ∑' o, (Fintype.card T : ℝ≥0∞)⁻¹ * (S F).indicator μ o := by
        simp only [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_left]
    _ = ∑' o, ∑ F, (Fintype.card T : ℝ≥0∞)⁻¹ * (S F).indicator μ o :=
        (Summable.tsum_finsetSum fun _ _ => ENNReal.summable).symm
    _ = ∑' o, μ o * Pr[F ← T : o ∈ S F] := tsum_congr hpr
    _ ≤ ∑' o, μ o * δ := ENNReal.tsum_le_tsum fun o => by gcongr; exact hS o
    _ = δ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The fresh-slice reduction against a pure algorithm with a per-branch count** (module
docstring, steps 1 and 2): for a pure algorithm with a per-branch count `qc` of `b` unpadded
queries whose padded queries act as the identity in its real runs (`hpad`), over a uniform salt
`σ` and a uniform oracle `H` the algorithm's output `o` satisfies `Bad σ H o` with probability at
most that of `Bad σ (replaceSlice saltOf σ H F) o` for the output against `H` and a further
uniform `F`, plus `2 b / √|Sd|`. -/
theorem prob_bad_le_fresh_of_count (qc : QueryCount e A b)
    (hpad : ∀ (H H' : Bits m → BitStr I J) (k : ℕ), k < t →
      permOp (queryPerm H') (mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k)) =
        mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k))
    (Bad : Sd → (Bits m → BitStr I J) → O → Prop) :
    ∑ σ, (Fintype.card Sd : ℝ≥0∞)⁻¹ * ∑ H, (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ *
        (A.outLaw H).toOuterMeasure {o | Bad σ H o} ≤
      ∑ σ, (Fintype.card Sd : ℝ≥0∞)⁻¹ * ∑ H, (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ *
          ∑ F, (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ *
            (A.outLaw H).toOuterMeasure {o | Bad σ (replaceSlice saltOf σ H F) o} +
        ENNReal.ofReal (2 * b / √(Fintype.card Sd : ℝ)) := by
  classical
  set u : ℝ≥0∞ := (Fintype.card Sd : ℝ≥0∞)⁻¹
  set c : ℝ≥0∞ := (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹
  set ext : ℝ≥0∞ := ENNReal.ofReal (2 * b / √(Fintype.card Sd : ℝ))
  set rs : Sd → (Bits m → BitStr I J) → (Bits m → BitStr I J) → Bits m → BitStr I J :=
    fun σ H F => replaceSlice saltOf σ H F
  -- the real probabilities
  set R : Sd → (Bits m → BitStr I J) → (Bits m → BitStr I J) → ℝ := fun σ H K =>
    prob {r | A.out r.1 ∈ {o | Bad σ H o}} (A.final K)
  have hP : ∀ σ H K, (A.outLaw K).toOuterMeasure {o | Bad σ H o} = ENNReal.ofReal (R σ H K) :=
    fun σ H K => QueryAlg.toOuterMeasure_outLaw A K _
  have hc1 : ∑ _F : Bits m → BitStr I J, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  -- pointwise: the run against `H` is the run against `rs σ H F` up to the distance
  have hpt : ∀ σ H F, ENNReal.ofReal (R σ H H) ≤
      (A.outLaw (rs σ H F)).toOuterMeasure {o | Bad σ H o} +
        ENNReal.ofReal |R σ H H - R σ H (rs σ H F)| := fun σ H F => by
    rw [hP, ← ENNReal.ofReal_add (prob_nonneg _ _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := le_abs_self (R σ H H - R σ H (rs σ H F))
    linarith
  -- the exchange of the slices of `σ` of `H` and `F`
  have hswap : ∀ σ, ∑ H, c * ∑ F, c * (A.outLaw (rs σ H F)).toOuterMeasure {o | Bad σ H o} =
      ∑ H, c * ∑ F, c * (A.outLaw H).toOuterMeasure {o | Bad σ (rs σ H F) o} := by
    intro σ
    simp only [Finset.mul_sum, ← Finset.sum_product']
    rw [Finset.univ_product_univ, ← Equiv.sum_comp (ROM.sliceSwap saltOf σ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hh : replaceSlice saltOf σ (replaceSlice saltOf σ p.1 p.2) (replaceSlice saltOf σ p.2 p.1) =
        p.1 := ROM.replaceSlice_sliceSwap saltOf σ p
    simp only [ROM.sliceSwap, Equiv.coe_fn_mk, rs, hh]
  -- the distance part
  have hdist : ∀ H F, ∑ σ, u * ENNReal.ofReal |R σ H H - R σ H (rs σ H F)| ≤ ext := by
    intro H F
    have h := sum_abs_prob_sub_le e saltOf A qc hpad H F fun σ => {o | Bad σ H o}
    rw [show ext = ENNReal.ofReal (2 * b / √(Fintype.card Sd : ℝ)) from rfl]
    refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal h)
    rw [ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg (by positivity) (abs_nonneg _)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by exact_mod_cast
      Fintype.card_pos), ENNReal.ofReal_natCast]
  calc ∑ σ, u * ∑ H, c * (A.outLaw H).toOuterMeasure {o | Bad σ H o}
      = ∑ σ, u * ∑ H, c * ∑ F, c * ENNReal.ofReal (R σ H H) := by
        refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.sum_congr rfl fun H _ => ?_)
        rw [← Finset.sum_mul, hc1, one_mul, hP]
    _ ≤ ∑ σ, u * ∑ H, c * ∑ F, c * ((A.outLaw (rs σ H F)).toOuterMeasure {o | Bad σ H o} +
          ENNReal.ofReal |R σ H H - R σ H (rs σ H F)|) := by
        gcongr
        exact hpt _ _ _
    _ = ∑ σ, u * ∑ H, c * ∑ F, c * (A.outLaw (rs σ H F)).toOuterMeasure {o | Bad σ H o} +
          ∑ H, c * ∑ F, c * ∑ σ, u * ENNReal.ofReal |R σ H H - R σ H (rs σ H F)| := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun σ _ => ?_
        ring
    _ ≤ ∑ σ, u * ∑ H, c * ∑ F, c * (A.outLaw H).toOuterMeasure {o | Bad σ (rs σ H F) o} +
          ∑ H, c * ∑ F, c * ext := by
        refine add_le_add (Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hswap σ).le zero_le)
          (Finset.sum_le_sum fun H _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun F _ => mul_le_mul_of_nonneg_left (hdist H F) zero_le) zero_le)
    _ = _ := by
        have hin : ∑ _F : Bits m → BitStr I J, c * ext = ext := by
          rw [← Finset.sum_mul, hc1, one_mul]
        rw [hin, hin]

/-- A weighted sum over `r`, then `σ` and `h`, of extended nonnegative reals is the weighted sum
over `σ` and `h` of the weighted sum over `r`. -/
theorem sum_mul_sum_mul_sum_mul_comm {R S H : Type} [Fintype R] [Fintype S] [Fintype H]
    (a b c : ℝ≥0∞) (f : R → S → H → ℝ≥0∞) :
    ∑ r, a * ∑ σ, b * ∑ h, c * f r σ h = ∑ σ, b * ∑ h, c * ∑ r, a * f r σ h := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **Adaptive completeness with coins against a pure algorithm with a per-branch count**: for a
pure algorithm with a per-branch count `qc` of `b` unpadded queries whose padded queries act as
the identity in its real runs (`hpad`), and an event `Bad r σ H o` that reads uniform coins `r`
drawn independently of the oracle and the algorithm and has probability at most `δ` over the
coins and a fresh slice of `σ` at every salt, oracle and output (`hslice`), the algorithm's output
`o` satisfies `Bad r σ H o` with probability at most `δ + 2 b / √|Sd|` over uniform coins, a
uniform salt and a uniform oracle. -/
theorem prob_bad_coins_le_of_count (qc : QueryCount e A b)
    (hpad : ∀ (H H' : Bits m → BitStr I J) (k : ℕ), k < t →
      permOp (queryPerm H') (mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k)) =
        mask {r | r.1 ∈ qc.C k}ᶜ ((A.toOracleAlg ∅).stage (queryPerm H) () k))
    {R : Type} [Fintype R] [Nonempty R] {Bad : R → Sd → (Bits m → BitStr I J) → O → Prop}
    {δ : ℝ≥0∞}
    (hslice : ∀ σ g o,
      Pr[q ← R × (Bits m → BitStr I J) : Bad q.1 σ (replaceSlice saltOf σ g q.2) o] ≤ δ) :
    ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ σ, (Fintype.card Sd : ℝ≥0∞)⁻¹ *
        ∑ H, (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ *
          (A.outLaw H).toOuterMeasure {o | Bad r σ H o} ≤
      δ + ENNReal.ofReal (2 * b / √(Fintype.card Sd : ℝ)) := by
  classical
  set ρ : ℝ≥0∞ := (Fintype.card R : ℝ≥0∞)⁻¹
  set u : ℝ≥0∞ := (Fintype.card Sd : ℝ≥0∞)⁻¹
  set c : ℝ≥0∞ := (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹
  refine (ROM.sum_inv_card_mul_le_add fun r =>
    prob_bad_le_fresh_of_count e saltOf A qc hpad (Bad r)).trans (add_le_add ?_ le_rfl)
  have hρc : ρ * c = (Fintype.card (R × (Bits m → BitStr I J)) : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  rw [sum_mul_sum_mul_sum_mul_comm ρ u c (fun r σ H => ∑ F, c *
    (A.outLaw H).toOuterMeasure {o | Bad r σ (replaceSlice saltOf σ H F) o})]
  calc ∑ σ, u * ∑ H, c * ∑ r, ρ * ∑ F, c *
          (A.outLaw H).toOuterMeasure {o | Bad r σ (replaceSlice saltOf σ H F) o}
      ≤ ∑ σ, u * ∑ H, c * δ := by
        gcongr with σ _ H _
        have h := sum_inv_mul_toOuterMeasure_le (A.outLaw H)
          (fun q : R × (Bits m → BitStr I J) => {o | Bad q.1 σ (replaceSlice saltOf σ H q.2) o})
          fun o => hslice σ H o
        rw [Fintype.sum_prod_type] at h
        refine le_of_eq_of_le ?_ h
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum, ← hρc]
        refine Finset.sum_congr rfl fun F _ => ?_
        ring
    _ = δ := by
        have hc : ∑ _H : Bits m → BitStr I J, c * δ = δ := ROM.sum_inv_card_mul_const δ
        have hu : ∑ _σ : Sd, u * δ = δ := ROM.sum_inv_card_mul_const δ
        rw [hc, hu]

end FreshSalt

end GordieHowe.QROM

/-! ### Padded queries of the composition of an adversary -/

namespace GordieHowe.Quantum.AdaptiveIAlg

variable {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {B : Type}

/-- **The padded queries of the trace-preserving composition act as the identity in its real
runs**: before query `k`, the part of the real run against `H` outside the record of query `k` of
the per-branch count (`tpQueryCount`) is fixed by every oracle permutation
(`GordieHowe.QROM.compiled_realPad`). -/
theorem tpRealPad (e : GordieHowe.QROM.BitStr I J ≃ B)
    (A : AdaptiveIAlg (GordieHowe.QROM.Bits m) (GordieHowe.QROM.BitStr I J) Req Resp O)
    (Ch : Challenger (GordieHowe.QROM.Bits m) (GordieHowe.QROM.BitStr I J) Req Resp) {O' O'' : Type}
    (f : A.toKindAlg.CW Ch → O') (g : Option O' → O'') (H H' : GordieHowe.QROM.Bits m → GordieHowe.QROM.BitStr I J)
    {k : ℕ} (hk : k < (A.toTPKindAlg.composeBothOut Ch f).depth) :
    permOp (queryPerm H') (mask {r | r.1 ∈ (tpQueryCount e A Ch f g).C k}ᶜ
        ((((A.toTPKindAlg.composeBothOut Ch f).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stage
          (queryPerm H) () k)) =
      mask {r | r.1 ∈ (tpQueryCount e A Ch f g).C k}ᶜ
        ((((A.toTPKindAlg.composeBothOut Ch f).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stage
          (queryPerm H) () k) :=
  GordieHowe.QROM.compiled_realPad (A.valid_fullCircBoth Ch) (fun p hp => A.initSys_good Ch p hp) H H' hk

end GordieHowe.Quantum.AdaptiveIAlg

namespace GordieHowe.QROM

open GordieHowe.Quantum GordieHowe.IOP GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-! ### Adaptive completeness against query-bounded adversaries -/

namespace QueryBoundedAdversary

variable {Sd : Type} [Fintype Sd] [Nonempty Sd] [DecidableEq Sd] (saltOf : Bits m → Option Sd)
  {O : Type} {t : ℕ} (𝒢 : Quantum.QueryBoundedAdversary (Bits m) (BitStr I J) Unit Empty O t)

/-- **Adaptive completeness of a salted argument with coins in the quantum random-oracle model**
(Unruh 2017 Definition 5, p. 14, with the honest prover's coins and salt drawn after the
adversary): if the event `Bad r σ (e ∘ H) o` has probability at most `δ` over uniform coins `r`
and a fresh slice of the salt `σ` at every oracle `g` and output `o` (`hslice`), then every
`t`-query adversary of `def:adversary` without proof queries outputs `o` with `Bad r σ (e ∘ H) o` with
probability at most `δ + 2 t / √|Sd|`, over its auxiliary input, uniform coins `r`, a uniform salt
`σ` and a uniform oracle `H`. -/
theorem adaptiveCompleteness_coins {B : Type} (e : BitStr I J ≃ B) {R : Type} [Fintype R]
    [Nonempty R] {Bad : R → Sd → (Bits m → B) → O → Prop} {δ : ℝ≥0∞}
    (hslice : ∀ σ g o,
      Pr[q ← R × (Bits m → BitStr I J) : Bad q.1 σ (e ∘ replaceSlice saltOf σ g q.2) o] ≤ δ) :
    ∑' a, 𝒢.aux a * ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ σ : Sd, (Fintype.card Sd : ℝ≥0∞)⁻¹ *
        ((𝒢.run a).realLaw e).toOuterMeasure {p | ∃ o ∈ p.out, Bad r σ p.oracle o} ≤
      δ + ENNReal.ofReal (2 * t / √(Fintype.card Sd : ℝ)) := by
  classical
  set bound := δ + ENNReal.ofReal (2 * t / √(Fintype.card Sd : ℝ))
  have hper : ∀ a, ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ σ : Sd, (Fintype.card Sd : ℝ≥0∞)⁻¹ *
      ((𝒢.run a).realLaw e).toOuterMeasure {p | ∃ o ∈ p.out, Bad r σ p.oracle o} ≤
      bound := by
    intro a
    set A := 𝒢.alg a
    set f : A.toKindAlg.CW (nullChallenger (Bits m) (BitStr I J) Unit Empty) → O :=
      fun v => A.out v.adv.workspace.1
    set Q := (A.toTPKindAlg.composeBothOut (nullChallenger (Bits m) (BitStr I J) Unit Empty)
      f).toQueryAlgCoh.mapOut id
    set qc := AdaptiveIAlg.tpQueryCount (Equiv.refl (BitStr I J)) A
      (nullChallenger (Bits m) (BitStr I J) Unit Empty) f id
    have hb : A.width * A.budget + (nullChallenger (Bits m) (BitStr I J) Unit Empty).Q *
        (nullChallenger (Bits m) (BitStr I J) Unit Empty).q + A.width * A.post ≤ t :=
      𝒢.queryCount_le a
    -- the real law as an average of the output laws of `Q`
    have hlaw : ∀ r σ, ((𝒢.run a).realLaw e).toOuterMeasure
        {p | ∃ o ∈ p.out, Bad r σ p.oracle o} =
        ∑ H, (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ *
          (Q.outLaw H).toOuterMeasure {oo | ∃ o ∈ oo, Bad r σ (e ∘ H) o} := fun r σ => by
      have hQ : ∀ H, Q.outLaw H = (𝒢.run a).outLaw H := fun H => by
        rw [GordieHowe.Quantum.QueryAlg.outLaw_mapOut, PMF.map_id]
        exact Alg.outLaw_toQueryAlgCoh _ H
      rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype]
      refine Finset.sum_congr rfl fun H _ => ?_
      rw [PMF.uniformOfFintype_apply, PMF.toOuterMeasure_map_apply, hQ]
      rfl
    simp_rw [hlaw]
    have h := prob_bad_coins_le_of_count (Equiv.refl (BitStr I J)) saltOf Q qc
      (fun H H' k hk => AdaptiveIAlg.tpRealPad _ A _ f id H H' hk)
      (Bad := fun r σ H oo => ∃ o ∈ oo, Bad r σ (e ∘ H) o) (δ := δ) fun σ g oo => by
        rcases oo with _ | o
        · rw [probUniform_eq_zero fun F ⟨o, ho, _⟩ => by cases ho]
          exact zero_le
        · refine (probUniform_mono fun F ⟨o', ho', hb'⟩ => ?_).trans (hslice σ g o)
          rw [Option.mem_some_iff] at ho'
          subst ho'
          exact hb'
    refine h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    have hb' : ((A.width * A.budget + (nullChallenger (Bits m) (BitStr I J) Unit Empty).Q *
        (nullChallenger (Bits m) (BitStr I J) Unit Empty).q + A.width * A.post : ℕ) : ℝ) ≤ t := by
      exact_mod_cast hb
    gcongr
  calc ∑' a, 𝒢.aux a * ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ σ : Sd, (Fintype.card Sd : ℝ≥0∞)⁻¹ *
          ((𝒢.run a).realLaw e).toOuterMeasure {p | ∃ o ∈ p.out, Bad r σ p.oracle o}
      ≤ ∑' a, 𝒢.aux a * bound := ENNReal.tsum_le_tsum fun a => by gcongr; exact hper a
    _ = bound := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end QueryBoundedAdversary

end GordieHowe.QROM
