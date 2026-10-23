-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range
public import Mathlib.Tactic.LinearCombination
public import GordieHowe.Foundations.Probability.ChallengeEventCount

@[expose] public section

/-!
# The LogUp identity over a committed table

The paper's `lem:logup-point`, part (3): for a table whose rows `tbl` are committed values, the
verifier cannot compute the weights `(α − tbl_j)⁻¹`, so the identity is checked with both sides'
denominators cleared, `N_v(α) · D_tbl(α) = D_v(α) · N_tbl(α)`, where `N_v / D_v = Σ_i 1/(X − v_i)`
and `N_tbl / D_tbl = Σ_j m_j/(X − tbl_j)` (`committedArgument`; the C++ is
`assert_log_derivative_committed`, `lib/gordiehowe/compiler/log_derivative.h`, two fraction trees
whose roots agree after clearing denominators).

* **Soundness** (`Range.committedArgument_sound`): with fewer needles than the characteristic, if
  the identity holds at `α` then every needle is a row (`Range.InRows`) or `α` is a root of the
  nonzero polynomial `committedBadPoly` of degree at most `#needles + T − 1`. No condition on `α`:
  the identity has no pole.
* **Completeness** (`Range.committedArgument_complete`): with every needle a row and the counts
  of `lem:logup` (`Range.rowHistogram`: the needle count of a row at its first occurrence, `0` at
  a repeated row), the identity holds at every `α`.
-/

namespace GordieHowe

open Polynomial IOP
open scoped NNReal ENNReal

namespace Range

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## The identity -/

/-- **The numerator of the table side** at `α`: `N_tbl(α) = Σ_j m_j ∏_{k ≠ j} (α − tbl_k)`. -/
def rowsNum {T : ℕ} (tbl m : Fin T → K) (α : K) : K :=
  ∑ j, m j * ∏ k ∈ Finset.univ.erase j, (α - tbl k)

/-- **The denominator of the table side** at `α`: `D_tbl(α) = ∏_k (α − tbl_k)`. -/
def rowsDen {T : ℕ} (tbl : Fin T → K) (α : K) : K :=
  ∏ k, (α - tbl k)

/-- **The LogUp identity over the committed rows `tbl`, denominators cleared**, at `α`, with the
counts `m`: `N_v(α) · D_tbl(α) = D_v(α) · N_tbl(α)`, the needle side by the fraction tree of the
range argument (`fracTree`). -/
def committedArgument {T : ℕ} (needles : List K) (tbl m : Fin T → K) (α : K) : Bool :=
  let (num, den) := fracTree (needles.map fun v => α - v)
  decide (num * rowsDen tbl α = den * rowsNum tbl m α)

theorem committedArgument_eq_true_iff {T : ℕ} {needles : List K} {tbl m : Fin T → K} {α : K} :
    committedArgument needles tbl m α = true ↔
      (fracTree (needles.map fun v => α - v)).1 * rowsDen tbl α =
        (fracTree (needles.map fun v => α - v)).2 * rowsNum tbl m α := by
  simp [committedArgument]

/-! ## The polynomials -/

/-- **The table side's denominator** `∏_k (X − tbl_k)`. -/
noncomputable def rowsDenPoly {T : ℕ} (tbl : Fin T → K) : K[X] :=
  ∏ k, (X - C (tbl k))

/-- **The table side's numerator** `Σ_j m_j ∏_{k ≠ j} (X − tbl_k)`. -/
noncomputable def rowsNumPoly {T : ℕ} (tbl m : Fin T → K) : K[X] :=
  ∑ j, C (m j) * ∏ k ∈ Finset.univ.erase j, (X - C (tbl k))

omit [DecidableEq K] in
theorem rowsDenPoly_eval {T : ℕ} (tbl : Fin T → K) (α : K) :
    (rowsDenPoly tbl).eval α = rowsDen tbl α := by
  simp [rowsDenPoly, rowsDen, eval_prod]

omit [DecidableEq K] in
theorem rowsNumPoly_eval {T : ℕ} (tbl m : Fin T → K) (α : K) :
    (rowsNumPoly tbl m).eval α = rowsNum tbl m α := by
  simp [rowsNumPoly, rowsNum, eval_finsetSum, eval_prod]

omit [DecidableEq K] in
/-- The table side's denominator has one linear factor per row. -/
theorem rowsDenPoly_natDegree {T : ℕ} (tbl : Fin T → K) : (rowsDenPoly tbl).natDegree = T := by
  simp [rowsDenPoly, natDegree_finsetProd_X_sub_C_eq_card]

omit [DecidableEq K] in
/-- Off the rows, the table side's denominator does not vanish. -/
theorem rowsDenPoly_eval_ne_zero {T : ℕ} {tbl : Fin T → K} {v : K} (hv : ∀ j, tbl j ≠ v) :
    (rowsDenPoly tbl).eval v ≠ 0 := by
  rw [rowsDenPoly, eval_prod, Finset.prod_ne_zero_iff]
  intro j _
  simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using (hv j).symm

omit [DecidableEq K] in
/-- Every summand of the table side's numerator omits one factor. -/
theorem rowsNumPoly_natDegree_le {T : ℕ} (tbl m : Fin T → K) :
    (rowsNumPoly tbl m).natDegree ≤ T - 1 := by
  unfold rowsNumPoly
  refine natDegree_sum_le_of_forall_le Finset.univ _ fun j _ => ?_
  calc
    (C (m j) * ∏ k ∈ Finset.univ.erase j, (X - C (tbl k))).natDegree
        ≤ (C (m j)).natDegree + (∏ k ∈ Finset.univ.erase j, (X - C (tbl k))).natDegree :=
      natDegree_mul_le
    _ ≤ 0 + (T - 1) := by
      gcongr
      · exact (natDegree_C _).le
      · rw [natDegree_finsetProd_X_sub_C_eq_card]
        simp
    _ = T - 1 := by omega

/-- **The cleared identity's difference** `N_v · D_tbl − D_v · N_tbl`, a polynomial defined from the
needles, the rows and the counts alone. -/
noncomputable def committedBadPoly {T : ℕ} (needles : List K) (tbl m : Fin T → K) : K[X] :=
  needleCount needles * rowsDenPoly tbl - needleDen needles * rowsNumPoly tbl m

/-- At `α`, the difference is the cleared identity's difference. -/
theorem committedBadPoly_eval {T : ℕ} (needles : List K) (tbl m : Fin T → K) (α : K) :
    (committedBadPoly needles tbl m).eval α =
      (fracTree (needles.map fun v => α - v)).1 * rowsDen tbl α -
        (fracTree (needles.map fun v => α - v)).2 * rowsNum tbl m α := by
  rw [fracTree_eq_eval, committedBadPoly, eval_sub, eval_mul, eval_mul, rowsDenPoly_eval,
    rowsNumPoly_eval]

/-- **A needle off the rows makes the difference nonzero**, with fewer needles than the
characteristic: the multiplicity of the needle `v` in `N_v · D_tbl` is one less than its count,
since `N_v` is the derivative of `D_v` and `D_tbl(v) ≠ 0`, and in `D_v · N_tbl` it is at least its
count. -/
theorem committedBadPoly_ne_zero_of_outside {p : ℕ} [CharP K p] {T : ℕ} {needles : List K}
    {tbl m : Fin T → K} {v : K} (hchar : needles.length < p) (hmem : v ∈ needles)
    (hout : ∀ j, tbl j ≠ v) : committedBadPoly needles tbl m ≠ 0 := by
  have hcountpos : 0 < needles.count v := List.count_pos_iff.mpr hmem
  have hcountlt : needles.count v < p := List.count_le_length.trans_lt hchar
  have hp : 0 < p := hcountpos.trans hcountlt
  have hcountcast : (needles.count v : K) ≠ 0 := by
    intro hz
    have := CharP.natCast_injOn_Iio K p hcountlt hp (by simpa using hz)
    omega
  have hD : needleDen needles ≠ 0 := (needleDen_monic needles).ne_zero
  have hDroot : (needleDen needles).IsRoot v := by
    apply (rootMultiplicity_pos hD).mp
    rw [needleDen_rootMultiplicity]
    exact hcountpos
  have hrootcast : ((needleDen needles).rootMultiplicity v : K) ≠ 0 := by
    rw [needleDen_rootMultiplicity]
    exact hcountcast
  have hderivrm : (needleDen needles).derivative.rootMultiplicity v = needles.count v - 1 := by
    rw [derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hDroot
      (mem_nonZeroDivisors_of_ne_zero hrootcast), needleDen_rootMultiplicity]
  have hderiv : (needleDen needles).derivative ≠ 0 :=
    needleDen_derivative_ne_zero needles (List.ne_nil_of_mem hmem) hchar
  have hTDeval : (rowsDenPoly tbl).eval v ≠ 0 := rowsDenPoly_eval_ne_zero hout
  have hTD : rowsDenPoly tbl ≠ 0 := fun hzero => hTDeval (by rw [hzero, eval_zero])
  have hTDrm : (rowsDenPoly tbl).rootMultiplicity v = 0 := by
    apply rootMultiplicity_eq_zero
    simpa only [IsRoot] using hTDeval
  intro hbad
  have heq : (needleDen needles).derivative * rowsDenPoly tbl =
      needleDen needles * rowsNumPoly tbl m := by
    apply sub_eq_zero.mp
    simpa only [committedBadPoly, needleNum_eq_derivative] using hbad
  have hleft : (needleDen needles).derivative * rowsDenPoly tbl ≠ 0 := mul_ne_zero hderiv hTD
  have hright : needleDen needles * rowsNumPoly tbl m ≠ 0 := by
    rw [← heq]
    exact hleft
  have hrm := congrArg (fun q : K[X] => q.rootMultiplicity v) heq
  rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hright, hderivrm, hTDrm,
    needleDen_rootMultiplicity] at hrm
  omega

/-- The difference has degree at most `#needles + T − 1`. -/
theorem committedBadPoly_natDegree_le {T : ℕ} (needles : List K) (tbl m : Fin T → K) :
    (committedBadPoly needles tbl m).natDegree ≤ needles.length + T - 1 := by
  cases needles with
  | nil =>
    simpa [committedBadPoly, needleCount, needleDen] using rowsNumPoly_natDegree_le tbl m
  | cons v needles =>
    cases T with
    | zero =>
      simpa [committedBadPoly, rowsNumPoly, rowsDenPoly] using needleNum_natDegree_le (v :: needles)
    | succ T =>
      unfold committedBadPoly
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · calc
          (needleCount (v :: needles) * rowsDenPoly tbl).natDegree
              ≤ (needleCount (v :: needles)).natDegree + (rowsDenPoly tbl).natDegree :=
            natDegree_mul_le
          _ ≤ ((v :: needles).length - 1) + (T + 1) := by
            rw [rowsDenPoly_natDegree]
            exact Nat.add_le_add_right (needleNum_natDegree_le (v :: needles)) (T + 1)
          _ ≤ (v :: needles).length + (T + 1) - 1 := by
            simp only [List.length_cons]
            omega
      · calc
          (needleDen (v :: needles) * rowsNumPoly tbl m).natDegree
              ≤ (needleDen (v :: needles)).natDegree + (rowsNumPoly tbl m).natDegree :=
            natDegree_mul_le
          _ ≤ (v :: needles).length + ((T + 1) - 1) := by
            rw [needleDen_natDegree]
            exact Nat.add_le_add_left (rowsNumPoly_natDegree_le tbl m) (v :: needles).length
          _ ≤ (v :: needles).length + (T + 1) - 1 := by
            simp only [List.length_cons]
            omega

/-- **The committed-table event in `α`**: `α` is a root of the nonzero `committedBadPoly`, of
degree at most `#needles + T − 1`. -/
noncomputable def committedEvent {T : ℕ} (needles : List K) (tbl m : Fin T → K) :
    ChallengeEvent K :=
  ⟨committedBadPoly needles tbl m, needles.length + T - 1,
    committedBadPoly_natDegree_le needles tbl m⟩

/-- **Every needle is a row** of `tbl`. -/
def InRows {T : ℕ} (tbl : Fin T → K) (needles : List K) : Prop :=
  ∀ v ∈ needles, ∃ j, tbl j = v

omit [DecidableEq K] in
/-- **A cast of a natural below `T` is a row of the range `[0, T)`.** -/
theorem isNatBelow_iff_exists_fin {T : ℕ} {v : K} : IsNatBelow T v ↔ ∃ j : Fin T, (j : K) = v :=
  ⟨fun ⟨n, hn, h⟩ => ⟨⟨n, hn⟩, h⟩, fun ⟨j, h⟩ => ⟨j, j.isLt, h⟩⟩

/-- **The rows of the range `[0, T)`**: every needle is a row iff every needle lies in the table. -/
theorem inRows_natCast_iff {T : ℕ} {needles : List K} :
    InRows (fun j : Fin T => (j : K)) needles ↔ InTable T needles :=
  forall₂_congr fun _ _ => isNatBelow_iff_exists_fin.symm

/-- **Paper `lem:logup-point`, part (3), soundness**: with fewer needles than the characteristic,
if the cleared identity holds at `α` then every needle is a row, or `α` is a root of the nonzero
`committedBadPoly` (`committedEvent`), of degree at most `#needles + T − 1`. The verifier draws `α`
uniformly from a set `F ∖ U`, and the event is charged at `(#needles + T − 1)/(|F| − |U|)`
(`ChallengeEvent.probUniform_badAt_le_compl`); `U` need not contain the rows. -/
theorem committedArgument_sound {p : ℕ} [CharP K p] {T : ℕ} {needles : List K}
    {tbl m : Fin T → K} {α : K} (hchar : needles.length < p)
    (h : committedArgument needles tbl m α = true) :
    InRows tbl needles ∨ (committedEvent needles tbl m).BadAt α := by
  by_cases hin : InRows tbl needles
  · exact Or.inl hin
  right
  simp only [InRows, not_forall, not_exists, exists_prop] at hin
  obtain ⟨v, hmem, hout⟩ := hin
  refine ⟨committedBadPoly_ne_zero_of_outside hchar hmem hout, ?_⟩
  change (committedBadPoly needles tbl m).eval α = 0
  rw [committedBadPoly_eval, sub_eq_zero]
  exact committedArgument_eq_true_iff.mp h

/-! ## Completeness -/

/-- **The honest counts over the rows `tbl`** (`lem:logup`): at a row's first occurrence, the
number of needles equal to it; at a repeated row, `0`. -/
-- spec-side
def rowHistogram {T : ℕ} (tbl : Fin T → K) (needles : List K) (j : Fin T) : K :=
  if ∀ k : Fin T, k < j → tbl k ≠ tbl j then (needles.count (tbl j) : K) else 0

omit [DecidableEq K] in
/-- The needle denominator of `v :: l`. -/
theorem needleDen_cons (v : K) (l : List K) :
    needleDen (v :: l) = (X - C v) * needleDen l := by
  simp [needleDen]

/-- The needle numerator of `v :: l`. -/
theorem needleCount_cons (v : K) (l : List K) :
    needleCount (v :: l) = needleDen l + (X - C v) * needleCount l := by
  rw [needleNum_eq_derivative, needleNum_eq_derivative, needleDen_cons, derivative_mul,
    derivative_X_sub_C, one_mul]

omit [Field K] in
/-- **A row's first occurrence**: for a value `v` among the rows, the least index `j` with
`tbl j = v` is the one index that is a first occurrence and holds `v`. -/
theorem exists_firstRow {T : ℕ} {tbl : Fin T → K} {v : K} (h : ∃ j, tbl j = v) :
    ∃ j₀, ∀ j, ((∀ k : Fin T, k < j → tbl k ≠ tbl j) ∧ tbl j = v) ↔ j = j₀ := by
  classical
  have hne : (Finset.univ.filter fun j => tbl j = v).Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simp [hj]⟩
  set j₀ := (Finset.univ.filter fun j => tbl j = v).min' hne
  have hj₀ : tbl j₀ = v := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hmin : ∀ k, tbl k = v → j₀ ≤ k := fun k hk =>
    Finset.min'_le _ _ (by simp [hk])
  refine ⟨j₀, fun j => ⟨fun ⟨hf, hj⟩ => ?_, fun hj => ?_⟩⟩
  · rcases lt_trichotomy j j₀ with hlt | heq | hgt
    · exact absurd (hmin j hj) (not_le.mpr hlt)
    · exact heq
    · exact absurd (hj₀.trans hj.symm) (hf j₀ hgt)
  · subst hj
    refine ⟨fun k hk hkv => ?_, hj₀⟩
    exact absurd (hmin k (hkv.trans hj₀)) (not_le.mpr hk)

/-- **The honest counts of `v :: l`**: those of `l`, plus one at the first occurrence of `v`. -/
theorem rowHistogram_cons {T : ℕ} {tbl : Fin T → K} {v : K} {j₀ : Fin T}
    (h₀ : ∀ j, ((∀ k : Fin T, k < j → tbl k ≠ tbl j) ∧ tbl j = v) ↔ j = j₀) (l : List K)
    (j : Fin T) :
    rowHistogram tbl (v :: l) j = rowHistogram tbl l j + if j = j₀ then 1 else 0 := by
  unfold rowHistogram
  by_cases hf : ∀ k : Fin T, k < j → tbl k ≠ tbl j
  · simp only [if_pos hf, List.count_cons, beq_iff_eq, Nat.cast_add]
    by_cases hv : tbl j = v
    · have hj := (h₀ j).1 ⟨hf, hv⟩
      subst hj
      simp [hv]
    · have hj : j ≠ j₀ := fun hj => hv ((h₀ j).2 hj).2
      have hv' : ¬ v = tbl j := fun h => hv h.symm
      simp [hv', hj]
  · have hj : j ≠ j₀ := fun hj => hf ((h₀ j).2 hj).1
    simp [if_neg hf, hj]

/-- **With every needle a row and the honest counts, the difference is the zero polynomial**
(`lem:logup`), by induction on the needles: adding a needle `v` multiplies `D_v` by `X − v`, adds
`D_v` to `(X − v) N_v`, and adds `∏_{k ≠ j₀} (X − tbl_k)` to `N_tbl` at `v`'s first row `j₀`, so the
difference is multiplied by `X − v`. -/
theorem committedBadPoly_rowHistogram {T : ℕ} (tbl : Fin T → K) :
    ∀ needles : List K, InRows tbl needles →
      committedBadPoly needles tbl (rowHistogram tbl needles) = 0
  | [], _ => by
    simp [committedBadPoly, needleCount, needleDen, rowsNumPoly, rowHistogram]
  | v :: l, hin => by
    have ih := committedBadPoly_rowHistogram tbl l fun w hw => hin w (List.mem_cons_of_mem _ hw)
    obtain ⟨j₀, h₀⟩ := exists_firstRow (hin v List.mem_cons_self)
    have hv : tbl j₀ = v := ((h₀ j₀).2 rfl).2
    set Q : K[X] := ∏ k ∈ Finset.univ.erase j₀, (X - C (tbl k))
    have hD : rowsDenPoly tbl = (X - C v) * Q := by
      rw [rowsDenPoly, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀), hv]
    have hN : rowsNumPoly tbl (rowHistogram tbl (v :: l)) =
        rowsNumPoly tbl (rowHistogram tbl l) + Q := by
      simp only [rowsNumPoly, rowHistogram_cons h₀, C_add, add_mul, Finset.sum_add_distrib]
      congr 1
      simp [Q, apply_ite C]
    rw [committedBadPoly, sub_eq_zero] at ih
    rw [committedBadPoly, needleCount_cons, needleDen_cons, hN, hD, sub_eq_zero]
    rw [hD] at ih
    linear_combination (X - C v) * ih

/-- **Paper `lem:logup-point`, part (3), completeness**: with every needle a row and the counts of
`lem:logup` (`rowHistogram`), the cleared identity holds at every `α`. -/
theorem committedArgument_complete {T : ℕ} {needles : List K} {tbl m : Fin T → K} (α : K)
    (hin : InRows tbl needles) (hm : ∀ j, m j = rowHistogram tbl needles j) :
    committedArgument needles tbl m α = true := by
  have h0 := committedBadPoly_rowHistogram tbl needles hin
  rw [show m = rowHistogram tbl needles from funext hm]
  rw [committedArgument_eq_true_iff, ← sub_eq_zero, ← committedBadPoly_eval, h0, eval_zero]

/-! ## The weighted identity over any table (`lem:logup-point`, parts (1) and (2)) -/

/-- **The LogUp identity at the weights `w_j = (α − tbl_j)⁻¹`** at `α`, with the counts `m`:
`N_v(α) = D_v(α) Σ_j m_j w_j`, the needle side by the fraction tree (`fracTree`); `w_j = 0` at a row
`α = tbl_j` (Lean's inverse of `0`, the paper's convention). -/
def weightedArgument {T : ℕ} (needles : List K) (tbl m : Fin T → K) (α : K) : Bool :=
  let (num, den) := fracTree (needles.map fun v => α - v)
  decide (num = (∑ j, m j * (α - tbl j)⁻¹) * den)

theorem weightedArgument_eq_true_iff {T : ℕ} {needles : List K} {tbl m : Fin T → K} {α : K} :
    weightedArgument needles tbl m α = true ↔
      (fracTree (needles.map fun v => α - v)).1 =
        (∑ j, m j * (α - tbl j)⁻¹) * (fracTree (needles.map fun v => α - v)).2 := by
  simp [weightedArgument]

omit [DecidableEq K] in
/-- Off the rows, the table side's denominator does not vanish at `α`. -/
theorem rowsDen_ne_zero {T : ℕ} {tbl : Fin T → K} {α : K} (hα : ∀ j, α ≠ tbl j) :
    rowsDen tbl α ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hα j)

/-- Off the rows, the table side's numerator is the weighted sum times the denominator. -/
theorem rowsNum_eq_weighted {T : ℕ} (tbl m : Fin T → K) {α : K} (hα : ∀ j, α ≠ tbl j) :
    rowsNum tbl m α = (∑ j, m j * (α - tbl j)⁻¹) * rowsDen tbl α := by
  unfold rowsNum rowsDen
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun k => α - tbl k) (Finset.mem_univ j),
    mul_assoc (m j), ← mul_assoc (α - tbl j)⁻¹, inv_mul_cancel₀ (sub_ne_zero.mpr (hα j)), one_mul]

/-- **Off the rows, the weighted identity is the cleared one** (`committedArgument`): both sides
multiplied by `D_tbl(α) ≠ 0`. -/
theorem weightedArgument_iff_committedArgument {T : ℕ} {needles : List K} {tbl m : Fin T → K}
    {α : K} (hα : ∀ j, α ≠ tbl j) :
    weightedArgument needles tbl m α = true ↔ committedArgument needles tbl m α = true := by
  rw [weightedArgument_eq_true_iff, committedArgument_eq_true_iff, rowsNum_eq_weighted tbl m hα]
  have hD := rowsDen_ne_zero hα
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    refine mul_right_cancel₀ hD ?_
    rw [h]
    ring

/-- **Paper `lem:logup-point`, part (1)**: for a table `tbl`, a set `U` containing its rows, needles
fewer than the characteristic one of which is not a row, and any counts `m`, the weighted identity
holds at `α` uniform outside `U` with probability at most `(N + T − 1)/(|F| − |U|)`. Off `U` it is
the cleared identity (`weightedArgument_iff_committedArgument`), so `α` is a root of the nonzero
`committedBadPoly` (`committedArgument_sound`). -/
theorem weightedArgument_prob_le {F : Type} [Field F] [Fintype F] [DecidableEq F] {p : ℕ}
    [CharP F p] {T : ℕ} {needles : List F}
    {tbl : Fin T → F} (m : Fin T → F) (U : Finset F) [Nonempty {x : F // x ∉ U}]
    (hU : ∀ j, tbl j ∈ U) (hchar : needles.length < p) (hout : ∃ v ∈ needles, ∀ j, tbl j ≠ v) :
    Pr[a ← {x : F // x ∉ U} : weightedArgument needles tbl m a = true] ≤
      ((((needles.length + T - 1 : ℕ) : ℝ≥0) / (Fintype.card F - U.card : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨v, hv, hvout⟩ := hout
  have hnot : ¬ InRows tbl needles := fun h => by
    obtain ⟨j, hj⟩ := h v hv
    exact hvout j hj
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono fun a ha => ?_).trans
    (ChallengeEvent.probUniform_badAt_le_compl (committedEvent needles tbl m) U)
  have hα : ∀ j, a.val ≠ tbl j := fun j h => a.2 (h ▸ hU j)
  have hc := (weightedArgument_iff_committedArgument hα).mp ha
  exact (committedArgument_sound hchar hc).resolve_left hnot

/-- **Paper `lem:logup-point`, part (2)**: with every needle a row and the counts of `lem:logup`
(`rowHistogram`), the weighted identity holds at every `α` that is not a row. -/
theorem weightedArgument_complete {T : ℕ} {needles : List K} {tbl m : Fin T → K} {α : K}
    (hα : ∀ j, α ≠ tbl j) (hin : InRows tbl needles) (hm : ∀ j, m j = rowHistogram tbl needles j) :
    weightedArgument needles tbl m α = true :=
  (weightedArgument_iff_committedArgument hα).mpr (committedArgument_complete α hin hm)

/-- **Paper `lem:logup-point`, part (3), as a probability**: for any set `U`, needles fewer than the
characteristic one of which is not a row, and any counts `m`, the cleared identity holds at `α`
uniform outside `U` with probability at most `(N + T − 1)/(|F| − |U|)`
(`committedArgument_sound`). -/
theorem committedArgument_prob_le {F : Type} [Field F] [Fintype F] [DecidableEq F] {p : ℕ}
    [CharP F p] {T : ℕ} {needles : List F}
    {tbl : Fin T → F} (m : Fin T → F) (U : Finset F) [Nonempty {x : F // x ∉ U}]
    (hchar : needles.length < p) (hout : ∃ v ∈ needles, ∀ j, tbl j ≠ v) :
    Pr[a ← {x : F // x ∉ U} : committedArgument needles tbl m a = true] ≤
      ((((needles.length + T - 1 : ℕ) : ℝ≥0) / (Fintype.card F - U.card : ℕ) : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨v, hv, hvout⟩ := hout
  have hnot : ¬ InRows tbl needles := fun h => by
    obtain ⟨j, hj⟩ := h v hv
    exact hvout j hj
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono fun a ha => ?_).trans
    (ChallengeEvent.probUniform_badAt_le_compl (committedEvent needles tbl m) U)
  exact (committedArgument_sound hchar ha).resolve_left hnot

end Range

end GordieHowe
