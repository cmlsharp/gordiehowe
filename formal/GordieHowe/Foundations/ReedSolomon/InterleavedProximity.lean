-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Probability.RepetitionCounting
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-!
# Interleaved linear-code proximity with repetitions (AHIV22 Lemma 4.2)

Ames, Hazay, Ishai and Venkitasubramaniam, ePrint 2022/1608, Lemma 4.2 (p. 14) and Lemma B.6
(p. 43). For a linear code `C ⊆ F^n` of minimum distance `d` (`IsMinDist`), `4e < d`, and a matrix
`U ∈ F^{ι×n}` that is not `e`-close to `C^ι` (`Close`: some codeword matrix agrees with `U`
outside `e` columns), take `σ` independent uniform combinations `r_h ∈ F^ι` and arbitrary shifts
`u_h ∈ F^n`. The rows `w_h = r_h^T U + u_h` are jointly `e`-close to `C^σ` (a common error set of
`e` columns) for at most an `(e + 1)/|F|^σ` fraction of the `r` (`card_close_mul_le`).

The proof is Lemma 4.2's, carried out for all repetitions at once.

* If some combination `v* = s^T U` is more than `2e` from every codeword, each line in direction
  `s` contains at most one `r_h` whose row is `e`-close (two would put `v*` within `2e` of a
  codeword, `smul_inv_sub_eq`), so every repetition is bad with probability `≤ 1/|F|`.
* Otherwise every row `U_i` is within `2e` of a codeword `c_i`; the columns `E` where `U` and
  `(c_i)` differ number more than `e`; fix `e + 1` of them and, for each, a row `i_j` in error.
  If the `w_h` are jointly close with error set `Δ`, some fixed column `j ∉ Δ`, and then each
  `w_h` is `e`-close to a codeword agreeing with it at `j`. Along a line in direction `e_{i_j}`
  this happens at most once, since two points would give a codeword within `2e` of `U_{i_j}`
  agreeing with it at `j`, which by `4e < d` is `c_{i_j}`, which disagrees with it at `j`.

AHIV22 section 4.7 sums the per-repetition bounds (Lemma B.2's proof replaces `|F|` by `|F|^σ`),
which bounds each repetition separately; the joint event needs the common error set, as here.

`rsCode` is the Reed–Solomon code `RS_{F,n,k,η}` (Def. 4.1) as a submodule, the evaluations at
`η` of the coefficient vectors of length `k`; `rsCode_isMinDist` is its distance `n − k + 1`.
-/

namespace GordieHowe.InterleavedProximity

open Finset GordieHowe.RepetitionCounting

variable {F : Type*} [Field F] {n : ℕ}

section Dist

variable [DecidableEq F]

/-- The Hamming norm of a difference is the Hamming distance. -/
theorem hammingNorm_sub (c c' : Fin n → F) : hammingNorm (c - c') = hammingDist c c' := by
  simp [hammingNorm, hammingDist, sub_eq_zero]

/-- `C` has minimum distance at least `d`: every nonzero codeword has at least `d` nonzero
entries. -/
def IsMinDist (C : Submodule F (Fin n → F)) (d : ℕ) : Prop :=
  ∀ c ∈ C, c ≠ 0 → d ≤ hammingNorm c

/-- Two codewords at distance below `d` are equal. -/
theorem IsMinDist.eq_of_hammingDist_lt {C : Submodule F (Fin n → F)} {d : ℕ}
    (hC : IsMinDist C d) {c c' : Fin n → F} (hc : c ∈ C) (hc' : c' ∈ C)
    (h : hammingDist c c' < d) : c = c' := by
  by_contra hne
  have := hC (c - c') (C.sub_mem hc hc') (sub_ne_zero.mpr hne)
  rw [hammingNorm_sub] at this
  omega

/-- Two codewords within `a` and `b` of one word with `a + b < d` are equal. -/
theorem IsMinDist.eq_of_hammingDist_le {C : Submodule F (Fin n → F)} {d : ℕ}
    (hC : IsMinDist C d) {w c c' : Fin n → F} (hc : c ∈ C) (hc' : c' ∈ C) {a b : ℕ}
    (ha : hammingDist w c ≤ a) (hb : hammingDist w c' ≤ b) (hab : a + b < d) : c = c' := by
  refine hC.eq_of_hammingDist_lt hc hc' ?_
  have := hammingDist_triangle c w c'
  rw [hammingDist_comm c w] at this
  omega

/-- Two distinct codewords agree on at most `n − d` columns. -/
theorem IsMinDist.card_agree_le {C : Submodule F (Fin n → F)} {d : ℕ}
    (hC : IsMinDist C d) {c c' : Fin n → F} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') :
    #{j | c j = c' j} ≤ n - d := by
  have hd := hC (c - c') (C.sub_mem hc hc') (sub_ne_zero.mpr hne)
  rw [hammingNorm_sub] at hd
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    fun j => c j = c' j
  simp only [card_univ, Fintype.card_fin] at hsplit
  have : hammingDist c c' = #{j | ¬ c j = c' j} := rfl
  omega

end Dist

section Matrix

variable [DecidableEq F]

/-- The columns at which two matrices `U, V ∈ F^{ι×n}` differ in some row. -/
def colErrors {ι : Type*} [Fintype ι] (U V : ι → Fin n → F) : Finset (Fin n) :=
  {j | ∃ i, U i j ≠ V i j}

omit [Field F] in
theorem mem_colErrors {ι : Type*} [Fintype ι] {U V : ι → Fin n → F}
    {j : Fin n} : j ∈ colErrors U V ↔ ∃ i, U i j ≠ V i j := by
  simp [colErrors]

omit [Field F] in
/-- A row is within the column errors: `d(U_i, V_i) ≤ #colErrors U V`. -/
theorem hammingDist_le_card_colErrors {ι : Type*} [Fintype ι]
    (U V : ι → Fin n → F) (i : ι) : hammingDist (U i) (V i) ≤ #(colErrors U V) :=
  card_le_card fun _ hj => mem_colErrors.mpr ⟨i, (mem_filter.mp hj).2⟩

/-- `U ∈ F^{ι×n}` is `e`-close to the interleaved code `C^ι`: some matrix of codewords agrees
with `U` outside at most `e` columns. -/
def Close {ι : Type*} [Fintype ι] (C : Submodule F (Fin n → F)) (e : ℕ)
    (U : ι → Fin n → F) : Prop :=
  ∃ V : ι → Fin n → F, (∀ i, V i ∈ C) ∧ #(colErrors U V) ≤ e

end Matrix

/-- The combination `r^T U = Σ_i r_i · U_i` of the rows of `U`. -/
def combo {ι : Type*} [Fintype ι] (r : ι → F) (U : ι → Fin n → F) : Fin n → F :=
  fun j => ∑ i, r i * U i j

theorem combo_add_smul {ι : Type*} [Fintype ι] (r s : ι → F) (α : F) (U : ι → Fin n → F) :
    combo (r + α • s) U = combo r U + α • combo s U := by
  funext j
  simp [combo, add_mul, sum_add_distrib, mul_sum, mul_assoc]

theorem combo_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (U : ι → Fin n → F) :
    combo (Pi.single i 1) U = U i := by
  funext j
  simp [combo, Pi.single_apply]

theorem combo_mem {ι : Type*} [Fintype ι] {C : Submodule F (Fin n → F)} (r : ι → F)
    {V : ι → Fin n → F} (hV : ∀ i, V i ∈ C) : combo r V ∈ C := by
  have : combo r V = ∑ i, r i • V i := by
    funext j
    simp [combo, Finset.sum_apply]
  rw [this]
  exact C.sum_mem fun i _ => C.smul_mem _ (hV i)

/-- If `w` agrees with `c₁` and `w + α • v` with `c₂` at a column (`α ≠ 0`), then `v` agrees
with `α⁻¹ • (c₂ − c₁)` there. -/
theorem smul_inv_sub_eq {w v c₁ c₂ : Fin n → F} {α : F} (hα : α ≠ 0) {j : Fin n}
    (h₁ : w j = c₁ j) (h₂ : (w + α • v) j = c₂ j) : v j = (α⁻¹ • (c₂ - c₁)) j := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h₂ ⊢
  rw [← h₂, ← h₁, add_sub_cancel_left, inv_mul_cancel_left₀ hα]

/-- If `w` is within `a` of `c₁` and `w + α • v` within `b` of `c₂` (`α ≠ 0`), then `v` is within
`a + b` of `α⁻¹ • (c₂ − c₁)`. -/
theorem hammingDist_smul_inv_sub_le [DecidableEq F] (w v c₁ c₂ : Fin n → F) {α : F}
    (hα : α ≠ 0) :
    hammingDist v (α⁻¹ • (c₂ - c₁)) ≤ hammingDist w c₁ + hammingDist (w + α • v) c₂ := by
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro j hj
  simp only [mem_filter, mem_univ, true_and, mem_union] at hj ⊢
  by_contra hno
  push Not at hno
  exact hj (smul_inv_sub_eq hα hno.1 hno.2)

variable [Fintype F] [DecidableEq F]

/-- **AHIV22 Lemma 4.2 / Lemma B.6, jointly over `σ` repetitions** (ePrint 2022/1608, pp. 14, 43).
For a linear code of minimum distance `d > 4e` and a matrix `U` not `e`-close to `C^ι`, the
combinations `r ∈ (F^ι)^σ` whose shifted rows `r_h^T U + u_h` are jointly `e`-close to `C^σ`
number at most `(e + 1) · |F^ι|^σ / |F|^σ`. -/
theorem card_close_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Submodule F (Fin n → F)}
    {d e : ℕ} (hC : IsMinDist C d) (he : 4 * e < d) {U : ι → Fin n → F} (hU : ¬ Close C e U)
    {σ : ℕ} (u : Fin σ → Fin n → F) [DecidablePred fun r : Fin σ → ι → F =>
      Close C e fun h => combo (r h) U + u h] :
    #{r : Fin σ → ι → F | Close C e fun h => combo (r h) U + u h} * Fintype.card F ^ σ ≤
      (e + 1) * Fintype.card (ι → F) ^ σ := by
  classical
  by_cases hfar : ∃ s : ι → F, ∀ c ∈ C, 2 * e < hammingDist (combo s U) c
  · -- Case 1: a combination far from the code.
    obtain ⟨s, hs⟩ := hfar
    let B : Fin σ → Finset (ι → F) := fun h =>
      {x | ∃ c ∈ C, hammingDist (combo x U + u h) c ≤ e}
    have hB : ∀ h, #(B h) * Fintype.card F ≤ Fintype.card (ι → F) := by
      intro h
      refine card_mul_card_le_of_line (B h) s fun x hx α hα hx' => ?_
      simp only [B, mem_filter, mem_univ, true_and] at hx hx'
      obtain ⟨c₁, hc₁, hd₁⟩ := hx
      obtain ⟨c₂, hc₂, hd₂⟩ := hx'
      have hmem : α⁻¹ • (c₂ - c₁) ∈ C := C.smul_mem _ (C.sub_mem hc₂ hc₁)
      have hle := hammingDist_smul_inv_sub_le (combo x U + u h) (combo s U) c₁ c₂ hα
      rw [combo_add_smul, add_right_comm] at hd₂
      have := hs _ hmem
      omega
    have hsub : (univ.filter fun r : Fin σ → ι → F => Close C e fun h => combo (r h) U + u h) ⊆
        Fintype.piFinset B := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨V, hV, hVe⟩ := hr
      refine Fintype.mem_piFinset.mpr fun h => ?_
      simp only [B, mem_filter, mem_univ, true_and]
      exact ⟨V h, hV h, (hammingDist_le_card_colErrors _ V h).trans hVe⟩
    calc _ ≤ #(Fintype.piFinset B) * Fintype.card F ^ σ :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ Fintype.card (ι → F) ^ σ := card_piFinset_mul_pow_le B hB
      _ ≤ (e + 1) * Fintype.card (ι → F) ^ σ := Nat.le_mul_of_pos_left _ (Nat.succ_pos e)
  · -- Case 2: every combination is within `2e` of the code.
    simp only [not_exists, not_forall, not_lt] at hfar
    have hrow : ∀ i, ∃ c ∈ C, hammingDist (U i) c ≤ 2 * e := by
      intro i
      obtain ⟨c, hc, hd⟩ := hfar (Pi.single i 1)
      rw [combo_single] at hd
      exact ⟨c, hc, hd⟩
    choose c hc hcd using hrow
    have hE : e < #(colErrors U c) := by
      by_contra hle
      exact hU ⟨c, hc, Nat.le_of_not_lt hle⟩
    obtain ⟨E', hE'sub, hE'card⟩ := exists_subset_card_eq hE
    have hsel : ∀ j ∈ E', ∃ i, U i j ≠ c i j := fun j hj => mem_colErrors.mp (hE'sub hj)
    have hne : Nonempty ι := by
      obtain ⟨j, hj⟩ : E'.Nonempty := card_pos.mp (by omega)
      obtain ⟨i, _⟩ := hsel j hj
      exact ⟨i⟩
    choose! row hrowj using hsel
    let B : Fin n → Fin σ → Finset (ι → F) := fun j h =>
      {x | ∃ c' ∈ C, hammingDist (combo x U + u h) c' ≤ e ∧ (combo x U + u h) j = c' j}
    have hB : ∀ j ∈ E', ∀ h, #(B j h) * Fintype.card F ≤ Fintype.card (ι → F) := by
      intro j hj h
      refine card_mul_card_le_of_line (B j h) (Pi.single (row j) 1) fun x hx α hα hx' => ?_
      simp only [B, mem_filter, mem_univ, true_and] at hx hx'
      obtain ⟨c₁, hc₁, hd₁, ha₁⟩ := hx
      obtain ⟨c₂, hc₂, hd₂, ha₂⟩ := hx'
      rw [combo_add_smul, combo_single, add_right_comm] at hd₂ ha₂
      have hmem : α⁻¹ • (c₂ - c₁) ∈ C := C.smul_mem _ (C.sub_mem hc₂ hc₁)
      have hle := hammingDist_smul_inv_sub_le (combo x U + u h) (U (row j)) c₁ c₂ hα
      have hagree := smul_inv_sub_eq hα ha₁ ha₂
      have hceq : α⁻¹ • (c₂ - c₁) = c (row j) :=
        hC.eq_of_hammingDist_le hmem (hc (row j)) (a := 2 * e) (b := 2 * e) (by omega)
          (hcd (row j)) (by omega)
      rw [hceq] at hagree
      exact hrowj j hj hagree
    have hsub : (univ.filter fun r : Fin σ → ι → F => Close C e fun h => combo (r h) U + u h) ⊆
        E'.biUnion fun j => Fintype.piFinset (B j) := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨V, hV, hVe⟩ := hr
      obtain ⟨j, hj, hjV⟩ := exists_mem_notMem_of_card_lt_card
        (s := colErrors (fun h => combo (r h) U + u h) V) (t := E')
        (by omega)
      refine mem_biUnion.mpr ⟨j, hj, Fintype.mem_piFinset.mpr fun h => ?_⟩
      simp only [B, mem_filter, mem_univ, true_and]
      refine ⟨V h, hV h, (hammingDist_le_card_colErrors _ V h).trans hVe, ?_⟩
      by_contra hneq
      exact hjV (mem_colErrors.mpr ⟨h, hneq⟩)
    calc _ ≤ #(E'.biUnion fun j => Fintype.piFinset (B j)) * Fintype.card F ^ σ :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ #E' * Fintype.card (ι → F) ^ σ := card_biUnion_piFinset_mul_pow_le E' B hB
      _ = (e + 1) * Fintype.card (ι → F) ^ σ := by rw [hE'card]

end GordieHowe.InterleavedProximity

namespace GordieHowe.InterleavedProximity

open Finset RSCode.BerlekampWelch

variable {F : Type*} [Field F] {n : ℕ}

/-- The evaluation map of `RS_{F,n,k,η}` (Def. 4.1): a coefficient vector of length `k` to the
values of its polynomial at `η`. -/
def rsEval (η : Fin n → F) (k : ℕ) : (Fin k → F) →ₗ[F] (Fin n → F) where
  toFun c j := evalCoeffs c (η j)
  map_add' c c' := by
    funext j
    simp [evalCoeffs, add_mul, sum_add_distrib]
  map_smul' a c := by
    funext j
    simp [evalCoeffs, mul_sum, mul_assoc]

@[simp] theorem rsEval_apply (η : Fin n → F) (k : ℕ) (c : Fin k → F) (j : Fin n) :
    rsEval η k c j = evalCoeffs c (η j) := rfl

/-- The Reed–Solomon code `RS_{F,n,k,η}` (Def. 4.1), as a submodule of `F^n`. -/
def rsCode (η : Fin n → F) (k : ℕ) : Submodule F (Fin n → F) :=
  LinearMap.range (rsEval η k)

theorem mem_rsCode {η : Fin n → F} {k : ℕ} {w : Fin n → F} :
    w ∈ rsCode η k ↔ ∃ c : Fin k → F, rsEval η k c = w :=
  LinearMap.mem_range

/-- `RS_{F,n,k,η}` has minimum distance `n − k + 1` (Def. 4.1). -/
theorem rsCode_isMinDist [DecidableEq F] {η : Fin n → F} (hη : Function.Injective η) (k : ℕ) :
    IsMinDist (rsCode η k) (n - k + 1) := by
  intro w hw hne
  obtain ⟨c, rfl⟩ := mem_rsCode.mp hw
  have hp : ofCoeffs c ≠ 0 := by
    intro h0
    apply hne
    funext j
    simp [← eval_ofCoeffs, h0]
  have hk : 0 < k := by
    by_contra hk
    apply hp
    obtain rfl : k = 0 := by omega
    simp [ofCoeffs]
  have hdeg := natDegree_ofCoeffs_lt hk c
  have hzeros := card_filter_eval_eq_zero_le hη hp
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    fun j => (ofCoeffs c).eval (η j) = 0
  simp only [card_univ, Fintype.card_fin] at hsplit
  have hnorm : hammingNorm (rsEval η k c) = #{j | ¬ (ofCoeffs c).eval (η j) = 0} := by
    simp only [hammingNorm, rsEval_apply, eval_ofCoeffs]
    congr
  have hpos : 0 < hammingNorm (rsEval η k c) := hammingNorm_pos_iff.mpr hne
  omega

end GordieHowe.InterleavedProximity
