-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Moving a projective measurement before a segment of queries

A projective measurement `(P_i)_i` (orthogonal projections with `∑_i P_i = 1`) applied to the
state `φ` before a segment `Seg = U_n O ⋯ U_1 O U_0` of unitaries `U_j` and `n` queries `O`, or
after it, gives two families `(Seg P_i φ)_i` and `(P_i Seg φ)_i` in the direct sum `⊕_i V`. If each
`U_j` commutes with every `P_i` on the state of the run it acts on, and each query moves the
family by at most `ε` (`∑_i ‖P_i O v − O P_i v‖² ≤ ε² ‖v‖²`), then the two families differ by at most
`n ε ‖φ‖` (`norm_segRun_famDiff_le`): one query at a time, the defect grows by the commutator of that
query (DFMS22, ePrint 2021/280, Corollary 3.2, p. 7, is the one-query case in trace distance;
CDHZ26, ePrint 2025/2166, Lemma 5.7, p. 31, the multi-query form for emulated oracles).

Born probabilities then move by at most the distance of the families: for unit vectors `a`, `b`
and an orthogonal projection `Π`, `|‖Π a‖² − ‖Π b‖²| ≤ ‖a − b‖` (`abs_norm_sq_sub_le`). This is the
bound "probabilities move by at most the trace distance, which is at most the vector distance",
proved here directly: with `x = ‖Πa‖`, `y = ‖Πb‖`, `x' = ‖a − Πa‖`, `y' = ‖b − Πb‖`, the difference
`d = x² − y² = y'² − x'²` satisfies `|d| ≤ ‖Π(a − b)‖ (x + y)` and `|d| ≤ ‖(a − b) − Π(a − b)‖ (x' + y')`,
and `(x + y)² (x' + y')² ≤ (x + y)² + (x' + y')²` since `x² + x'² = y² + y'² = 1`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.QROM

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {Λ : Type*} [Fintype Λ]

/-! ### The direct sum of copies of `V` -/

/-- **A family of vectors as a vector of the direct sum** `⊕_i V` (the `L²` sum): the state of
`V ⊗ ℂ^Λ` with the family `x` in the label register; its squared norm is `∑_i ‖x i‖²`
(`norm_famVec_sq`). -/
abbrev famVec (x : Λ → V) : PiLp 2 fun _ : Λ => V :=
  WithLp.toLp 2 x

omit [InnerProductSpace ℂ V] in
theorem norm_famVec_sq (x : Λ → V) : ‖famVec x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

omit [InnerProductSpace ℂ V] in
/-- A norm-preserving map applied to every member preserves the norm of the family. -/
theorem norm_famVec_map {f : V → V} (hf : ∀ v, ‖f v‖ = ‖v‖) (x : Λ → V) :
    ‖famVec fun i => f (x i)‖ = ‖famVec x‖ := by
  have h : ‖famVec fun i => f (x i)‖ ^ 2 = ‖famVec x‖ ^ 2 := by
    rw [norm_famVec_sq, norm_famVec_sq]
    simp_rw [hf]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

omit [InnerProductSpace ℂ V] in
/-- A family whose squared norms sum to at most `r²` has norm at most `r` in the direct sum. -/
theorem norm_famVec_le_of_sum_sq_le {x : Λ → V} {r : ℝ} (hr : 0 ≤ r)
    (h : ∑ i, ‖x i‖ ^ 2 ≤ r ^ 2) : ‖famVec x‖ ≤ r := by
  rw [← norm_famVec_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 h

/-! ### The segment and the swap bound -/

/-- **The run of a segment** `U_j O ⋯ U_1 O U_0 v`: `segRun U O 0 v = U 0 v` and
`segRun U O (j + 1) v = U (j + 1) (O (segRun U O j v))`. -/
def segRun (U : ℕ → V →ₗ[ℂ] V) (O : V →ₗ[ℂ] V) : ℕ → V → V
  | 0, v => U 0 v
  | j + 1, v => U (j + 1) (O (segRun U O j v))

/-- The state the unitary `U j` acts on in the run of `φ`: `φ` for `j = 0`, the query applied to
the run so far afterwards. -/
def segInput (U : ℕ → V →ₗ[ℂ] V) (O : V →ₗ[ℂ] V) (φ : V) : ℕ → V
  | 0 => φ
  | j + 1 => O (segRun U O j φ)

theorem norm_segRun {U : ℕ → V →ₗ[ℂ] V} {O : V →ₗ[ℂ] V} (hU : ∀ j v, ‖U j v‖ = ‖v‖)
    (hO : ∀ v, ‖O v‖ = ‖v‖) (v : V) : ∀ j, ‖segRun U O j v‖ = ‖v‖
  | 0 => hU 0 v
  | j + 1 => by rw [segRun, hU, hO, norm_segRun hU hO v j]

/-- **The swap bound**: if every unitary `U j` commutes with each projector `P i` at the state
`segInput U O φ j` it acts on, and each query moves the measured family by at most `ε ‖v‖`, then
measuring `φ` before the first `j` queries of the segment and measuring after them give families
at distance at most `j ε ‖φ‖`. -/
theorem norm_segRun_famDiff_le (P : Λ → V →ₗ[ℂ] V) {U : ℕ → V →ₗ[ℂ] V} {O : V →ₗ[ℂ] V}
    (hU : ∀ j v, ‖U j v‖ = ‖v‖) (hO : ∀ v, ‖O v‖ = ‖v‖) {ε : ℝ}
    (hε : ∀ v, ‖famVec fun i => P i (O v) - O (P i v)‖ ≤ ε * ‖v‖) {φ : V}
    (hcomm : ∀ j i, U j (P i (segInput U O φ j)) = P i (U j (segInput U O φ j))) :
    ∀ j, ‖famVec fun i => P i (segRun U O j φ) - segRun U O j (P i φ)‖ ≤ j * ε * ‖φ‖
  | 0 => by
    have h : (fun i => P i (segRun U O 0 φ) - segRun U O 0 (P i φ)) = fun _ => 0 := by
      funext i
      have := hcomm 0 i
      simp only [segInput] at this
      simp only [segRun]
      rw [← this, sub_self]
    rw [h]
    simp only [CharP.cast_eq_zero, zero_mul, norm_le_zero_iff]
    rfl
  | j + 1 => by
    set x := segRun U O j φ
    have hsplit : (fun i => P i (segRun U O (j + 1) φ) - segRun U O (j + 1) (P i φ)) =
        fun i => U (j + 1) (P i (O x) - O (P i x)) +
          U (j + 1) (O (P i x - segRun U O j (P i φ))) := by
      funext i
      have := hcomm (j + 1) i
      simp only [segInput] at this
      simp only [segRun]
      rw [← this]
      simp only [map_sub, x]
      abel
    rw [hsplit]
    have h1 := norm_famVec_map (hU (j + 1)) fun i => P i (O x) - O (P i x)
    have h2 := norm_famVec_map (fun v => (hU (j + 1) (O v)).trans (hO v))
      fun i => P i x - segRun U O j (P i φ)
    have hx : ‖x‖ = ‖φ‖ := norm_segRun hU hO φ j
    calc ‖famVec fun i => U (j + 1) (P i (O x) - O (P i x)) +
          U (j + 1) (O (P i x - segRun U O j (P i φ)))‖
        ≤ ‖famVec fun i => U (j + 1) (P i (O x) - O (P i x))‖ +
            ‖famVec fun i => U (j + 1) (O (P i x - segRun U O j (P i φ)))‖ :=
          norm_add_le (famVec fun i => U (j + 1) (P i (O x) - O (P i x)))
            (famVec fun i => U (j + 1) (O (P i x - segRun U O j (P i φ))))
      _ ≤ ε * ‖x‖ + j * ε * ‖φ‖ := by
          rw [h1, h2]
          exact add_le_add (hε x) (norm_segRun_famDiff_le P hU hO hε hcomm j)
      _ = (j + 1 : ℕ) * ε * ‖φ‖ := by
          rw [hx]
          push_cast
          ring

/-! ### Born probabilities of nearby states -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An inequality on two reals: if `0 ≤ P ≤ A` and `0 ≤ Q ≤ 4 − A`, then `P Q ≤ P + Q`, since
`(P − 1)(Q − 1) ≤ (A − 1)(3 − A) ≤ 1` when both factors are nonnegative. -/
theorem mul_le_add_of_le_two_mul {P Q A : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hP : P ≤ A)
    (hQ : Q ≤ 4 - A) : P * Q ≤ P + Q := by
  rcases le_total P 1 with hP1 | hP1
  · nlinarith
  · rcases le_total Q 1 with hQ1 | hQ1
    · nlinarith
    · have h1 : (P - 1) * (Q - 1) ≤ (A - 1) * (3 - A) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      nlinarith [sq_nonneg (A - 2)]

/-- **Born probabilities of two unit vectors differ by at most their distance**: for a linear map
`Pr` with `‖Pr v‖² + ‖v − Pr v‖² = ‖v‖²` (an orthogonal projection), `|‖Pr a‖² − ‖Pr b‖²| ≤ ‖a − b‖`
(module docstring). -/
theorem abs_norm_sq_sub_le (Pr : E →ₗ[ℂ] E) (hPr : ∀ v, ‖Pr v‖ ^ 2 + ‖v - Pr v‖ ^ 2 = ‖v‖ ^ 2)
    {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |‖Pr a‖ ^ 2 - ‖Pr b‖ ^ 2| ≤ ‖a - b‖ := by
  set x := ‖Pr a‖
  set y := ‖Pr b‖
  set x' := ‖a - Pr a‖
  set y' := ‖b - Pr b‖
  set δ₁ := ‖Pr (a - b)‖
  set δ₂ := ‖(a - b) - Pr (a - b)‖
  have hx := hPr a
  have hy := hPr b
  rw [ha] at hx
  rw [hb] at hy
  have hδ : δ₁ ^ 2 + δ₂ ^ 2 = ‖a - b‖ ^ 2 := hPr (a - b)
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have hx'0 : 0 ≤ x' := norm_nonneg _
  have hy'0 : 0 ≤ y' := norm_nonneg _
  have hδ₁ : |x - y| ≤ δ₁ := by
    show |‖Pr a‖ - ‖Pr b‖| ≤ ‖Pr (a - b)‖
    rw [map_sub]
    exact abs_norm_sub_norm_le _ _
  have hδ₂ : |x' - y'| ≤ δ₂ := by
    have : (a - b) - Pr (a - b) = (a - Pr a) - (b - Pr b) := by
      rw [map_sub]
      abel
    show |‖a - Pr a‖ - ‖b - Pr b‖| ≤ ‖(a - b) - Pr (a - b)‖
    rw [this]
    exact abs_norm_sub_norm_le _ _
  set d := x ^ 2 - y ^ 2
  have hd1 : |d| ≤ δ₁ * (x + y) := by
    rw [show d = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x + y)]
    exact mul_le_mul_of_nonneg_right hδ₁ (by positivity)
  have hd2 : |d| ≤ δ₂ * (x' + y') := by
    rw [show d = -((x' - y') * (x' + y')) by
        have : x ^ 2 - y ^ 2 = y' ^ 2 - x' ^ 2 := by linarith
        rw [show d = x ^ 2 - y ^ 2 from rfl, this]
        ring,
      abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x' + y')]
    exact mul_le_mul_of_nonneg_right hδ₂ (by positivity)
  set p := x + y
  set q := x' + y'
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  -- `p² q² ≤ p² + q²`, from `p² ≤ 2(x² + y²)` and `q² ≤ 2(x'² + y'²) = 4 − 2(x² + y²)`
  have hpq : p ^ 2 * q ^ 2 ≤ p ^ 2 + q ^ 2 := by
    have hp2 : p ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
    have hq2 : q ^ 2 ≤ 2 * (x' ^ 2 + y' ^ 2) := by nlinarith [sq_nonneg (x' - y')]
    exact mul_le_add_of_le_two_mul (sq_nonneg p) (sq_nonneg q) hp2 (by linarith)
  have hpq0 : 0 < p ^ 2 + q ^ 2 := by
    have h1 : x ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hx0 (by linarith) 2
    have h2 : x' ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hx'0 (by linarith) 2
    have h3 : x ^ 2 + x' ^ 2 = 1 := by rw [hx, one_pow]
    linarith
  have hd1' : d ^ 2 ≤ δ₁ ^ 2 * p ^ 2 := by
    rw [← sq_abs d]
    calc |d| ^ 2 ≤ (δ₁ * p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd1 2
      _ = δ₁ ^ 2 * p ^ 2 := by ring
  have hd2' : d ^ 2 ≤ δ₂ ^ 2 * q ^ 2 := by
    rw [← sq_abs d]
    calc |d| ^ 2 ≤ (δ₂ * q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd2 2
      _ = δ₂ ^ 2 * q ^ 2 := by ring
  have hkey : d ^ 2 * (p ^ 2 + q ^ 2) ≤ (δ₁ ^ 2 + δ₂ ^ 2) * (p ^ 2 + q ^ 2) := by
    have h1 : d ^ 2 * q ^ 2 ≤ δ₁ ^ 2 * (p ^ 2 * q ^ 2) :=
      (mul_le_mul_of_nonneg_right hd1' (sq_nonneg q)).trans_eq (by ring)
    have h2 : d ^ 2 * p ^ 2 ≤ δ₂ ^ 2 * (p ^ 2 * q ^ 2) :=
      (mul_le_mul_of_nonneg_right hd2' (sq_nonneg p)).trans_eq (by ring)
    have h3 : δ₁ ^ 2 * (p ^ 2 * q ^ 2) ≤ δ₁ ^ 2 * (p ^ 2 + q ^ 2) :=
      mul_le_mul_of_nonneg_left hpq (sq_nonneg _)
    have h4 : δ₂ ^ 2 * (p ^ 2 * q ^ 2) ≤ δ₂ ^ 2 * (p ^ 2 + q ^ 2) :=
      mul_le_mul_of_nonneg_left hpq (sq_nonneg _)
    have e1 : d ^ 2 * (p ^ 2 + q ^ 2) = d ^ 2 * p ^ 2 + d ^ 2 * q ^ 2 := by ring
    have e2 : (δ₁ ^ 2 + δ₂ ^ 2) * (p ^ 2 + q ^ 2) =
        δ₁ ^ 2 * (p ^ 2 + q ^ 2) + δ₂ ^ 2 * (p ^ 2 + q ^ 2) := by ring
    rw [e1, e2]
    linarith
  have hsq : d ^ 2 ≤ ‖a - b‖ ^ 2 := by
    rw [← hδ]
    exact le_of_mul_le_mul_right hkey hpq0
  rw [← sq_abs d] at hsq
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

end GordieHowe.QROM
