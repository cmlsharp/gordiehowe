-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Reprogram
public import GordieHowe.Foundations.ToMathlib.UniformFunction
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Headline

@[expose] public section

/-!
# A residual-state test that queries the oracle defeats extractors that simulate it

Unruh 2017 (ePrint 2017/398) Definition 14, eq. (6) (p. 21), tests the adversary's residual state
in the Extract game with a projective measurement that may query `H(ass)`: the game's uniformly
random oracle `H` patched by a classical assignment list `ass` of length at most `ℓ` that the
extractor outputs. This file proves the following boundary result (our statement).

**The oracle-test gap lemma.** Let `X0` be a set of `N` oracle inputs. Consider an adversary that,
besides its honest run, queries the uniform superposition `N^-1/2 ∑_{x ∈ X0} |x⟩|0⟩` once and keeps
both registers, and the test that queries the oracle once more to uncompute the answer and projects
onto `N^-1/2 ∑_{x ∈ X0} |x⟩|0⟩` (`testAccept`). In Prove, where the final oracle is `H` on `X0`, the
kept registers are the graph state `χ_H = N^-1/2 ∑_{x ∈ X0} |x, H x⟩` and the test accepts with
probability `1`. In Extract, for every extractor whose output — the
residual state of the kept registers together with its classical assignment list — has a law that
does not depend on `H` on `X0` (`BlindExtractor`; every extractor that answers the adversary's
queries on `X0` from registers it prepared itself, without querying `H` there, is of this kind), the
test against `H(ass)` accepts with probability at most `(1/√|Y| + √(ℓ / N))²`
(`BlindExtractor.extractAccept_le`), so the gap between Prove and Extract is at least
`1 − (2^-m/2 + √(ℓ/N))²` for `|Y| = 2^m`. With Prove near `1` and Extract
negligible along a family, eq. (6) fails eventually for every polynomial `p`, degree `d` and
negligible `µ` (`eq6_fails_eventually`).

The straight-line extractors of the literature (CMS19's database extractor, used here; the
extractable random-oracle simulator of DFMS21; the emulated oracles of CDHZ26) answer every query
from a simulated oracle, so none meets eq. (6) literally for tests that query the oracle. The
variant of eq. (6) in which the test queries the extractor's simulated oracle is proved for the
spBCS compiler (`SPBCS.simulation_sound_extractability_sim_oracle`).

**The proof.** For each value of `H` off `X0` the extractor's output is
fixed, and `H` on `X0` is uniform and independent of it (`expect_patch`). Fix a residual vector `φ`
and an assignment list `ass`. The overlap `⟨χ_{H(ass)}, φ⟩` splits into the inputs of `X0` without
an assignment, where `H(ass) = H` is uniform, and those with one, at most `ℓ`, whose part has norm
at most `√(ℓ/N)`. On the first part the average squared overlap is at most `1/|Y|`
(`expect_norm_sum_sq_le`: distinct inputs have independent uniform values; Cauchy–Schwarz). Jensen's
inequality combines the two.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GordieHowe.Quantum

/-! ### Reprogramming at an assigned input -/

section Assigned

variable {X Y : Type*} [DecidableEq X]

/-- An input with an assignment has a value in `lastAssign`. -/
theorem lastAssign_isSome_of_assigned {ass : List (Assignment X Y)} {x : X}
    (h : ∃ a ∈ ass, a.input = x) : (lastAssign ass x).isSome := by
  induction ass using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l a ih =>
    rw [lastAssign_append_singleton]
    by_cases ha : a.input = x
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      obtain ⟨b, hb, hbx⟩ := h
      rcases List.mem_append.1 hb with hb | hb
      · exact ih ⟨b, hb, hbx⟩
      · rw [List.mem_singleton] at hb
        exact absurd (hb ▸ hbx) ha

/-- **At an assigned input, a reprogrammed oracle does not depend on the base oracle.** -/
theorem reprogram_apply_eq_of_assigned (H H' : X → Y) {ass : List (Assignment X Y)} {x : X}
    (h : ∃ a ∈ ass, a.input = x) : H.reprogram ass x = H'.reprogram ass x := by
  rw [reprogram_apply_eq_lastAssign, reprogram_apply_eq_lastAssign]
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (lastAssign_isSome_of_assigned h)
  rw [hy]
  rfl

end Assigned

/-! ### The graph state and the test -/

theorem inner_eq_sum_conj {ι : Type*} [Fintype ι] (u v : QState ι) :
    inner ℂ u v = ∑ i, conj (u i) * v i := by
  simp [PiLp.inner_apply, mul_comm]

section Test

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **The graph state of `G` on `X0`**: `N^-1/2 ∑_{x ∈ X0} |x, G x⟩`, `N = |X0|`. -/
noncomputable def graphState (X0 : Finset X) (G : X → Y) : QState (X × Y) :=
  WithLp.toLp 2 fun p => if p.1 ∈ X0 ∧ p.2 = G p.1 then (((√(X0.card : ℝ))⁻¹ : ℝ) : ℂ) else 0

/-- The uniform superposition of `X0` with the answer register at `0`: the graph state of the
zero function. -/
noncomputable def zeroUniform [Zero Y] (X0 : Finset X) : QState (X × Y) :=
  graphState X0 0

/-- The query that uncomputes an answer of `G`: `|x, y⟩ ↦ |x, y − G x⟩`. -/
def uncompute [AddGroup Y] (G : X → Y) : Equiv.Perm (X × Y) :=
  Equiv.prodShear (Equiv.refl X) fun x => Equiv.subRight (G x)

/-- **The residual-state test**: one query to the oracle `G` that
uncomputes the answer register, then the projective measurement onto the uniform superposition
of `X0` with the answer register at `0`; the probability that it accepts the vector `φ`. -/
noncomputable def testAccept [AddGroup Y] (X0 : Finset X) (G : X → Y) (φ : QState (X × Y)) : ℝ :=
  ‖inner ℂ (zeroUniform X0) (permOp (uncompute G) φ)‖ ^ 2

theorem inner_graphState (X0 : Finset X) (G : X → Y) (φ : QState (X × Y)) :
    inner ℂ (graphState X0 G) φ = (((√(X0.card : ℝ))⁻¹ : ℝ) : ℂ) * ∑ x ∈ X0, φ (x, G x) := by
  rw [inner_eq_sum_conj, Fintype.sum_prod_type, mul_sum, ← sum_filter_add_sum_filter_not univ
    (· ∈ X0), filter_mem_eq_inter, univ_inter]
  have h0 : ∑ x ∈ univ.filter (· ∉ X0), ∑ y, conj ((graphState X0 G) (x, y)) * φ (x, y) = 0 :=
    sum_eq_zero fun x hx => sum_eq_zero fun y _ => by
      simp only [mem_filter, mem_univ, true_and] at hx
      simp [graphState, hx]
  rw [h0, add_zero]
  refine sum_congr rfl fun x hx => ?_
  rw [Fintype.sum_eq_single (G x) fun y hy => by simp [graphState, hy]]
  simp [graphState, hx]

theorem permOp_uncompute_graphState [AddGroup Y] (X0 : Finset X) (G : X → Y) :
    permOp (uncompute G) (graphState X0 G) = zeroUniform X0 := by
  ext ⟨x, y⟩
  simp [permOp_apply, uncompute, zeroUniform, graphState]

/-- **The test projects onto the graph state of the oracle**: its acceptance probability is the
squared overlap with `χ_G`. -/
theorem testAccept_eq [AddGroup Y] (X0 : Finset X) (G : X → Y) (φ : QState (X × Y)) :
    testAccept X0 G φ = ‖inner ℂ (graphState X0 G) φ‖ ^ 2 := by
  rw [testAccept, ← permOp_uncompute_graphState, LinearIsometryEquiv.inner_map_map]

end Test

/-! ### Averages over the oracle on `X0` -/

section Average

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- `H` off `X0` and `F` on `X0`. -/
def patch (X0 : Finset X) (H F : X → Y) : X → Y :=
  fun x => if x ∈ X0 then F x else H x

/-- **The oracle on `X0` is uniform and independent of the oracle off `X0`**: averaging a function
of a uniform oracle is averaging it over the oracle off `X0` and, independently, on `X0`. The map
`(H, F) ↦ (patch H F, patch F H)` is an involution. -/
theorem expect_patch (X0 : Finset X) (f : (X → Y) → ℝ) :
    𝔼 H : X → Y, f H = 𝔼 H : X → Y, 𝔼 F : X → Y, f (patch X0 H F) := by
  let e : Equiv.Perm ((X → Y) × (X → Y)) := Function.Involutive.toPerm
    (fun p => (patch X0 p.1 p.2, patch X0 p.2 p.1)) fun p => by
      ext x <;> by_cases hx : x ∈ X0 <;> simp [patch, hx]
  have h := Fintype.expect_equiv e (fun p => f (patch X0 p.1 p.2)) (fun q => f q.1) fun p => rfl
  simp only [← Finset.univ_product_univ, Finset.expect_product] at h
  rw [h]
  simp

end Average

/-! ### The average squared overlap on the inputs without an assignment -/

section Overlap

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

theorem conj_expect {ι : Type*} [Fintype ι] (f : ι → ℂ) : conj (𝔼 i, f i) = 𝔼 i, conj (f i) := by
  simp [Finset.expect_eq_sum_div_card, map_sum, map_div₀]

/-- **The average squared overlap of uniform independent values** (the
bound `‖E_H |χ_out⟩⟨χ_out|‖ ≤ 2^-m`): for a uniform `F` and a set `S` of inputs,
`E_F |∑_{x ∈ S} φ(x, F x)|² ≤ (|S| / |Y|) ∑_{x ∈ S} ∑_y |φ(x, y)|²`. Distinct inputs have
independent uniform values, and Cauchy–Schwarz bounds the cross terms. -/
theorem expect_norm_sum_sq_le (S : Finset X) (φ : QState (X × Y)) :
    𝔼 F : X → Y, ‖∑ x ∈ S, φ (x, F x)‖ ^ 2 ≤
      S.card / Fintype.card Y * ∑ x ∈ S, ∑ y, ‖φ (x, y)‖ ^ 2 := by
  set μ : X → ℂ := fun x => 𝔼 y, φ (x, y)
  set a : X → ℝ := fun x => 𝔼 y, ‖φ (x, y)‖ ^ 2
  have hY : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  -- the norm as a double sum
  have hsq : ∀ F : X → Y, ‖∑ x ∈ S, φ (x, F x)‖ ^ 2 =
      (∑ x ∈ S, ∑ x' ∈ S, conj (φ (x, F x)) * φ (x', F x')).re := by
    intro F
    rw [← sum_mul_sum, ← map_sum, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  -- the average of each term
  have hterm : ∀ x x', 𝔼 F : X → Y, conj (φ (x, F x)) * φ (x', F x') =
      if x = x' then ((a x : ℝ) : ℂ) else conj (μ x) * μ x' := by
    intro x x'
    split_ifs with h
    · subst h
      rw [expect_comp_apply x (fun y => conj (φ (x, y)) * φ (x, y)), Complex.ofReal_expect]
      refine Finset.expect_congr rfl fun y _ => ?_
      rw [Complex.conj_mul', Complex.ofReal_pow]
    · rw [expect_comp_apply_mul_comp_apply h (fun y => conj (φ (x, y))) (fun y => φ (x', y)),
        conj_expect]
  have hsplit : ∑ x ∈ S, ∑ x' ∈ S, (if x = x' then ((a x : ℝ) : ℂ) else conj (μ x) * μ x') =
      ∑ x ∈ S, (((a x : ℝ) : ℂ) - conj (μ x) * μ x) + conj (∑ x ∈ S, μ x) * ∑ x ∈ S, μ x := by
    rw [map_sum, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    have he : ∀ x', (if x = x' then ((a x : ℝ) : ℂ) else conj (μ x) * μ x') =
        conj (μ x) * μ x' + if x = x' then ((a x : ℝ) : ℂ) - conj (μ x) * μ x else 0 := by
      intro x'
      split_ifs with h
      · subst h
        ring
      · ring
    rw [sum_congr rfl fun x' _ => he x', sum_add_distrib, sum_ite_eq S x]
    simp only [hx, ↓reduceIte]
    ring
  have hexp : 𝔼 F : X → Y, ‖∑ x ∈ S, φ (x, F x)‖ ^ 2 =
      ∑ x ∈ S, (a x - ‖μ x‖ ^ 2) + ‖∑ x ∈ S, μ x‖ ^ 2 := by
    simp_rw [hsq]
    rw [← Complex.re_expect, Finset.expect_sum_comm]
    simp_rw [Finset.expect_sum_comm, hterm]
    rw [hsplit, Complex.add_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.re_sum]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [Complex.sub_re, Complex.ofReal_re, Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.ofReal_re]
  -- the bounds
  have hμ : ∀ x, ‖μ x‖ ^ 2 ≤ a x := by
    intro x
    have h1 : ‖μ x‖ ≤ 𝔼 y, ‖φ (x, y)‖ := RCLike.norm_expect_le (K := ℂ)
    have h2 := expect_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) fun y => ‖φ (x, y)‖
    simp only [one_mul, one_pow, Finset.expect_const univ_nonempty] at h2
    calc ‖μ x‖ ^ 2 ≤ (𝔼 y, ‖φ (x, y)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ a x := by simpa using h2
  have hsum : ‖∑ x ∈ S, μ x‖ ^ 2 ≤ S.card * ∑ x ∈ S, ‖μ x‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
  have ha : ∑ x ∈ S, ∑ y, ‖φ (x, y)‖ ^ 2 = Fintype.card Y * ∑ x ∈ S, a x := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [a, Finset.expect_eq_sum_div_card, card_univ]
    field_simp
  rw [hexp, ha, ← mul_assoc, div_mul_cancel₀ _ hY.ne']
  have hma : ∑ x ∈ S, ‖μ x‖ ^ 2 ≤ ∑ x ∈ S, a x := sum_le_sum fun x _ => hμ x
  have hm0 : 0 ≤ ∑ x ∈ S, ‖μ x‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_sub_distrib]
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · have h1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
    nlinarith

end Overlap

/-! ### The oracle-test gap lemma -/

section Lemma1

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

/-- **The test against a reprogrammed oracle whose values on the unassigned inputs of `X0` are
uniform** (the oracle-test gap lemma at a fixed residual vector and assignment list): for
a vector `φ` of norm at most `1` and an assignment list of length at most `ℓ`, the test against
`(patch H F)(ass)` accepts `φ`, averaged over a uniform `F` (the oracle on `X0`), with probability at
most `(1/√|Y| + √(ℓ / N))²`. -/
theorem expect_testAccept_patch_le {X0 : Finset X} (hX0 : X0.Nonempty) (H : X → Y)
    {φ : QState (X × Y)} (hφ : ‖φ‖ ≤ 1) {ℓ : ℕ} {ass : List (Assignment X Y)}
    (hass : ass.length ≤ ℓ) :
    𝔼 F : X → Y, testAccept X0 ((patch X0 H F).reprogram ass) φ ≤
      ((√(Fintype.card Y : ℝ))⁻¹ + √(ℓ / X0.card)) ^ 2 := by
  classical
  set N : ℝ := (X0.card : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 hX0.card_pos
  have hY : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.2 Fintype.card_pos
  set D := X0.filter fun x => ∃ a ∈ ass, a.input = x
  set S := X0.filter fun x => ¬ ∃ a ∈ ass, a.input = x
  set v : X → Y := H.reprogram ass
  set c0 : ℂ := ∑ x ∈ D, φ (x, v x)
  set A : (X → Y) → ℂ := fun F => ∑ x ∈ S, φ (x, F x)
  -- the overlap splits into the unassigned and the assigned inputs
  have hsplit : ∀ F, ∑ x ∈ X0, φ (x, (patch X0 H F).reprogram ass x) = A F + c0 := by
    intro F
    rw [← sum_filter_not_add_sum_filter X0 fun x => ∃ a ∈ ass, a.input = x]
    congr 1
    · refine sum_congr rfl fun x hx => ?_
      simp only [S, mem_filter] at hx
      rw [QROM.reprogram_apply_of_forall_ne _ fun a ha e => hx.2 ⟨a, ha, e⟩]
      simp [patch, hx.1]
    · refine sum_congr rfl fun x hx => ?_
      simp only [D, mem_filter] at hx
      rw [reprogram_apply_eq_of_assigned _ H hx.2]
  have hacc : ∀ F, testAccept X0 ((patch X0 H F).reprogram ass) φ = ‖A F + c0‖ ^ 2 / N := by
    intro F
    rw [testAccept_eq, inner_graphState, hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_pow, inv_pow, Real.sq_sqrt hN.le]
    ring
  -- the assigned part
  have hφsq : ∑ p, ‖φ p‖ ^ 2 ≤ 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    exact pow_le_one₀ (norm_nonneg _) hφ
  have hD : (D.card : ℝ) ≤ ℓ := by
    have : D ⊆ (ass.map Assignment.input).toFinset := fun x hx => by
      simp only [D, mem_filter] at hx
      obtain ⟨a, ha, rfl⟩ := hx.2
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨a, ha, rfl⟩
    have h1 := (card_le_card this).trans ((List.toFinset_card_le _).trans_eq (List.length_map _))
    exact_mod_cast h1.trans hass
  have hc0 : ‖c0‖ ≤ √ℓ := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : ‖c0‖ ^ 2 ≤ D.card * ∑ x ∈ D, ‖φ (x, v x)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
    have h2 : ∑ x ∈ D, ‖φ (x, v x)‖ ^ 2 ≤ 1 := by
      rw [← sum_image (f := fun p => ‖φ p‖ ^ 2) (g := fun x => (x, v x))
        fun x _ y _ h => (Prod.ext_iff.1 h).1]
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _).trans hφsq
    calc ‖c0‖ ^ 2 ≤ D.card * 1 := h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
      _ ≤ ℓ := by rw [mul_one]; exact hD
  -- the unassigned part
  have hA : 𝔼 F : X → Y, ‖A F‖ ^ 2 ≤ N / Fintype.card Y := by
    refine (expect_norm_sum_sq_le S φ).trans ?_
    have hS : (S.card : ℝ) ≤ N := by
      simp only [N]
      exact_mod_cast card_le_card (filter_subset _ X0)
    have hsum : ∑ x ∈ S, ∑ y, ‖φ (x, y)‖ ^ 2 ≤ 1 := by
      refine le_trans ?_ hφsq
      rw [Fintype.sum_prod_type]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ =>
        sum_nonneg fun _ _ => sq_nonneg _
    calc (S.card : ℝ) / Fintype.card Y * ∑ x ∈ S, ∑ y, ‖φ (x, y)‖ ^ 2
        ≤ N / Fintype.card Y * 1 := by gcongr
      _ = N / Fintype.card Y := mul_one _
  -- Jensen
  set e := 𝔼 F : X → Y, ‖A F‖ ^ 2
  have he0 : 0 ≤ e := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hjensen : 𝔼 F : X → Y, ‖A F‖ ≤ √e := by
    have := Real.expect_sqrt_le_sqrt_expect (fun F => ‖A F‖ ^ 2) fun _ => sq_nonneg _
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hmain : 𝔼 F : X → Y, ‖A F + c0‖ ^ 2 ≤ (√e + ‖c0‖) ^ 2 := by
    calc 𝔼 F : X → Y, ‖A F + c0‖ ^ 2
        ≤ 𝔼 F : X → Y, (‖A F‖ ^ 2 + 2 * ‖c0‖ * ‖A F‖ + ‖c0‖ ^ 2) :=
          Finset.expect_le_expect fun F _ => by
            nlinarith [norm_add_le (A F) c0, norm_nonneg (A F + c0), norm_nonneg (A F),
              norm_nonneg c0]
      _ = e + 2 * ‖c0‖ * 𝔼 F : X → Y, ‖A F‖ + ‖c0‖ ^ 2 := by
          rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
            Finset.expect_const univ_nonempty]
      _ ≤ e + 2 * ‖c0‖ * √e + ‖c0‖ ^ 2 := by gcongr
      _ = (√e + ‖c0‖) ^ 2 := by
          rw [add_sq, Real.sq_sqrt he0]
          ring
  simp_rw [hacc]
  rw [← Finset.expect_div]
  have hse : √e ≤ √(N / Fintype.card Y) := Real.sqrt_le_sqrt hA
  calc (𝔼 F : X → Y, ‖A F + c0‖ ^ 2) / N ≤ (√(N / Fintype.card Y) + √ℓ) ^ 2 / N := by
        gcongr
        exact hmain.trans (by gcongr)
    _ = ((√(Fintype.card Y : ℝ))⁻¹ + √(ℓ / N)) ^ 2 := by
        rw [Real.sqrt_div hN.le, Real.sqrt_div' _ hN.le]
        have hsN : 0 < √N := Real.sqrt_pos.2 hN
        field_simp
        exact Real.sq_sqrt hN.le

/-- **An extractor that does not consult the oracle on `X0`** (the hypothesis of the oracle-test gap
lemma): what Unruh's Extract game hands to the test after the extractor has run — the residual state
of the adversary's kept registers `X × Y` and the classical assignment list `ass` of length at most
`ℓ` — given as a finite ensemble of outcomes `o` with probabilities `law H o`, a residual vector
`residual o` and an assignment list `assignments o`, whose law depends on the oracle `H` only off
`X0` (`blind`).

Modelling. Every joint state of a classical assignment list and a quantum register is a finite
mixture of pure states with classical labels, so the ensemble form is general (unnormalized
vectors of norm at most `1` are allowed). An extractor that answers the adversary's queries on
`X0` from registers it prepared itself, never querying `H` on `X0` (and never invoking Unruh's
`Π^{oracle,H,ℓ}` there), runs the same for any two oracles that agree off `X0`, so its output law
depends on `H` only off `X0`: this is the class. CMS19's database extractor, the extractable
random-oracle simulator of DFMS21 (Fig. 2, p. 11) and the emulated oracles of CDHZ26
(Definitions 7.3 and 10.3) answer all queries from a simulated oracle and belong to it. -/
structure BlindExtractor (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] (X0 : Finset X)
    (ℓ : ℕ) where
  /-- The outcomes of the extraction. -/
  Out : Type
  [instFintypeOut : Fintype Out]
  /-- The probability of each outcome for the oracle `H`. -/
  law : (X → Y) → Out → ℝ
  law_nonneg : ∀ H o, 0 ≤ law H o
  law_sum : ∀ H, ∑ o, law H o = 1
  /-- The residual vector of the kept registers at each outcome. -/
  residual : Out → QState (X × Y)
  norm_residual_le : ∀ o, ‖residual o‖ ≤ 1
  /-- The assignment list output at each outcome. -/
  assignments : Out → List (Assignment X Y)
  length_assignments_le : ∀ o, (assignments o).length ≤ ℓ
  /-- The law does not depend on the oracle on `X0`. -/
  blind : ∀ H H' : X → Y, (∀ x ∉ X0, H x = H' x) → law H = law H'

attribute [instance] BlindExtractor.instFintypeOut

namespace BlindExtractor

variable {X0 : Finset X} {ℓ : ℕ} (E : BlindExtractor X Y X0 ℓ)

/-- **The probability that the test accepts in Extract** (Unruh 2017 Definition 14, Extract,
`ok_A ← Π^{H(ass)}_{x‖π}(S_A)` after the extractor): the oracle uniform, the extractor's outcome
drawn, and the test of the residual vector against the oracle reprogrammed by the output
assignment list. -/
noncomputable def extractAccept : ℝ :=
  𝔼 H : X → Y, ∑ o, E.law H o * testAccept X0 (H.reprogram (E.assignments o)) (E.residual o)

/-- **The oracle-test gap lemma** (our statement): for every extractor that does not consult the
oracle on `X0`, the test accepts in Extract with probability at most
`(1/√|Y| + √(ℓ / N))²`, `N = |X0|`. -/
theorem extractAccept_le (hX0 : X0.Nonempty) :
    E.extractAccept ≤ ((√(Fintype.card Y : ℝ))⁻¹ + √(ℓ / X0.card)) ^ 2 := by
  set B := ((√(Fintype.card Y : ℝ))⁻¹ + √(ℓ / X0.card)) ^ 2
  rw [extractAccept, expect_patch X0]
  have hlaw : ∀ H F, E.law (patch X0 H F) = E.law H := fun H F =>
    E.blind _ _ fun x hx => by simp [patch, hx]
  have key : ∀ H, 𝔼 F : X → Y, ∑ o, E.law H o *
      testAccept X0 ((patch X0 H F).reprogram (E.assignments o)) (E.residual o) ≤ B := by
    intro H
    rw [Finset.expect_sum_comm]
    calc ∑ o, 𝔼 F : X → Y, E.law H o *
          testAccept X0 ((patch X0 H F).reprogram (E.assignments o)) (E.residual o)
        = ∑ o, E.law H o * 𝔼 F : X → Y,
            testAccept X0 ((patch X0 H F).reprogram (E.assignments o)) (E.residual o) :=
          sum_congr rfl fun o _ => (Finset.mul_expect _ _ _).symm
      _ ≤ ∑ o, E.law H o * B := sum_le_sum fun o _ =>
          mul_le_mul_of_nonneg_left (expect_testAccept_patch_le hX0 H (E.norm_residual_le o)
            (E.length_assignments_le o)) (E.law_nonneg H o)
      _ = B := by rw [← sum_mul, E.law_sum, one_mul]
  simp_rw [hlaw]
  exact (Finset.expect_le_expect fun H _ => key H).trans_eq (Finset.expect_const univ_nonempty B)

end BlindExtractor

end Lemma1

/-- **Eq. (6) fails eventually when Prove is near `1` and Extract is negligible** (the arithmetic
after the oracle-test gap lemma): if Prove succeeds with probability at least `1 − ε`,
`ε` eventually at most `1/2`, Extract with probability at most `a`, and `a` and `µ` are negligible
(below `η^-k` eventually, for every `k`; Unruh 2017, Definition 14, p. 21, quantifies over "a
negligible `µ`"), then for every `p` bounded by `C η^c` and every `d`, eventually
`Pr[Extract] < (1/p) Pr[Prove]^d − µ`. -/
theorem eq6_fails_eventually {prove extract a μ ε p : ℕ → ℝ} {C : ℝ} {c d : ℕ} (hC : 0 < C)
    (hp : ∀ η, 0 < p η) (hpoly : ∀ η, p η ≤ C * (η : ℝ) ^ c)
    (hprove : ∀ᶠ η in Filter.atTop, 1 - ε η ≤ prove η) (hε : ∀ᶠ η in Filter.atTop, ε η ≤ 1 / 2)
    (hext : ∀ᶠ η in Filter.atTop, extract η ≤ a η)
    (ha : ∀ k : ℕ, ∀ᶠ η : ℕ in Filter.atTop, (η : ℝ) ^ k * a η ≤ 1)
    (hμ : ∀ k : ℕ, ∀ᶠ η : ℕ in Filter.atTop, (η : ℝ) ^ k * μ η ≤ 1) :
    ∀ᶠ η in Filter.atTop, extract η < (p η)⁻¹ * prove η ^ d - μ η := by
  filter_upwards [hprove, hε, hext, ha (c + 1), hμ (c + 1),
    Filter.eventually_gt_atTop ⌈4 * C * 2 ^ d⌉₊] with η h1 h2 h3 h4 h5 h6
  have hx : 4 * C * 2 ^ d < (η : ℝ) := Nat.lt_of_ceil_lt h6
  have hx0 : (0 : ℝ) < η := lt_of_le_of_lt (by positivity) hx
  have hxc : (0 : ℝ) < (η : ℝ) ^ c := pow_pos hx0 c
  have hxc1 : (0 : ℝ) < (η : ℝ) ^ (c + 1) := pow_pos hx0 (c + 1)
  have hprove' : (1 / 2 : ℝ) ≤ prove η := by linarith
  have hpow : (1 / 2 : ℝ) ^ d ≤ prove η ^ d := pow_le_pow_left₀ (by norm_num) hprove' d
  have hpinv : (C * (η : ℝ) ^ c)⁻¹ ≤ (p η)⁻¹ := inv_anti₀ (hp η) (hpoly η)
  have hlow : (C * (η : ℝ) ^ c)⁻¹ * (1 / 2 : ℝ) ^ d ≤ (p η)⁻¹ * prove η ^ d :=
    mul_le_mul hpinv hpow (by positivity) (inv_nonneg.2 (hp η).le)
  have ha' : a η ≤ 1 / (η : ℝ) ^ (c + 1) := (le_div_iff₀' hxc1).2 h4
  have hμ' : μ η ≤ 1 / (η : ℝ) ^ (c + 1) := (le_div_iff₀' hxc1).2 h5
  have key : 2 / (η : ℝ) ^ (c + 1) < (C * (η : ℝ) ^ c)⁻¹ * (1 / 2 : ℝ) ^ d := by
    rw [show (C * (η : ℝ) ^ c)⁻¹ * (1 / 2 : ℝ) ^ d = 1 / (C * 2 ^ d * (η : ℝ) ^ c) by
      rw [one_div, inv_pow]
      field_simp, show 2 / (η : ℝ) ^ (c + 1) = 2 / ((η : ℝ) * (η : ℝ) ^ c) by ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have h2 : (0 : ℝ) < ((η : ℝ) - 2 * C * 2 ^ d) * (η : ℝ) ^ c :=
      mul_pos (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) d]) hxc
    nlinarith
  have hsum : 1 / (η : ℝ) ^ (c + 1) + 1 / (η : ℝ) ^ (c + 1) = 2 / (η : ℝ) ^ (c + 1) := by ring
  linarith

end GordieHowe.Quantum
