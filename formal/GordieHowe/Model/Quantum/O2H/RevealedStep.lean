-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.JuntaDegree

@[expose] public section

/-!
# One reprogramming of a purified oracle at a revealed set

The step of Grilo, Hövelmanns, Hülsing and Majenz ("Tight adaptive reprogramming in the QROM",
ASIACRYPT 2021, ePrint 2020/1361; GHHM21), Theorem 6, in a form that compares two families of
runs averaged over a random oracle `h : X → Y` and fresh values `z : X → Y`.

Let `γ h` be the state of a run at the oracle `h` just before the reprogramming of the oracle on
a finite set `S`, and `V h` the rest of the run with the oracle `h`, which no longer depends on the
fresh values. Without reprogramming the run ends in `V h (γ h)`. With the values of the oracle on
`S` replaced by the fresh values `z` and the two exchanged (`swapOn S`, which preserves the
uniform law of `(h, z)`), it ends in `V h (γ (setOn S h z))`: the state before the reprogramming
was produced by the oracle `setOn S h z`, and the rest of the run uses `h`.
`abs_sum_prob_sub_le` bounds the difference of the two average acceptance probabilities by
`√(∑ ‖γ h‖²) √(∑ ‖γ h − Π_S γ h‖²) + ½ ∑ ‖γ h − Π_S γ h‖²` (times `|Y^X|`, for the sums over the
pairs), where `Π_S` averages over the values of the oracle on `S` (`avgOn`). This is GHHM21
equation (11) averaged over the oracle, `√ε + ε/2` for `ε = ‖(1 − Π_S) γ‖²` and a unit state.

The proof differs from GHHM21's, which bounds the trace distance of the two density matrices. It
writes the acceptance probability of `V v` as `½ (‖v‖² + Re ⟪v, W v⟫)` with `W` the reflection
`2 P − 1` (`P` the accepting projection) conjugated by `V`, an operator of norm at most `1`
(`acceptProb_eq_reflection`), and bounds the difference of this quadratic form at `c + β` and at
`c + β'` for `c = Π_S γ` and the parts `β`, `β'` of the two states orthogonal to it
(`abs_sub_le_of_reflection`).
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GordieHowe.Quantum

/-! ### The reflection bound -/

section Reflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The reflection bound.** For an operator `W` that is symmetric and of norm at most `1`, and
vectors `c`, `β`, `β'` with `β ⟂ c`, `β' ⟂ c`, `W β' ⟂ c` and `‖β'‖ = ‖β‖`, the quadratic form
`F v = ½ (‖v‖² + Re ⟪v, W v⟫)` changes by at most `‖c + β‖ ‖β‖ + ‖β‖²/2` from `c + β` to
`c + β'`. -/
theorem abs_sub_le_of_reflection (W : E →ₗ[ℂ] E) (hsym : ∀ v w, inner ℂ (W v) w = inner ℂ v (W w))
    (hnorm : ∀ v, ‖W v‖ ≤ ‖v‖) {c β β' : E} (h₁ : inner ℂ c β = 0) (h₂ : inner ℂ c β' = 0)
    (h₃ : inner ℂ c (W β') = 0) (h₄ : ‖β'‖ = ‖β‖) :
    |(‖c + β‖ ^ 2 + (inner ℂ (c + β) (W (c + β))).re) / 2 -
        (‖c + β'‖ ^ 2 + (inner ℂ (c + β') (W (c + β'))).re) / 2| ≤
      ‖c + β‖ * ‖β‖ + ‖β‖ ^ 2 / 2 := by
  have hβc : inner ℂ β (W c) = conj (inner ℂ c (W β)) := by rw [← inner_conj_symm, hsym]
  have hβ'c : inner ℂ β' (W c) = 0 := by rw [← inner_conj_symm, hsym, h₃, map_zero]
  have hcc : RCLike.re (inner ℂ c c) = ‖c‖ ^ 2 := inner_self_eq_norm_sq c
  have e1 : ‖c + β‖ ^ 2 = ‖c‖ ^ 2 + ‖β‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), h₁, map_zero]; ring
  have e1' : ‖c + β'‖ ^ 2 = ‖c‖ ^ 2 + ‖β‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), h₂, map_zero, h₄]; ring
  have e2 : (inner ℂ (c + β) (W (c + β))).re =
      (inner ℂ c (W c)).re + 2 * (inner ℂ c (W β)).re + (inner ℂ β (W β)).re := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hβc]
    simp only [Complex.add_re, Complex.conj_re]; ring
  have e3 : (inner ℂ (c + β') (W (c + β'))).re =
      (inner ℂ c (W c)).re + (inner ℂ β' (W β')).re := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hβ'c, h₃]
    simp only [Complex.add_re, Complex.zero_re]; ring
  have hu : (inner ℂ (c + c + β) (W β)).re = 2 * (inner ℂ c (W β)).re + (inner ℂ β (W β)).re := by
    simp only [inner_add_left, Complex.add_re]; ring
  have hun : ‖c + c + β‖ ^ 2 = 4 * ‖c‖ ^ 2 + ‖β‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ) c c, inner_add_left, h₁, add_zero, hcc,
      map_zero]
    ring
  have hb1 : |(inner ℂ (c + c + β) (W β)).re| ≤ ‖c + c + β‖ * ‖β‖ :=
    (Complex.abs_re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hnorm β) (norm_nonneg _)))
  have hb2 : |(inner ℂ β' (W β')).re| ≤ ‖β‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [← h₄, sq]
    exact mul_le_mul_of_nonneg_left (hnorm β') (norm_nonneg _)
  have hu2 : ‖c + c + β‖ ≤ 2 * ‖c + β‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, hun, e1]
    nlinarith [sq_nonneg ‖β‖]
  have hb3 : ‖c + c + β‖ * ‖β‖ ≤ 2 * ‖c + β‖ * ‖β‖ := mul_le_mul_of_nonneg_right hu2 (norm_nonneg _)
  rw [e1, e1', e2, e3]
  obtain ⟨hb1l, hb1r⟩ := abs_le.mp hb1
  obtain ⟨hb2l, hb2r⟩ := abs_le.mp hb2
  rw [abs_le]
  constructor <;> nlinarith

/-- A unitary moves to the other side of an inner product as its inverse (left argument). -/
theorem inner_symm_apply_left (V : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ (V.symm x) y = inner ℂ x (V y) := by
  rw [← V.inner_map_map, V.apply_symm_apply]

/-- A unitary moves to the other side of an inner product as its inverse (right argument). -/
theorem inner_symm_apply_right (V : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ x (V.symm y) = inner ℂ (V x) y := by
  rw [← V.inner_map_map, V.apply_symm_apply]

end Reflection

section Accept

variable {ι : Type*} [Fintype ι]

/-- **The reflection of an accepting set**: `+1` on the accepting outcomes, `−1` on the others. -/
noncomputable def reflectOn (A : Set ι) : QState ι →ₗ[ℂ] QState ι :=
  (mask A).toLinearMap - (mask Aᶜ).toLinearMap

/-- The masks of a set and of its complement are orthogonal. -/
theorem mask_mask_compl (A : Set ι) (v : QState ι) : mask A (mask Aᶜ v) = 0 := by
  ext i
  by_cases h : i ∈ A <;> simp [h]

/-- The reflection of a set is self-adjoint. -/
theorem inner_reflectOn_left (A : Set ι) (v w : QState ι) :
    inner ℂ (reflectOn A v) w = inner ℂ v (reflectOn A w) := by
  simp only [reflectOn, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, inner_sub_left,
    inner_sub_right, inner_mask_left]

/-- The reflection of a set preserves norms. -/
theorem norm_reflectOn (A : Set ι) (v : QState ι) : ‖reflectOn A v‖ = ‖v‖ := by
  have h0 : inner ℂ (mask A v) (mask Aᶜ v) = 0 := by
    rw [inner_mask_left, mask_mask_compl, inner_zero_right]
  have h1 : ‖mask A v - mask Aᶜ v‖ ^ 2 =
      ‖mask A v‖ ^ 2 - 2 * RCLike.re (inner ℂ (mask A v) (mask Aᶜ v)) + ‖mask Aᶜ v‖ ^ 2 :=
    @norm_sub_sq ℂ _ _ _ _ _ _
  rw [h0, map_zero] at h1
  simp only [reflectOn, LinearMap.sub_apply, ContinuousLinearMap.coe_coe]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), h1, norm_sq_eq_norm_mask_sq_add A v]
  ring

/-- **An acceptance probability as a quadratic form of a reflection**: for a unitary `V`,
`prob A (V v) = ½ (‖v‖² + Re ⟪v, W v⟫)` with `W = V⁻¹ ∘ reflectOn A ∘ V`. -/
theorem acceptProb_eq_reflection (V : QState ι ≃ₗᵢ[ℂ] QState ι) (A : Set ι) (v : QState ι) :
    prob A (V v) =
      (‖v‖ ^ 2 + (inner ℂ v (V.symm (reflectOn A (V v)))).re) / 2 := by
  rw [inner_symm_apply_right]
  have hv : ‖v‖ = ‖V v‖ := (V.norm_map v).symm
  have k : ∀ B : Set ι, (inner ℂ (V v) (mask B (V v))).re = ‖mask B (V v)‖ ^ 2 := by
    intro B
    have : inner ℂ (V v) (mask B (V v)) = inner ℂ (mask B (V v)) (mask B (V v)) := by
      rw [inner_mask_left, mask_mask]
    rw [this]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hv, norm_sq_eq_norm_mask_sq_add A (V v), prob]
  simp only [reflectOn, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, inner_sub_right,
    Complex.sub_re, k]
  ring

end Accept

/-! ### One reprogramming of a purified oracle -/

section OneShot

variable {ι X Y : Type*} [Fintype ι] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y]

/-- **The average over the values on `S` of a family of states**:
`|Y^X|⁻¹ ∑_z γ (setOn S h z)`. -/
noncomputable def avgFam (S : Finset X) (γ : (X → Y) → QState ι) (h : X → Y) : QState ι :=
  (Fintype.card (X → Y) : ℂ)⁻¹ • ∑ z, γ (Junta.setOn S h z)

omit [DecidableEq Y] [Nonempty Y] in
/-- The average over the values on `S` does not depend on the values on `S`. -/
theorem avgFam_setOn (S : Finset X) (γ : (X → Y) → QState ι) (h z : X → Y) :
    avgFam S γ (Junta.setOn S h z) = avgFam S γ h := by
  simp only [avgFam, Junta.setOn_setOn_left]

omit [DecidableEq Y] [Nonempty Y] in
/-- A double sum over the oracle and the fresh values is invariant under `swapOn S`. -/
theorem sum_setOn_swap {M : Type*} [AddCommMonoid M] (S : Finset X)
    (F : (X → Y) → (X → Y) → M) :
    ∑ h, ∑ z, F (Junta.setOn S h z) (Junta.setOn S z h) = ∑ h, ∑ z, F h z := by
  have := Equiv.sum_comp (Junta.swapOn S) (fun p => F p.1 p.2)
  simpa only [Fintype.sum_prod_type, Junta.swapOn_apply] using this

omit [DecidableEq Y] in
/-- The sum over the values on `S` is `|Y^X|` copies of the average. -/
theorem sum_fam_setOn (S : Finset X) (γ : (X → Y) → QState ι) (h : X → Y) :
    ∑ z, γ (Junta.setOn S h z) = ∑ _z : X → Y, avgFam S γ h := by
  have hN : (Fintype.card (X → Y) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_const, card_univ, avgFam, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN,
    one_smul]

omit [DecidableEq Y] in
/-- **One reprogramming at a revealed set, averaged over the oracle and the fresh values.** For
states `γ h` before the reprogramming and unitaries `V h` after it, the acceptance probabilities
of `V h (γ h)` and of `V h (γ (setOn S h z))` for an accepting set `A h`, which may depend on
the oracle, summed over the oracle `h` and the fresh values `z`, differ by at most
`|Y^X| (√(∑_h ‖γ h‖²) √(∑_h ‖γ h − Π_S γ h‖²) + ½ ∑_h ‖γ h − Π_S γ h‖²)`. -/
theorem abs_sum_prob_sub_le (γ : (X → Y) → QState ι) (V : (X → Y) → QState ι ≃ₗᵢ[ℂ] QState ι)
    (A : (X → Y) → Set ι) (S : Finset X) :
    |∑ h, ∑ _z : X → Y, prob (A h) (V h (γ h)) -
        ∑ h, ∑ z, prob (A h) (V h (γ (Junta.setOn S h z)))| ≤
      Fintype.card (X → Y) *
        (√(∑ h, ‖γ h‖ ^ 2) * √(∑ h, ‖γ h - avgFam S γ h‖ ^ 2) +
          (∑ h, ‖γ h - avgFam S γ h‖ ^ 2) / 2) := by
  classical
  obtain ⟨Wh, hWh⟩ : ∃ Wh : (X → Y) → QState ι →ₗ[ℂ] QState ι,
      ∀ h v, Wh h v = (V h).symm (reflectOn (A h) (V h v)) :=
    ⟨fun h => (V h).symm.toLinearMap ∘ₗ reflectOn (A h) ∘ₗ (V h).toLinearMap, fun _ _ => rfl⟩
  have hWsym : ∀ h v w, inner ℂ (Wh h v) w = inner ℂ v (Wh h w) := by
    intro h v w
    rw [hWh, hWh, inner_symm_apply_left, inner_reflectOn_left, inner_symm_apply_right]
  have hWnorm : ∀ h v, ‖Wh h v‖ = ‖v‖ := by
    intro h v
    rw [hWh, LinearIsometryEquiv.norm_map, norm_reflectOn, LinearIsometryEquiv.norm_map]
  obtain ⟨W, hW⟩ : ∃ W : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι) →ₗ[ℂ]
      PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι), ∀ v p, W v p = Wh p.1 (v p) :=
    ⟨{ toFun := fun v => WithLp.toLp 2 (fun p => Wh p.1 (v p))
       map_add' := fun v w => PiLp.ext fun p => by simp
       map_smul' := fun r v => PiLp.ext fun p => by simp }, fun _ _ => rfl⟩
  have hinner : ∀ x y : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι),
      inner ℂ x y = ∑ h, ∑ z, inner ℂ (x (h, z)) (y (h, z)) := by
    intro x y
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
  have hnormsq : ∀ x : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι),
      ‖x‖ ^ 2 = ∑ h, ∑ z, ‖x (h, z)‖ ^ 2 := by
    intro x
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  have hsym : ∀ v w, inner ℂ (W v) w = inner ℂ v (W w) := by
    intro v w
    simp only [PiLp.inner_apply, hW, hWsym]
  have hnorm : ∀ v, ‖W v‖ ≤ ‖v‖ := by
    intro v
    refine le_of_eq ?_
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2]
    simp only [hW, hWnorm]
  have hprob : ∀ (f : (X → Y) → (X → Y) → QState ι)
      (x : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι)), (∀ h z, x (h, z) = f h z) →
      ∑ h, ∑ z, prob (A h) (V h (f h z)) = (‖x‖ ^ 2 + (inner ℂ x (W x)).re) / 2 := by
    intro f x hx
    rw [hnormsq, hinner]
    simp only [hW, hx, acceptProb_eq_reflection, ← hWh, add_div, sum_add_distrib, sum_div,
      Complex.re_sum]
  obtain ⟨a, ha⟩ : ∃ a : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι), ∀ p, a p = γ p.1 :=
    ⟨WithLp.toLp 2 fun p => γ p.1, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι),
      ∀ p, b p = γ (Junta.setOn S p.1 p.2) :=
    ⟨WithLp.toLp 2 fun p => γ (Junta.setOn S p.1 p.2), fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : PiLp 2 (fun _ : (X → Y) × (X → Y) => QState ι),
      ∀ p, c p = avgFam S γ p.1 :=
    ⟨WithLp.toLp 2 fun p => avgFam S γ p.1, fun _ => rfl⟩
  have hsum := sum_fam_setOn S γ
  have hca : inner ℂ c a = inner ℂ c c := by
    rw [hinner, hinner]
    simp only [hc, ha]
    have key := sum_setOn_swap S (fun h _ => inner ℂ (avgFam S γ h) (γ h))
    simp only [avgFam_setOn] at key
    rw [← key]
    simp only [← inner_sum, hsum]
  have hcb : inner ℂ c b = inner ℂ c c := by
    rw [hinner, hinner]
    simp only [hc, hb, ← inner_sum, hsum]
  have h₁ : inner ℂ c (a - c) = 0 := by rw [inner_sub_right, hca, sub_self]
  have h₂ : inner ℂ c (b - c) = 0 := by rw [inner_sub_right, hcb, sub_self]
  have h₃ : inner ℂ c (W (b - c)) = 0 := by
    rw [hinner]
    simp only [hW, hc, PiLp.sub_apply, hb, ← inner_sum, ← map_sum, sum_sub_distrib, hsum,
      sub_self, map_zero, inner_zero_right, sum_const_zero]
  have h₄ : ‖b - c‖ = ‖a - c‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hnormsq, hnormsq]
    simp only [PiLp.sub_apply, ha, hb, hc]
    have key := sum_setOn_swap S (fun h _ => ‖γ h - avgFam S γ h‖ ^ 2)
    simp only [avgFam_setOn] at key
    exact key
  have hA : ∑ h, ∑ _z : X → Y, prob (A h) (V h (γ h)) = (‖a‖ ^ 2 + (inner ℂ a (W a)).re) / 2 :=
    hprob (fun h _ => γ h) a fun h z => ha (h, z)
  have hB : ∑ h, ∑ z, prob (A h) (V h (γ (Junta.setOn S h z))) =
      (‖b‖ ^ 2 + (inner ℂ b (W b)).re) / 2 :=
    hprob (fun h z => γ (Junta.setOn S h z)) b fun h z => hb (h, z)
  have key := abs_sub_le_of_reflection W hsym hnorm h₁ h₂ h₃ h₄
  rw [add_sub_cancel, add_sub_cancel] at key
  rw [hA, hB]
  refine key.trans (le_of_eq ?_)
  have hSa : 0 ≤ ∑ h, ‖γ h‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hSb : 0 ≤ ∑ h, ‖γ h - avgFam S γ h‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hN : (0 : ℝ) ≤ Fintype.card (X → Y) := Nat.cast_nonneg _
  have na : ‖a‖ ^ 2 = Fintype.card (X → Y) * ∑ h, ‖γ h‖ ^ 2 := by
    rw [hnormsq]
    simp only [ha, sum_const, card_univ, nsmul_eq_mul]
    rw [mul_sum]
  have nb : ‖a - c‖ ^ 2 = Fintype.card (X → Y) * ∑ h, ‖γ h - avgFam S γ h‖ ^ 2 := by
    rw [hnormsq]
    simp only [PiLp.sub_apply, ha, hc, sum_const, card_univ, nsmul_eq_mul]
    rw [mul_sum]
  have ea : ‖a‖ = √(Fintype.card (X → Y) * ∑ h, ‖γ h‖ ^ 2) := by
    rw [← na, Real.sqrt_sq (norm_nonneg _)]
  have eb : ‖a - c‖ = √(Fintype.card (X → Y) * ∑ h, ‖γ h - avgFam S γ h‖ ^ 2) := by
    rw [← nb, Real.sqrt_sq (norm_nonneg _)]
  rw [ea, eb, Real.sq_sqrt (mul_nonneg hN hSb), Real.sqrt_mul hN, Real.sqrt_mul hN]
  linear_combination (√(∑ h, ‖γ h‖ ^ 2) * √(∑ h, ‖γ h - avgFam S γ h‖ ^ 2)) *
    Real.mul_self_sqrt hN

end OneShot

end GordieHowe.Quantum
