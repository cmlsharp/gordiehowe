-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Couplings of finite PMFs

- `exists_coupling_le_tvDist`: two PMFs `p`, `q` on a finite type have a coupling (a joint law
  with marginals `p` and `q`) under which the two coordinates differ with probability at most
  `tvDist p q` (the maximal coupling; Lindvall, *Lectures on the Coupling Method*, 1992,
  Theorem I.5.2).
- `condLaw`, `isDisintegration_condLaw`: the conditional law of `a ← p` given `φ a = b`.
- `exists_coupling_map_le_tvDist`: two PMFs `p`, `q` have a coupling under which the images by
  `φ` differ with probability at most `tvDist (p.map φ) (q.map φ)` (the maximal coupling of the
  images, followed by the two conditional laws).

About Mathlib objects only; a candidate for upstreaming.
-/

open Finset
open scoped BigOperators ENNReal

namespace PMF

variable {α β : Type*} [Fintype α]

/-- The common part of two masses plus the one-sided excess is the first mass. -/
theorem min_add_tsub_eq (x y : ℝ≥0∞) : min x y + (x - y) = x := by
  rw [add_comm]; exact tsub_add_min

/-- The mass of a fiber of a map, as a finite sum. -/
theorem map_apply_eq_sum [DecidableEq β] (p : PMF α) (φ : α → β) (b : β) :
    p.map φ b = ∑ a, if φ a = b then p a else 0 := by
  rw [map_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun a _ => by by_cases h : φ a = b <;> simp [h, Ne.symm]

/-- A point's mass is at most the mass of its fiber. -/
theorem apply_le_map_apply {γ : Type*} (p : PMF γ) (f : γ → β) (x : γ) : p x ≤ p.map f (f x) := by
  classical
  rw [map_apply]
  have := ENNReal.le_tsum (f := fun a => if f x = f a then p a else 0) x
  simp only [if_true] at this
  convert this

variable [DecidableEq α]

/-- **The maximal coupling** (Lindvall 1992, Theorem I.5.2): two PMFs on a finite type have a joint
law with marginals `p` and `q` whose coordinates differ with probability at most `tvDist p q`. -/
theorem exists_coupling_le_tvDist (p q : PMF α) :
    ∃ J : PMF (α × α), J.map Prod.fst = p ∧ J.map Prod.snd = q ∧
      (J.toOuterMeasure {x | x.1 ≠ x.2}).toReal ≤ tvDist p q := by
  set t : ℝ≥0∞ := ∑ a, (p a - q a) with ht
  have htq : t = ∑ a, (q a - p a) := by
    have := tsum_tsub_comm p q
    rwa [tsum_fintype, tsum_fintype] at this
  have htv : tvDist p q = t.toReal := by rw [tvDist_eq_toReal_tsum_tsub, tsum_fintype]
  have htop : t ≠ ⊤ := by
    have := tsum_tsub_ne_top p q
    rwa [tsum_fintype] at this
  by_cases h0 : t = 0
  · -- `p ≤ q` and `q ≤ p` pointwise, so `p = q`: the diagonal coupling.
    have hpq : p = q := by
      ext a
      refine le_antisymm ?_ ?_
      · have h0' : ∑ a, (p a - q a) = 0 := h0
        exact tsub_eq_zero_iff_le.1 ((Finset.sum_eq_zero_iff.1 h0') a (mem_univ a))
      · have h0' : ∑ a, (q a - p a) = 0 := htq ▸ h0
        exact tsub_eq_zero_iff_le.1 ((Finset.sum_eq_zero_iff.1 h0') a (mem_univ a))
    subst hpq
    have hdiag : (fun a : α => (a, a)) ⁻¹' {x : α × α | x.1 ≠ x.2} = ∅ := by ext; simp
    refine ⟨p.map fun a => (a, a), ?_, ?_, ?_⟩
    · rw [map_comp]; exact map_id _
    · rw [map_comp]; exact map_id _
    · rw [toOuterMeasure_map_apply, hdiag]; simp
  -- the common part on the diagonal, the product of the excesses off it
  let f : α × α → ℝ≥0∞ := fun x =>
    (if x.1 = x.2 then min (p x.1) (q x.1) else 0) + (p x.1 - q x.1) * (q x.2 - p x.2) / t
  have hrow : ∀ a, ∑ b, f (a, b) = p a := fun a => by
    simp only [f, Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, if_true]
    rw [show ∑ b, (p a - q a) * (q b - p b) / t = (p a - q a) * (∑ b, (q b - p b)) / t by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]]
    rw [← htq, ENNReal.mul_div_cancel_right h0 htop]
    exact min_add_tsub_eq _ _
  have hcol : ∀ b, ∑ a, f (a, b) = q b := fun b => by
    simp only [f, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' univ b, if_pos (mem_univ b)]
    rw [show ∑ a, (p a - q a) * (q b - p b) / t = (∑ a, (p a - q a)) * (q b - p b) / t by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]]
    rw [← ht, mul_comm, ENNReal.mul_div_cancel_right h0 htop, min_comm]
    exact min_add_tsub_eq _ _
  have hsum : ∑ x, f x = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hrow]
    rw [← tsum_fintype (L := SummationFilter.unconditional α)]; exact p.tsum_coe
  let J := PMF.ofFintype f hsum
  have hmap1 : J.map Prod.fst = p := by
    ext a
    rw [map_apply, tsum_fintype, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a (fun a' _ ha' => Finset.sum_eq_zero fun b _ => by
      simp [Ne.symm ha']) (by simp)]
    simp only [if_true, ofFintype_apply, J]
    exact hrow a
  have hmap2 : J.map Prod.snd = q := by
    ext b
    rw [map_apply, tsum_fintype, Fintype.sum_prod_type_right]
    rw [Finset.sum_eq_single b (fun b' _ hb' => Finset.sum_eq_zero fun a _ => by
      simp [Ne.symm hb']) (by simp)]
    simp only [if_true, ofFintype_apply, J]
    exact hcol b
  refine ⟨J, hmap1, hmap2, ?_⟩
  rw [htv]
  refine ENNReal.toReal_mono htop ?_
  rw [toOuterMeasure_apply, tsum_fintype]
  calc ∑ x, Set.indicator {x : α × α | x.1 ≠ x.2} J x
      ≤ ∑ x : α × α, (p x.1 - q x.1) * (q x.2 - p x.2) / t := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : x.1 = x.2
        · simp [Set.indicator, hx]
        · simp [Set.indicator, hx, J, f]
    _ = t := by
        rw [Fintype.sum_prod_type]
        simp only [div_eq_mul_inv]
        rw [show ∑ a, ∑ b, (p a - q a) * (q b - p b) * t⁻¹ =
            (∑ a, (p a - q a)) * (∑ b, (q b - p b)) * t⁻¹ by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum, Finset.sum_mul]]
        rw [← htq, ← ht, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one]

variable [Fintype β] [DecidableEq β]

omit [DecidableEq α] in
/-- The conditional mass function sums to one where the fiber has positive mass. -/
theorem sum_div_map_apply (p : PMF α) (φ : α → β) {b : β} (h : p.map φ b ≠ 0) :
    ∑ a, (if φ a = b then p a else 0) / p.map φ b = 1 := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← map_apply_eq_sum]
  exact ENNReal.mul_inv_cancel h (ne_top_of_le_ne_top ENNReal.one_ne_top (coe_le_one _ _))

/-- **The conditional law** of `a ← p` given `φ a = b`; `p` itself where `p.map φ b = 0`. -/
noncomputable def condLaw (p : PMF α) (φ : α → β) (b : β) : PMF α :=
  if h : p.map φ b = 0 then p else
    PMF.ofFintype (fun a => (if φ a = b then p a else 0) / p.map φ b) (sum_div_map_apply p φ h)

omit [DecidableEq α] in
theorem condLaw_apply_of_ne (p : PMF α) (φ : α → β) {b : β} (h : p.map φ b ≠ 0) (a : α) :
    condLaw p φ b a = (if φ a = b then p a else 0) / p.map φ b := by
  rw [condLaw, dif_neg h, ofFintype_apply]

omit [DecidableEq α] in
/-- `condLaw p φ` is a disintegration of `p` along `φ`. -/
theorem isDisintegration_condLaw (p : PMF α) (φ : α → β) :
    IsDisintegration p φ (condLaw p φ) := by
  intro b a
  by_cases h : p.map φ b = 0
  · rw [h, zero_mul]
    split_ifs with hab
    · rw [map_apply_eq_sum] at h
      have := (Finset.sum_eq_zero_iff.1 h) a (mem_univ a)
      rw [if_pos hab] at this
      exact this.symm
    · rfl
  · rw [condLaw_apply_of_ne p φ h, ENNReal.mul_div_cancel h
      (ne_top_of_le_ne_top ENNReal.one_ne_top (coe_le_one _ _))]

omit [DecidableEq α] in
/-- Mixing the conditional laws by the image law gives back the law. -/
theorem bind_condLaw (p : PMF α) (φ : α → β) : (p.map φ).bind (condLaw p φ) = p := by
  have h := congrArg (PMF.map Prod.fst) (isDisintegration_condLaw p φ).map_pair_eq
  rw [map_comp, map_bind] at h
  simp only [map_comp, Function.comp_def] at h
  have e : ∀ r : PMF α, r.map (fun x => x) = r := fun r => map_id r
  simp only [e] at h
  exact h.symm

/-- **A coupling along a map**: two PMFs have a joint law with marginals `p` and `q` under which
the images by `φ` differ with probability at most `tvDist (p.map φ) (q.map φ)`: the maximal
coupling of the images (`exists_coupling_le_tvDist`), followed by the two conditional laws
(`condLaw`). -/
theorem exists_coupling_map_le_tvDist (p q : PMF α) (φ : α → β) :
    ∃ J : PMF (α × α), J.map Prod.fst = p ∧ J.map Prod.snd = q ∧
      (J.toOuterMeasure {x | φ x.1 ≠ φ x.2}).toReal ≤ tvDist (p.map φ) (q.map φ) := by
  obtain ⟨K, hK1, hK2, hK⟩ := exists_coupling_le_tvDist (p.map φ) (q.map φ)
  let J : PMF (α × α) := K.bind fun bb =>
    (condLaw p φ bb.1).bind fun a => (condLaw q φ bb.2).map fun a' => (a, a')
  refine ⟨J, ?_, ?_, ?_⟩
  · rw [map_bind]
    have : ∀ bb : β × β, ((condLaw p φ bb.1).bind fun a =>
        (condLaw q φ bb.2).map fun a' => (a, a')).map Prod.fst = condLaw p φ bb.1 := fun bb => by
      rw [map_bind]
      simp only [map_comp, Function.comp_def]
      have e : ∀ a : α, ((condLaw q φ bb.2).map fun _ => a) = pure a := fun a => map_const _ _
      simp only [e]
      exact bind_pure _
    simp only [this]
    rw [show (fun bb : β × β => condLaw p φ bb.1) = condLaw p φ ∘ Prod.fst from rfl,
      ← bind_map, hK1]
    exact bind_condLaw p φ
  · rw [map_bind]
    have : ∀ bb : β × β, ((condLaw p φ bb.1).bind fun a =>
        (condLaw q φ bb.2).map fun a' => (a, a')).map Prod.snd = condLaw q φ bb.2 := fun bb => by
      rw [map_bind]
      simp only [map_comp, Function.comp_def]
      have e : ∀ r : PMF α, r.map (fun x => x) = r := fun r => map_id r
      simp only [e]
      exact bind_const _ _
    simp only [this]
    rw [show (fun bb : β × β => condLaw q φ bb.2) = condLaw q φ ∘ Prod.snd from rfl,
      ← bind_map, hK2]
    exact bind_condLaw q φ
  · refine le_trans (ENNReal.toReal_mono ?_ ?_) hK
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one _ _)
    · -- the conditional laws keep the images
      rw [toOuterMeasure_bind_apply, toOuterMeasure_apply]
      refine ENNReal.tsum_le_tsum fun bb => ?_
      by_cases hbb : bb.1 ≠ bb.2
      · simp only [Set.indicator, Set.mem_setOf_eq]
        rw [if_pos hbb]
        exact mul_le_of_le_one_right' (toOuterMeasure_apply_le_one _ _)
      rw [not_not] at hbb
      by_cases hK0 : K bb = 0
      · simp [hK0]
      have hp0 : p.map φ bb.1 ≠ 0 := by
        rw [← hK1]; exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hK0)
          (apply_le_map_apply K Prod.fst bb))
      have hq0 : q.map φ bb.2 ≠ 0 := by
        rw [← hK2]; exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hK0)
          (apply_le_map_apply K Prod.snd bb))
      have hin : ((condLaw p φ bb.1).bind fun a =>
          (condLaw q φ bb.2).map fun a' => (a, a')).toOuterMeasure {x | φ x.1 ≠ φ x.2} = 0 := by
        rw [toOuterMeasure_bind_apply]
        refine ENNReal.tsum_eq_zero.2 fun a => ?_
        by_cases ha : φ a = bb.1
        · rw [toOuterMeasure_map_apply]
          refine mul_eq_zero_of_right _ ((toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
          rw [Set.disjoint_iff]
          rintro a' ⟨h1, h2⟩
          simp only [Set.mem_preimage, Set.mem_setOf_eq] at h2
          rw [mem_support_iff, condLaw_apply_of_ne q φ hq0] at h1
          have : φ a' = bb.2 := by
            by_contra hne; simp [hne] at h1
          exact h2 (by rw [ha, this, hbb])
        · refine mul_eq_zero_of_left ?_ _
          rw [condLaw_apply_of_ne p φ hp0, if_neg ha, ENNReal.zero_div]
      rw [hin, mul_zero]
      exact zero_le'

/-! ### Identical until bad -/

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- **Two kernels mixed by one law, identical until bad**: the mixtures are at most the
probability that the kernels differ apart. -/
theorem tvDist_bind_le_toOuterMeasure_ne {γ : Type*} (p : PMF γ) (k₁ k₂ : γ → PMF β) :
    tvDist (p.bind k₁) (p.bind k₂) ≤ (p.toOuterMeasure {a | k₁ a ≠ k₂ a}).toReal := by
  classical
  simp only [tvDist_eq_toReal_tsum_tsub]
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (toOuterMeasure_apply_le_one _ _)) ?_
  rw [toOuterMeasure_apply]
  calc ∑' b, ((p.bind k₁) b - (p.bind k₂) b)
      ≤ ∑' b, ∑' a, p a * (k₁ a b - k₂ a b) := by
        refine ENNReal.tsum_le_tsum fun b => tsub_le_iff_left.2 ?_
        simp only [bind_apply]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a => ?_
        rw [← mul_add]
        gcongr
        exact le_add_tsub
    _ = ∑' a, p a * ∑' b, (k₁ a b - k₂ a b) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun a => ENNReal.tsum_mul_left
    _ ≤ ∑' a, Set.indicator {a | k₁ a ≠ k₂ a} p a := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases h : k₁ a = k₂ a
        · simp [h]
        · rw [Set.indicator_of_mem (show a ∈ {a | k₁ a ≠ k₂ a} from h)]
          exact mul_le_of_le_one_right' (tsum_tsub_le_one _ _)

/-! ### One coordinate of a product law -/

section PiCoord

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ι → Type*} [∀ i, Fintype (δ i)]
  [∀ i, DecidableEq (δ i)]

/-- Resampling coordinate `j`: `pi ν (update T j b) · ν_j (T j) = pi ν T · ν_j b`. -/
theorem pi_update_mul (ν : ∀ i, PMF (δ i)) (j : ι) (T : ∀ i, δ i) (b : δ j) :
    pi ν (Function.update T j b) * ν j (T j) = pi ν T * ν j b := by
  simp only [pi_apply]
  have h1 : ∏ i, ν i (Function.update T j b i) =
      ν j b * ∏ i ∈ univ \ {j}, ν i (T i) := by
    rw [show (fun i => ν i (Function.update T j b i)) =
        Function.update (fun i => ν i (T i)) j (ν j b) from
      funext fun i => Function.apply_update (fun i => ν i) T j b i]
    exact Finset.prod_update_of_mem (mem_univ j) _ _
  have h2 : ∏ i, ν i (T i) = ν j (T j) * ∏ i ∈ univ \ {j}, ν i (T i) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ j), Finset.sdiff_singleton_eq_erase]
  rw [h1, h2]
  ring

/-- **Resampling one coordinate of a product law**: if `G T` does not depend on coordinate `j`
of `T`, the average of `G T (T j)` over `T ← pi ν` is the average of the `ν_j`-average of `G T`. -/
theorem sum_pi_mul_apply_eq (ν : ∀ i, PMF (δ i)) (j : ι) (G : (∀ i, δ i) → δ j → ℝ≥0∞)
    (hG : ∀ T b, G (Function.update T j b) = G T) :
    ∑ T, pi ν T * G T (T j) = ∑ T, pi ν T * ∑ b, ν j b * G T b := by
  -- the pair `(T, b)` and the pair `(update T j b, T j)` have the same law
  let e : (∀ i, δ i) × δ j ≃ (∀ i, δ i) × δ j :=
    { toFun := fun x => (Function.update x.1 j x.2, x.1 j)
      invFun := fun x => (Function.update x.1 j x.2, x.1 j)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  calc ∑ T, pi ν T * G T (T j)
      = ∑ x : (∀ i, δ i) × δ j, pi ν x.1 * ν j x.2 * G x.1 (x.1 j) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_coe, mul_one]
    _ = ∑ x : (∀ i, δ i) × δ j, pi ν (e x).1 * ν j (e x).2 * G (e x).1 ((e x).1 j) :=
        (Fintype.sum_equiv e _ _ fun _ => rfl).symm
    _ = ∑ x : (∀ i, δ i) × δ j, pi ν x.1 * ν j x.2 * G x.1 x.2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [e, Equiv.coe_fn_mk, Function.update_self, hG]
        rw [pi_update_mul]
    _ = ∑ T, pi ν T * ∑ b, ν j b * G T b := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- **An average over a product law, one coordinate at a time**: if `G T` does not depend on
coordinate `j` of `T` and every `ν_j`-average of `G T` is at most `ε`, the average of
`G T (T j)` over `T ← pi ν` is at most `ε`. -/
theorem sum_pi_mul_apply_le (ν : ∀ i, PMF (δ i)) (j : ι) (G : (∀ i, δ i) → δ j → ℝ≥0∞)
    (hG : ∀ T b, G (Function.update T j b) = G T) {ε : ℝ≥0∞}
    (hε : ∀ T, ∑ b, ν j b * G T b ≤ ε) :
    ∑ T, pi ν T * G T (T j) ≤ ε := by
  rw [sum_pi_mul_apply_eq ν j G hG]
  calc ∑ T, pi ν T * ∑ b, ν j b * G T b ≤ ∑ T, pi ν T * ε :=
        Finset.sum_le_sum fun T _ => by gcongr; exact hε T
    _ = ε := by rw [← Finset.sum_mul, sum_coe, one_mul]

/-- **A coordinate of a product law has the coordinate's law.** -/
theorem sum_pi_mul_apply_coord (ν : ∀ i, PMF (δ i)) (j : ι) (φ : δ j → ℝ≥0∞) :
    ∑ T, pi ν T * φ (T j) = ∑ b, ν j b * φ b := by
  rw [sum_pi_mul_apply_eq ν j (fun _ => φ) fun _ _ => rfl, ← Finset.sum_mul, sum_coe, one_mul]

end PiCoord

/-! ### Averages of probabilities -/

omit [DecidableEq α] in
/-- **The averages of two families of probabilities differ by at most the average difference.** -/
theorem abs_sum_mul_sub_sum_mul_le (μ : PMF α) {f g : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1)
    (hg : ∀ a, g a ≤ 1) :
    |(∑ a, μ a * f a).toReal - (∑ a, μ a * g a).toReal| ≤
      ∑ a, (μ a).toReal * |(f a).toReal - (g a).toReal| := by
  have hft : ∀ a, μ a * f a ≠ ⊤ := fun a => ENNReal.mul_ne_top (μ.apply_ne_top a)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hf a))
  have hgt : ∀ a, μ a * g a ≠ ⊤ := fun a => ENNReal.mul_ne_top (μ.apply_ne_top a)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hg a))
  rw [ENNReal.toReal_sum fun a _ => hft a, ENNReal.toReal_sum fun a _ => hgt a,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

end PMF
