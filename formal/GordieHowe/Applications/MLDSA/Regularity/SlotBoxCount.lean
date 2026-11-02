-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.HybridAnnihilator
public import GordieHowe.Applications.MLDSA.Regularity.EnvelopeFive
public import GordieHowe.Foundations.ToMathlib.BoxCharacterCount
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

/-!
# The sharp box count for slot conditions

The fixed-mode route of `SecondMoment.lean` bounds the probability that a mask drawn from a
`G`-box satisfies the slot conditions `x̂_j ∈ span ŝ₁(j)` (`j ∈ T`) by `G^{-(ℓ-1)#T}`, through the
rank bound `card_filter_sub_mem_le_pow_finrank`. This file replaces `G` by the field size `q`.

* `card_filter_slotSpan_le`: for a box whose sides have Fourier bound `f`
  (`‖∑_{x ∈ S i} ψ (a x)‖ ≤ #(S i) · f a`), the masks `z` with `(E z - w)_j ∈ span {s_j}` for
  every `j ∈ T` number at most `#B · (q / q^ℓ)^#T · (∑_{y ∈ C_T} ∏_c f (y c))^ℓ`, where `C_T` is
  the code of words `c ↦ ∑_{j ∈ T} λ_j r_j^c` (`powerCode`). The conditions are the vanishing of
  the forms `(b, c) ↦ ∑_j r_j^c u_{j,b}` with `u_j ⊥ s_j` (`slotForms`, `slotConditionSpace`), a
  space of at least `q^{(ℓ-1)#T}` forms whose rows `b` lie in `C_T`; then
  `AddChar.card_filter_forall_dot_eq_zero_le`. The sum over `C_T` is `1 + δ'_{#T}` with the
  small-support bound `δ'` of the box kernel `f` (`SmallSupportBounds`).
* `card_admissible_le_box`: the two-stage form for one mode,
  `(q / q^ℓ)^#T · (∑_{y ∈ C_T} ∏_c f (y c))^{2ℓ}`; `sum_powerCode_le_one_add` bounds the sum by
  `1 + δ'_{#T}`.
* `sum_supportMoment_le_box`, `averagedSecondMoment_le_box`: support sizes `m < t ≤ m'` with
  `2t ≤ n` take `(q / q^ℓ)^t (1 + δ'_t)^{2ℓ} T₂^{kt}` (`boxSupportTerm`).
* `envelope_box_mldsa44`: at ML-DSA-44 the second-moment envelope is at most `2^-154`.
  Numerically the two-window term at `t = 6` (`2^-154.48`) dominates, and the `t = 5` term, which
  dominates `envelope_mldsa44` at `2^-127.66`, is `2^-202.7` with the sharp count.

The box sides are intervals of `G = 2(γ₁ - β) - 1` residues, so `f = min(1, q / (2G|a|))`
(`norm_sum_interval_le`), a kernel bound with `C = q / (2G) ≤ q / 523383` at every parameter set,
for which the spectral recursion gives `δ'_t` up to `t = 5` (`smallSupportBounds_five_of_isKernelBound`).

Source of the setting: "A shorter proof of the stated HighBits regularity claim" (10 September
2026), Section 3, equations (4)-(6); the count is the Fourier inversion of the indicator of an
affine subspace, with the interval bound on each side.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section SlotCount

variable {n ℓ : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- The dot product with `s` as a linear form. -/
def dotForm (s : Fin ℓ → F) : (Fin ℓ → F) →ₗ[F] F where
  toFun u := ∑ b, u b * s b
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_assoc]

omit [Fintype F] [DecidableEq F] in
theorem dotForm_apply (s u : Fin ℓ → F) : dotForm s u = ∑ b, u b * s b := rfl

omit [Fintype F] [DecidableEq F] in
/-- The coefficient forms of slot-domain dual vectors: `u ↦ ((b, c) ↦ ∑_j r_j^c u_{j,b})`. -/
def slotForms (r : Fin n → F) : (Fin n → Fin ℓ → F) →ₗ[F] (Fin ℓ × Fin n → F) where
  toFun u bc := ∑ j, r j ^ (bc.2 : ℕ) * u j bc.1
  map_add' u v := by
    funext bc
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext bc
    simp [Finset.mul_sum, mul_left_comm]

omit [Fintype F] [DecidableEq F] in
theorem slotForms_apply (r : Fin n → F) (u : Fin n → Fin ℓ → F) (b : Fin ℓ) (c : Fin n) :
    slotForms r u (b, c) = ∑ j, r j ^ (c : ℕ) * u j b := rfl

theorem slotForms_injective {r : Fin n → F} (hr : Function.Injective r) :
    Function.Injective (slotForms (ℓ := ℓ) r) := by
  intro u v h
  funext j b
  have hw : slotWord r (fun j => u j b) = slotWord r (fun j => v j b) := funext fun c => by
    have := congrFun h (b, c)
    simpa only [slotForms_apply, slotWord_apply] using this
  exact congrFun (slotWord_injective hr hw) j

omit [Fintype F] [DecidableEq F] in
/-- The dual vectors of the slot conditions on `T`: `u_j ⊥ s_j` for `j ∈ T`, `u_j = 0`
otherwise. -/
def slotConditionSpace (s : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    Submodule F (Fin n → Fin ℓ → F) :=
  Submodule.pi Set.univ fun j => if j ∈ T then LinearMap.ker (dotForm (s j)) else ⊥

omit [Fintype F] [DecidableEq F] in
theorem finrank_ker_dotForm_ge (s : Fin ℓ → F) :
    ℓ - 1 ≤ Module.finrank F (LinearMap.ker (dotForm s)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotForm s)
  have h1 : Module.finrank F (LinearMap.range (dotForm s)) ≤ 1 :=
    (Submodule.finrank_le _).trans_eq (Module.finrank_self F)
  rw [Module.finrank_fin_fun] at h
  omega

omit [Fintype F] [DecidableEq F] in
theorem finrank_slotConditionSpace_ge (s : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    (ℓ - 1) * #T ≤ Module.finrank F (slotConditionSpace s T) := by
  rw [slotConditionSpace, Submodule.finrank_pi_univ]
  calc (ℓ - 1) * #T = ∑ j, if j ∈ T then ℓ - 1 else 0 := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
        by_cases hj : j ∈ T
        · rw [if_pos hj, if_pos hj]
          exact finrank_ker_dotForm_ge (s j)
        · rw [if_neg hj]
          exact Nat.zero_le _

open Classical in
/-- **The sharp box count for slot conditions.** For the slot transform
`E z j b = ∑_c z (b, c) r_j^c` with distinct nonzero roots, a nontrivial character `ψ` and box
sides with `‖∑_{x ∈ S i} ψ (a x)‖ ≤ #(S i) · f a`, `0 ≤ f`, the masks with
`(E z - w)_j ∈ span {s_j}` for all `j ∈ T'` number at most
`#B · (q / q^ℓ)^#T' · (∑_{y ∈ C_T} ∏_c f (y c))^ℓ`, `q = #F`, for every `T ⊇ T'`. -/
theorem card_filter_slotSpan_le (E : (Fin ℓ × Fin n → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    {r : Fin n → F} (hE : ∀ z j b, E z j b = ∑ c, z (b, c) * r j ^ (c : ℕ))
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) (hℓ : 1 ≤ ℓ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 0)
    (S : Fin ℓ × Fin n → Finset F) {f : F → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hf : ∀ i a, ‖∑ x ∈ S i, ψ (a * x)‖ ≤ #(S i) * f a) (s : Fin n → Fin ℓ → F)
    {T' T : Finset (Fin n)} (hT' : T' ⊆ T) (w : Fin n → Fin ℓ → F) :
    (#((Fintype.piFinset S).filter fun z => ∀ j ∈ T', (E z - w) j ∈ Submodule.span F {s j}) :
        ℝ) ≤
      #(Fintype.piFinset S) * ((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T' *
        (∑ y ∈ powerCode T r n, ∏ c, f (y c)) ^ ℓ := by
  set B := Fintype.piFinset S
  set K := slotConditionSpace s T'
  set Λ := K.map (slotForms r)
  set q : ℝ := (Fintype.card F : ℝ)
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  -- every form of `Λ` vanishes on the masks of the event
  have hsub : B.filter (fun z => ∀ j ∈ T', (E z - w) j ∈ Submodule.span F {s j}) ⊆
      B.filter (fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - E.symm w i) = 0) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, fun a ha => ?_⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp ha
    set x := z - E.symm w
    have hEx : E x = E z - w := by rw [map_sub, LinearEquiv.apply_symm_apply]
    have hterm : ∀ j, ∑ b, u j b * (E z - w) j b = 0 := by
      intro j
      have huj : u j ∈ (if j ∈ T' then LinearMap.ker (dotForm (s j)) else ⊥) :=
        hu j (Set.mem_univ j)
      by_cases hj : j ∈ T'
      · rw [if_pos hj, LinearMap.mem_ker, dotForm_apply] at huj
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hz.2 j hj)
        rw [← ht]
        simp only [Pi.smul_apply, smul_eq_mul]
        calc ∑ b, u j b * (t * s j b) = t * ∑ b, u j b * s j b := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun b _ => by ring
          _ = 0 := by rw [huj, mul_zero]
      · rw [if_neg hj, Submodule.mem_bot] at huj
        simp [huj]
    calc ∑ i, slotForms r u i * (z i - E.symm w i)
        = ∑ b : Fin ℓ, ∑ c : Fin n, ∑ j, r j ^ (c : ℕ) * u j b * x (b, c) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          rw [slotForms_apply, Finset.sum_mul]
          rfl
      _ = ∑ b : Fin ℓ, ∑ j, ∑ c : Fin n, r j ^ (c : ℕ) * u j b * x (b, c) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ j, ∑ b : Fin ℓ, ∑ c : Fin n, r j ^ (c : ℕ) * u j b * x (b, c) := Finset.sum_comm
      _ = ∑ j, ∑ b, u j b * (E z - w) j b := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← hEx, hE, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = 0 := Finset.sum_eq_zero fun j _ => hterm j
  have hcount := AddChar.card_filter_forall_dot_eq_zero_le ψ hψ Λ S hf (E.symm w)
  -- the forms of `Λ` are the images of `K`
  have hΛs : univ.filter (· ∈ Λ) = (univ.filter (· ∈ K)).image (slotForms r) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Λ,
      Submodule.mem_map]
  have hinj := slotForms_injective (ℓ := ℓ) hr
  have hcardΛ : (q ^ ((ℓ - 1) * #T') : ℝ) ≤ #(univ.filter (· ∈ Λ)) := by
    rw [hΛs, Finset.card_image_of_injective _ hinj]
    have h1 : #(univ.filter (· ∈ K)) = Fintype.card F ^ Module.finrank F K := by
      rw [← Module.card_eq_pow_finrank (K := F) (V := K), ← Fintype.card_subtype]
    rw [h1]
    push_cast
    exact pow_le_pow_right₀ (Nat.one_le_cast.mpr Fintype.card_pos)
      (finrank_slotConditionSpace_ge s T')
  -- the forms of `Λ` have rows in the code `C_T`
  let ext : (Fin ℓ → T → F) → Fin n → Fin ℓ → F := fun μ j b => extendSlots T (μ b) j
  have hext : Function.Injective ext := by
    intro μ μ' h
    funext b j
    have := congrFun (congrFun h j) b
    simpa only [ext, extendSlots, dif_pos j.2] using this
  have hKsub : univ.filter (· ∈ K) ⊆ univ.image ext := by
    intro u hu
    have huK := (Finset.mem_filter.mp hu).2
    refine Finset.mem_image.mpr ⟨fun b j => u j b, Finset.mem_univ _, funext fun j => ?_⟩
    funext b
    simp only [ext, extendSlots]
    split_ifs with hj
    · rfl
    · have : u j ∈ (if j ∈ T' then LinearMap.ker (dotForm (s j)) else ⊥) :=
        huK j (Set.mem_univ j)
      rw [if_neg fun h => hj (hT' h), Submodule.mem_bot] at this
      rw [this]
      rfl
  have hword : ∀ μ b c, slotForms r (ext μ) (b, c) = powerCodeWord T r n (μ b) c := by
    intro μ b c
    have h := coeffOfSlots_extendSlots r T (μ b) c
    simp only [coeffOfSlots, smul_eq_mul] at h
    rw [slotForms_apply, powerCodeWord]
    simp only [ext]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hG0 : ∀ a : Fin ℓ × Fin n → F, 0 ≤ ∏ i, f (a i) := fun a =>
    Finset.prod_nonneg fun i _ => hf0 _
  set P := ∑ y ∈ powerCode T r n, ∏ c, f (y c)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun y _ => Finset.prod_nonneg fun c _ => hf0 _
  have hsum : ∑ a ∈ univ.filter (· ∈ Λ), ∏ i, f (a i) ≤ P ^ ℓ := by
    rw [hΛs, Finset.sum_image fun u _ u' _ h => hinj h]
    calc ∑ u ∈ univ.filter (· ∈ K), ∏ i, f (slotForms r u i)
        ≤ ∑ u ∈ univ.image ext, ∏ i, f (slotForms r u i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hKsub fun u _ _ => hG0 _
      _ = ∑ μ : Fin ℓ → T → F, ∏ b, ∏ c, f (powerCodeWord T r n (μ b) c) := by
          rw [Finset.sum_image fun μ _ μ' _ h => hext h]
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [Fintype.prod_prod_type]
          exact Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun c _ => by
            rw [hword]
      _ = ∏ _b : Fin ℓ, ∑ lam : T → F, ∏ c, f (powerCodeWord T r n lam c) :=
          (Fintype.prod_sum fun _ lam => ∏ c, f (powerCodeWord T r n lam c)).symm
      _ = P ^ ℓ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          rw [show P = ∑ y ∈ univ.image (powerCodeWord T r n), ∏ c, f (y c) from rfl,
            Finset.sum_image fun l _ l' _ h => powerCodeWord_injective hr hr0 T h]
  have hpos : (0 : ℝ) < q ^ ((ℓ - 1) * #T') := by positivity
  have hqℓ : (q / q ^ ℓ) ^ #T' = 1 / q ^ ((ℓ - 1) * #T') := by
    obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [pow_succ', div_mul_cancel_left₀ hq.ne', Nat.add_sub_cancel, pow_mul, one_div,
      inv_pow]
  calc (#(B.filter fun z => ∀ j ∈ T', (E z - w) j ∈ Submodule.span F {s j}) : ℝ)
      ≤ #(B.filter fun z => ∀ a ∈ Λ, ∑ i, a i * (z i - E.symm w i) = 0) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ #B / #(univ.filter (· ∈ Λ)) * ∑ a ∈ univ.filter (· ∈ Λ), ∏ i, f (a i) := hcount
    _ ≤ #B / q ^ ((ℓ - 1) * #T') * P ^ ℓ := by
        gcongr
        exact Finset.sum_nonneg fun a _ => hG0 a
    _ = #B * (q / q ^ ℓ) ^ #T' * P ^ ℓ := by rw [hqℓ]; ring

end SlotCount

section FixedModes

variable {n k ℓ : ℕ}

open Classical in
/-- **Fixed modes with the sharp count**: a mode with slot support `T` is admissible for two
masks drawn from a box with probability at most `(q / q^ℓ)^#T · P_T^{2ℓ}`, with
`P_T = ∑_{y ∈ C_T} ∏_c f (y c)`. The two stages of `card_admissible_le` (the `x̂`-conditions on
`T_x`, then the `x̂'`-conditions on `T_y`, `T_x ⊔ T_y = T`) each take `card_filter_slotSpan_le`. -/
theorem card_admissible_le_box (E : (Fin ℓ × Fin n → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    {r : Fin n → F} (hE : ∀ z j b, E z j b = ∑ c, z (b, c) * r j ^ (c : ℕ))
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) (hℓ : 1 ≤ ℓ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 0)
    (S : Fin ℓ × Fin n → Finset F) {f : F → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hf : ∀ i a, ‖∑ x ∈ S i, ψ (a * x)‖ ≤ #(S i) * f a) (s w₀ : Fin n → Fin ℓ → F)
    {μ : Fin k → Fin n → F × F} {T : Finset (Fin n)} (hT : modeSupport μ = T) :
    (#((Fintype.piFinset S ×ˢ Fintype.piFinset S).filter fun p =>
        Admissible s (E p.1 - w₀) (E p.2 - w₀) μ) : ℝ) ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) *
        (((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T *
          (∑ y ∈ powerCode T r n, ∏ c, f (y c)) ^ (2 * ℓ)) := by
  set B := Fintype.piFinset S
  set g : ℝ := (Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ
  set P := ∑ y ∈ powerCode T r n, ∏ c, f (y c)
  have hg : 0 ≤ g := by positivity
  have hP : 0 ≤ P := Finset.sum_nonneg fun y _ => Finset.prod_nonneg fun c _ => hf0 _
  -- a nonzero pair `p j = μ i j` at every slot of the support
  let p : Fin n → F × F := fun j => if h : ∃ i, μ i j ≠ 0 then μ h.choose j else 0
  have hp : ∀ j ∈ T, p j ≠ 0 ∧ ∃ i, μ i j = p j := by
    intro j hj
    rw [← hT, modeSupport, Finset.mem_filter] at hj
    have h := hj.2
    simp only [p, dif_pos h]
    exact ⟨h.choose_spec, _, rfl⟩
  let Tx := T.filter fun j => (p j).2 = 0
  let Ty := T.filter fun j => (p j).2 ≠ 0
  let shift : (Fin n → Fin ℓ → F) → Fin n → Fin ℓ → F := fun x j =>
    if j ∈ Ty then ((p j).2⁻¹ * (p j).1) • x j else 0
  have hsub : (B ×ˢ B).filter (fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) ⊆
      (B ×ˢ B).filter (fun q => (∀ j ∈ Tx, (E q.1 - w₀) j ∈ Submodule.span F {s j}) ∧
        ∀ j ∈ Ty, (E q.2 - (w₀ + shift (E q.1 - w₀))) j ∈ Submodule.span F {s j}) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, fun j hj => ?_, fun j hj => ?_⟩
    · obtain ⟨hjT, hb⟩ := Finset.mem_filter.mp hj
      obtain ⟨hp0, i, hi⟩ := hp j hjT
      have h := hq.2 i j
      rw [hi, mem_slotAnnihilator] at h
      exact (mem_span_of_slotPairing hp0 h).1 hb
    · obtain ⟨hjT, hb⟩ := Finset.mem_filter.mp hj
      obtain ⟨hp0, i, hi⟩ := hp j hjT
      have h := hq.2 i j
      rw [hi, mem_slotAnnihilator] at h
      have := (mem_span_of_slotPairing hp0 h).2 hb
      simpa only [shift, Pi.sub_apply, Pi.add_apply, if_pos hj, sub_add_eq_sub_sub,
        SetLike.mem_coe] using this
  have hTx : Tx ⊆ T := Finset.filter_subset _ _
  have hTy : Ty ⊆ T := Finset.filter_subset _ _
  have hcount := card_filter_product_le B
    (fun z => ∀ j ∈ Tx, (E z - w₀) j ∈ Submodule.span F {s j})
    (fun z z' => ∀ j ∈ Ty, (E z' - (w₀ + shift (E z - w₀))) j ∈ Submodule.span F {s j})
    (by positivity : (0 : ℝ) ≤ #B * g ^ #Ty * P ^ ℓ)
    (card_filter_slotSpan_le E hE hr hr0 hℓ ψ hψ S hf0 hf s hTx w₀)
    (fun z => card_filter_slotSpan_le E hE hr hr0 hℓ ψ hψ S hf0 hf s hTy _)
  have hcard : #Tx + #Ty = #T := Finset.card_filter_add_card_filter_not _
  calc (#((B ×ˢ B).filter fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) : ℝ)
      ≤ #((B ×ˢ B).filter (fun q => (∀ j ∈ Tx, (E q.1 - w₀) j ∈ Submodule.span F {s j}) ∧
          ∀ j ∈ Ty, (E q.2 - (w₀ + shift (E q.1 - w₀))) j ∈ Submodule.span F {s j})) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (#B * g ^ #Tx * P ^ ℓ) * (#B * g ^ #Ty * P ^ ℓ) := hcount
    _ = #B * #B * (g ^ #T * P ^ (2 * ℓ)) := by
        rw [← hcard, pow_add, two_mul, pow_add]
        ring

open Classical in
/-- Fixed modes with the sharp count, summed: the support-`T` part of the second moment, summed
over the box pairs, is at most
`#B² · (q / q^ℓ)^#T · P_T^{2ℓ} · (∏_i rowMass_i - ∏_i ∏_c κ i c 0)`. -/
theorem sum_supportMoment_le_fixedModes_box (E : (Fin ℓ × Fin n → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    {r : Fin n → F} (hE : ∀ z j b, E z j b = ∑ c, z (b, c) * r j ^ (c : ℕ))
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) (hℓ : 1 ≤ ℓ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 0)
    (S : Fin ℓ × Fin n → Finset F) {f : F → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hf : ∀ i a, ‖∑ x ∈ S i, ψ (a * x)‖ ≤ #(S i) * f a)
    {κ : Fin k → Fin n → F × F → ℝ} (hκ0 : ∀ i c u, 0 ≤ κ i c u) (s w₀ : Fin n → Fin ℓ → F)
    {T : Finset (Fin n)} (hT : T ≠ ∅) :
    ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
        supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) *
        (((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T *
          (∑ y ∈ powerCode T r n, ∏ c, f (y c)) ^ (2 * ℓ)) *
        (∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0) := by
  set B := Fintype.piFinset S
  set P := univ.filter (fun μ : Fin k → Fin n → F × F => modeSupport μ = T)
  set c₀ : ℝ := ((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T *
    (∑ y ∈ powerCode T r n, ∏ c, f (y c)) ^ (2 * ℓ)
  have hw0 : ∀ μ, 0 ≤ modeWeight r κ μ := fun μ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ => hκ0 i c _
  have hrw : ∀ q : (Fin ℓ × Fin n → F) × (Fin ℓ × Fin n → F),
      supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T =
      ∑ μ ∈ P, if Admissible s (E q.1 - w₀) (E q.2 - w₀) μ then modeWeight r κ μ else 0 := by
    intro q
    rw [supportMoment, ← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun μ _ => and_comm) fun _ _ => rfl
  simp_rw [hrw]
  rw [Finset.sum_comm]
  calc ∑ μ ∈ P, ∑ q ∈ B ×ˢ B,
        (if Admissible s (E q.1 - w₀) (E q.2 - w₀) μ then modeWeight r κ μ else 0)
      = ∑ μ ∈ P, modeWeight r κ μ *
          #((B ×ˢ B).filter fun q => Admissible s (E q.1 - w₀) (E q.2 - w₀) μ) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ μ ∈ P, modeWeight r κ μ * (#B * #B * c₀) := by
        refine Finset.sum_le_sum fun μ hμ => mul_le_mul_of_nonneg_left ?_ (hw0 μ)
        exact card_admissible_le_box E hE hr hr0 hℓ ψ hψ S hf0 hf s w₀
          (Finset.mem_filter.mp hμ).2
    _ = #B * #B * c₀ * ∑ μ ∈ P, modeWeight r κ μ := by
        rw [← Finset.sum_mul, mul_comm]
    _ ≤ #B * #B * c₀ * (∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0) := by
        have hc : 0 ≤ c₀ := by
          have : 0 ≤ ∑ y ∈ powerCode T r n, ∏ c, f (y c) :=
            Finset.sum_nonneg fun y _ => Finset.prod_nonneg fun c _ => hf0 _
          positivity
        gcongr
        exact sum_modeWeight_support_le hκ0 hT

/-- The word sum of a support is `1 + δ'` under the small-support bound of a kernel `f ≤ 1`. -/
theorem sum_powerCode_le_one_add {r : Fin n → F} {f : F → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hf1 : ∀ a, f a ≤ 1) {m' : ℕ} {δ' : ℕ → ℝ} (hδ' : SmallSupportBounds r f m' δ')
    {T : Finset (Fin n)} (hT0 : T ≠ ∅) (hTm : #T ≤ m') :
    ∑ y ∈ powerCode T r n, ∏ c, f (y c) ≤ 1 + δ' #T := by
  classical
  have h0 : (0 : Fin n → F) ∈ powerCode T r n :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, powerCodeWord_zero r T⟩
  rw [← Finset.sum_filter_add_sum_filter_not (powerCode T r n) (· ≠ 0), add_comm]
  have hz : (powerCode T r n).filter (fun y => ¬ y ≠ 0) = {0} := by
    ext y
    simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨h0, rfl⟩
  rw [hz, Finset.sum_singleton]
  exact add_le_add (Finset.prod_le_one₀ (fun c _ => hf0 _) fun c _ => hf1 _)
    (hδ'.bound T hT0 hTm)

end FixedModes

section Main

variable {n k ℓ : ℕ}

/-- The support-`t` bound with the sharp count on `m < t ≤ m'`, `2t ≤ n`:
`(Q / Q^ℓ)^t (1 + δ'_t)^{2ℓ} T₂^{kt}` (two windows on the rows); `supportTerm` otherwise. -/
noncomputable def boxSupportTerm (n k ℓ G Q m m' : ℕ) (δ δ' : ℕ → ℝ) (S₁ T₂ : ℝ) (t : ℕ) : ℝ :=
  if m < t ∧ t ≤ m' ∧ t + t ≤ n then
    ((Q : ℝ) / (Q : ℝ) ^ ℓ) ^ t * (1 + δ' t) ^ (2 * ℓ) * (T₂ ^ t) ^ k
  else supportTerm n k ℓ G m δ S₁ T₂ t

open Classical in
/-- **The averaged second moment with the sharp slot count.** Under the hypotheses of
`averagedSecondMoment_le_hybrid`, for the slot transform `E z j b = ∑_c z (b, c) r_j^c`, a
nontrivial character `ψ`, box sides with Fourier bound `0 ≤ f' ≤ 1`
(`‖∑_{x ∈ S i} ψ (a x)‖ ≤ #(S i) · f' a`) and small-support bounds `δ'` of `f'` up to `m'`:
`averagedSecondMoment ≤ ∑_{t = 1}^n C(n, t) · min (boxSupportTerm t) (Y ^ t)`, `Q = #F`. -/
theorem averagedSecondMoment_le_box (E : (Fin ℓ × Fin n → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : Fin ℓ × Fin n → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F}
    (hE : ∀ z j b, E z j b = ∑ c, z (b, c) * r j ^ (c : ℕ))
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) (hℓ : 1 ≤ ℓ)
    {κ : Fin k → Fin n → F × F → ℝ}
    {φ : Fin k → Fin n → F → ℝ} {f : F → ℝ} {S₁ T₂ : ℝ} (hκ : KernelBounds κ φ f S₁ T₂)
    {S₂ : ℝ} (hS₂0 : 0 ≤ S₂) (hS₂ : ∀ i c, ∑ u, φ i c u ^ 2 ≤ S₂) {m : ℕ} {δ : ℕ → ℝ}
    (hδ : SmallSupportBounds r f m δ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 0) {f' : F → ℝ}
    (hf'0 : ∀ a, 0 ≤ f' a) (hf'1 : ∀ a, f' a ≤ 1)
    (hf' : ∀ i a, ‖∑ x ∈ S i, ψ (a * x)‖ ≤ #(S i) * f' a) {m' : ℕ} {δ' : ℕ → ℝ}
    (hδ' : SmallSupportBounds r f' m' δ') (s w₀ : Fin n → Fin ℓ → F) :
    averagedSecondMoment E S r κ s w₀ ≤
      ∑ t ∈ range (n + 1), (n.choose t : ℝ) * (if t = 0 then 0 else
        min (boxSupportTerm n k ℓ G (Fintype.card F) m m' δ δ' S₁ T₂ t)
          (hybridFactor S₁ S₂ k G ℓ ^ t)) := by
  have hφ : ∀ i, WeightBounds (φ i) S₁ S₂ := fun i =>
    ⟨hκ.weight_nonneg i, hκ.weight_le_one i, hκ.weight_sum_le i, hS₂ i⟩
  have hS₁0 : 0 ≤ S₁ := zero_le_one.trans hκ.one_le_mass
  refine averagedSecondMoment_le_of_sum_supportMoment_le E S hG hS r κ s w₀ fun T hT0 => ?_
  have hB : (0 : ℝ) ≤ #(Fintype.piFinset S) * #(Fintype.piFinset S) := by positivity
  rw [mul_min_of_nonneg _ _ hB]
  refine le_min ?_ (sum_supportMoment_le_hybrid E S hG hS hr hr0 hS₁0 hS₂0 hκ.kernel_nonneg
    hκ.kernel_le_mul hφ s w₀ T)
  unfold boxSupportTerm
  split_ifs with hbox
  · obtain ⟨-, hTm, hmed⟩ := hbox
    have hP := sum_powerCode_le_one_add hf'0 hf'1 hδ' hT0 hTm
    have hP0 : 0 ≤ ∑ y ∈ powerCode T r n, ∏ c, f' (y c) :=
      Finset.sum_nonneg fun y _ => Finset.prod_nonneg fun c _ => hf'0 _
    have hκ0 := hκ.kernel_nonneg
    have ha0 : ∀ i, 0 ≤ ∏ c, κ i c 0 := fun i => Finset.prod_nonneg fun c _ => hκ0 i c _
    have hrow0 : ∀ i, ∏ c, κ i c 0 ≤ rowMass r κ i T := by
      intro i
      have := Finset.single_le_sum (f := fun lam : T → F × F => ∏ c, κ i c (pairWord r T lam c))
        (fun lam _ => Finset.prod_nonneg fun c _ => hκ0 i c _) (Finset.mem_univ 0)
      simpa [rowMass, pairWord_zero] using this
    have hrows : ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 ≤ (T₂ ^ #T) ^ k :=
      calc ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 ≤ ∏ i, rowMass r κ i T :=
            sub_le_self _ (Finset.prod_nonneg fun i _ => ha0 i)
        _ ≤ ∏ _i : Fin k, T₂ ^ #T := Finset.prod_le_prod₀
            (fun i _ => (ha0 i).trans (hrow0 i)) fun i _ =>
              rowMass_le_two_windows hr hr0 hκ0 hκ.kernel_le_one hκ.kernel_sq_sum_le i hmed
        _ = (T₂ ^ #T) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (sum_supportMoment_le_fixedModes_box E hE hr hr0 hℓ ψ hψ S hf'0 hf' hκ0 s w₀
      hT0).trans ?_
    have hrows0 : 0 ≤ ∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0 := by
      have := Finset.prod_le_prod₀ (s := univ) (fun i _ => ha0 i) fun i _ => hrow0 i
      linarith
    have hg : (0 : ℝ) ≤ ((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T := by positivity
    calc #(Fintype.piFinset S) * #(Fintype.piFinset S) *
          (((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T *
            (∑ y ∈ powerCode T r n, ∏ c, f' (y c)) ^ (2 * ℓ)) *
          (∏ i, rowMass r κ i T - ∏ i, ∏ c, κ i c 0)
        ≤ #(Fintype.piFinset S) * #(Fintype.piFinset S) *
          (((Fintype.card F : ℝ) / (Fintype.card F : ℝ) ^ ℓ) ^ #T * (1 + δ' #T) ^ (2 * ℓ)) *
          (T₂ ^ #T) ^ k :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hP0 hP _) hg) (by positivity)) hrows hrows0
            (mul_nonneg (by positivity) (mul_nonneg hg (pow_nonneg (hP0.trans hP) _)))
      _ = _ := by ring
  · exact sum_supportMoment_le_supportTerm E S hG hS hr hr0 hκ hδ s w₀ hT0

end Main

section Envelope

/-- The four-block closure of `∑_t C(256, t) · min (boxSupportTerm t) (Y ^ t)` with small
supports up to `4` and the sharp count at `t = 5`: the small block, the sharp term at `t = 5`,
the two-window block `t ∈ [6, 128]` (`≤ a^6 / (720 (1 - a))`) and the hybrid block `t ≥ 129`. -/
theorem sum_min_boxSupportTerm_le {k ℓ G Q : ℕ} {δ δ' : ℕ → ℝ} {S₁ T₂ Y : ℝ}
    (hT₂ : 0 ≤ T₂) (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        8809549056 * (((Q : ℝ) / (Q : ℝ) ^ ℓ) ^ 5 * (1 + δ' 5) ^ (2 * ℓ) * (T₂ ^ 5) ^ k) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 6 /
          (720 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * Y ^ 129 := by
  set g : ℝ := (G : ℝ) / (G : ℝ) ^ ℓ
  set a : ℝ := 256 * g * T₂ ^ k
  have hg : 0 ≤ g := by positivity
  have ha0 : 0 ≤ a := by positivity
  rw [← Finset.sum_range_add_sum_Ico _ (show 6 ≤ 257 by norm_num),
    ← Finset.sum_Ico_consecutive _ (show 6 ≤ 129 by norm_num) (show 129 ≤ 257 by norm_num),
    Finset.sum_range_succ]
  have h1 : ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else g ^ t * ((1 + δ t) ^ (2 * k) - 1)) := by
    refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have : t ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    split_ifs with h0
    · exact le_rfl
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [boxSupportTerm, supportTerm, if_neg (show ¬ (4 < t ∧ t ≤ 5 ∧ t + t ≤ 256) by
        omega), if_pos this, g]
  have h5 : ((256 : ℕ).choose 5 : ℝ) *
      (if 5 = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ 5) (Y ^ 5)) ≤
      8809549056 * (((Q : ℝ) / (Q : ℝ) ^ ℓ) ^ 5 * (1 + δ' 5) ^ (2 * ℓ) * (T₂ ^ 5) ^ k) := by
    rw [if_neg (by norm_num), choose_256_five]
    push_cast
    refine mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (le_of_eq ?_)) (by norm_num)
    simp only [boxSupportTerm, if_pos (show 4 < 5 ∧ 5 ≤ 5 ∧ 5 + 5 ≤ 256 by norm_num)]
  have h2 : ∑ t ∈ Ico 6 129, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      a ^ 6 / (720 * (1 - a)) := by
    calc _ ≤ ∑ t ∈ Ico 6 129, a ^ t / 720 := by
          refine Finset.sum_le_sum fun t ht => ?_
          obtain ⟨ht6, ht129⟩ := Finset.mem_Ico.mp ht
          have hne : t ≠ 0 := by omega
          have hbox : boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t = g ^ t * (T₂ ^ t) ^ k := by
            simp only [boxSupportTerm, supportTerm,
              if_neg (show ¬ (4 < t ∧ t ≤ 5 ∧ t + t ≤ 256) by omega),
              if_neg (show ¬ t ≤ 4 by omega), if_pos (show t + t ≤ 256 by omega), g]
          rw [if_neg hne]
          have hch : ((256 : ℕ).choose t : ℝ) ≤ (256 : ℝ) ^ t / t.factorial := by
            have := Nat.choose_le_pow_div (α := ℝ) t 256
            simpa using this
          have hfac : (720 : ℝ) ≤ t.factorial := by
            have : (6 : ℕ).factorial ≤ t.factorial := Nat.factorial_le ht6
            exact_mod_cast (show (720 : ℕ) ≤ t.factorial by simpa [Nat.factorial] using this)
          have hX : 0 ≤ g ^ t * (T₂ ^ t) ^ k := by positivity
          calc ((256 : ℕ).choose t : ℝ) *
                min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t) (Y ^ t)
              ≤ ((256 : ℕ).choose t : ℝ) * (g ^ t * (T₂ ^ t) ^ k) :=
                mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hbox.le) (Nat.cast_nonneg _)
            _ ≤ (256 : ℝ) ^ t / t.factorial * (g ^ t * (T₂ ^ t) ^ k) :=
                mul_le_mul_of_nonneg_right hch hX
            _ ≤ (256 : ℝ) ^ t / 720 * (g ^ t * (T₂ ^ t) ^ k) := by
                gcongr
            _ = a ^ t / 720 := by
                simp only [a]
                rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm t k]
                ring
      _ = (∑ t ∈ Ico 6 129, a ^ t) / 720 := by rw [Finset.sum_div]
      _ ≤ a ^ 6 / (1 - a) / 720 := by
          gcongr
          exact geom_sum_Ico_le_of_lt_one ha0 ha
      _ = a ^ 6 / (720 * (1 - a)) := by rw [div_div, mul_comm]
  have h3 : ∑ t ∈ Ico 129 257, ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (boxSupportTerm 256 k ℓ G Q 4 5 δ δ' S₁ T₂ t) (Y ^ t)) ≤
      2 ^ 256 * Y ^ 129 := by
    calc _ ≤ ∑ t ∈ range 257, ((256 : ℕ).choose t : ℝ) * Y ^ 129 := by
          refine (Finset.sum_le_sum fun t ht => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => Finset.mem_range.mpr
              (Finset.mem_Ico.mp ht).2) fun t _ _ => by positivity)
          obtain ⟨ht1, -⟩ := Finset.mem_Ico.mp ht
          rw [if_neg (by omega)]
          exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans
            (pow_le_pow_of_le_one hY0 hY ht1)) (Nat.cast_nonneg _)
      _ = 2 ^ 256 * Y ^ 129 := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose 256
  linarith

/-- **The ML-DSA-44 envelope with the sharp slot count.** With `k = ℓ = 4`, `L = 190307`,
`G = 261987`, `q = 8380417`, `T₂ = q² / (44 L²)`, the kernel bounds `δ₁ ≤ 2^-512, δ₂ ≤ 2^-210,
δ₃ ≤ 2^-155, δ₄ ≤ 2^-52`, the box bound `δ'₅ ≤ 2^-7`, `S₁ ≤ 1620` and `S₂ ≤ q / L`:
`∑_t C(256, t) · min (boxSupportTerm t) (hybridFactor ^ t) ≤ 2^-154`. The two-window term at
`t = 6` dominates (`2^-154.48`); the sharp term at `t = 5` is `2^-202.7`. -/
theorem envelope_box_mldsa44 {δ δ' : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t) (hδ1 : δ 1 ≤ 1 / 2 ^ 512)
    (hδ2 : δ 2 ≤ 1 / 2 ^ 210) (hδ3 : δ 3 ≤ 1 / 2 ^ 155) (hδ4 : δ 4 ≤ 1 / 2 ^ 52)
    (hδ'0 : 0 ≤ δ' 5) (hδ'5 : δ' 5 ≤ 1 / 2 ^ 7) {S₁ S₂ : ℝ}
    (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 1620) (hS₂0 : 0 ≤ S₂) (hS₂ : S₂ ≤ 8380417 / 190307) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (boxSupportTerm 256 4 4 261987 8380417 4 5 δ δ' S₁
          (8380417 ^ 2 / (44 * 190307 ^ 2)) t) (hybridFactor S₁ S₂ 4 261987 4 ^ t)) ≤
      1 / 2 ^ 154 := by
  have hY := hybridFactor_mldsa44_le hS₁0 hS₁ hS₂0 hS₂
  have hY0 : 0 ≤ hybridFactor S₁ S₂ 4 261987 4 := by
    rw [hybridFactor_eq _ _ _ (show 1 ≤ 261987 by norm_num)]
    positivity
  set Y := hybridFactor S₁ S₂ 4 261987 4
  refine (sum_min_boxSupportTerm_le (by positivity) (by norm_num) hY0
    (hY.trans (by norm_num))).trans ?_
  have h4 : 4 * Y ≤ 1 / 256 := by linarith
  have h40 : 0 ≤ 4 * Y := by positivity
  have hlarge : 2 ^ 256 * Y ^ 129 ≤ (1 / 256) ^ 32 := by
    calc 2 ^ 256 * Y ^ 129 ≤ 2 ^ 256 * Y ^ 128 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hY0 (hY.trans (by norm_num))
            (by norm_num)) (by positivity)
      _ = (4 * Y) ^ 128 := by rw [mul_pow]; norm_num
      _ ≤ (4 * Y) ^ 32 := pow_le_pow_of_le_one h40 (h4.trans (by norm_num)) (by norm_num)
      _ ≤ (1 / 256) ^ 32 := pow_le_pow_left₀ h40 h4 _
  have h5 : (1 + δ' 5) ^ (2 * 4) ≤ (1 + 1 / 2 ^ 7) ^ (2 * 4) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  rw [sum_range_five_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 1) hδ1
    (by rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]; norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 4) hδ4 (by norm_num)
  set g : ℝ := ((261987 : ℕ) : ℝ) / (261987 : ℝ) ^ 4
  set gq : ℝ := ((8380417 : ℕ) : ℝ) / (8380417 : ℝ) ^ 4
  have hg : 0 ≤ g := by positivity
  have hgq : 0 ≤ gq := by positivity
  set T₂ : ℝ := 8380417 ^ 2 / (44 * 190307 ^ 2)
  have hT₂ : 0 ≤ T₂ := by positivity
  have hsharp : 8809549056 * (gq ^ 5 * (1 + δ' 5) ^ (2 * 4) * (T₂ ^ 5) ^ 4) ≤
      8809549056 * (gq ^ 5 * (1 + 1 / 2 ^ 7) ^ (2 * 4) * (T₂ ^ 5) ^ 4) := by
    gcongr
  have hnum : 256 * (g ^ 1 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 512))) +
      32640 * (g ^ 2 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 210))) +
      2763520 * (g ^ 3 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 155))) +
      174792640 * (g ^ 4 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 52))) +
      8809549056 * (gq ^ 5 * (1 + 1 / 2 ^ 7) ^ (2 * 4) * (T₂ ^ 5) ^ 4) +
      (256 * g * T₂ ^ 4) ^ 6 / (720 * (1 - 256 * g * T₂ ^ 4)) +
      (1 / 256) ^ 32 ≤ 1 / 2 ^ 154 := by
    rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]
    simp only [g, gq, T₂]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4)]

end Envelope

end GordieHowe.MLDSA.Regularity
