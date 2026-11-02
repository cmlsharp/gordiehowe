-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.Envelope
public import GordieHowe.Applications.MLDSA.Regularity.KernelMass
public import GordieHowe.Foundations.ToMathlib.InformationSetFibres

@[expose] public section

/-!
# Large supports: the hybrid annihilator bound

The fixed-mask route of `SecondMoment.lean` bounds a row's kernel mass over the admissible modes
`∏_{j ∈ T} D_j` (`D_j` the slot annihilator at the masks) by `S₁ ^ dim`, paying the `ℓ¹` mass
`S₁` for every free coordinate. This file replaces `S₁` by the `ℓ²` mass `S₂` on the diagonal
slots, where `D_j` is a line `η = c_j ξ` with `c_j ≠ 0`.

* `rowSum_le_prod_lineWeight`: a row's kernel mass over `∏_{j ∈ T} D_j` is at most
  `S₂ ^ #T_D · S₁ ^ (#T_X + #T_Y)`, with `T_D` the diagonal slots, `T_X` the slots containing
  `(1, 0)` and `T_Y` those containing `(0, 1)` (a full slot is in both). The modes are
  `ξ^∨ = y + s`, `η^∨ = Φ y + t` (`y` on `T_D`, `s` on `T_X`, `t` on `T_Y`, `Φ` the scaling by
  `c_j`), and the bound is `sum_fibreSum_mul_fibreSum_le` with the consecutive windows of
  `isFibredCode_slotVectors` as information sets.
* `supportMoment_le_hybrid`, `sum_supportMoment_le_hybrid`: per slot the weight `S₁^k`
  (`ξ`-line, `x̂ ∈ span ŝ₁`), `S₁^k` (`η`-line, `x̂' ∈ span ŝ₁`), `S₂^k` (diagonal,
  `x̂' ∈ span (x̂, ŝ₁)`) or `S₁^{2k}` (full, both in `span ŝ₁`), and averaging the masks in two
  stages gives `#B² · Y ^ #T` with
  `Y = hybridFactor = 2 G^{-(ℓ-1)} S₁^k + G^{-(ℓ-2)} S₂^k + G^{-2(ℓ-1)} S₁^{2k}`.
* `averagedSecondMoment_le_hybrid`: every support size `t` takes
  `min (supportTerm t) (Y ^ t)` in the sum of `averagedSecondMoment_le`.
* `envelope_mldsa44`: at ML-DSA-44 (`k = ℓ = 4`, `L = 190307`, `G = 261987`, `S₁ ≤ 1620` by
  `sum_le_1620`, `S₂ ≤ q / L`) the sum is at most `2^-127`; the hybrid term closes every
  `t ≥ 129` (`hybridFactor_mldsa44_le`: `Y ≤ 2^-10`).

Source of the setting: "A shorter proof of the stated HighBits regularity claim" (10 September
2026), Section 3, equations (4)-(6). The general row bound (Cauchy–Schwarz over the diagonal part,
information sets on the fibres) is in `GordieHowe/Foundations/ToMathlib/InformationSetFibres.lean`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section SlotCodes

variable {n : ℕ}

/-- The coefficient map `v ↦ (c ↦ ∑_j r_j ^ c v_j)` on scalar slot vectors, as an additive map. -/
def slotWord (r : Fin n → F) : (Fin n → F) →+ (Fin n → F) where
  toFun := coeffOfSlots r
  map_zero' := coeffOfSlots_zero r
  map_add' v w := by
    funext c
    simp [coeffOfSlots, Finset.sum_add_distrib, mul_add]

theorem slotWord_apply (r : Fin n → F) (v : Fin n → F) (c : Fin n) :
    slotWord r v c = ∑ j, r j ^ (c : ℕ) * v j := rfl

/-- For distinct roots the coefficient map is injective (a transposed Vandermonde matrix). -/
theorem slotWord_injective {r : Fin n → F} (hr : Function.Injective r) :
    Function.Injective (slotWord r) := by
  have hdet : (Matrix.vandermonde r).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hr
  intro v w h
  have h0 : (fun j => v j - w j) = 0 := by
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet (funext fun c => ?_)
    have := congrFun h c
    simp only [slotWord_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, this, sub_self]
  funext j
  exact sub_eq_zero.mp (congrFun h0 j)

/-- The slot vectors supported on `T`. -/
def slotVectors (T : Finset (Fin n)) : Finset (Fin n → F) :=
  univ.filter fun v => ∀ j ∉ T, v j = 0

theorem mem_slotVectors {T : Finset (Fin n)} {v : Fin n → F} :
    v ∈ slotVectors T ↔ ∀ j ∉ T, v j = 0 := by
  simp [slotVectors]

/-- The words of the slot vectors supported on `T` are the power code of `T`. -/
theorem image_slotWord_slotVectors (r : Fin n → F) (T : Finset (Fin n)) :
    (slotVectors T).image (slotWord r) = powerCode T r n := by
  ext w
  simp only [Finset.mem_image, powerCode, Finset.mem_univ, true_and, mem_slotVectors]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun j => v j, funext fun c => ?_⟩
    rw [powerCodeWord, slotWord_apply, ← Finset.sum_subset (Finset.subset_univ T)
      fun j _ hj => by rw [hv j hj, mul_zero], ← Finset.sum_coe_sort T]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨lam, rfl⟩
    refine ⟨extendSlots T lam, fun j hj => by simp [extendSlots, hj], funext fun c => ?_⟩
    have := coeffOfSlots_extendSlots r T lam c
    simp only [smul_eq_mul] at this
    rw [powerCodeWord]
    show coeffOfSlots r (extendSlots T lam) c = _
    rw [this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Every window of `#T` consecutive coefficients is an information set of the words of the slot
vectors supported on `T` (`vandermonde_isInformationSet`). -/
theorem isInformationSet_slotVectors {r : Fin n → F} (hr : Function.Injective r)
    (hr0 : ∀ j, r j ≠ 0) {T : Finset (Fin n)} {s : ℕ} (hs : s + #T ≤ n) :
    IsInformationSet ((slotVectors T).image (slotWord r)) (consecutiveWindow hs) := by
  rw [image_slotWord_slotVectors]
  exact vandermonde_isInformationSet hr.injOn (fun j _ => hr0 j) hs

theorem consecutiveWindow_subset {m m' : ℕ} (h : 0 + m ≤ n) (h' : 0 + m' ≤ n) (hm : m ≤ m') :
    consecutiveWindow h ⊆ consecutiveWindow h' := by
  intro b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hb
  exact Finset.mem_map.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem card_le_of_subset_fin (T : Finset (Fin n)) : 0 + #T ≤ n := by
  simpa using (Finset.card_le_univ T).trans (Fintype.card_fin n).le

/-- Slot vectors supported on disjoint `D` and `X` form a fibred code: the sums lie in the
vectors supported on `D ∪ X`, the first `#D + #X` coefficients are an information set of those,
and the first `#X` an information set of the fibre. -/
theorem isFibredCode_slotVectors {r : Fin n → F} (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0)
    {D X : Finset (Fin n)} (hDX : Disjoint D X) :
    ∃ J J₁ : Finset (Fin n), IsFibredCode (slotWord r) (slotVectors D) (slotVectors X)
      (slotVectors (D ∪ X)) J J₁ ∧ #J - #J₁ = #D ∧ #J₁ = #X := by
  have hU := card_le_of_subset_fin (D ∪ X)
  have hX := card_le_of_subset_fin X
  have hcard : #(D ∪ X) = #D + #X := Finset.card_union_of_disjoint hDX
  refine ⟨consecutiveWindow hU, consecutiveWindow hX, ⟨?_, ?_, ?_, ?_,
    isInformationSet_slotVectors hr hr0 hU, isInformationSet_slotVectors hr hr0 hX,
    consecutiveWindow_subset hX hU (by omega)⟩, ?_, card_consecutiveWindow hX⟩
  · intro a ha b hb
    rw [mem_slotVectors] at ha hb ⊢
    intro j hj
    simp [ha j hj, hb j hj]
  · intro a ha b hb
    rw [mem_slotVectors] at ha hb ⊢
    intro j hj
    simp [ha j hj, hb j hj]
  · intro p hp q hq
    rw [mem_slotVectors] at hp hq ⊢
    intro j hj
    rw [Finset.mem_union, not_or] at hj
    simp [hp j hj.1, hq j hj.2]
  · rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_slotVectors] at hpq hpq' h
    have hp : p = p' := funext fun j => by
      by_cases hj : j ∈ X
      · rw [hpq.1 j (Finset.disjoint_right.mp hDX hj), hpq'.1 j (Finset.disjoint_right.mp hDX hj)]
      · have := congrFun h j
        simp only [Pi.add_apply, hpq.2 j hj, hpq'.2 j hj, add_zero] at this
        exact this
    subst hp
    exact Prod.ext rfl (add_left_cancel h)
  · rw [card_consecutiveWindow, card_consecutiveWindow, hcard, Nat.add_sub_cancel]

end SlotCodes

section Lines

/-! ### Slot annihilators by type

A nonzero slot annihilator `D ⊆ F²` contains `(1, 0)` (the `ξ`-line, or all of `F²`), contains
`(0, 1)` (the `η`-line, or all of `F²`), or is a diagonal line `η = c ξ` with `c ≠ 0`. -/

omit [Fintype F] [DecidableEq F] in
theorem snd_eq_zero_of_mem {D : Submodule F (F × F)} (hX : ((1 : F), (0 : F)) ∈ D)
    (hY : ((0 : F), (1 : F)) ∉ D) {p : F × F} (hp : p ∈ D) : p.2 = 0 := by
  by_contra hb
  apply hY
  convert D.smul_mem p.2⁻¹ (D.sub_mem hp (D.smul_mem p.1 hX)) using 1
  ext <;> simp [hb]

omit [Fintype F] [DecidableEq F] in
theorem fst_eq_zero_of_mem {D : Submodule F (F × F)} (hY : ((0 : F), (1 : F)) ∈ D)
    (hX : ((1 : F), (0 : F)) ∉ D) {p : F × F} (hp : p ∈ D) : p.1 = 0 := by
  by_contra ha
  apply hX
  convert D.smul_mem p.1⁻¹ (D.sub_mem hp (D.smul_mem p.2 hY)) using 1
  ext <;> simp [ha]

omit [Fintype F] [DecidableEq F] in
/-- A nonzero slot annihilator without `(1, 0)` has a point with nonzero second coordinate. -/
theorem exists_mem_snd_ne_zero {D : Submodule F (F × F)} (hD : D ≠ ⊥)
    (hX : ((1 : F), (0 : F)) ∉ D) : ∃ p ∈ D, p.2 ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  refine ⟨p, hp, fun hb => hX ?_⟩
  have ha : p.1 ≠ 0 := fun ha => hne (Prod.ext ha hb)
  convert D.smul_mem p.1⁻¹ hp using 1
  ext <;> simp [ha, hb]

omit [Fintype F] [DecidableEq F] in
/-- A nonzero slot annihilator containing neither `(1, 0)` nor `(0, 1)` is a diagonal line
`η = c ξ` with `c ≠ 0`. -/
theorem exists_slope {D : Submodule F (F × F)} (hD : D ≠ ⊥) (hX : ((1 : F), (0 : F)) ∉ D)
    (hY : ((0 : F), (1 : F)) ∉ D) : ∃ c : F, c ≠ 0 ∧ ∀ p ∈ D, p.2 = c * p.1 := by
  obtain ⟨p₀, hp₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have h1 : p₀.1 ≠ 0 := by
    intro ha
    have hb : p₀.2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
    apply hY
    convert D.smul_mem p₀.2⁻¹ hp₀ using 1
    ext <;> simp [ha, hb]
  have h2 : p₀.2 ≠ 0 := by
    intro hb
    apply hX
    convert D.smul_mem p₀.1⁻¹ hp₀ using 1
    ext <;> simp [h1, hb]
  refine ⟨p₀.2 / p₀.1, div_ne_zero h2 h1, fun p hp => ?_⟩
  have hw := D.sub_mem (D.smul_mem p₀.1 hp) (D.smul_mem p.1 hp₀)
  by_cases hc : p₀.1 * p.2 - p.1 * p₀.2 = 0
  · field_simp
    linear_combination hc
  · exfalso
    apply hY
    convert D.smul_mem (p₀.1 * p.2 - p.1 * p₀.2)⁻¹ hw using 1
    ext
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      ring
    · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      rw [inv_mul_cancel₀ hc]

open Classical in
/-- The row weight of a slot annihilator in the hybrid bound: `S₂` for a diagonal line, `S₁` for
each of `(1, 0)`, `(0, 1)` it contains (so `S₁` for an axis line, `S₁²` for all of `F²`). -/
noncomputable def lineWeight (S₁ S₂ : ℝ) (D : Submodule F (F × F)) : ℝ :=
  (if ((1 : F), (0 : F)) ∉ D ∧ ((0 : F), (1 : F)) ∉ D then S₂ else 1) *
    (if ((1 : F), (0 : F)) ∈ D then S₁ else 1) * (if ((0 : F), (1 : F)) ∈ D then S₁ else 1)

end Lines

section HybridRow

variable {n : ℕ}

omit [Fintype F] [DecidableEq F] in
open Classical in
/-- The product of the row weights over `T` splits by slot type:
`∏_{j ∈ T} lineWeight (D j) = S₂ ^ #T_D · S₁ ^ #T_X · S₁ ^ #T_Y`. -/
theorem prod_lineWeight (S₁ S₂ : ℝ) (D : Fin n → Submodule F (F × F)) (T : Finset (Fin n)) :
    ∏ j ∈ T, lineWeight S₁ S₂ (D j) =
      S₂ ^ #(T.filter fun j => ((1 : F), (0 : F)) ∉ D j ∧ ((0 : F), (1 : F)) ∉ D j) *
        S₁ ^ #(T.filter fun j => ((1 : F), (0 : F)) ∈ D j) *
        S₁ ^ #(T.filter fun j => ((0 : F), (1 : F)) ∈ D j) := by
  simp only [lineWeight, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, one_pow,
    mul_one]

open Classical in
/-- **The hybrid row bound at fixed masks.** For slot annihilators `D j ≠ 0` on `T`, a row's
kernel mass over the modes in `∏_{j ∈ T} D j` is at most `∏_{j ∈ T} lineWeight (D j)`, that is
`S₂ ^ #T_D · S₁ ^ (#T_X + #T_Y)`. The modes are `ξ^∨ = y + s`, `η^∨ = Φ y + t` with `y` on the
diagonal slots `T_D`, `s` on `T_X` (slots containing `(1, 0)`), `t` on `T_Y` (slots containing
`(0, 1)`) and `Φ` the diagonal scaling, so the mass is at most
`∑_y (∑_s F (y + s)) (∑_t F (Φ y + t))` (`sum_fibreSum_mul_fibreSum_le`). -/
theorem rowSum_le_prod_lineWeight {r : Fin n → F} (hr : Function.Injective r)
    (hr0 : ∀ j, r j ≠ 0) {κ : Fin n → F × F → ℝ} {φ : Fin n → F → ℝ} {S₁ S₂ : ℝ}
    (hκ0 : ∀ c u, 0 ≤ κ c u) (hκφ : ∀ c u, κ c u ≤ φ c u.1 * φ c u.2)
    (hφ : WeightBounds φ S₁ S₂) (D : Fin n → Submodule F (F × F)) (T : Finset (Fin n))
    (hD : ∀ j ∈ T, D j ≠ ⊥) :
    ∑ ν ∈ univ.filter (· ∈ Submodule.pi Set.univ fun j => if j ∈ T then D j else ⊥),
        ∏ c, κ c (coeffOfSlots r ν c) ≤ ∏ j ∈ T, lineWeight S₁ S₂ (D j) := by
  set R : Submodule F (Fin n → F × F) := Submodule.pi Set.univ fun j => if j ∈ T then D j else ⊥
  set TX := T.filter fun j => ((1 : F), (0 : F)) ∈ D j
  set TY := T.filter fun j => ((0 : F), (1 : F)) ∈ D j
  set TD := T.filter fun j => ((1 : F), (0 : F)) ∉ D j ∧ ((0 : F), (1 : F)) ∉ D j
  have hslope : ∀ j, ∃ c : F, c ≠ 0 ∧ (j ∈ TD → ∀ p ∈ D j, p.2 = c * p.1) := by
    intro j
    by_cases hj : j ∈ TD
    · obtain ⟨hjT, hx, hy⟩ : j ∈ T ∧ ((1 : F), (0 : F)) ∉ D j ∧ ((0 : F), (1 : F)) ∉ D j :=
        Finset.mem_filter.mp hj
      obtain ⟨c, hc, h⟩ := exists_slope (hD j hjT) hx hy
      exact ⟨c, hc, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hj⟩
  choose lam hlam0 hlam using hslope
  set Φ : (Fin n → F) → (Fin n → F) := fun v j => lam j * v j
  set restr : Finset (Fin n) → (Fin n → F) → (Fin n → F) := fun S v j => if j ∈ S then v j else 0
  set fs : (Fin n → F × F) → (Fin n → F) := fun ν j => (ν j).1
  set sn : (Fin n → F × F) → (Fin n → F) := fun ν j => (ν j).2
  set Fw : (Fin n → F) → ℝ := fun w => ∏ c, φ c (w c)
  -- the kernel weight of a mode is at most the product of the weights of its two words
  have hW : ∀ ν, ∏ c, κ c (coeffOfSlots r ν c) ≤ Fw (slotWord r (fs ν)) * Fw (slotWord r (sn ν)) := by
    intro ν
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun c _ => hκ0 c _) fun c _ => ?_
    have e1 : (coeffOfSlots r ν c).1 = slotWord r (fs ν) c := by
      simp [coeffOfSlots, slotWord_apply, Prod.fst_sum, fs]
    have e2 : (coeffOfSlots r ν c).2 = slotWord r (sn ν) c := by
      simp [coeffOfSlots, slotWord_apply, Prod.snd_sum, sn]
    rw [← e1, ← e2]
    exact hκφ c _
  -- the decomposition of an admissible mode
  have key : ∀ ν ∈ univ.filter (· ∈ R), ∀ j,
      (ν j).1 = restr TD (fs ν) j + restr TX (fs ν) j ∧
        (ν j).2 = Φ (restr TD (fs ν)) j + restr TY (sn ν) j := by
    intro ν hν j
    have hm : ν j ∈ (if j ∈ T then D j else ⊥) :=
      (Submodule.mem_pi.mp (Finset.mem_filter.mp hν).2) j (Set.mem_univ j)
    by_cases hjT : j ∈ T
    · rw [if_pos hjT] at hm
      by_cases hx : ((1 : F), (0 : F)) ∈ D j <;> by_cases hy : ((0 : F), (1 : F)) ∈ D j
      · simp [restr, Φ, fs, sn, TD, TX, TY, hjT, hx, hy]
      · simp [restr, Φ, fs, sn, TD, TX, TY, hjT, hx, hy, snd_eq_zero_of_mem hx hy hm]
      · simp [restr, Φ, fs, sn, TD, TX, TY, hjT, hx, hy, fst_eq_zero_of_mem hy hx hm]
      · have hjD : j ∈ TD := Finset.mem_filter.mpr ⟨hjT, hx, hy⟩
        simp [restr, Φ, fs, sn, TD, TX, TY, hjT, hx, hy, hlam j hjD _ hm]
    · rw [if_neg hjT, Submodule.mem_bot] at hm
      simp [restr, Φ, fs, sn, TD, TX, TY, hjT, hm]
  have hfs : ∀ ν ∈ univ.filter (· ∈ R), fs ν = restr TD (fs ν) + restr TX (fs ν) :=
    fun ν hν => funext fun j => (key ν hν j).1
  have hsn : ∀ ν ∈ univ.filter (· ∈ R), sn ν = Φ (restr TD (fs ν)) + restr TY (sn ν) :=
    fun ν hν => funext fun j => (key ν hν j).2
  -- the three codes
  set VD := (slotVectors TD : Finset (Fin n → F))
  set VX := (slotVectors TX : Finset (Fin n → F))
  set VY := (slotVectors TY : Finset (Fin n → F))
  set dec : (Fin n → F × F) → ((Fin n → F) × (Fin n → F)) × (Fin n → F) := fun ν =>
    ((restr TD (fs ν), restr TX (fs ν)), restr TY (sn ν))
  set Gw : ((Fin n → F) × (Fin n → F)) × (Fin n → F) → ℝ := fun x =>
    Fw (slotWord r (x.1.1 + x.1.2)) * Fw (slotWord r (Φ x.1.1 + x.2))
  have hFw0 : ∀ w, 0 ≤ Fw w := fun w => Finset.prod_nonneg fun c _ => hφ.nonneg c _
  have hrestr : ∀ S v, restr S v ∈ (slotVectors S : Finset (Fin n → F)) := fun S v =>
    mem_slotVectors.mpr fun j hj => by simp [restr, hj]
  have hdecinj : Set.InjOn dec (univ.filter (· ∈ R) : Finset (Fin n → F × F)) := by
    intro ν hν ν' hν' h
    simp only [dec, Prod.mk.injEq] at h
    have h1 : fs ν = fs ν' := by rw [hfs ν hν, hfs ν' hν', h.1.1, h.1.2]
    have h2 : sn ν = sn ν' := by rw [hsn ν hν, hsn ν' hν', h.1.1, h.2]
    funext j
    exact Prod.ext (congrFun h1 j) (congrFun h2 j)
  have hDX : Disjoint TD TX := by
    rw [Finset.disjoint_filter]
    exact fun j _ h hx => h.1 hx
  have hDY : Disjoint TD TY := by
    rw [Finset.disjoint_filter]
    exact fun j _ h hy => h.2 hy
  obtain ⟨J, J₁, hC, hJ, hJ₁⟩ := isFibredCode_slotVectors hr hr0 hDX
  obtain ⟨J', J₁', hC', hJ', hJ₁'⟩ := isFibredCode_slotVectors hr hr0 hDY
  have hΦ : ∀ p ∈ VD, Φ p ∈ VD := fun p hp => mem_slotVectors.mpr fun j hj => by
    simp [Φ, mem_slotVectors.mp hp j hj]
  have hΦinj : Set.InjOn Φ VD := fun p _ p' _ h => funext fun j =>
    mul_left_cancel₀ (hlam0 j) (congrFun h j)
  calc ∑ ν ∈ univ.filter (· ∈ R), ∏ c, κ c (coeffOfSlots r ν c)
      ≤ ∑ ν ∈ univ.filter (· ∈ R), Gw (dec ν) := by
        refine Finset.sum_le_sum fun ν hν => (hW ν).trans (le_of_eq ?_)
        simp only [Gw, dec]
        rw [← hfs ν hν, ← hsn ν hν]
    _ ≤ ∑ x ∈ (VD ×ˢ VX) ×ˢ VY, Gw x := by
        rw [← Finset.sum_image hdecinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ =>
          mul_nonneg (hFw0 _) (hFw0 _)
        intro x hx
        obtain ⟨ν, -, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hrestr _ _, hrestr _ _⟩,
          hrestr _ _⟩
    _ = ∑ y ∈ VD, fibreSum (slotWord r) VX φ y * fibreSum (slotWord r) VY φ (Φ y) := by
        rw [Finset.sum_product, Finset.sum_product]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [fibreSum, fibreSum, Finset.sum_mul_sum]
    _ ≤ S₂ ^ #TD * S₁ ^ (#TX + #TY) := by
        have := sum_fibreSum_mul_fibreSum_le (slotWord_injective hr) hC hC' hJ hJ' hΦ hΦinj hφ hφ
        rwa [hJ₁, hJ₁'] at this
    _ = ∏ j ∈ T, lineWeight S₁ S₂ (D j) := by
        rw [prod_lineWeight, pow_add, mul_assoc]

end HybridRow

section HybridMasks

variable {n k ℓ : ℕ}

open Classical in
/-- The weight of a slot annihilator `D` in the hybrid fixed-mask bound: `0` for `D = 0`, else
`lineWeight D ^ k` (one factor per row). -/
noncomputable def hybridSlotWeight (S₁ S₂ : ℝ) (k : ℕ) (D : Submodule F (F × F)) : ℝ :=
  if D = ⊥ then 0 else lineWeight S₁ S₂ D ^ k

open Classical in
/-- Fixed masks, hybrid form: for given masks the support-`T` part of the second moment is at
most `∏_{j ∈ T} hybridSlotWeight D_j`. Every row of an admissible mode supported in `T` lies in
`∏_{j ∈ T} D_j`, and each row's kernel mass there is at most `∏_{j ∈ T} lineWeight D_j`
(`rowSum_le_prod_lineWeight`). -/
theorem supportMoment_le_hybrid {r : Fin n → F} (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0)
    {κ : Fin k → Fin n → F × F → ℝ} {φ : Fin k → Fin n → F → ℝ} {S₁ S₂ : ℝ}
    (hκ0 : ∀ i c u, 0 ≤ κ i c u) (hκφ : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2)
    (hφ : ∀ i, WeightBounds (φ i) S₁ S₂) (s x x' : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    supportMoment r κ s x x' T ≤ ∏ j ∈ T, hybridSlotWeight S₁ S₂ k (slotAnnihilators s x x' j) := by
  set D := slotAnnihilators s x x'
  by_cases hD : ∃ j ∈ T, D j = ⊥
  · -- no mode has support `T`, and the bound has a zero factor
    obtain ⟨j, hj, hj0⟩ := hD
    have hempty : (univ : Finset (Fin k → Fin n → F × F)).filter
        (fun μ => Admissible s x x' μ ∧ modeSupport μ = T) = ∅ := by
      refine Finset.filter_false_of_mem fun μ _ ⟨hadm, hsupp⟩ => ?_
      rw [← hsupp, modeSupport, Finset.mem_filter] at hj
      obtain ⟨i, hi⟩ := hj.2
      have := hadm i j
      change μ i j ∈ D j at this
      rw [hj0, Submodule.mem_bot] at this
      exact hi this
    rw [supportMoment, hempty, Finset.sum_empty]
    exact le_of_eq (Finset.prod_eq_zero hj (by simp [hybridSlotWeight, hj0])).symm
  push Not at hD
  set R : Submodule F (Fin n → F × F) :=
    Submodule.pi Set.univ fun j => if j ∈ T then D j else ⊥
  have hsub : univ.filter (fun μ => Admissible s x x' μ ∧ modeSupport μ = T) ⊆
      Fintype.piFinset fun _ : Fin k => univ.filter (· ∈ R) := by
    intro μ hμ
    obtain ⟨hadm, hsupp⟩ := (Finset.mem_filter.mp hμ).2
    rw [Fintype.mem_piFinset]
    intro i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j _ => ?_⟩
    show μ i j ∈ (if j ∈ T then D j else ⊥)
    split_ifs with hj
    · exact hadm i j
    · rw [Submodule.mem_bot]
      by_contra hne
      exact hj (hsupp ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hne⟩)
  have hw0 : ∀ μ, 0 ≤ modeWeight r κ μ := fun μ =>
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun c _ => hκ0 i c _
  calc supportMoment r κ s x x' T
      ≤ ∑ μ ∈ Fintype.piFinset (fun _ : Fin k => univ.filter (· ∈ R)), modeWeight r κ μ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun μ _ _ => hw0 μ
    _ = ∏ i, ∑ ν ∈ univ.filter (· ∈ R), ∏ c, κ i c (coeffOfSlots r ν c) := by
        rw [Finset.prod_univ_sum (fun _ : Fin k => univ.filter (· ∈ R))
          (fun i ν => ∏ c, κ i c (coeffOfSlots r ν c))]
        rfl
    _ ≤ ∏ _i : Fin k, ∏ j ∈ T, lineWeight S₁ S₂ (D j) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun ν _ =>
          Finset.prod_nonneg fun c _ => hκ0 i c _) fun i _ =>
            rowSum_le_prod_lineWeight hr hr0 (hκ0 i) (hκφ i) (hφ i) D T hD
    _ = ∏ j ∈ T, hybridSlotWeight S₁ S₂ k (D j) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun j hj => by rw [hybridSlotWeight, if_neg (hD j hj)]

/-- The first-stage subspace of hybrid slot event `τ` (a condition on `x̂`): `span ŝ₁` for the
`ξ`-line (`0`) and the full slot (`3`), everything otherwise. -/
def hybridFirst (τ : Fin 4) (s : Fin ℓ → F) : Submodule F (Fin ℓ → F) :=
  if τ = 0 ∨ τ = 3 then Submodule.span F {s} else ⊤

/-- The second-stage subspace of hybrid slot event `τ` (a condition on `x̂'` given `x̂`):
everything for the `ξ`-line (`0`), `span (x̂, ŝ₁)` for the diagonal (`2`), `span ŝ₁` for the
`η`-line (`1`) and the full slot (`3`). -/
def hybridSecond (τ : Fin 4) (s x : Fin ℓ → F) : Submodule F (Fin ℓ → F) :=
  if τ = 0 then ⊤ else if τ = 2 then Submodule.span F {x, s} else Submodule.span F {s}

/-- The weights of the hybrid slot events: `S₁^k` (`ξ`-line), `S₁^k` (`η`-line), `S₂^k`
(diagonal), `S₁^{2k}` (full). -/
def hybridEventWeight (S₁ S₂ : ℝ) (k : ℕ) : Fin 4 → ℝ := ![S₁ ^ k, S₁ ^ k, S₂ ^ k, (S₁ ^ k) ^ 2]

/-- Dimension bounds of the first-stage subspaces. -/
def hybridFirstDim (ℓ : ℕ) : Fin 4 → ℕ := ![1, ℓ, ℓ, 1]

/-- Dimension bounds of the second-stage subspaces. -/
def hybridSecondDim (ℓ : ℕ) : Fin 4 → ℕ := ![ℓ, 1, 2, 1]

theorem finrank_hybridFirst_le (τ : Fin 4) (s : Fin ℓ → F) :
    Module.finrank F (hybridFirst τ s) ≤ hybridFirstDim ℓ τ := by
  fin_cases τ <;> simp only [hybridFirst, hybridFirstDim] <;> simp <;>
    first
    | exact finrank_span_singleton_le_one s
    | exact (finrank_top F (Fin ℓ → F)).trans (Module.finrank_fin_fun F) |>.le

theorem finrank_hybridSecond_le (τ : Fin 4) (s x : Fin ℓ → F) :
    Module.finrank F (hybridSecond τ s x) ≤ hybridSecondDim ℓ τ := by
  fin_cases τ <;> simp only [hybridSecond, hybridSecondDim] <;> simp <;>
    first
    | exact finrank_span_singleton_le_one s
    | exact finrank_span_pair_le_two x s
    | exact (finrank_top F (Fin ℓ → F)).trans (Module.finrank_fin_fun F) |>.le

open Classical in
/-- A nonzero slot annihilator forces a hybrid slot event of the same weight: hence
`hybridSlotWeight D ≤ ∑_τ hybridEventWeight τ · 1[x̂ ∈ first τ ∧ x̂' ∈ second τ]`. -/
theorem hybridSlotWeight_le_sum {S₁ S₂ : ℝ} (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (k : ℕ)
    (s x x' : Fin ℓ → F) :
    hybridSlotWeight S₁ S₂ k (slotAnnihilator s x x') ≤
      ∑ τ, hybridEventWeight S₁ S₂ k τ *
        if x ∈ hybridFirst τ s ∧ x' ∈ hybridSecond τ s x then 1 else 0 := by
  set D := slotAnnihilator s x x'
  have hw : ∀ τ, 0 ≤ hybridEventWeight S₁ S₂ k τ *
      if x ∈ hybridFirst τ s ∧ x' ∈ hybridSecond τ s x then 1 else 0 := by
    intro τ
    refine mul_nonneg ?_ (by split_ifs <;> norm_num)
    fin_cases τ <;> simp [hybridEventWeight] <;> positivity
  -- one event `τ` holds and carries the weight
  have hone : ∀ τ, x ∈ hybridFirst τ s → x' ∈ hybridSecond τ s x →
      lineWeight S₁ S₂ D ^ k ≤ hybridEventWeight S₁ S₂ k τ →
      lineWeight S₁ S₂ D ^ k ≤ ∑ τ, hybridEventWeight S₁ S₂ k τ *
        if x ∈ hybridFirst τ s ∧ x' ∈ hybridSecond τ s x then 1 else 0 := by
    intro τ h1 h2 hle
    refine le_trans ?_ (Finset.single_le_sum (fun τ _ => hw τ) (Finset.mem_univ τ))
    rw [if_pos ⟨h1, h2⟩, mul_one]
    exact hle
  unfold hybridSlotWeight
  split_ifs with hD
  · exact Finset.sum_nonneg fun τ _ => hw τ
  have hxs : ((1 : F), (0 : F)) ∈ D → x ∈ Submodule.span F {s} := fun h => by
    simpa [D, mem_slotAnnihilator] using h
  have hx's : ((0 : F), (1 : F)) ∈ D → x' ∈ Submodule.span F {s} := fun h => by
    have := Submodule.neg_mem _ (show (0 : F) • x - (1 : F) • x' ∈ Submodule.span F {s} from h)
    simpa using this
  by_cases hx : ((1 : F), (0 : F)) ∈ D <;> by_cases hy : ((0 : F), (1 : F)) ∈ D
  · refine hone 3 ?_ ?_ (le_of_eq ?_)
    · simpa [hybridFirst] using hxs hx
    · simpa [hybridSecond] using hx's hy
    · simp [lineWeight, hx, hy, hybridEventWeight, ← pow_mul, ← sq]
      ring
  · refine hone 0 ?_ ?_ (le_of_eq ?_)
    · simpa [hybridFirst] using hxs hx
    · simp [hybridSecond]
    · simp [lineWeight, hx, hy, hybridEventWeight]
  · refine hone 1 ?_ ?_ (le_of_eq ?_)
    · simp [hybridFirst]
    · simpa [hybridSecond] using hx's hy
    · simp [lineWeight, hx, hy, hybridEventWeight]
  · refine hone 2 ?_ ?_ (le_of_eq ?_)
    · simp [hybridFirst]
    · obtain ⟨p, hp, hb⟩ := exists_mem_snd_ne_zero hD hx
      have hp0 : p ≠ 0 := fun h => hb (by simp [h])
      have hmem := (mem_span_of_slotPairing hp0 hp).2 hb
      have hsub : Submodule.span F {s} ≤ Submodule.span F {x, s} :=
        Submodule.span_mono (by simp)
      have hxm : x ∈ Submodule.span F {x, s} := Submodule.subset_span (by simp)
      have := Submodule.add_mem _ (hsub hmem) (Submodule.smul_mem _ (p.2⁻¹ * p.1) hxm)
      simpa [hybridSecond] using this
    · simp [lineWeight, hx, hy, hybridEventWeight]

end HybridMasks

section HybridAverage

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n k ℓ : ℕ}

open Classical in
/-- Two-stage box counting: at most `#B² (∏_j u₁ j) (∏_j u₂ j)` pairs of box masks have
`x̂ ∈ ∏_j L₁ j` and `x̂' ∈ ∏_j L₂ x̂ j`, when the box factors are bounded by `u₁`, `u₂`. -/
theorem card_twoStage_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F) {G : ℕ}
    (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (w₀ : Fin n → Fin ℓ → F)
    (L₁ : Fin n → Submodule F (Fin ℓ → F))
    (L₂ : (Fin n → Fin ℓ → F) → Fin n → Submodule F (Fin ℓ → F)) {u₁ u₂ : Fin n → ℝ}
    (hb₁ : ∀ j, boxFactor G (L₁ j) ≤ u₁ j) (hb₂ : ∀ x j, boxFactor G (L₂ x j) ≤ u₂ j) :
    (#((Fintype.piFinset S ×ˢ Fintype.piFinset S).filter fun q =>
        E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
          E q.2 - w₀ ∈ Submodule.pi Set.univ (L₂ (E q.1 - w₀))) : ℝ) ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * ((∏ j, u₁ j) * ∏ j, u₂ j) := by
  set B := Fintype.piFinset S
  have hu₂ : 0 ≤ ∏ j, u₂ j := Finset.prod_nonneg fun j _ =>
    (boxFactor_nonneg G (L₂ 0 j)).trans (hb₂ 0 j)
  have hcount := card_filter_product_le B (fun z => E z - w₀ ∈ Submodule.pi Set.univ L₁)
    (fun z z' => E z' - w₀ ∈ Submodule.pi Set.univ (L₂ (E z - w₀)))
    (c₁ := #B * ∏ j, u₁ j) (c₂ := #B * ∏ j, u₂ j)
    (mul_nonneg (Nat.cast_nonneg _) hu₂)
    ((card_box_pi_le E S hG hS L₁ w₀).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => boxFactor_nonneg _ _) fun j _ => hb₁ j)
      (Nat.cast_nonneg _)))
    (fun z => (card_box_pi_le E S hG hS _ w₀).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => boxFactor_nonneg _ _) fun j _ => hb₂ _ j)
      (Nat.cast_nonneg _)))
  refine hcount.trans (le_of_eq ?_)
  ring

/-- The box factor bound `G^{d₁ τ} / G^ℓ · G^{d₂ τ} / G^ℓ` of hybrid slot event `τ`. -/
noncomputable def hybridEventFactor (G ℓ : ℕ) (τ : Fin 4) : ℝ :=
  (G : ℝ) ^ hybridFirstDim ℓ τ / (G : ℝ) ^ ℓ * ((G : ℝ) ^ hybridSecondDim ℓ τ / (G : ℝ) ^ ℓ)

open Classical in
/-- Two-stage averaging of a hybrid slot-event pattern `σ` on `T`: at most
`#B² ∏_{j ∈ T} hybridEventFactor (σ j)` pairs of box masks realize it. -/
theorem card_hybridEvents_le (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F)) (S : ι → Finset F)
    {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) (s w₀ : Fin n → Fin ℓ → F)
    (T : Finset (Fin n)) (σ : T → Fin 4) :
    (#((Fintype.piFinset S ×ˢ Fintype.piFinset S).filter fun q =>
        ∀ j : T, (E q.1 - w₀) j ∈ hybridFirst (σ j) (s j) ∧
          (E q.2 - w₀) j ∈ hybridSecond (σ j) (s j) ((E q.1 - w₀) j)) : ℝ) ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * ∏ j : T, hybridEventFactor G ℓ (σ j) := by
  set B := Fintype.piFinset S
  let L₁ : Fin n → Submodule F (Fin ℓ → F) := fun j =>
    if h : j ∈ T then hybridFirst (σ ⟨j, h⟩) (s j) else ⊤
  let L₂ : (Fin n → Fin ℓ → F) → Fin n → Submodule F (Fin ℓ → F) := fun x j =>
    if h : j ∈ T then hybridSecond (σ ⟨j, h⟩) (s j) (x j) else ⊤
  let u₁ : Fin n → ℝ := fun j =>
    if h : j ∈ T then (G : ℝ) ^ hybridFirstDim ℓ (σ ⟨j, h⟩) / (G : ℝ) ^ ℓ else 1
  let u₂ : Fin n → ℝ := fun j =>
    if h : j ∈ T then (G : ℝ) ^ hybridSecondDim ℓ (σ ⟨j, h⟩) / (G : ℝ) ^ ℓ else 1
  have hb₁ : ∀ j, boxFactor G (L₁ j) ≤ u₁ j := by
    intro j
    simp only [L₁, u₁]
    split_ifs with h
    · exact boxFactor_le hG (finrank_hybridFirst_le _ _)
    · rw [boxFactor_top G hG]
  have hb₂ : ∀ x j, boxFactor G (L₂ x j) ≤ u₂ j := by
    intro x j
    simp only [L₂, u₂]
    split_ifs with h
    · exact boxFactor_le hG (finrank_hybridSecond_le _ _ _)
    · rw [boxFactor_top G hG]
  have hsub : (B ×ˢ B).filter (fun q =>
        ∀ j : T, (E q.1 - w₀) j ∈ hybridFirst (σ j) (s j) ∧
          (E q.2 - w₀) j ∈ hybridSecond (σ j) (s j) ((E q.1 - w₀) j)) ⊆
      (B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
        E q.2 - w₀ ∈ Submodule.pi Set.univ (L₂ (E q.1 - w₀))) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, fun j _ => ?_, fun j _ => ?_⟩
    · show (E q.1 - w₀) j ∈ L₁ j
      simp only [L₁]
      split_ifs with hj
      · exact (hq.2 ⟨j, hj⟩).1
      · exact Submodule.mem_top
    · show (E q.2 - w₀) j ∈ L₂ (E q.1 - w₀) j
      simp only [L₂]
      split_ifs with hj
      · exact (hq.2 ⟨j, hj⟩).2
      · exact Submodule.mem_top
  have hprod : (∏ j, u₁ j) * ∏ j, u₂ j = ∏ j : T, hybridEventFactor G ℓ (σ j) := by
    rw [← Finset.prod_mul_distrib, ← prod_dite_mem_eq T]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [u₁, u₂, hybridEventFactor]
    split_ifs <;> simp
  calc (#((B ×ˢ B).filter fun q =>
        ∀ j : T, (E q.1 - w₀) j ∈ hybridFirst (σ j) (s j) ∧
          (E q.2 - w₀) j ∈ hybridSecond (σ j) (s j) ((E q.1 - w₀) j)) : ℝ)
      ≤ #((B ×ˢ B).filter (fun q => E q.1 - w₀ ∈ Submodule.pi Set.univ L₁ ∧
          E q.2 - w₀ ∈ Submodule.pi Set.univ (L₂ (E q.1 - w₀)))) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ #B * #B * ((∏ j, u₁ j) * ∏ j, u₂ j) := card_twoStage_le E S hG hS w₀ L₁ L₂ hb₁ hb₂
    _ = #B * #B * ∏ j : T, hybridEventFactor G ℓ (σ j) := by rw [hprod]

/-- The per-slot factor of the hybrid route:
`∑_τ hybridEventWeight τ · hybridEventFactor τ`, that is
`2 G^{-(ℓ-1)} S₁^k + G^{-(ℓ-2)} S₂^k + G^{-2(ℓ-1)} S₁^{2k}` (`hybridFactor_eq`). -/
noncomputable def hybridFactor (S₁ S₂ : ℝ) (k G ℓ : ℕ) : ℝ :=
  ∑ τ, hybridEventWeight S₁ S₂ k τ * hybridEventFactor G ℓ τ

/-- The hybrid factor in closed form. -/
theorem hybridFactor_eq (S₁ S₂ : ℝ) (k : ℕ) {G : ℕ} (hG : 1 ≤ G) (ℓ : ℕ) :
    hybridFactor S₁ S₂ k G ℓ = 2 * S₁ ^ k * ((G : ℝ) / (G : ℝ) ^ ℓ) +
      S₂ ^ k * ((G : ℝ) ^ 2 / (G : ℝ) ^ ℓ) +
      (S₁ ^ k) ^ 2 * (((G : ℝ) / (G : ℝ) ^ ℓ) * ((G : ℝ) / (G : ℝ) ^ ℓ)) := by
  have hGℓ : (G : ℝ) ^ ℓ / (G : ℝ) ^ ℓ = 1 := div_self (by positivity)
  simp only [hybridFactor, Fin.sum_univ_four, hybridEventWeight, hybridEventFactor,
    hybridFirstDim, hybridSecondDim]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, pow_one, hGℓ, mul_one, one_mul]
  ring

open Classical in
/-- **Fixed masks, hybrid form, averaged over two masks from a box**: the support-`T` part of
the second moment, summed over the box pairs, is at most `#B² · Y ^ #T` with
`Y = hybridFactor S₁ S₂ k G ℓ`. -/
theorem sum_supportMoment_le_hybrid (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F}
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) {κ : Fin k → Fin n → F × F → ℝ}
    {φ : Fin k → Fin n → F → ℝ} {S₁ S₂ : ℝ} (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hκ0 : ∀ i c u, 0 ≤ κ i c u) (hκφ : ∀ i c u, κ i c u ≤ φ i c u.1 * φ i c u.2)
    (hφ : ∀ i, WeightBounds (φ i) S₁ S₂) (s w₀ : Fin n → Fin ℓ → F) (T : Finset (Fin n)) :
    ∑ q ∈ Fintype.piFinset S ×ˢ Fintype.piFinset S,
        supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      #(Fintype.piFinset S) * #(Fintype.piFinset S) * hybridFactor S₁ S₂ k G ℓ ^ #T := by
  set B := Fintype.piFinset S
  set w := hybridEventWeight S₁ S₂ k
  set ev : T → Fin 4 → (ι → F) × (ι → F) → Prop := fun j τ q =>
    (E q.1 - w₀) j ∈ hybridFirst τ (s j) ∧
      (E q.2 - w₀) j ∈ hybridSecond τ (s j) ((E q.1 - w₀) j)
  have hw0 : ∀ τ, 0 ≤ w τ := by
    intro τ
    fin_cases τ <;> simp [w, hybridEventWeight] <;> positivity
  have hsw0 : ∀ D : Submodule F (F × F), 0 ≤ hybridSlotWeight S₁ S₂ k D := by
    intro D
    unfold hybridSlotWeight lineWeight
    split_ifs <;> positivity
  have step1 : ∀ q : (ι → F) × (ι → F), supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T ≤
      ∑ σ : T → Fin 4, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 := by
    intro q
    refine (supportMoment_le_hybrid hr hr0 hκ0 hκφ hφ s _ _ T).trans ?_
    calc ∏ j ∈ T, hybridSlotWeight S₁ S₂ k (slotAnnihilators s (E q.1 - w₀) (E q.2 - w₀) j)
        = ∏ j : T, hybridSlotWeight S₁ S₂ k
            (slotAnnihilator (s j) ((E q.1 - w₀) j) ((E q.2 - w₀) j)) :=
          (Finset.prod_coe_sort T _).symm
      _ ≤ ∏ j : T, ∑ τ, w τ * if ev j τ q then 1 else 0 :=
          Finset.prod_le_prod₀ (fun j _ => hsw0 _)
            fun j _ => hybridSlotWeight_le_sum hS₁ hS₂ k _ _ _
      _ = ∑ σ : T → Fin 4, ∏ j, (w (σ j) * if ev j (σ j) q then 1 else 0) :=
          Fintype.prod_sum _
      _ = ∑ σ : T → Fin 4, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_boole]
          simp
  calc ∑ q ∈ B ×ˢ B, supportMoment r κ s (E q.1 - w₀) (E q.2 - w₀) T
      ≤ ∑ q ∈ B ×ˢ B, ∑ σ : T → Fin 4, (∏ j, w (σ j)) * if ∀ j, ev j (σ j) q then 1 else 0 :=
        Finset.sum_le_sum fun q _ => step1 q
    _ = ∑ σ : T → Fin 4, (∏ j, w (σ j)) * #((B ×ˢ B).filter fun q => ∀ j, ev j (σ j) q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ ∑ σ : T → Fin 4, (∏ j, w (σ j)) *
          (#B * #B * ∏ j : T, hybridEventFactor G ℓ (σ j)) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
          (card_hybridEvents_le E S hG hS s w₀ T σ) (Finset.prod_nonneg fun j _ => hw0 _)
    _ = #B * #B * ∏ _j : T, hybridFactor S₁ S₂ k G ℓ := by
        rw [hybridFactor, Finset.prod_univ_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [Finset.prod_mul_distrib, w]
        ring
    _ = #B * #B * hybridFactor S₁ S₂ k G ℓ ^ #T := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

open Classical in
/-- **The averaged second moment with the hybrid large-support term.** Under the hypotheses of
`averagedSecondMoment_le` and `∑_u φ i c u ^ 2 ≤ S₂` with `0 ≤ S₂` (Parseval for the single-coefficient
weights), each support size `t` takes the smaller of `supportTerm t` and the hybrid term
`Y ^ t`, `Y = hybridFactor S₁ S₂ k G ℓ`:
`averagedSecondMoment ≤ ∑_{t = 1}^n C(n, t) · min (supportTerm t) (Y ^ t)`. -/
theorem averagedSecondMoment_le_hybrid (E : (ι → F) ≃ₗ[F] (Fin n → Fin ℓ → F))
    (S : ι → Finset F) {G : ℕ} (hG : 1 ≤ G) (hS : ∀ i, #(S i) = G) {r : Fin n → F}
    (hr : Function.Injective r) (hr0 : ∀ j, r j ≠ 0) {κ : Fin k → Fin n → F × F → ℝ}
    {φ : Fin k → Fin n → F → ℝ} {f : F → ℝ} {S₁ T₂ : ℝ} (hκ : KernelBounds κ φ f S₁ T₂)
    {S₂ : ℝ} (hS₂0 : 0 ≤ S₂) (hS₂ : ∀ i c, ∑ u, φ i c u ^ 2 ≤ S₂) {m : ℕ} {δ : ℕ → ℝ}
    (hδ : SmallSupportBounds r f m δ) (s w₀ : Fin n → Fin ℓ → F) :
    averagedSecondMoment E S r κ s w₀ ≤
      ∑ t ∈ range (n + 1), (n.choose t : ℝ) * (if t = 0 then 0 else
        min (supportTerm n k ℓ G m δ S₁ T₂ t) (hybridFactor S₁ S₂ k G ℓ ^ t)) := by
  have hφ : ∀ i, WeightBounds (φ i) S₁ S₂ := fun i =>
    ⟨hκ.weight_nonneg i, hκ.weight_le_one i, hκ.weight_sum_le i, hS₂ i⟩
  have hS₁0 : 0 ≤ S₁ := zero_le_one.trans hκ.one_le_mass
  refine averagedSecondMoment_le_of_sum_supportMoment_le E S hG hS r κ s w₀ fun T hT0 => ?_
  have hB : (0 : ℝ) ≤ #(Fintype.piFinset S) * #(Fintype.piFinset S) := by positivity
  rw [mul_min_of_nonneg _ _ hB]
  exact le_min (sum_supportMoment_le_supportTerm E S hG hS hr hr0 hκ hδ s w₀ hT0)
    (sum_supportMoment_le_hybrid E S hG hS hr hr0 hS₁0 hS₂0 hκ.kernel_nonneg hκ.kernel_le_mul hφ
      s w₀ T)

end HybridAverage

section Envelope

theorem fixedMaskFactor_zero {k : ℕ} (hk : k ≠ 0) (G ℓ : ℕ) : fixedMaskFactor 0 k G ℓ = 0 := by
  rw [fixedMaskFactor_eq]
  simp [zero_pow hk]

/-- The three-block closure of `∑_t C(256, t) · min (supportTerm t) (Y ^ t)` for small supports
up to `4`: the small and medium blocks as in `sum_supportTerm_le` (they do not involve `S₁`), and
the large block `t ≥ 129` from the hybrid term, `∑_{t ≥ 129} C(256, t) Y^t ≤ 2^256 Y^129`. -/
theorem sum_min_supportTerm_le {k ℓ G : ℕ} (hk : k ≠ 0) {δ : ℕ → ℝ} {S₁ T₂ Y : ℝ}
    (hT₂ : 0 ≤ T₂) (ha : 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k < 1) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 1) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm 256 k ℓ G 4 δ S₁ T₂ t) (Y ^ t)) ≤
      ∑ t ∈ range 5, ((256 : ℕ).choose t : ℝ) *
          (if t = 0 then 0 else ((G : ℝ) / (G : ℝ) ^ ℓ) ^ t * ((1 + δ t) ^ (2 * k) - 1)) +
        (256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k) ^ 5 /
          (120 * (1 - 256 * ((G : ℝ) / (G : ℝ) ^ ℓ) * T₂ ^ k)) +
        2 ^ 256 * Y ^ 129 := by
  have hX0 : fixedMaskFactor 0 k G ℓ = 0 := fixedMaskFactor_zero hk G ℓ
  have hsplit : ∀ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
      (if t = 0 then 0 else min (supportTerm 256 k ℓ G 4 δ S₁ T₂ t) (Y ^ t)) ≤
      ((256 : ℕ).choose t : ℝ) * (if t = 0 then 0 else supportTerm 256 k ℓ G 4 δ 0 T₂ t) +
        ((256 : ℕ).choose t : ℝ) * (if 128 < t then Y ^ t else 0) := by
    intro t _
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    split_ifs with h0 hbig
    · omega
    · simp
    · refine (min_le_right _ _).trans (le_of_eq ?_)
      simp only [supportTerm, if_neg (show ¬ t ≤ 4 by omega),
        if_neg (show ¬ t + t ≤ 256 by omega), hX0, zero_pow h0, zero_add]
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      simp only [supportTerm, add_zero]
      split_ifs <;> first | rfl | omega
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 := sum_supportTerm_le (δ := δ) (le_refl (0 : ℝ)) hT₂ ha (by rw [hX0]; exact zero_le_one)
  rw [hX0, zero_pow (by norm_num), mul_zero, add_zero] at h1
  have h2 : ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) * (if 128 < t then Y ^ t else 0) ≤
      2 ^ 256 * Y ^ 129 := by
    calc _ ≤ ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) * Y ^ 129 := by
          refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          split_ifs with h
          · exact pow_le_pow_of_le_one hY0 hY (by omega)
          · positivity
      _ = 2 ^ 256 * Y ^ 129 := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose 256
  linarith

/-- The hybrid factor at ML-DSA-44 (`k = ℓ = 4`, `G = 261987`) for `S₁ ≤ 1620` and
`S₂ ≤ q / 190307`: `Y ≤ 2^-10`. -/
theorem hybridFactor_mldsa44_le {S₁ S₂ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 1620) (hS₂0 : 0 ≤ S₂)
    (hS₂ : S₂ ≤ 8380417 / 190307) : hybridFactor S₁ S₂ 4 261987 4 ≤ 1 / 2 ^ 10 := by
  rw [hybridFactor_eq _ _ _ (by norm_num)]
  calc _ ≤ 2 * 1620 ^ 4 * (((261987 : ℕ) : ℝ) / ((261987 : ℕ) : ℝ) ^ 4) +
        (8380417 / 190307) ^ 4 * (((261987 : ℕ) : ℝ) ^ 2 / ((261987 : ℕ) : ℝ) ^ 4) +
        ((1620 : ℝ) ^ 4) ^ 2 * ((((261987 : ℕ) : ℝ) / ((261987 : ℕ) : ℝ) ^ 4) *
          (((261987 : ℕ) : ℝ) / ((261987 : ℕ) : ℝ) ^ 4)) := by
        gcongr
    _ ≤ 1 / 2 ^ 10 := by norm_num

/-- **The ML-DSA-44 envelope.** With `k = ℓ = 4`, `L = 190307`, `G = 261987`,
`T₂ = q² / (44 L²)`, the small-support bounds `δ₁ ≤ 2^-512, δ₂ ≤ 2^-210, δ₃ ≤ 2^-155,
δ₄ ≤ 2^-52`, `S₁ ≤ 1620` (`sum_le_1620`) and `S₂ ≤ q / L`:
`∑_t C(256, t) · min (supportTerm t) (hybridFactor ^ t) ≤ 2^-127`. The two-window term at
`t = 5` dominates (`2^-127.66`); the hybrid term closes every `t ≥ 129` (`Y ≤ 2^-10`). -/
theorem envelope_mldsa44 {δ : ℕ → ℝ} (hδ0 : ∀ t, 0 ≤ δ t) (hδ1 : δ 1 ≤ 1 / 2 ^ 512)
    (hδ2 : δ 2 ≤ 1 / 2 ^ 210) (hδ3 : δ 3 ≤ 1 / 2 ^ 155) (hδ4 : δ 4 ≤ 1 / 2 ^ 52) {S₁ S₂ : ℝ}
    (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ 1620) (hS₂0 : 0 ≤ S₂) (hS₂ : S₂ ≤ 8380417 / 190307) :
    ∑ t ∈ range (256 + 1), ((256 : ℕ).choose t : ℝ) *
        (if t = 0 then 0 else min (supportTerm 256 4 4 261987 4 δ S₁
          (8380417 ^ 2 / (44 * 190307 ^ 2)) t) (hybridFactor S₁ S₂ 4 261987 4 ^ t)) ≤
      1 / 2 ^ 127 := by
  have hY := hybridFactor_mldsa44_le hS₁0 hS₁ hS₂0 hS₂
  have hY0 : 0 ≤ hybridFactor S₁ S₂ 4 261987 4 := by
    rw [hybridFactor_eq _ _ _ (show 1 ≤ 261987 by norm_num)]
    positivity
  set Y := hybridFactor S₁ S₂ 4 261987 4
  refine (sum_min_supportTerm_le (by norm_num) (by positivity) (by norm_num) hY0
    (hY.trans (by norm_num))).trans ?_
  -- the large block: `2^256 Y^129 ≤ (4 Y)^128 ≤ (4 Y)^32 ≤ 2^-256`
  have h4 : 4 * Y ≤ 1 / 256 := by linarith
  have h40 : 0 ≤ 4 * Y := by positivity
  have hlarge : 2 ^ 256 * Y ^ 129 ≤ (1 / 256) ^ 32 := by
    calc 2 ^ 256 * Y ^ 129 ≤ 2 ^ 256 * Y ^ 128 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hY0 (hY.trans (by norm_num))
            (by norm_num)) (by positivity)
      _ = (4 * Y) ^ 128 := by rw [mul_pow]; norm_num
      _ ≤ (4 * Y) ^ 32 := pow_le_pow_of_le_one h40 (h4.trans (by norm_num)) (by norm_num)
      _ ≤ (1 / 256) ^ 32 := pow_le_pow_left₀ h40 h4 _
  rw [sum_range_five_smallTerms]
  have e1 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 1) hδ1
    (by rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]; norm_num)
  have e2 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 2) hδ2 (by norm_num)
  have e3 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 3) hδ3 (by norm_num)
  have e4 := one_add_pow_sub_one_le_of_le (N := 2 * 4) (hδ0 4) hδ4 (by norm_num)
  set g : ℝ := ((261987 : ℕ) : ℝ) / (261987 : ℝ) ^ 4
  have hg : 0 ≤ g := by positivity
  have hnum : 256 * (g ^ 1 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 512))) +
      32640 * (g ^ 2 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 210))) +
      2763520 * (g ^ 3 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 155))) +
      174792640 * (g ^ 4 * (2 * (2 * 4 : ℕ) * (1 / 2 ^ 52))) +
      (256 * g * (8380417 ^ 2 / (44 * 190307 ^ 2)) ^ 4) ^ 5 /
        (120 * (1 - 256 * g * (8380417 ^ 2 / (44 * 190307 ^ 2)) ^ 4)) +
      (1 / 256) ^ 32 ≤ 1 / 2 ^ 127 := by
    rw [show (2 : ℝ) ^ 512 = (2 ^ 256) ^ 2 by rw [← pow_mul]]
    simp only [g]
    norm_num
  have hpow : ∀ t, 0 ≤ g ^ t := fun t => pow_nonneg hg t
  nlinarith [mul_le_mul_of_nonneg_left e1 (hpow 1), mul_le_mul_of_nonneg_left e2 (hpow 2),
    mul_le_mul_of_nonneg_left e3 (hpow 3), mul_le_mul_of_nonneg_left e4 (hpow 4)]

end Envelope

end GordieHowe.MLDSA.Regularity
