-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.SecondMoment
public import GordieHowe.Applications.MLDSA.Regularity.SmallSupport

@[expose] public section

/-!
# From the spectral support sums to `SmallSupportBounds`

`SmallSupportBounds r f m δ` (`SecondMoment.lean`) sums over the nonzero words of a slot support
`T ⊆ Fin n`, parametrized by amplitudes `λ : T → F` through the slot roots `r`; the spectral
recursion (`SmallSupport.lean`) sums over amplitudes `l : K → K` supported on a set of roots
`T' ⊆ K`. For injective `r` the two agree on `T' = T.image r`
(`sum_powerCode_le_spectralSum`), so the uniform bounds `δ₁ ≤ 2^-617, …, δ₄ ≤ 2^-52` of the
recursion give `SmallSupportBounds r f 4 smallSupportDelta` for any `n = 256` distinct roots of
`X^256 + 1` in `ZMod q` (`smallSupportBounds_of_isKernelBound`). At cell size at least `523383`
(ML-DSA-65 and ML-DSA-87) the recursion with the Hadamard form gives
`SmallSupportBounds r f 5 cellSupportDelta` with `δ₁ ≤ 2^-512, δ₂ ≤ 2^-358, δ₃ ≤ 2^-214,
δ₄ ≤ 2^-99, δ₅ ≤ 2^-7` (`smallSupportBounds_five_of_isKernelBound`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

/-- The amplitude vector on `K` of slot amplitudes `λ : T → K`: `l ρ = ∑_{j ∈ T, r j = ρ} λ j`. -/
def amplitudeOfSlots (r : Fin n → K) (T : Finset (Fin n)) (lam : T → K) : K → K :=
  fun ρ => ∑ j : T, if r j = ρ then lam j else 0

omit [Fintype K] in
theorem amplitudeOfSlots_apply_root {r : Fin n → K} (hr : Function.Injective r)
    (T : Finset (Fin n)) (lam : T → K) (j : T) : amplitudeOfSlots r T lam (r j) = lam j := by
  unfold amplitudeOfSlots
  rw [Finset.sum_eq_single j (fun j' _ hj' => if_neg fun h => hj' (Subtype.ext (hr h)))
    (fun h => absurd (Finset.mem_univ j) h), if_pos rfl]

theorem word_amplitudeOfSlots (r : Fin n → K) (T : Finset (Fin n)) (lam : T → K) (b : ℕ) :
    word (amplitudeOfSlots r T lam) b = ∑ j : T, lam j * r j ^ b := by
  unfold word amplitudeOfSlots
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- The power-code sum is at most the spectral sum on the image roots. -/
theorem sum_powerCode_le_spectralSum {r : Fin n → K} (hr : Function.Injective r)
    (hr0 : ∀ j, r j ≠ 0) {f : K → ℝ} (hf0 : ∀ x, 0 ≤ f x) (T : Finset (Fin n)) :
    ∑ y ∈ (powerCode T r n).filter (· ≠ 0), ∏ c, f (y c) ≤
      spectralSum f n 1 (T.image r) := by
  have hinj := powerCodeWord_injective hr hr0 T
  have hrw : ∑ y ∈ (powerCode T r n).filter (· ≠ 0), ∏ c, f (y c) =
      ∑ lam ∈ (univ : Finset (T → K)).erase 0, ∏ c, f (powerCodeWord T r n lam c) := by
    rw [← Finset.sum_image (f := fun y : Fin n → K => ∏ c, f (y c)) fun l _ l' _ h => hinj h]
    congr 1
    ext y
    simp only [powerCode, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_erase, ne_eq]
    constructor
    · rintro ⟨⟨lam, rfl⟩, hy⟩
      refine ⟨lam, ⟨fun h => hy (by rw [h, powerCodeWord_zero]), trivial⟩, rfl⟩
    · rintro ⟨lam, ⟨hlam, -⟩, rfl⟩
      exact ⟨⟨lam, rfl⟩, fun h => hlam (hinj (h.trans (powerCodeWord_zero r T).symm))⟩
  rw [hrw, spectralSum]
  have hg : ∀ lam : T → K, ∏ c, f (powerCodeWord T r n lam c) =
      weight f n 1 (amplitudeOfSlots r T lam) := by
    intro lam
    rw [weight, ← Fin.prod_univ_eq_prod_range (fun b => f (word (amplitudeOfSlots r T lam) b) ^ 1)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_one, word_amplitudeOfSlots]
    rfl
  simp_rw [hg]
  refine sum_comp_le_sum_of_injOn (F := weight f n 1) ?_ ?_ fun l _ =>
    weight_nonneg hf0 n 1 l
  · intro lam _ lam' _ h
    funext j
    have := congrFun h (r j)
    rwa [amplitudeOfSlots_apply_root hr, amplitudeOfSlots_apply_root hr] at this
  · intro lam hlam
    rw [Finset.mem_erase] at hlam ⊢
    refine ⟨fun h => hlam.1 (funext fun j => ?_), mem_amplitudes.2 fun ρ hρ => ?_⟩
    · have := congrFun h (r j)
      rwa [amplitudeOfSlots_apply_root hr] at this
    · unfold amplitudeOfSlots at hρ
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hρ
      have : r j = ρ := by
        by_contra h
        exact hj (if_neg h)
      exact Finset.mem_image.2 ⟨j, j.2, this⟩

/-- The uniform small-support bounds of the spectral recursion, by support size. -/
noncomputable def smallSupportDelta (t : ℕ) : ℝ :=
  if t ≤ 1 then 1 / 2 ^ 617 else if t ≤ 2 then 1 / 2 ^ 210 else if t ≤ 3 then 1 / 2 ^ 155
  else 1 / 2 ^ 52

/-- **The small-support bounds at `q = 8380417`.** For distinct roots `r j` of `X^256 + 1` and a
kernel bound `f` with `C ≤ q / 190307`, `SmallSupportBounds r f 4 smallSupportDelta`. -/
theorem smallSupportBounds_of_isKernelBound {r : Fin 256 → ZMod 8380417}
    (hr : Function.Injective r) (hroot : ∀ j, r j ^ 256 = -1) {C : ℝ}
    {f : ZMod 8380417 → ℝ} (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 190307) :
    SmallSupportBounds r f 4 smallSupportDelta := by
  have hr0 : ∀ j, r j ≠ 0 := fun j h => by
    have := hroot j
    rw [h, zero_pow (by norm_num)] at this
    exact absurd this (by decide)
  refine ⟨fun T _ hT4 => (sum_powerCode_le_spectralSum hr hr0 hf.nonneg T).trans ?_⟩
  have hT' : ∀ ρ ∈ T.image r, ρ ^ 256 = -1 := by
    intro ρ hρ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hρ
    exact hroot j
  have hcard : (T.image r).card = #T := Finset.card_image_of_injective _ hr
  unfold smallSupportDelta
  split_ifs with h1 h2 h3
  · exact spectralSum_le_one_div_two_pow_617 hf hC hT' (by omega)
  · exact spectralSum_le_one_div_two_pow_210 hf hC hT' (by omega)
  · exact spectralSum_le_one_div_two_pow_155 hf hC hT' (by omega)
  · exact spectralSum_le_one_div_two_pow_52 hf hC hT' (by omega)

/-- The small-support bounds up to five roots at cell size at least `523383`. -/
noncomputable def cellSupportDelta (t : ℕ) : ℝ :=
  if t ≤ 1 then 1 / (2 ^ 256) ^ 2 else if t ≤ 2 then 1 / (2 ^ 179) ^ 2
  else if t ≤ 3 then 1 / 2 ^ 214 else if t ≤ 4 then 1 / 2 ^ 99 else 1 / 2 ^ 7

/-- **The small-support bounds up to five roots at `q = 8380417`.** For distinct roots `r j` of
`X^256 + 1` and a kernel bound `f` with `C ≤ q / 523383`,
`SmallSupportBounds r f 5 cellSupportDelta`. -/
theorem smallSupportBounds_five_of_isKernelBound {r : Fin 256 → ZMod 8380417}
    (hr : Function.Injective r) (hroot : ∀ j, r j ^ 256 = -1) {C : ℝ}
    {f : ZMod 8380417 → ℝ} (hf : IsKernelBound C f) (hC : C ≤ 8380417 / 523383) :
    SmallSupportBounds r f 5 cellSupportDelta := by
  have hr0 : ∀ j, r j ≠ 0 := fun j h => by
    have := hroot j
    rw [h, zero_pow (by norm_num)] at this
    exact absurd this (by decide)
  refine ⟨fun T _ hT5 => (sum_powerCode_le_spectralSum hr hr0 hf.nonneg T).trans ?_⟩
  have hT' : ∀ ρ ∈ T.image r, ρ ^ 256 = -1 := by
    intro ρ hρ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hρ
    exact hroot j
  have hcard : (T.image r).card = #T := Finset.card_image_of_injective _ hr
  unfold cellSupportDelta
  split_ifs with h1 h2 h3 h4
  · exact spectralSum_cell₁_le hf hC hT' (by omega)
  · exact spectralSum_cell₂_le hf hC hT' (by omega)
  · exact spectralSum_cell₃_le hf hC hT' (by omega)
  · exact spectralSum_cell₄_le hf hC hT' (by omega)
  · exact spectralSum_cell₅_le hf hC hT' (by omega)

end GordieHowe.MLDSA.Regularity
