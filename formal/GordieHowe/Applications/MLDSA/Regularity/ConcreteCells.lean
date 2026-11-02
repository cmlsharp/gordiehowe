-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.CellKernel
public import GordieHowe.Applications.MLDSA.Signing.Counting
public import GordieHowe.Applications.MLDSA.Signing.Surrogate
public import GordieHowe.Foundations.ToMathlib.CountIndicator

@[expose] public section

/-!
# The accepted cells of one coefficient and their hint-firing parts

For bucket `r1`, r0-shift `a` (`|a| ≤ β`) and ct₀-shift `b` (`|b| < γ₂`), the residues passing
the r0-check form the cell `rejectionBucket γ₂ β r1 a`, an interval of `L = 2(γ₂ - β) - 1`
residues (`rejectionBucket_eq_interval`), and the residues whose FIPS 204 hint
`MakeHint(-b, x - a + b)` fires form an initial or a final segment of it
(`hintFires_segment`). So the hint-firing part `F` and its complement `A ∖ F` are residue
intervals (`isResidueInterval_hintPart`, `isResidueInterval_sdiff_hintPart`), as the Fourier
bound `norm_fourierCoeff_cellFun_le` requires.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete

/-- The `u`-th point of the cell (`0 ≤ u < 2(γ₂ - β) - 1`): offset `a - (γ₂ - β) + 1 + u`. -/
def cellPoint (γ₂ β r1 : ℕ) (a : ℤ) (u : ℕ) : Coeff :=
  bucketPoint γ₂ r1 (a - ((γ₂ : ℤ) - β) + 1 + u)

theorem cellPoint_eq_add (γ₂ β r1 : ℕ) (a : ℤ) (u : ℕ) :
    cellPoint γ₂ β r1 a u = cellPoint γ₂ β r1 a 0 + (u : Coeff) := by
  unfold cellPoint
  rw [show ((u : ℕ) : Coeff) = (((u : ℤ)) : Coeff) by norm_cast, bucketPoint_add]
  congr 1
  push_cast
  ring

/-- The hint-firing part of a cell. -/
def hintPart (γ₂ β r1 : ℕ) (a b : ℤ) : Finset Coeff :=
  (rejectionBucket γ₂ β r1 a).filter fun x =>
    makeHintCoeff (-(b : Coeff)) (x - (a : Coeff) + (b : Coeff)) γ₂ = true

variable {γ₂ β : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (hM : 2 * γ₂ < modulus - 1)
  {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {a : ℤ} (ha : |a| ≤ β) (hβ : β < γ₂)

include hγ hdvd hr1 ha hβ in
/-- The cell is the image of `u < 2(γ₂ - β) - 1` under `cellPoint`. -/
theorem rejectionBucket_eq_cellPoints :
    rejectionBucket γ₂ β r1 a = (range (2 * (γ₂ - β) - 1)).image (cellPoint γ₂ β r1 a) := by
  rw [rejectionBucket_eq_image hγ hdvd hr1 ha]
  ext x
  simp only [Finset.mem_image, Finset.mem_Ioo, Finset.mem_range, cellPoint]
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    refine ⟨(s + ((γ₂ : ℤ) - β) - 1).toNat, by omega, ?_⟩
    congr 1
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · rintro ⟨u, hu, rfl⟩
    refine ⟨-((γ₂ : ℤ) - β) + 1 + u, ⟨by omega, by omega⟩, ?_⟩
    congr 1
    ring

include hγ hdvd hM hr1 hβ in
/-- The hint fires at the `u`-th cell point exactly when the shifted offset leaves the bucket. -/
theorem hintFires_cellPoint_iff {b : ℤ} (hb : |b| < γ₂) {u : ℕ}
    (hu : u < 2 * (γ₂ - β) - 1) :
    makeHintCoeff (-(b : Coeff)) (cellPoint γ₂ β r1 a u - (a : Coeff) + (b : Coeff)) γ₂ = true ↔
      ¬ ((-(γ₂ : ℤ) < -((γ₂ : ℤ) - β) + 1 + u + b ∧ -((γ₂ : ℤ) - β) + 1 + u + b ≤ γ₂) ∨
        (r1 = 0 ∧ -((γ₂ : ℤ) - β) + 1 + u + b = -(γ₂ : ℤ))) := by
  rw [abs_lt] at hb
  have hs : |(-((γ₂ : ℤ) - β) + 1 + u : ℤ)| < γ₂ := by rw [abs_lt]; constructor <;> omega
  have hpt : cellPoint γ₂ β r1 a u = bucketPoint γ₂ r1 ((-((γ₂ : ℤ) - β) + 1 + u) + a) := by
    unfold cellPoint; congr 1; ring
  rw [hpt, makeHintCoeff_bucketPoint hγ hdvd hr1 hs a b, decide_eq_true_iff, ne_eq,
    highBits_bucketPoint_eq_iff hγ hdvd hM hr1 ⟨by omega, by omega⟩]

include hγ hdvd hM hr1 ha hβ in
/-- **The hint-firing points form an initial or a final segment of the cell.** -/
theorem hintFires_segment {b : ℤ} (hb : |b| < γ₂) :
    ∃ d ≤ 2 * (γ₂ - β) - 1,
      (∀ u < 2 * (γ₂ - β) - 1, (makeHintCoeff (-(b : Coeff))
        (cellPoint γ₂ β r1 a u - (a : Coeff) + (b : Coeff)) γ₂ = true ↔ u < d)) ∨
      (∀ u < 2 * (γ₂ - β) - 1, (makeHintCoeff (-(b : Coeff))
        (cellPoint γ₂ β r1 a u - (a : Coeff) + (b : Coeff)) γ₂ = true ↔
          2 * (γ₂ - β) - 1 - d ≤ u)) := by
  have hb' := abs_lt.mp hb
  set L := 2 * (γ₂ - β) - 1
  rcases le_or_gt 0 b with hb0 | hb0
  · -- `b ≥ 0`: the final segment `u ≥ 2γ₂ - β - b`
    refine ⟨L - min L (2 * (γ₂ : ℤ) - β - b).toNat, Nat.sub_le _ _, Or.inr fun u hu => ?_⟩
    rw [hintFires_cellPoint_iff hγ hdvd hM hr1 hβ hb hu]
    have : L - (L - min L (2 * (γ₂ : ℤ) - β - b).toNat) = min L (2 * (γ₂ : ℤ) - β - b).toNat := by
      have := min_le_left L (2 * (γ₂ : ℤ) - β - b).toNat
      omega
    rw [this]
    constructor
    · intro h
      by_contra hc
      apply h
      left
      constructor
      · omega
      · rw [min_le_iff, not_or] at hc
        omega
    · intro h hc
      rcases hc with ⟨_, h2⟩ | ⟨_, h2⟩
      · rcases min_le_iff.mp h with h' | h'
        · omega
        · omega
      · omega
  · -- `b < 0`: the initial segment `u < -b - β - [r1 = 0]`
    by_cases hr0 : r1 = 0
    · refine ⟨min L (-b - β - 1).toNat, min_le_left _ _, Or.inl fun u hu => ?_⟩
      rw [hintFires_cellPoint_iff hγ hdvd hM hr1 hβ hb hu, lt_min_iff]
      constructor
      · intro h
        refine ⟨hu, ?_⟩
        by_contra hc
        exact h (if hcase : (-((γ₂ : ℤ) - β) + 1 + u + b) = -(γ₂ : ℤ) then Or.inr ⟨hr0, hcase⟩
          else Or.inl ⟨by omega, by omega⟩)
      · rintro ⟨_, h⟩ hc
        rcases hc with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
    · refine ⟨min L (-b - β).toNat, min_le_left _ _, Or.inl fun u hu => ?_⟩
      rw [hintFires_cellPoint_iff hγ hdvd hM hr1 hβ hb hu, lt_min_iff]
      constructor
      · intro h
        refine ⟨hu, ?_⟩
        by_contra hc
        exact h (Or.inl ⟨by omega, by omega⟩)
      · rintro ⟨_, h⟩ hc
        rcases hc with ⟨h1, _⟩ | ⟨h2, _⟩
        · omega
        · exact hr0 h2

include hγ hdvd hM hr1 ha hβ in
/-- The hint-firing part of a cell and its complement are residue intervals. -/
theorem isResidueInterval_hintPart {b : ℤ} (hb : |b| < γ₂) :
    IsResidueInterval (hintPart γ₂ β r1 a b) ∧
      IsResidueInterval (rejectionBucket γ₂ β r1 a \ hintPart γ₂ β r1 a b) := by
  have hLN : 2 * (γ₂ - β) - 1 ≤ modulus := by
    have := Nat.div_le_self (modulus - 1) (2 * γ₂)
    omega
  set L := 2 * (γ₂ - β) - 1
  set c := cellPoint γ₂ β r1 a 0
  have hA := rejectionBucket_eq_cellPoints hγ hdvd hr1 ha hβ (γ₂ := γ₂) (β := β)
  have hg : ∀ u, cellPoint γ₂ β r1 a u = c + (u : Coeff) := cellPoint_eq_add γ₂ β r1 a
  set P : Coeff → Prop := fun x => makeHintCoeff (-(b : Coeff)) (x - (a : Coeff) + (b : Coeff)) γ₂ = true
  have hF : hintPart γ₂ β r1 a b = ((range L).filter fun u => P (cellPoint γ₂ β r1 a u)).image
      fun u : ℕ => c + (u : Coeff) := by
    rw [hintPart, hA, Finset.filter_image]
    exact Finset.image_congr fun u _ => hg u
  have hAF : rejectionBucket γ₂ β r1 a \ hintPart γ₂ β r1 a b =
      ((range L).filter fun u => ¬ P (cellPoint γ₂ β r1 a u)).image fun u : ℕ => c + (u : Coeff) := by
    ext x
    simp only [Finset.mem_sdiff, hintPart, Finset.mem_filter, hA, Finset.mem_image,
      Finset.mem_range, hg]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hn⟩
      exact ⟨u, ⟨hu, fun hp => hn ⟨⟨u, hu, rfl⟩, hp⟩⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hn⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, fun h => hn h.2⟩
  obtain ⟨d, hd, hcase | hcase⟩ := hintFires_segment hγ hdvd hM hr1 ha hβ hb
  · have h1 : ((range L).filter fun u => P (cellPoint γ₂ β r1 a u)) = Ico 0 d := by
      ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hp⟩; exact ⟨Nat.zero_le _, (hcase u hu).mp hp⟩
      · rintro ⟨-, hu⟩; exact ⟨by omega, (hcase u (by omega)).mpr hu⟩
    have h2 : ((range L).filter fun u => ¬ P (cellPoint γ₂ β r1 a u)) = Ico d L := by
      ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hp⟩; exact ⟨by by_contra h; exact hp ((hcase u hu).mpr (by omega)), hu⟩
      · rintro ⟨h1, hu⟩; exact ⟨hu, fun hp => by have := (hcase u hu).mp hp; omega⟩
    rw [hAF, hF, h1, h2]
    exact ⟨isResidueInterval_image_Ico c (by omega), isResidueInterval_image_Ico c hLN⟩
  · have h1 : ((range L).filter fun u => P (cellPoint γ₂ β r1 a u)) = Ico (L - d) L := by
      ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hp⟩; exact ⟨(hcase u hu).mp hp, hu⟩
      · rintro ⟨h1, hu⟩; exact ⟨hu, (hcase u hu).mpr h1⟩
    have h2 : ((range L).filter fun u => ¬ P (cellPoint γ₂ β r1 a u)) = Ico 0 (L - d) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hp⟩; exact ⟨Nat.zero_le _, by by_contra h; exact hp ((hcase u hu).mpr (by omega))⟩
      · rintro ⟨-, hu⟩; exact ⟨by omega, fun hp => by have := (hcase u (by omega)).mp hp; omega⟩
    rw [hAF, hF, h1, h2]
    exact ⟨isResidueInterval_image_Ico c hLN, isResidueInterval_image_Ico c (by omega)⟩

include hγ hdvd hr1 ha in
/-- The cell has `2(γ₂ - β) - 1` residues. -/
theorem card_rejectionBucket' : #(rejectionBucket γ₂ β r1 a) = 2 * (γ₂ - β) - 1 :=
  bucket_r0_card hγ hdvd hr1 ha

theorem hintPart_subset (b : ℤ) : hintPart γ₂ β r1 a b ⊆ rejectionBucket γ₂ β r1 a :=
  Finset.filter_subset _ _

/-! ### The accept indicator as a combination of products of cell functions -/

section Expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : ℕ} [NeZero M]

/-- The cell function of coordinate `i` for the expansion term `t`: the ct₀ indicator times
`1_{A_i ∖ F_i} + e(t) 1_{F_i}`, with `A_i` the r0-check cell of bucket `v_i` and `F_i` its
hint-firing part. -/
noncomputable def acceptCell (γ₂ β : ℕ) (a b : ι → ℤ) (t : ZMod M) (i : ι)
    (r1 : ℕ) (x : Coeff) : ℂ :=
  (if ∀ j, |b j| < γ₂ then 1 else 0) *
    cellFun (rejectionBucket γ₂ β r1 (a i)) (hintPart γ₂ β r1 (a i) (b i)) (ZMod.stdAddChar t) x

omit [DecidableEq ι] [Nonempty ι] in
theorem acceptCell_apply (γ₂ β : ℕ) (a b : ι → ℤ) (t : ZMod M) (i : ι) (r1 : ℕ) (x : Coeff) :
    acceptCell γ₂ β a b t i r1 x = (if ∀ j, |b j| < γ₂ then 1 else 0) *
      cellFun (rejectionBucket γ₂ β r1 (a i)) (hintPart γ₂ β r1 (a i) (b i)) (ZMod.stdAddChar t) x :=
  rfl

/-- **The accept indicator expansion**: for `ω < M` and `N = |ι| < M`,
`1[w ∈ acceptSet a b v] = ∑_t c_t ∏_i acceptCell t i (v i) (w i)` with the coefficients
`c_t = countCoeff M ω t` of `1[#fires ≤ ω]`, for any `M > max(N, ω)`. -/
theorem indicator_acceptSet_eq (γ₂ β ω : ℕ) (hω : ω < M) (hN : Fintype.card ι < M) (a b : ι → ℤ)
    (v : ι → ℕ) (w : ι → Coeff) :
    (if w ∈ acceptSet γ₂ β ω a b v then (1 : ℂ) else 0) =
      ∑ t, ZMod.countCoeff M ω t *
        ∏ i, acceptCell γ₂ β a b t i (v i) (w i) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hct : ∀ j, |b j| < γ₂
  · have hfac : ∀ t i, acceptCell γ₂ β a b t i (v i) (w i) =
        cellFun (rejectionBucket γ₂ β (v i) (a i)) (hintPart γ₂ β (v i) (a i) (b i))
          (ZMod.stdAddChar t) (w i) := fun t i => by
      rw [acceptCell_apply (M := M), if_pos hct, one_mul]
    simp_rw [hfac]
    by_cases hA : ∀ i, w i ∈ rejectionBucket γ₂ β (v i) (a i)
    · -- all coordinates in their cells: the product is `e(t · #fires)`
      set fires := (univ.filter fun i => w i ∈ hintPart γ₂ β (v i) (a i) (b i))
      have hprod : ∀ t : ZMod M, ∏ i, cellFun (rejectionBucket γ₂ β (v i) (a i))
          (hintPart γ₂ β (v i) (a i) (b i)) (ZMod.stdAddChar t) (w i) =
          ZMod.stdAddChar (t * (#fires : ZMod M)) := by
        intro t
        have : ∀ i, cellFun (rejectionBucket γ₂ β (v i) (a i)) (hintPart γ₂ β (v i) (a i) (b i))
            (ZMod.stdAddChar t) (w i) =
            if i ∈ fires then ZMod.stdAddChar t else 1 := fun i => by
          simp only [cellFun, fires, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs <;> first | rfl | exact absurd (hA i) ‹_›
        simp_rw [this]
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, ← AddChar.map_nsmul_eq_pow,
          nsmul_eq_mul, mul_comm]
      simp_rw [hprod]
      rw [← ZMod.indicator_le_eq_sum hω (lt_of_le_of_lt (Finset.card_le_univ _) hN)]
      have hmem : w ∈ acceptSet γ₂ β ω a b v ↔ #fires ≤ ω := by
        simp only [acceptSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hA' := fun i => (Finset.mem_filter.mp (hA i)).2
        have hfeq : (univ.filter fun i => makeHintCoeff (-(b i : Coeff))
            (w i - (a i : Coeff) + (b i : Coeff)) γ₂ = true) = fires := by
          ext i
          simp only [fires, hintPart, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => ⟨hA i, h⟩, fun h => h.2⟩
        rw [hfeq]
        exact ⟨fun h => h.2.2.2, fun h => ⟨fun i => (hA' i).1, fun i => (hA' i).2, hct, h⟩⟩
      by_cases hf : #fires ≤ ω
      · rw [if_pos (hmem.mpr hf), if_pos hf]
      · rw [if_neg (fun h => hf (hmem.mp h)), if_neg hf]
    · -- some coordinate outside its cell: both sides vanish
      push Not at hA
      obtain ⟨i₀, hi₀⟩ := hA
      have hnot : w ∉ acceptSet γ₂ β ω a b v := by
        intro h
        simp only [acceptSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact hi₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1 i₀, h.2.1 i₀⟩)
      rw [if_neg hnot]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀), mul_zero]
      have : w i₀ ∉ hintPart γ₂ β (v i₀) (a i₀) (b i₀) := fun h => hi₀ (hintPart_subset _ h)
      simp [cellFun, this, hi₀]
  · have hnot : w ∉ acceptSet γ₂ β ω a b v := by
      intro h
      simp only [acceptSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact hct h.2.2.1
    rw [if_neg hnot]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    rw [Finset.prod_eq_zero (Finset.mem_univ i₀), mul_zero]
    simp [acceptCell_apply, hct]

end Expansion

/-! ### The cell functions satisfy the kernel hypotheses -/

section CellFacts

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : ℕ} [NeZero M]

theorem norm_cellFun_le_one {A F : Finset Coeff} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (x : Coeff) :
    ‖cellFun A F ζ x‖ ≤ 1 := by
  unfold cellFun
  split_ifs <;> simp [hζ]

theorem cellFun_eq_zero_of_notMem {A F : Finset Coeff} (hFA : F ⊆ A) {ζ : ℂ} {x : Coeff}
    (hx : x ∉ A) : cellFun A F ζ x = 0 := by
  have : x ∉ F := fun h => hx (hFA h)
  simp [cellFun, this, hx]

theorem fourierCoeff_const_mul (c : ℂ) (g : Coeff → ℂ) (a : Coeff) :
    ZMod.fourierCoeff (fun x => c * g x) a = c * ZMod.fourierCoeff g a := by
  rw [ZMod.fourierCoeff_apply, ZMod.fourierCoeff_apply, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Cells of different buckets are disjoint. -/
theorem acceptCell_disjoint (γ₂ β : ℕ) (a b : ι → ℤ) (t : ZMod M) (i : ι)
    {r1 r1' : ℕ} (h : r1 ≠ r1') (x : Coeff) :
    acceptCell γ₂ β a b t i r1 x * starRingEnd ℂ (acceptCell γ₂ β a b t i r1' x) = 0 := by
  by_cases hx : x ∈ rejectionBucket γ₂ β r1 (a i)
  · have hx' : x ∉ rejectionBucket γ₂ β r1' (a i) := fun hx' =>
      h ((Finset.mem_filter.mp hx).2.1.symm.trans (Finset.mem_filter.mp hx').2.1)
    rw [acceptCell_apply (M := M), acceptCell_apply (M := M), cellFun_eq_zero_of_notMem (hintPart_subset _) hx', mul_zero,
      map_zero, mul_zero]
  · rw [acceptCell_apply (M := M), cellFun_eq_zero_of_notMem (hintPart_subset _) hx, mul_zero, zero_mul]

/-- `∑_x ‖g x‖² ≤ #cell`. -/
theorem sum_norm_acceptCell_sq_le (γ₂ β : ℕ) (a b : ι → ℤ) (t : ZMod M)
    (i : ι) (r1 : ℕ) :
    ∑ x, ‖acceptCell γ₂ β a b t i r1 x‖ ^ 2 ≤ #(rejectionBucket γ₂ β r1 (a i)) := by
  have hpt : ∀ x, ‖acceptCell γ₂ β a b t i r1 x‖ ^ 2 ≤
      if x ∈ rejectionBucket γ₂ β r1 (a i) then 1 else 0 := by
    intro x
    split_ifs with hx
    · have h1 : ‖acceptCell γ₂ β a b t i r1 x‖ ≤ 1 := by
        rw [acceptCell_apply (M := M), norm_mul]
        refine (mul_le_mul (by split_ifs <;> simp)
          (norm_cellFun_le_one (by simp [AddChar.norm_apply]) x) (norm_nonneg _)
          zero_le_one).trans_eq (one_mul 1)
      nlinarith [norm_nonneg (acceptCell γ₂ β a b t i r1 x)]
    · rw [acceptCell_apply (M := M), cellFun_eq_zero_of_notMem (hintPart_subset _) hx, mul_zero, norm_zero]
      norm_num
  calc ∑ x, ‖acceptCell γ₂ β a b t i r1 x‖ ^ 2
      ≤ ∑ x, (if x ∈ rejectionBucket γ₂ β r1 (a i) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = #(rejectionBucket γ₂ β r1 (a i)) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_one]

end CellFacts

include hγ hdvd hM hr1 hβ in
/-- **The Fourier bound of an accepted cell function**:
`‖ĝ(x)‖ ≤ (L/q) · min(1, (q/L)/|x|)` with `L = 2(γ₂ - β) - 1`. -/
theorem norm_fourierCoeff_acceptCell_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : ℕ} [NeZero M]
    (a b : ι → ℤ) (t : ZMod M) (i : ι) (ha : |a i| ≤ β) (x : Coeff) :
    ‖ZMod.fourierCoeff (acceptCell γ₂ β a b t i r1) x‖ ≤
      ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) / modulus *
        hintKernel ((modulus : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)) x := by
  have hL : 0 < 2 * (γ₂ - β) - 1 := by omega
  have hN : (0 : ℝ) < modulus := by norm_num [modulus]
  have hrhs : 0 ≤ ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) / modulus *
      hintKernel ((modulus : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)) x :=
    mul_nonneg (by positivity) (hintKernel_nonneg (by positivity) x)
  change ‖ZMod.fourierCoeff (fun y => (if ∀ j, |b j| < γ₂ then (1 : ℂ) else 0) *
    cellFun (rejectionBucket γ₂ β r1 (a i)) (hintPart γ₂ β r1 (a i) (b i))
      (ZMod.stdAddChar t) y) x‖ ≤ _
  rw [fourierCoeff_const_mul]
  split_ifs with hct
  · rw [one_mul]
    obtain ⟨h₂, h₁⟩ := isResidueInterval_hintPart hγ hdvd hM hr1 ha hβ (hct i)
    have hcard := card_rejectionBucket' hγ hdvd hr1 ha (γ₂ := γ₂)
    have := norm_fourierCoeff_cellFun_le (hintPart_subset (b i)) (ζ := ZMod.stdAddChar t)
      (AddChar.norm_apply _ _)
      h₁ h₂ (by rw [hcard]; exact hL) x
    rwa [hcard] at this
  · rw [zero_mul, norm_zero]
    exact hrhs

end GordieHowe.MLDSA.Regularity
