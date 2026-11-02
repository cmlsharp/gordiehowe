-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PairKernel
public import GordieHowe.Foundations.ToMathlib.CharacterSums
public import GordieHowe.Applications.MLDSA.Regularity.SecondMoment

@[expose] public section

/-!
# The normalized pair kernel of a cell family

For the accepted-cell functions `g_v` of one coefficient (`v` ranging over the `m` buckets, each
`g_v` supported on its cell of `L` residues, with `|g_v| ≤ 1` and disjoint cells), the normalized
pair kernel and single-coefficient weight are

    κ(a, b) = ‖∑_v ĝ_v(a) conj ĝ_v(b)‖ / (m (L/N)²),    φ(a) = √(∑_v ‖ĝ_v(a)‖² / m) / (L/N).

This file proves the hypotheses of `KernelBounds` for them (`kernelBounds_of_cells`):
`κ ≤ φ ⊗ φ` (Cauchy–Schwarz), `φ ≤ f` when every `‖ĝ_v(a)‖ ≤ (L/N) f(a)`, and the pair Parseval
bound `∑ κ² ≤ N² / (m L²)` (note, Section 6, (17)); and the single-coefficient Parseval bound
`∑_a φ(a)² ≤ N / L` (`sum_normWeight_sq_le`).
-/

open Finset ComplexConjugate
open scoped BigOperators

namespace GordieHowe.MLDSA.Regularity

variable {N : ℕ} [NeZero N] {V : Type*} [Fintype V] [DecidableEq V]

/-- The normalized pair kernel `‖∑_v ĝ_v(a) conj ĝ_v(b)‖ / (m (L/N)²)`. -/
noncomputable def normKernel (g : V → ZMod N → ℂ) (L : ℝ) (u : ZMod N × ZMod N) : ℝ :=
  ‖ZMod.cellKernel g u‖ / (Fintype.card V * (L / N) ^ 2)

/-- The normalized single-coefficient weight `√(∑_v ‖ĝ_v(a)‖² / m) / (L/N)`. -/
noncomputable def normWeight (g : V → ZMod N → ℂ) (L : ℝ) (a : ZMod N) : ℝ :=
  √((∑ v, ‖ZMod.fourierCoeff (g v) a‖ ^ 2) / Fintype.card V) / (L / N)

section Normalized

variable [Nonempty V] (g : V → ZMod N → ℂ) {L : ℝ} (hL : 0 < L)
include hL

omit [DecidableEq V] [Nonempty V] in
theorem normWeight_nonneg (a : ZMod N) : 0 ≤ normWeight g L a := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold normWeight
  positivity

omit [DecidableEq V] in
theorem normKernel_nonneg (u : ZMod N × ZMod N) : 0 ≤ normKernel g L u := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold normKernel
  positivity

omit [DecidableEq V] in
/-- `κ(a, b) ≤ φ(a) φ(b)`. -/
theorem normKernel_le_mul (u : ZMod N × ZMod N) :
    normKernel g L u ≤ normWeight g L u.1 * normWeight g L u.2 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hm : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0 : ℝ) < Fintype.card V * (L / N) ^ 2 := by positivity
  unfold normKernel normWeight
  rw [div_le_iff₀ hc]
  refine (ZMod.norm_cellKernel_le g u).trans (le_of_eq ?_)
  rw [Real.sqrt_div' _ hm.le, Real.sqrt_div' _ hm.le]
  have hs : √(Fintype.card V : ℝ) ^ 2 = Fintype.card V := Real.sq_sqrt hm.le
  have hs0 : 0 < √(Fintype.card V : ℝ) := Real.sqrt_pos.mpr hm
  field_simp
  rw [hs]

omit [DecidableEq V] in
/-- `φ ≤ f` when every `‖ĝ_v(a)‖ ≤ (L/N) f(a)`. -/
theorem normWeight_le {f : ZMod N → ℝ} (hf0 : ∀ a, 0 ≤ f a)
    (hg : ∀ v a, ‖ZMod.fourierCoeff (g v) a‖ ≤ L / N * f a) (a : ZMod N) :
    normWeight g L a ≤ f a := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hm : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hLN : 0 < L / N := by positivity
  unfold normWeight
  rw [div_le_iff₀ hLN]
  refine Real.sqrt_le_iff.mpr ⟨mul_nonneg (hf0 a) hLN.le, ?_⟩
  rw [div_le_iff₀ hm]
  calc ∑ v, ‖ZMod.fourierCoeff (g v) a‖ ^ 2 ≤ ∑ _v : V, (L / N * f a) ^ 2 :=
        Finset.sum_le_sum fun v _ => pow_le_pow_left₀ (norm_nonneg _) (hg v a) 2
    _ = (f a * (L / N)) ^ 2 * Fintype.card V := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

/-- **Pair Parseval, normalized**: `∑ κ² ≤ N² / (m L²)`, for disjoint cells with
`∑_x ‖g_v x‖² ≤ L`. -/
theorem sum_normKernel_sq_le (hdisj : ∀ v v' x, v ≠ v' → g v x * conj (g v' x) = 0)
    (hL2 : ∀ v, ∑ x, ‖g v x‖ ^ 2 ≤ L) :
    ∑ u, normKernel g L u ^ 2 ≤ (N : ℝ) ^ 2 / (Fintype.card V * L ^ 2) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hm : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0 : ℝ) < Fintype.card V * (L / N) ^ 2 := by positivity
  have h := ZMod.sum_norm_cellKernel_sq_le g hdisj hL2
  unfold normKernel
  simp_rw [div_pow]
  rw [← Finset.sum_div, div_le_iff₀ (by positivity)]
  refine h.trans (le_of_eq ?_)
  field_simp

omit [DecidableEq V] in
/-- **Single-coefficient Parseval, normalized**: `∑_a φ(a)² ≤ N / L` for `∑_x ‖g_v x‖² ≤ L`. -/
theorem sum_normWeight_sq_le (hL2 : ∀ v, ∑ x, ‖g v x‖ ^ 2 ≤ L) :
    ∑ a, normWeight g L a ^ 2 ≤ N / L := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hm : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hpars : ∀ v, ∑ a, ‖ZMod.fourierCoeff (g v) a‖ ^ 2 ≤ L / N := by
    intro v
    have h := ZMod.sum_fourierCoeff_mul_conj (g v) (g v)
    have hre : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := fun z => by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have e1 : ∑ a, ‖ZMod.fourierCoeff (g v) a‖ ^ 2 =
        (∑ a, ZMod.fourierCoeff (g v) a * conj (ZMod.fourierCoeff (g v) a)).re := by
      rw [Complex.re_sum]; exact Finset.sum_congr rfl fun a _ => hre _
    have e2 : (((N : ℂ)⁻¹ * ∑ x, g v x * conj (g v x))).re = (N : ℝ)⁻¹ * ∑ x, ‖g v x‖ ^ 2 := by
      rw [show ((N : ℂ)⁻¹) = ((N : ℝ)⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
        Complex.re_sum]
      congr 1
      exact Finset.sum_congr rfl fun x _ => (hre _).symm
    rw [e1, h, e2, inv_mul_eq_div]
    gcongr
    exact hL2 v
  unfold normWeight
  have hLN : 0 < L / N := by positivity
  calc ∑ a, (√((∑ v, ‖ZMod.fourierCoeff (g v) a‖ ^ 2) / Fintype.card V) / (L / N)) ^ 2
      = (∑ v, ∑ a, ‖ZMod.fourierCoeff (g v) a‖ ^ 2) / Fintype.card V / (L / N) ^ 2 := by
        rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [div_pow, Real.sq_sqrt (by positivity)]
    _ ≤ (∑ _v : V, L / N) / Fintype.card V / (L / N) ^ 2 := by
        gcongr with v
        exact hpars v
    _ = N / L := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        field_simp

omit hL in
/-- **The kernel bounds of a family of cell families**: for every row `i` and coefficient `c` a
cell family `g i c` with disjoint cells, `∑_x ‖g x‖² ≤ L`, Fourier coefficients
`‖ĝ_v(a)‖ ≤ (L/N) f(a)` and `0 ≤ f ≤ 1`, `∑ f ≤ S₁`, `1 ≤ S₁`. -/
theorem kernelBounds_of_cells [Fact N.Prime] {k n : ℕ} (G : Fin k → Fin n → V → ZMod N → ℂ)
    (hL : 0 < L) {f : ZMod N → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) {S₁ : ℝ}
    (hS₁ : 1 ≤ S₁) (hfS : ∑ a, f a ≤ S₁)
    (hdisj : ∀ i c v v' x, v ≠ v' → G i c v x * conj (G i c v' x) = 0)
    (hL2 : ∀ i c v, ∑ x, ‖G i c v x‖ ^ 2 ≤ L)
    (hG : ∀ i c v a, ‖ZMod.fourierCoeff (G i c v) a‖ ≤ L / N * f a) :
    KernelBounds (F := ZMod N) (fun i c => normKernel (G i c) L)
      (fun i c => normWeight (G i c) L) f S₁ ((N : ℝ) ^ 2 / (Fintype.card V * L ^ 2)) where
  kernel_nonneg _ _ u := normKernel_nonneg _ hL u
  kernel_le_mul _ _ u := normKernel_le_mul _ hL u
  weight_nonneg _ _ u := normWeight_nonneg _ hL u
  weight_le_one i c u := (normWeight_le _ hL hf0 (hG i c) u).trans (hf1 u)
  weight_le i c u := normWeight_le _ hL hf0 (hG i c) u
  bound_nonneg := hf0
  weight_sum_le i c := (Finset.sum_le_sum fun u _ => normWeight_le _ hL hf0 (hG i c) u).trans hfS
  one_le_mass := hS₁
  kernel_sq_sum_le i c := sum_normKernel_sq_le _ hL (hdisj i c) (hL2 i c)

end Normalized

section HintCell

/-- The hint-split kernel bound `f(a) = min(1, C / |a|)` (`f(0) = 1`), with `|a|` the centered
absolute value. -/
noncomputable def hintKernel (C : ℝ) (a : ZMod N) : ℝ :=
  if a = 0 then 1 else min 1 (C / |(a.valMinAbs : ℝ)|)

omit [NeZero N] in
theorem hintKernel_nonneg {C : ℝ} (hC : 0 ≤ C) (a : ZMod N) : 0 ≤ hintKernel C a := by
  unfold hintKernel
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

omit [NeZero N] in
theorem hintKernel_le_one (C : ℝ) (a : ZMod N) : hintKernel C a ≤ 1 := by
  unfold hintKernel
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

omit [NeZero N] in
theorem hintKernel_mul_abs_le {C : ℝ} {a : ZMod N} (ha : a ≠ 0) :
    hintKernel C a * |(a.valMinAbs : ℝ)| ≤ C := by
  have hpos : 0 < |(a.valMinAbs : ℝ)| := abs_pos.mpr (by exact_mod_cast (ZMod.valMinAbs_eq_zero a).not.mpr ha)
  unfold hintKernel
  rw [if_neg ha]
  calc min 1 (C / |(a.valMinAbs : ℝ)|) * |(a.valMinAbs : ℝ)|
      ≤ C / |(a.valMinAbs : ℝ)| * |(a.valMinAbs : ℝ)| := by gcongr; exact min_le_right _ _
    _ = C := div_mul_cancel₀ _ hpos.ne'

/-- A set of residues is an interval: the image of `u ↦ c + u` on `u < len`, `len ≤ N`. -/
def IsResidueInterval (S : Finset (ZMod N)) : Prop :=
  ∃ c : ZMod N, ∃ len : ℕ, len ≤ N ∧ S = (range len).image fun u : ℕ => c + (u : ZMod N)

/-- The cell function `1_{A ∖ F} + ζ · 1_F` of a cell `A` with hint-firing part `F ⊆ A`. -/
noncomputable def cellFun (A F : Finset (ZMod N)) (ζ : ℂ) (x : ZMod N) : ℂ :=
  if x ∈ F then ζ else if x ∈ A then 1 else 0

theorem norm_sum_interval_le {S : Finset (ZMod N)} (hS : IsResidueInterval S) {a : ZMod N}
    (ha : a ≠ 0) : ‖∑ x ∈ S, ZMod.stdAddChar (-(x * a))‖ ≤ N / (2 * |(a.valMinAbs : ℝ)|) := by
  obtain ⟨c, len, hlen, rfl⟩ := hS
  have hinj : Set.InjOn (fun u : ℕ => c + (u : ZMod N)) (range len) := by
    intro u hu v hv h
    have h' : (u : ZMod N) = v := add_left_cancel h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hu)
      hlen), Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hv) hlen)] at h'
    exact h'
  rw [Finset.sum_image hinj]
  have h := ZMod.norm_sum_stdAddChar_le (neg_ne_zero.mpr ha) c len
  have habs : |(((-a).valMinAbs : ℤ) : ℝ)| = |(a.valMinAbs : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs,
      ZMod.natAbs_valMinAbs_neg]
  rw [habs] at h
  refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun u _ => ?_)) h
  congr 1
  ring

/-- **The Fourier coefficients of a hint-split cell**: for intervals `A ∖ F` and `F ⊆ A` and
`‖ζ‖ = 1`, `‖ĝ(a)‖ ≤ (#A / N) · hintKernel (N / #A) a`. -/
theorem norm_fourierCoeff_cellFun_le {A F : Finset (ZMod N)} (hFA : F ⊆ A) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) (h₁ : IsResidueInterval (A \ F)) (h₂ : IsResidueInterval F) (hA : 0 < #A)
    (a : ZMod N) :
    ‖ZMod.fourierCoeff (cellFun A F ζ) a‖ ≤ #A / N * hintKernel (N / #A) a := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA
  have hexp : ZMod.fourierCoeff (cellFun A F ζ) a = (N : ℂ)⁻¹ *
      (∑ x ∈ A \ F, ZMod.stdAddChar (-(x * a)) + ζ * ∑ x ∈ F, ZMod.stdAddChar (-(x * a))) := by
    rw [ZMod.fourierCoeff_apply]
    congr 1
    have hsplit : ∀ x, ZMod.stdAddChar (-(x * a)) * cellFun A F ζ x =
        (if x ∈ A \ F then ZMod.stdAddChar (-(x * a)) else 0) +
          ζ * (if x ∈ F then ZMod.stdAddChar (-(x * a)) else 0) := by
      intro x
      unfold cellFun
      by_cases hF : x ∈ F
      · have : x ∉ A \ F := fun h => (Finset.mem_sdiff.mp h).2 hF
        simp [hF, this, mul_comm]
      · by_cases hA : x ∈ A
        · have : x ∈ A \ F := Finset.mem_sdiff.mpr ⟨hA, hF⟩
          simp [hF, hA, this]
        · have : x ∉ A \ F := fun h => hA (Finset.mem_sdiff.mp h).1
          simp [hF, hA, this]
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
      Finset.univ_inter]
  have hcard : #(A \ F) + #F = #A := Finset.card_sdiff_add_card_eq_card hFA
  have hnorm : ‖ZMod.fourierCoeff (cellFun A F ζ) a‖ ≤ (N : ℝ)⁻¹ *
      (‖∑ x ∈ A \ F, ZMod.stdAddChar (-(x * a))‖ + ‖∑ x ∈ F, ZMod.stdAddChar (-(x * a))‖) := by
    rw [hexp, norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, hζ, one_mul]
  have htriv : ∀ S : Finset (ZMod N), ‖∑ x ∈ S, ZMod.stdAddChar (-(x * a))‖ ≤ #S := fun S =>
    (norm_sum_le _ _).trans (le_of_eq (by simp [AddChar.norm_apply]))
  have hfirst : ‖ZMod.fourierCoeff (cellFun A F ζ) a‖ ≤ #A / N := by
    refine hnorm.trans ?_
    calc (N : ℝ)⁻¹ * (‖∑ x ∈ A \ F, ZMod.stdAddChar (-(x * a))‖ +
          ‖∑ x ∈ F, ZMod.stdAddChar (-(x * a))‖) ≤ (N : ℝ)⁻¹ * (#(A \ F) + #F) := by
          gcongr
          · exact htriv _
          · exact htriv _
      _ = #A / N := by rw [← hcard]; push_cast; ring
  unfold hintKernel
  split_ifs with ha
  · rw [mul_one]; exact hfirst
  · have hpos : 0 < |(a.valMinAbs : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast (ZMod.valMinAbs_eq_zero a).not.mpr ha)
    have hsecond : ‖ZMod.fourierCoeff (cellFun A F ζ) a‖ ≤ 1 / |(a.valMinAbs : ℝ)| := by
      refine hnorm.trans ?_
      calc (N : ℝ)⁻¹ * (‖∑ x ∈ A \ F, ZMod.stdAddChar (-(x * a))‖ +
            ‖∑ x ∈ F, ZMod.stdAddChar (-(x * a))‖) ≤
            (N : ℝ)⁻¹ * (N / (2 * |(a.valMinAbs : ℝ)|) + N / (2 * |(a.valMinAbs : ℝ)|)) := by
            gcongr
            · exact norm_sum_interval_le h₁ ha
            · exact norm_sum_interval_le h₂ ha
        _ = 1 / |(a.valMinAbs : ℝ)| := by field_simp; ring
    rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
    refine le_min hfirst (hsecond.trans (le_of_eq ?_))
    field_simp

omit [NeZero N] in
theorem isResidueInterval_image_Ico (c : ZMod N) {s e : ℕ} (he : e ≤ N) :
    IsResidueInterval ((Ico s e).image fun u : ℕ => c + (u : ZMod N)) := by
  refine ⟨c + s, e - s, by omega, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    refine ⟨u - s, by omega, ?_⟩
    rw [Nat.cast_sub h1]
    ring
  · rintro ⟨v, hv, rfl⟩
    refine ⟨s + v, ⟨by omega, by omega⟩, ?_⟩
    push_cast
    ring

end HintCell

end GordieHowe.MLDSA.Regularity
