-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.FourierProduct
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The pair kernel of a family of functions on `ZMod N`

For functions `g_v : ZMod N → ℂ` (`v ∈ V`), the pair kernel is
`k(a, b) = ∑_v ĝ_v(a) conj ĝ_v(b)` with `ĝ = fourierCoeff`. This file proves:

- `ZMod.sum_fourierCoeff_mul_conj` (Parseval):
  `∑_a ĝ(a) conj ĥ(a) = N⁻¹ ∑_x g(x) conj h(x)`;
- `ZMod.sum_norm_cellKernel_sq_le`: for `g_v` with pairwise disjoint supports (`g_v · conj g_{v'} = 0`
  for `v ≠ v'`) and `∑_x ‖g_v x‖² ≤ L`, `∑_{a,b} ‖k(a, b)‖² ≤ |V| (L / N)²`. This is the
  same-cell pair Parseval of the HighBits regularity note (Section 6, (17));
- `ZMod.norm_cellKernel_le`: `‖k(a, b)‖ ≤ √(∑_v ‖ĝ_v a‖²) · √(∑_v ‖ĝ_v b‖²)` (Cauchy–Schwarz).
-/

open Finset ComplexConjugate
open scoped BigOperators ZMod

namespace ZMod

variable {N : ℕ} [NeZero N]

theorem fourierCoeff_apply (g : ZMod N → ℂ) (a : ZMod N) :
    fourierCoeff g a = (N : ℂ)⁻¹ * ∑ x, stdAddChar (-(x * a)) * g x := by
  rw [fourierCoeff, dft_apply]
  simp only [smul_eq_mul]

/-- `∑_a e(a t) = N` for `t = 0` and `0` otherwise. -/
theorem sum_stdAddChar_mul (t : ZMod N) :
    ∑ a : ZMod N, stdAddChar (a * t) = if t = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift t (isPrimitive_stdAddChar N), ZMod.card]
  split_ifs <;> simp

/-- **Parseval on `ZMod N`**: `∑_a ĝ(a) conj ĥ(a) = N⁻¹ ∑_x g(x) conj h(x)`. -/
theorem sum_fourierCoeff_mul_conj (g h : ZMod N → ℂ) :
    ∑ a, fourierCoeff g a * conj (fourierCoeff h a) = (N : ℂ)⁻¹ * ∑ x, g x * conj (h x) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp_rw [fourierCoeff_apply, map_mul, map_inv₀, map_natCast, map_sum, map_mul,
    ← AddChar.map_neg_eq_conj, neg_neg, Finset.mul_sum, Finset.sum_mul]
  -- `∑_a ∑_x ∑_y N⁻² e(-xa) g x e(ya) conj (h y)`
  have key : ∀ x y : ZMod N, ∑ a : ZMod N, (N : ℂ)⁻¹ * (stdAddChar (-(x * a)) * g x) *
      ((N : ℂ)⁻¹ * (stdAddChar (y * a) * conj (h y))) =
      if x = y then (N : ℂ)⁻¹ * (g x * conj (h x)) else 0 := by
    intro x y
    have : ∀ a : ZMod N, (N : ℂ)⁻¹ * (stdAddChar (-(x * a)) * g x) *
        ((N : ℂ)⁻¹ * (stdAddChar (y * a) * conj (h y))) =
        ((N : ℂ)⁻¹ * (N : ℂ)⁻¹ * (g x * conj (h y))) * stdAddChar (a * (y - x)) := by
      intro a
      rw [show a * (y - x) = -(x * a) + y * a by ring, AddChar.map_add_eq_mul]
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_stdAddChar_mul]
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, if_true]
      field_simp
    · have : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
      rw [if_neg this, if_neg hxy, mul_zero]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => key x y).trans ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite_eq' univ y (fun x => (N : ℂ)⁻¹ * (g x * conj (h x))), if_pos (mem_univ _)]

variable {V : Type*} [Fintype V]

/-- The pair kernel `k(a, b) = ∑_v ĝ_v(a) conj ĝ_v(b)` of a family of functions. -/
noncomputable def cellKernel (g : V → ZMod N → ℂ) (u : ZMod N × ZMod N) : ℂ :=
  ∑ v, fourierCoeff (g v) u.1 * conj (fourierCoeff (g v) u.2)

/-- Cauchy–Schwarz for the pair kernel. -/
theorem norm_cellKernel_le (g : V → ZMod N → ℂ) (u : ZMod N × ZMod N) :
    ‖cellKernel g u‖ ≤ √(∑ v, ‖fourierCoeff (g v) u.1‖ ^ 2) *
      √(∑ v, ‖fourierCoeff (g v) u.2‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_conj]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- **Pair Parseval**: for functions with pairwise disjoint supports and `∑_x ‖g_v x‖² ≤ L`,
`∑_{a,b} ‖k(a, b)‖² ≤ |V| (L / N)²`. Expanding the square gives `∑_{v,v'} |⟨ĝ_v, ĝ_{v'}⟩|²`, and by
Parseval `⟨ĝ_v, ĝ_{v'}⟩ = N⁻¹ ⟨g_v, g_{v'}⟩`, which vanishes for `v ≠ v'`. -/
theorem sum_norm_cellKernel_sq_le [DecidableEq V] (g : V → ZMod N → ℂ)
    (hdisj : ∀ v v' x, v ≠ v' → g v x * conj (g v' x) = 0) {L : ℝ}
    (hL : ∀ v, ∑ x, ‖g v x‖ ^ 2 ≤ L) :
    ∑ u, ‖cellKernel g u‖ ^ 2 ≤ Fintype.card V * (L / N) ^ 2 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set P : V → V → ℂ := fun v v' => ∑ a, fourierCoeff (g v) a * conj (fourierCoeff (g v') a)
  have hP : ∀ v v', P v v' = (N : ℂ)⁻¹ * ∑ x, g v x * conj (g v' x) :=
    fun v v' => sum_fourierCoeff_mul_conj _ _
  have hexp : ∑ u, cellKernel g u * conj (cellKernel g u) = ∑ v, ∑ v', P v v' * conj (P v v') := by
    have lhs : ∀ u : ZMod N × ZMod N, cellKernel g u * conj (cellKernel g u) =
        ∑ v, ∑ v', fourierCoeff (g v) u.1 * conj (fourierCoeff (g v') u.1) *
          (conj (fourierCoeff (g v) u.2) * fourierCoeff (g v') u.2) := by
      intro u
      simp only [cellKernel, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun v' _ => ?_
      ring
    have rhs : ∀ v v', P v v' * conj (P v v') = ∑ u : ZMod N × ZMod N,
        fourierCoeff (g v) u.1 * conj (fourierCoeff (g v') u.1) *
          (conj (fourierCoeff (g v) u.2) * fourierCoeff (g v') u.2) := by
      intro v v'
      simp only [P, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum,
        Fintype.sum_prod_type]
    simp_rw [lhs, rhs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_comm
  have hoff : ∀ v v', v ≠ v' → P v v' = 0 := fun v v' h => by
    rw [hP, Finset.sum_eq_zero fun x _ => hdisj v v' x h, mul_zero]
  have hdiag : ∀ v, ‖P v v‖ ≤ L / N := by
    intro v
    rw [hP, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    gcongr
    refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) (hL v))
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, Complex.norm_conj, sq]
  have hre : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  calc ∑ u, ‖cellKernel g u‖ ^ 2 = (∑ u, cellKernel g u * conj (cellKernel g u)).re := by
        rw [Complex.re_sum]; exact Finset.sum_congr rfl fun u _ => hre _
    _ = ∑ v, ∑ v', ‖P v v'‖ ^ 2 := by
        rw [hexp, Complex.re_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun v' _ => (hre _).symm
    _ = ∑ v, ‖P v v‖ ^ 2 := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_eq_single v (fun v' _ h => by rw [hoff v v' (Ne.symm h), norm_zero,
          sq, mul_zero]) (fun h => absurd (Finset.mem_univ v) h)]
    _ ≤ ∑ _v : V, (L / N) ^ 2 := Finset.sum_le_sum fun v _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hdiag v) 2
    _ = Fintype.card V * (L / N) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end ZMod
