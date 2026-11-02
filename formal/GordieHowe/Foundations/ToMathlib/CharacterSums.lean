-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Character sums: averaging over a kernel, intervals, and the `ℓ¹`-`ℓ²` comparison

Three facts about finite sums, candidates for Mathlib:

- `Finset.sum_abs_le_sqrt_card_mul_sum_sq`: `∑_{i ∈ s} |f i| ≤ √(#s · ∑_{i ∈ s} f i ^ 2)`
  (Cauchy–Schwarz against the constant function);
- `AddChar.sum_comp_mul_eq_zero` (averaging over a kernel): for an additive map `φ : M →+ N` of
  finite groups, a character `ψ` of `M` and any `G : N → ℂ`, `∑_A G (φ A) · ψ A = 0` as soon as
  `ψ` is nontrivial on `ker φ`. A function of `A` that sees `A` only through `φ A` thus cannot
  correlate with a character that is nontrivial on `ker φ`;
- `ZMod.norm_sum_stdAddChar_le`: for `x ≠ 0` in `ZMod N`, the character sum over an interval of
  any length, `‖∑_{u < len} e((c + u) x / N)‖`, is at most `N / (2 |x|)`, where `|x|` is the
  absolute value of the centered representative `x.valMinAbs`. This is the geometric-series bound
  `2 / |e(x/N) - 1| = 1 / |sin (π x / N)|` with Jordan's inequality `sin t ≥ 2t/π` on `[0, π/2]`.
-/

open Finset Real
open scoped BigOperators

namespace Finset

/-- The `ℓ¹` norm of a finitely supported real function is at most `√(#s)` times its `ℓ²` norm. -/
theorem sum_abs_le_sqrt_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, |f i| ≤ √(#s * ∑ i ∈ s, f i ^ 2) := by
  refine Real.le_sqrt_of_sq_le ?_
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |f i|)
  simpa only [sq_abs] using h

end Finset

namespace AddChar

/-- Averaging over a kernel: if the character `ψ` of `M` is nontrivial on the kernel of
`φ : M →+ N`, then `∑_A G (φ A) · ψ A = 0` for every `G : N → ℂ`. The sum is invariant under the
shift `A ↦ A + K` by a kernel element `K` with `ψ K ≠ 1`, which multiplies it by `ψ K`. -/
theorem sum_comp_mul_eq_zero {M N : Type*} [AddCommGroup M] [Fintype M] [AddCommGroup N]
    (φ : M →+ N) (ψ : AddChar M ℂ) (G : N → ℂ) {K : M} (hK : φ K = 0) (hψ : ψ K ≠ 1) :
    ∑ A, G (φ A) * ψ A = 0 := by
  set S := ∑ A, G (φ A) * ψ A
  have hshift : S = ψ K * S := by
    calc S = ∑ A, G (φ (A + K)) * ψ (A + K) :=
          (Fintype.sum_equiv (Equiv.addRight K) _ _ fun A => rfl).symm
      _ = ψ K * S := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [map_add, hK, add_zero, AddChar.map_add_eq_mul]
          ring
  have h1 : (1 - ψ K) * S = 0 := by rw [sub_mul, one_mul, ← hshift, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hψ))

open Classical in
/-- The bound form of `sum_comp_mul_eq_zero`: `‖∑_A G (φ A) · ψ A‖` is at most `∑_A ‖G (φ A)‖`,
and vanishes unless `ψ` is trivial on `ker φ`. -/
theorem norm_sum_comp_mul_le {M N : Type*} [AddCommGroup M] [Fintype M] [AddCommGroup N]
    (φ : M →+ N) (ψ : AddChar M ℂ) (G : N → ℂ) :
    ‖∑ A, G (φ A) * ψ A‖ ≤
      if ∀ K, φ K = 0 → ψ K = 1 then ∑ A, ‖G (φ A)‖ else 0 := by
  split_ifs with h
  · refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun A _ => ?_))
    rw [norm_mul, AddChar.norm_apply, mul_one]
  · push Not at h
    obtain ⟨K, hK, hψ⟩ := h
    rw [sum_comp_mul_eq_zero φ ψ G hK hψ, norm_zero]

end AddChar

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- `‖e(x/N) - 1‖ ≥ 4|x|/N` for the centered representative `x.valMinAbs`. -/
theorem four_mul_abs_valMinAbs_div_le_norm_stdAddChar_sub_one (x : ZMod N) :
    4 * |(x.valMinAbs : ℝ)| / N ≤ ‖stdAddChar x - 1‖ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set m := x.valMinAbs
  have hm : |(m : ℝ)| * 2 ≤ N := by
    obtain ⟨h1, h2⟩ := x.valMinAbs_mem_Ioc
    have h' : |m| * 2 ≤ (N : ℤ) := by
      have : |m * 2| ≤ (N : ℤ) := abs_le.mpr ⟨h1.le, h2⟩
      rwa [abs_mul, abs_two] at this
    exact_mod_cast h'
  have hx : stdAddChar x = Complex.exp (Complex.I * ((2 * π * m / N : ℝ) : ℂ)) := by
    rw [stdAddChar_apply, ← x.coe_valMinAbs, toCircle_intCast]
    push_cast
    congr 1
    simp only [m]
    ring
  rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have ht : |2 * π * m / N / 2| ≤ π / 2 := by
    rw [show 2 * π * (m : ℝ) / N / 2 = π * m / N by ring, abs_div, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos hN, div_le_iff₀ hN]
    nlinarith [Real.pi_pos, abs_nonneg (m : ℝ)]
  have hj := Real.mul_abs_le_abs_sin ht
  rw [show 2 * π * (m : ℝ) / N / 2 = π * m / N by ring, abs_div, abs_mul,
    abs_of_pos Real.pi_pos, abs_of_pos hN] at hj
  have : 2 / π * (π * |(m : ℝ)| / N) = 2 * |(m : ℝ)| / N := by
    field_simp
  rw [this] at hj
  rw [show 2 * π * (m : ℝ) / N / 2 = π * m / N by ring]
  calc 4 * |(m : ℝ)| / N = 2 * (2 * |(m : ℝ)| / N) := by ring
    _ ≤ 2 * |Real.sin (π * m / N)| := by gcongr

/-- The character sum over an interval: for `x ≠ 0`,
`‖∑_{u < len} e((c + u) x / N)‖ ≤ N / (2 |x|)` with `|x| = |x.valMinAbs|`. -/
theorem norm_sum_stdAddChar_le {x : ZMod N} (hx : x ≠ 0) (c : ZMod N) (len : ℕ) :
    ‖∑ u ∈ range len, stdAddChar ((c + (u : ZMod N)) * x)‖ ≤ N / (2 * |(x.valMinAbs : ℝ)|) := by
  have hm0 : (x.valMinAbs : ℝ) ≠ 0 := by
    exact_mod_cast (ZMod.valMinAbs_eq_zero x).not.mpr hx
  have hmpos : 0 < |(x.valMinAbs : ℝ)| := abs_pos.mpr hm0
  set z := stdAddChar x with hz
  have hz1 : z ≠ 1 := by
    intro h
    apply hx
    apply injective_stdAddChar
    rw [← hz, h, AddChar.map_zero_eq_one]
  have hsum : ∑ u ∈ range len, stdAddChar ((c + (u : ZMod N)) * x) =
      stdAddChar (c * x) * ∑ u ∈ range len, z ^ u := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [add_mul, AddChar.map_add_eq_mul, hz, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hlow := four_mul_abs_valMinAbs_div_le_norm_stdAddChar_sub_one x
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  rw [hsum, norm_mul, AddChar.norm_apply, one_mul, geom_sum_eq hz1, norm_div]
  have hnum : ‖z ^ len - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hz, AddChar.norm_apply, one_pow, norm_one]
    norm_num
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  calc ‖z ^ len - 1‖ / ‖z - 1‖ ≤ 2 / (4 * |(x.valMinAbs : ℝ)| / N) := by
        gcongr
    _ = N / (2 * |(x.valMinAbs : ℝ)|) := by
        field_simp
        norm_num

end ZMod
