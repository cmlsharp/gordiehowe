-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Total variation distance of joint laws with a uniform first coordinate

For a uniform `c` on a finite type and two families of laws `f c`, `g c`, the joint laws of
`(c, a)` with `a ← f c` and with `a ← g c` are at the average over `c` of the distances of
`f c` and `g c` (`tvDist_uniformOfFintype_bind_map_prodMk`). This is the statistical distance of
two views that share their uniform first part (the verifier's challenges in honest-verifier zero
knowledge), read conditionally on that part.

About Mathlib objects only; a candidate for upstreaming with `GordieHowe/Foundations/ToMathlib/PMFTV.lean`.
-/

open Finset
open scoped BigOperators

namespace PMF

variable {γ β : Type*} [Fintype γ] [Nonempty γ]

/-- **The joint law of a uniform `c` and `a ← f c`** at `(c, a)`: `f c a / |γ|`. -/
theorem uniformOfFintype_bind_map_prodMk_apply (f : γ → PMF β) (c : γ) (a : β) :
    (uniformOfFintype γ).bind (fun c => (f c).map (Prod.mk c)) (c, a) =
      (Fintype.card γ : ENNReal)⁻¹ * f c a := by
  rw [bind_apply, tsum_eq_single c fun c' hc' => ?_]
  · rw [uniformOfFintype_apply, map_apply, tsum_eq_single a fun a' ha' => ?_]
    · simp
    · simp [Ne.symm ha']
  · rw [map_apply, ENNReal.tsum_eq_zero.2 fun a' => ?_, mul_zero]
    simp [Ne.symm hc']

/-- **The distance of joint laws with a shared uniform first coordinate is the average
conditional distance**: for a uniform `c` on a finite type, the laws of `(c, a)` with `a ← f c`
and with `a ← g c` are at total variation distance `𝔼 c, tvDist (f c) (g c)`. -/
theorem tvDist_uniformOfFintype_bind_map_prodMk (f g : γ → PMF β) :
    tvDist ((uniformOfFintype γ).bind fun c => (f c).map (Prod.mk c))
        ((uniformOfFintype γ).bind fun c => (g c).map (Prod.mk c)) =
      𝔼 c, tvDist (f c) (g c) := by
  have hN : (Fintype.card γ : ENNReal)⁻¹ ≠ ⊤ := by simp
  rw [tvDist_eq_toReal_tsum_tsub]
  have hpt : ∀ z : γ × β,
      (uniformOfFintype γ).bind (fun c => (f c).map (Prod.mk c)) z -
        (uniformOfFintype γ).bind (fun c => (g c).map (Prod.mk c)) z =
      (Fintype.card γ : ENNReal)⁻¹ * (f z.1 z.2 - g z.1 z.2) := fun z => by
    rw [uniformOfFintype_bind_map_prodMk_apply, uniformOfFintype_bind_map_prodMk_apply,
      ENNReal.mul_sub fun _ _ => hN]
  rw [tsum_congr hpt, ENNReal.tsum_mul_left,
    ENNReal.tsum_prod (f := fun c a => f c a - g c a), tsum_fintype,
    ENNReal.toReal_mul, ENNReal.toReal_sum fun c _ => tsum_tsub_ne_top (f c) (g c),
    Fintype.expect_eq_sum_div_card, div_eq_inv_mul]
  simp only [tvDist_eq_toReal_tsum_tsub, ENNReal.toReal_inv, ENNReal.toReal_natCast]

end PMF
