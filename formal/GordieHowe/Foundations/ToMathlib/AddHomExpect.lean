-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Uniform elements through a surjective additive map

`expect_comp_of_surjective`: an additive surjection `Ψ : G → H` of finite additive groups sends
the uniform element of `G` to the uniform element of `H`, `𝔼_g F (Ψ g) = 𝔼_h F h`. Translating
`g` by a preimage of `h₀` shows `∑_g F (Ψ g) = ∑_g F (Ψ g + h₀)` for every `h₀`; averaging over
`h₀` gives `|H| ∑_g F (Ψ g) = |G| ∑_h F h`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

variable {G H : Type*} [AddGroup G] [Fintype G] [AddGroup H] [Fintype H]

/-- **An additive surjection preserves the uniform law**: for `Ψ (x + y) = Ψ x + Ψ y` and `Ψ`
surjective, `𝔼_g F (Ψ g) = 𝔼_h F h`. -/
theorem expect_comp_of_surjective {Ψ : G → H} (hadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ : Function.Surjective Ψ) (F : H → ℝ) : 𝔼 g, F (Ψ g) = 𝔼 h, F h := by
  have hshift : ∀ h₀ : H, ∑ g, F (Ψ g + h₀) = ∑ g, F (Ψ g) := fun h₀ => by
    obtain ⟨g₀, rfl⟩ := hΨ h₀
    simp_rw [← hadd]
    exact Fintype.sum_equiv (Equiv.addRight g₀) _ _ fun _ => rfl
  have hcount : (Fintype.card H : ℝ) * ∑ g, F (Ψ g) = Fintype.card G * ∑ h, F h := by
    calc (Fintype.card H : ℝ) * ∑ g, F (Ψ g) = ∑ h₀ : H, ∑ g, F (Ψ g + h₀) := by
          rw [Finset.sum_congr rfl fun h₀ _ => hshift h₀, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ = ∑ g, ∑ h₀ : H, F (Ψ g + h₀) := Finset.sum_comm
      _ = ∑ _g : G, ∑ h, F h := Finset.sum_congr rfl fun g _ =>
          Fintype.sum_equiv (Equiv.addLeft (Ψ g)) _ _ fun _ => rfl
      _ = Fintype.card G * ∑ h, F h := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hH : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.card_univ, div_eq_div_iff hG hH]
  rw [mul_comm, hcount, mul_comm]

end GordieHowe
