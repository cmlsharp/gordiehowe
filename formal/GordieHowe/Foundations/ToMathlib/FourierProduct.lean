-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

/-!
# Fourier expansion of product functions on `(ZMod N)^I`

With `e = ZMod.stdAddChar` and the normalized coefficients
`fourierCoeff g a = N⁻¹ · 𝓕 g a = N⁻¹ ∑_x e(-a x) g x`:

- `ZMod.sum_fourierCoeff_mul`: Fourier inversion, `∑_a fourierCoeff g a · e(a x) = g x`;
- `ZMod.prod_eq_sum_fourier`: a product function expands over characters of `(ZMod N)^I`,
  `∏_i g_i(u_i) = ∑_ξ (∏_i fourierCoeff g_i ξ_i) · e(ξ · u)`;
- `ZMod.sum_stdAddChar_dot`: orthogonality, `∑_u e(ξ · u) = N^|I|` for `ξ = 0` and `0` otherwise;
- `ZMod.dotAddChar`: `A ↦ e(ℓ A)` for an additive map `ℓ : M →+ ZMod N`, as a character of `M`.
-/

open Finset
open scoped BigOperators ZMod

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The normalized Fourier coefficient `N⁻¹ ∑_x e(-a x) g x`. -/
noncomputable def fourierCoeff (g : ZMod N → ℂ) (a : ZMod N) : ℂ := (N : ℂ)⁻¹ * 𝓕 g a

/-- Fourier inversion on `ZMod N`: `∑_a fourierCoeff g a · e(a x) = g x`. -/
theorem sum_fourierCoeff_mul (g : ZMod N → ℂ) (x : ZMod N) :
    ∑ a, fourierCoeff g a * stdAddChar (a * x) = g x := by
  have h := congrFun (LinearEquiv.symm_apply_apply (dft (N := N) (E := ℂ)) g) x
  rw [invDFT_apply, smul_eq_mul, Finset.mul_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fourierCoeff, smul_eq_mul]
  ring

/-- The dot-product character `e(ξ · u)` is the product of the coordinate characters. -/
theorem stdAddChar_dot {I : Type*} [Fintype I] (ξ u : I → ZMod N) :
    stdAddChar (∑ i, ξ i * u i) = ∏ i, stdAddChar (ξ i * u i) := by
  classical
  induction (univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

/-- A product function on `(ZMod N)^I` expands over the characters `e(ξ · u)`. -/
theorem prod_eq_sum_fourier {I : Type*} [Fintype I] [DecidableEq I] (g : I → ZMod N → ℂ)
    (u : I → ZMod N) :
    ∏ i, g i (u i) =
      ∑ ξ : I → ZMod N, (∏ i, fourierCoeff (g i) (ξ i)) * stdAddChar (∑ i, ξ i * u i) := by
  conv_lhs => rw [show (fun i => g i (u i)) = fun i => ∑ a, fourierCoeff (g i) a *
    stdAddChar (a * u i) from funext fun i => (sum_fourierCoeff_mul (g i) (u i)).symm]
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_congr _ _ fun ξ => ?_
  rw [stdAddChar_dot, ← Finset.prod_mul_distrib]

/-- The character `A ↦ e(ℓ A)` of `M` for an additive map `ℓ : M →+ ZMod N`. -/
noncomputable def dotAddChar {M : Type*} [AddCommGroup M] (ℓ : M →+ ZMod N) : AddChar M ℂ :=
  (stdAddChar : AddChar (ZMod N) ℂ).compAddMonoidHom ℓ

@[simp] theorem dotAddChar_apply {M : Type*} [AddCommGroup M] (ℓ : M →+ ZMod N) (A : M) :
    dotAddChar ℓ A = stdAddChar (ℓ A) := rfl

/-- Orthogonality on `(ZMod N)^I`: `∑_u e(ξ · u)` is `N^|I|` for `ξ = 0` and `0` otherwise. -/
theorem sum_stdAddChar_dot {I : Type*} [Fintype I] [DecidableEq I] (ξ : I → ZMod N) :
    ∑ u : I → ZMod N, stdAddChar (∑ i, ξ i * u i) =
      if ξ = 0 then (N : ℂ) ^ Fintype.card I else 0 := by
  split_ifs with hξ
  · subst hξ
    simp [Finset.card_univ, ZMod.card]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
    let ℓ : (I → ZMod N) →+ ZMod N :=
      { toFun := fun u => ∑ i, ξ i * u i
        map_zero' := by simp
        map_add' := fun u v => by simp [mul_add, Finset.sum_add_distrib] }
    have hne : dotAddChar ℓ ≠ 0 := by
      intro h
      have := congrArg (fun ψ : AddChar (I → ZMod N) ℂ => ψ (Pi.single i 1)) h
      simp only [dotAddChar_apply, AddChar.zero_apply] at this
      apply hi
      apply injective_stdAddChar
      rw [Pi.zero_apply, AddChar.map_zero_eq_one, ← this]
      congr 1
      simp [ℓ, Pi.single_apply]
    exact (AddChar.sum_eq_zero_iff_ne_zero.mpr hne)

end ZMod
