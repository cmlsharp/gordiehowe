-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.NegacyclicSpectrum
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Complex.Basic

public section

/-!
# Parseval's identity for the negacyclic transform over `ℂ`

For `f : Fin n → ℤ` and `n ≠ 0`, `spec f j` is the value of `f` at `ψ ^ (2j + 1)` with
`ψ = negRoot n = exp (π i / n)`, a primitive `2n`-th root of unity, and `specSq f j = ‖spec f j‖²`.

* `sum_norm_sq_dft`: Parseval for `dft` at a primitive `n`-th root of unity in `ℂ`,
  `∑ k, ‖dft ω a k‖² = n ∑ i, ‖a i‖²`.
* `sum_specSq`: `∑ j, specSq f j = n ∑ i, f i²`.
* `specSq_negacyclicConvCoeff`: `specSq (f ⋆ g) j = specSq f j · specSq g j`.
* `sum_sq_negacyclicConvCoeff`: `∑ i, (f ⋆ g)_i² = (1 / n) ∑ j, specSq f j · specSq g j`.
* `specSq_le_sq`, `sum_specSq_of_ternary`: for `f` with coefficients in `{-1, 0, 1}` and
  exactly `τ` of them nonzero, `specSq f j ≤ τ²` and `∑ j, specSq f j = n τ`.
-/

namespace GordieHowe.DFT

open Finset ComplexConjugate

variable {n : ℕ}

/-- **Parseval's identity for the transform over `ℂ`**: for a primitive `n`-th root of unity `ω`,
`∑ k, ‖dft ω a k‖² = n ∑ i, ‖a i‖²`. -/
theorem sum_norm_sq_dft {ω : ℂ} (hω : IsPrimitiveRoot ω n) (a : Fin n → ℂ) :
    ∑ k, ‖dft ω a k‖ ^ 2 = n * ∑ i, ‖a i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hconj : conj ω = ω⁻¹ := (Complex.inv_eq_conj (hω.norm'_eq_one hn.ne')).symm
  have hconj_dft : ∀ k : Fin n, conj (dft ω a k) =
      ∑ l : Fin n, conj (a l) * ω⁻¹ ^ ((k : ℕ) * l) := fun k => by
    simp only [dft, map_sum, map_mul, map_pow, hconj, Nat.mul_comm (k : ℕ)]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj']
  simp only [hconj_dft]
  simp only [dft, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have step : ∀ l : Fin n, ∑ k : Fin n, ∑ i : Fin n,
      a i * ω ^ ((i : ℕ) * k) * (conj (a l) * ω⁻¹ ^ ((k : ℕ) * l)) =
      ∑ i : Fin n, a i * conj (a l) *
        ∑ k : Fin n, ω ^ ((i : ℕ) * k) * ω⁻¹ ^ ((k : ℕ) * l) := fun l => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [step]
  rw [Finset.sum_comm]
  simp only [sum_pow_mul_inv_pow_eq hω, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The root `exp (π i / n)` of the negacyclic transform of length `n` over `ℂ`, written
`exp (2π i / (2n))`. -/
noncomputable def negRoot (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ))

/-- `negRoot n` is a primitive `2n`-th root of unity. -/
theorem isPrimitiveRoot_negRoot [NeZero n] : IsPrimitiveRoot (negRoot n) (2 * n) :=
  Complex.isPrimitiveRoot_exp (2 * n) (by have := NeZero.ne n; omega)

/-- `negRoot n ^ n = -1`. -/
theorem negRoot_pow [NeZero n] : negRoot n ^ n = -1 :=
  IsPrimitiveRoot.pow_half_eq_neg_one isPrimitiveRoot_negRoot (NeZero.ne n)

/-- `‖negRoot n‖ = 1`. -/
theorem norm_negRoot [NeZero n] : ‖negRoot n‖ = 1 :=
  isPrimitiveRoot_negRoot.norm'_eq_one (by have := NeZero.ne n; omega)

/-- **The negacyclic spectrum of an integer vector**: the value of `f` at `ψ ^ (2j + 1)`,
`ψ = negRoot n`. -/
noncomputable def spec (f : Fin n → ℤ) (j : Fin n) : ℂ :=
  negSpectrum (negRoot n) (fun i => (f i : ℂ)) j

/-- The squared norm of the negacyclic spectrum at frequency `j`. -/
noncomputable def specSq (f : Fin n → ℤ) (j : Fin n) : ℝ :=
  ‖spec f j‖ ^ 2

/-- The squared spectrum is nonnegative. -/
theorem specSq_nonneg (f : Fin n → ℤ) (j : Fin n) : 0 ≤ specSq f j :=
  sq_nonneg _

/-- The root of the negacyclic transform, `exp (2π i / (2n))`. -/
theorem negRoot_eq (n : ℕ) :
    negRoot n = Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ)) := by
  rw [negRoot]

/-- The spectrum at `j` is `∑ i, f i · ψ ^ (i (2j + 1))`. -/
theorem spec_eq_sum (f : Fin n → ℤ) (j : Fin n) :
    spec f j = ∑ i, (f i : ℂ) * negRoot n ^ ((i : ℕ) * (2 * j + 1)) := by
  rw [spec]
  rfl

/-- The squared spectrum is the squared norm of the spectrum. -/
theorem specSq_eq (f : Fin n → ℤ) (j : Fin n) : specSq f j = ‖spec f j‖ ^ 2 := by
  rw [specSq]

variable [NeZero n]

/-- **Parseval for the negacyclic spectrum**: `∑ j, specSq f j = n ∑ i, f i²`. -/
theorem sum_specSq (f : Fin n → ℤ) : ∑ j, specSq f j = n * ∑ i, (f i : ℝ) ^ 2 := by
  have h := sum_norm_sq_dft (IsPrimitiveRoot.sq_of_two_mul isPrimitiveRoot_negRoot (NeZero.ne n))
    (twist (negRoot n) fun i => (f i : ℂ))
  simp only [specSq, spec, negSpectrum_eq_dft, h, twist, norm_mul, norm_pow, norm_negRoot,
    one_pow, one_mul, Complex.norm_intCast, sq_abs]

/-- **The spectrum is multiplicative** on the negacyclic product. -/
theorem spec_negacyclicConvCoeff (f g : Fin n → ℤ) (j : Fin n) :
    spec (LatticeCrypto.negacyclicConvCoeff f g) j = spec f j * spec g j := by
  have hcast : (fun i => ((LatticeCrypto.negacyclicConvCoeff f g i : ℤ) : ℂ)) =
      LatticeCrypto.negacyclicConvCoeff (fun i => (f i : ℂ)) fun i => (g i : ℂ) := by
    funext i
    exact negacyclicConvCoeff_map (Int.castRingHom ℂ) f g i
  rw [spec, hcast, negSpectrum_negacyclicConvCoeff negRoot_pow]
  rfl

/-- **The squared spectrum is multiplicative** on the negacyclic product. -/
theorem specSq_negacyclicConvCoeff (f g : Fin n → ℤ) (j : Fin n) :
    specSq (LatticeCrypto.negacyclicConvCoeff f g) j = specSq f j * specSq g j := by
  rw [specSq, spec_negacyclicConvCoeff, norm_mul, mul_pow, specSq, specSq]

/-- **The squared norm of a negacyclic product**:
`∑ i, (f ⋆ g)_i² = (1 / n) ∑ j, specSq f j · specSq g j`. -/
theorem sum_sq_negacyclicConvCoeff (f g : Fin n → ℤ) :
    ∑ i, ((LatticeCrypto.negacyclicConvCoeff f g i : ℤ) : ℝ) ^ 2 =
      (1 / n) * ∑ j, specSq f j * specSq g j := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [← Finset.sum_congr rfl fun j _ => specSq_negacyclicConvCoeff f g j, sum_specSq]
  field_simp

/-- An integer of absolute value at most `1` has `|z| = z² = [z ≠ 0]` over `ℝ`. -/
theorem abs_eq_ite_of_abs_le_one {z : ℤ} (hz : |z| ≤ 1) :
    |(z : ℝ)| = (if z ≠ 0 then 1 else 0) ∧ (z : ℝ) ^ 2 = if z ≠ 0 then 1 else 0 := by
  have h := abs_le.1 hz
  obtain h | h | h : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  all_goals subst h; norm_num

/-- **A ternary vector's spectrum is at most its weight squared**: for `f` with coefficients
in `{-1, 0, 1}` and exactly `τ` of them nonzero, `specSq f j ≤ τ²`. -/
theorem specSq_le_sq {f : Fin n → ℤ} {τ : ℕ} (hf : ∀ i, |f i| ≤ 1)
    (hτ : (univ.filter fun i => f i ≠ 0).card = τ) (j : Fin n) : specSq f j ≤ (τ : ℝ) ^ 2 := by
  have hnorm : ‖spec f j‖ ≤ τ := by
    calc ‖spec f j‖
        = ‖∑ i, (f i : ℂ) * negRoot n ^ ((i : ℕ) * (2 * j + 1))‖ := rfl
      _ ≤ ∑ i, ‖(f i : ℂ) * negRoot n ^ ((i : ℕ) * (2 * j + 1))‖ := norm_sum_le _ _
      _ = ∑ i, (if f i ≠ 0 then 1 else 0 : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_pow, norm_negRoot, one_pow, mul_one, Complex.norm_intCast]
          exact (abs_eq_ite_of_abs_le_one (hf i)).1
      _ = τ := by rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hτ,
            nsmul_eq_mul, mul_one]
  rw [specSq]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **A ternary vector's spectrum sums to `n τ`**: for `f` with coefficients in `{-1, 0, 1}`
and exactly `τ` of them nonzero, `∑ j, specSq f j = n τ`. -/
theorem sum_specSq_of_ternary {f : Fin n → ℤ} {τ : ℕ} (hf : ∀ i, |f i| ≤ 1)
    (hτ : (univ.filter fun i => f i ≠ 0).card = τ) : ∑ j, specSq f j = n * τ := by
  rw [sum_specSq, Finset.sum_congr rfl fun i _ => (abs_eq_ite_of_abs_le_one (hf i)).2,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hτ, nsmul_eq_mul, mul_one]

end GordieHowe.DFT
