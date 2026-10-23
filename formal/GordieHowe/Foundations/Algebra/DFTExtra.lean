-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.DFT

@[expose] public section

/-!
# Further facts about transforms, convolutions and roots of unity

General facts the transform-based row evaluators use beside those of `GordieHowe.Foundations.Algebra.DFT`: the transform
commutes with negation, cyclic convolution with a reversed vector is a correlation, and a primitive
root of order `2n` supplies the `ψ ^ n = -1` and the primitive `n`-th root `ψ ^ 2` of the negacyclic
transform.
-/

namespace GordieHowe.DFT

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

theorem dft_neg (ω : R) (a : Fin n → R) : dft ω (-a) = -dft ω a := by
  funext k
  simp [dft, Finset.sum_neg_distrib]

/-- `dft` is linear in its input: scaling every coefficient by a constant
scales the transform by the same constant. -/
theorem dft_smul (ω c : R) (a : Fin n → R) : dft ω (fun j => c * a j) = fun k => c * dft ω a k := by
  funext k
  simp only [dft, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [CommRing R] in
theorem rev_apply (v : Fin n → R) (a : Fin n) : rev v a = v (-a) := by
  rw [Fin.neg_def]
  rfl

/-- Cyclic convolution with a reversed vector is the cyclic correlation. -/
theorem cyclicConv_rev_apply (u v : Fin n → R) (k : Fin n) :
    cyclicConv u (rev v) k = ∑ a, u (k + a) * v a := by
  have : NeZero n := ⟨fun h => by subst h; exact k.elim0⟩
  have hidx : ∀ i j : Fin n, ((i : ℕ) + j) % n = k ↔ j = k - i := by
    intro i j
    rw [eq_sub_iff_add_eq', Fin.ext_iff, Fin.val_add]
  simp only [cyclicConv, Fintype.sum_prod_type, hidx, rev_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact Fintype.sum_equiv (Equiv.addLeft k).symm _ _ fun i => by simp [sub_eq_neg_add]

end CommRing

section Field

variable {F : Type*} [Field F] {n : ℕ} {ψ : F}

/-- A primitive root of order `2n` has `ψ ^ n = -1`. -/
theorem IsPrimitiveRoot.pow_half_eq_neg_one (hψ : IsPrimitiveRoot ψ (2 * n)) (hn : n ≠ 0) :
    ψ ^ n = -1 :=
  (hψ.pow (by omega) (by ring)).eq_neg_one_of_two_right

/-- The square of a primitive root of order `2n` is a primitive `n`-th root. -/
theorem IsPrimitiveRoot.sq_of_two_mul (hψ : IsPrimitiveRoot ψ (2 * n)) (hn : n ≠ 0) :
    IsPrimitiveRoot (ψ ^ 2) n :=
  hψ.pow (by omega) rfl

end Field

end GordieHowe.DFT
