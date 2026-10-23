-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import GordieHowe.Language.Realizations.Range

@[expose] public section

/-!
# `Range.reconstruct` as a weighted digit sum

`Range.reconstruct` is defined by folding over a list of limbs; this file restates it as a
`Finset.sum` over `Fin k`, which is what the telescoping arguments of `GordieHowe.Falcon512.NativeNorm` need to relate
a reconstructed wire to its natural-number ripple-carry digit chain.
-/

namespace GordieHowe.Range

variable {K : Type*} [Field K]

/-- Reconstruction of `k` fixed-width limbs is their base-`B` weighted sum. -/
theorem reconstruct_eq_sum {k B : ℕ} (f : Fin k → K) :
    reconstruct B (List.ofFn f) = ∑ l : Fin k, f l * (B : K) ^ (l : ℕ) := by
  induction k with
  | zero => simp [reconstruct]
  | succ k ih =>
      rw [List.ofFn_succ, reconstruct_cons, Fin.sum_univ_succ, ih fun i => f i.succ]
      have hshift : ∀ i : Fin k,
          f i.succ * (B : K) ^ (i.succ : ℕ) = (f i.succ * (B : K) ^ (i : ℕ)) * (B : K) := by
        intro i
        rw [Fin.val_succ, pow_succ]
        ring
      simp only [hshift, ← Finset.sum_mul, Fin.val_zero, pow_zero, mul_one]
      ring

/-- Reconstruction of limbs that are each the cast of a natural digit is the
cast of the natural-valued weighted digit sum. -/
theorem reconstruct_natCast {k B : ℕ} (dig : Fin k → ℕ) (f : Fin k → K)
    (hf : ∀ l, (dig l : K) = f l) :
    reconstruct B (List.ofFn f) = ((∑ l : Fin k, dig l * B ^ (l : ℕ) : ℕ) : K) := by
  rw [reconstruct_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun l _ => by rw [hf l]

end GordieHowe.Range
