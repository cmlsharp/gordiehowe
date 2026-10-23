-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePacking

@[expose] public section

/-!
# A change of relative basis

A relative basis `β` of `K/E` with trace-dual `dual` (`RelativeBasis`) and a matrix `A` over `E`
with a right inverse `A'` (`Σ_l A_il A'_lj = δ_ij`, entries in `E`) give the relative basis
`β'_i = Σ_l A_il β_l` with trace-dual `dual'_j = Σ_l A'_lj dual_l` (`RelativeBasis.change`):
`Tr(dual'_j β'_i) = Σ_l A_il A'_lj = δ_ij` by `E`-linearity of the trace. The C++ packing stages use
power bases of a generator (`stage.h`, `power_basis`); a power basis of `1 + x` is a change of the
power basis of `x` by the binomial matrix.
-/

namespace GordieHowe.RelativePacking

variable {K : Type*} [Field K] {p : ℕ} [ExpChar K p] {m D : ℕ}

/-- The relative trace of a finite sum is the sum of the traces. -/
theorem relTrace_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    relTrace p m D (∑ i ∈ s, f i) = ∑ i ∈ s, relTrace p m D (f i) := by
  simp only [relTrace, phi_sum]
  exact Finset.sum_comm

/-- **A change of relative basis**: `β'_i = Σ_l A_il β_l` with trace-dual `dual'_j = Σ_l A'_lj
dual_l`, for matrices `A`, `A'` with entries in `E` (`hA`, `hA'`) and `A A' = 1` (`hinv`). -/
def RelativeBasis.change (B : RelativeBasis K p m D) (A A' : Fin D → Fin D → K)
    (hA : ∀ i l, A i l ∈ fixedField K p m) (hA' : ∀ l j, A' l j ∈ fixedField K p m)
    (hinv : ∀ i j, ∑ l, A i l * A' l j = if i = j then 1 else 0) : RelativeBasis K p m D where
  β i := ∑ l, A i l * B.β l
  dual j := ∑ l, A' l j * B.dual l
  trace_dual j i := by
    have h : (∑ l, A' l j * B.dual l) * (∑ l', A i l' * B.β l') =
        ∑ l, ∑ l', (A' l j * A i l') * (B.dual l * B.β l') := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h, relTrace_sum]
    simp_rw [relTrace_sum, relTrace_mul_left (mul_mem (hA' _ j) (hA i _)), B.trace_dual,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [show (if j = i then (1 : K) else 0) = if i = j then 1 else 0 from by
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h], ← hinv i j]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem RelativeBasis.change_β (B : RelativeBasis K p m D) (A A' : Fin D → Fin D → K) (hA hA' hinv)
    (i : Fin D) : (B.change A A' hA hA' hinv).β i = ∑ l, A i l * B.β l :=
  rfl

theorem RelativeBasis.change_dual (B : RelativeBasis K p m D) (A A' : Fin D → Fin D → K)
    (hA hA' hinv) (j : Fin D) : (B.change A A' hA hA' hinv).dual j = ∑ l, A' l j * B.dual l :=
  rfl

end GordieHowe.RelativePacking
