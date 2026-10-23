-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.OuterMeasure.Operations

@[expose] public section

/-!
# Born weights and operators given by their matrices

- `bornWeight v` is the outer measure on the computational basis that gives a set `S` of basis
  states the weight `∑ i ∈ S, ‖v i‖²`, the Born probability `prob S v` of measuring `v` in the
  computational basis and obtaining an outcome in `S`. For a unit vector it is the probability
  distribution `born v hv`.
- `kernelOp K` is the operator with matrix `K`: `(kernelOp K v) i = ∑ j, K i j * v j`, so
  `kernelOp K |j⟩ = ∑ i, K i j |i⟩`.

Everything here is about Mathlib objects only.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

variable {ι : Type*} [Fintype ι]

/-! ### Born weights -/

/-- **The Born weights of `v`**: the outer measure on the computational basis with
`bornWeight v S = ∑ i ∈ S, ‖v i‖²`, the probability of an outcome in `S` when `v` is measured in
the computational basis (`bornWeight_apply_eq_sum`). -/
noncomputable def bornWeight (v : QState ι) : OuterMeasure ι :=
  OuterMeasure.sum fun i => (‖v i‖ₑ ^ 2) • OuterMeasure.dirac i

/-- The Born weight of a set is the sum of the squared amplitudes of its elements. -/
theorem bornWeight_apply_eq_sum (v : QState ι) (S : Set ι) :
    bornWeight v S = ∑ i, S.indicator (fun i => ‖v i‖ₑ ^ 2) i := by
  rw [bornWeight, OuterMeasure.sum_apply, tsum_fintype]
  refine sum_congr rfl fun i _ => ?_
  rw [OuterMeasure.smul_apply, OuterMeasure.dirac_apply, smul_eq_mul]
  by_cases h : i ∈ S <;> simp [h]

theorem sum_enorm_sq (v : QState ι) : ∑ i, ‖v i‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  refine sum_congr rfl fun i _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **The Born distribution of a unit vector**: the law of the outcome of measuring `v` in the
computational basis, `Pr[i] = ‖v i‖²`. -/
noncomputable def born (v : QState ι) (hv : ‖v‖ = 1) : PMF ι :=
  PMF.ofFintype (fun i => ‖v i‖ₑ ^ 2) (by rw [sum_enorm_sq, hv]; simp)

/-! ### Operators given by their matrices -/

/-- **The operator with matrix `K`**: `(kernelOp K v) i = ∑ j, K i j * v j`. -/
noncomputable def kernelOp (K : ι → ι → ℂ) : QState ι →L[ℂ] QState ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun i => ∑ j, K i j * v j
      map_add' := fun v w => by
        ext i
        simp [mul_add, sum_add_distrib]
      map_smul' := fun c v => by
        ext i
        simp [mul_sum, mul_left_comm] }

@[simp]
theorem kernelOp_apply (K : ι → ι → ℂ) (v : QState ι) (i : ι) :
    kernelOp K v i = ∑ j, K i j * v j :=
  rfl

/-- An involutive matrix gives an involution: if `K · K = 1`, then `K (K v) = v`. -/
theorem kernelOp_kernelOp_of_inv [DecidableEq ι] {K : ι → ι → ℂ}
    (hinv : ∀ i k, ∑ j, K i j * K j k = if i = k then 1 else 0) (v : QState ι) :
    kernelOp K (kernelOp K v) = v := by
  ext i
  simp only [kernelOp_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hinv]
  simp

/-- A self-adjoint involutive matrix gives an isometry: if `K j i = conj (K i j)` and
`K · K = 1`, then `‖kernelOp K v‖ = ‖v‖`. -/
theorem norm_kernelOp_of_involutive [DecidableEq ι] {K : ι → ι → ℂ} (hsym : ∀ i j, K j i = star (K i j))
    (hinv : ∀ i k, ∑ j, K i j * K j k = if i = k then 1 else 0) (v : QState ι) :
    ‖kernelOp K v‖ = ‖v‖ := by
  have hKK : kernelOp K (kernelOp K v) = v := kernelOp_kernelOp_of_inv hinv v
  have hadj : ∀ w u : QState ι, inner ℂ (kernelOp K w) u = inner ℂ w (kernelOp K u) := by
    intro w u
    simp only [PiLp.inner_apply, kernelOp_apply, RCLike.inner_apply, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]
    simp only [RCLike.star_def]
    ring
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, hadj, hKK]

/-- The matrix `1 − 2 ∑_B u_B u_Bᵀ` of a reflection across the orthogonal complement of unit
vectors `u_B` with disjoint supports, written with `w = √2 · u`: `blk i` is the block of the basis
state `i` and `w i` the entry of `√2 u_B` at `i`, so the matrix is `1 − ∑_B w_B w_Bᵀ`. -/
def reflKernel [DecidableEq ι] {β : Type*} [DecidableEq β] (blk : ι → β)
    (w : ι → ℝ) (i j : ι) : ℂ :=
  (if i = j then 1 else 0) - (if blk i = blk j then ((w i * w j : ℝ) : ℂ) else 0)

theorem reflKernel_symm [DecidableEq ι] {β : Type*} [DecidableEq β] (blk : ι → β) (w : ι → ℝ)
    (i j : ι) : reflKernel blk w j i = star (reflKernel blk w i j) := by
  unfold reflKernel
  by_cases h : i = j
  · subst h
    simp [Complex.conj_ofReal]
  · have h' : j ≠ i := Ne.symm h
    by_cases hb : blk i = blk j
    · simp [h, h', hb, mul_comm, Complex.conj_ofReal]
    · simp [h, h', hb, Ne.symm hb]

/-- The reflection matrix is involutive when every block vector `u_B = w_B/√2` is a unit vector:
`∑_{j ∈ B} w j ^ 2 = 2`. -/
theorem reflKernel_inv [DecidableEq ι] {β : Type*} [DecidableEq β] (blk : ι → β) (w : ι → ℝ)
    (hn : ∀ i, w i ≠ 0 → ∑ j, (if blk j = blk i then w j ^ 2 else 0) = 2) (i k : ι) :
    ∑ j, reflKernel blk w i j * reflKernel blk w j k = if i = k then 1 else 0 := by
  set A : ι → ι → ℂ := fun i j => if blk i = blk j then ((w i * w j : ℝ) : ℂ) else 0
  have hK : ∀ i j, reflKernel blk w i j = (if i = j then 1 else 0) - A i j := fun _ _ => rfl
  have hAA : ∑ j, A i j * A j k = 2 * A i k := by
    by_cases hai : w i = 0
    · simp [A, hai]
    · have hsum := hn i hai
      by_cases hik : blk i = blk k
      · calc ∑ j, A i j * A j k
            = ∑ j, ((w i * w k : ℝ) : ℂ) * ((if blk j = blk i then w j ^ 2 else 0 : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases hj : blk j = blk i
              · have h1 : A i j = ((w i * w j : ℝ) : ℂ) := if_pos hj.symm
                have h2 : A j k = ((w j * w k : ℝ) : ℂ) := if_pos (hj.trans hik)
                rw [h1, h2, if_pos hj]
                push_cast
                ring
              · have hj' : blk i ≠ blk j := fun h => hj h.symm
                have hj'' : blk j ≠ blk k := fun h => hj (h.trans hik.symm)
                simp [A, hj', hj'', hj]
          _ = 2 * A i k := by
              rw [← Finset.mul_sum, ← Complex.ofReal_sum, hsum]
              simp only [A, if_pos hik]
              push_cast
              ring
      · refine (Finset.sum_eq_zero fun j _ => ?_).trans (by simp [A, hik])
        by_cases hj : blk i = blk j
        · have : blk j ≠ blk k := fun h => hik (hj.trans h)
          simp [A, this]
        · simp [A, hj]
  simp_rw [hK, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hAA]
  ring

/-- Composing operators multiplies their matrices. -/
theorem kernelOp_kernelOp (K₁ K₂ : ι → ι → ℂ) (v : QState ι) :
    kernelOp K₁ (kernelOp K₂ v) = kernelOp (fun i j => ∑ k, K₁ i k * K₂ k j) v := by
  ext i
  simp only [kernelOp_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- **A diagonal matrix between two reflections**: for `i ≠ j`,
`(R Φ R) i j = −[blk i = blk j] w i w j (φ i + φ j − ∑_{k ∈ blk j} w k² φ k)`. -/
theorem reflKernel_sandwich [DecidableEq ι] {β : Type*} [DecidableEq β] (blk : ι → β) (w : ι → ℝ)
    (φ : ι → ℂ) {i j : ι} (hij : i ≠ j) :
    ∑ k, reflKernel blk w i k * (φ k * reflKernel blk w k j) =
      -(if blk i = blk j then ((w i * w j : ℝ) : ℂ) *
        (φ i + φ j - ∑ k, (if blk k = blk j then ((w k ^ 2 : ℝ) : ℂ) * φ k else 0)) else 0) := by
  set A : ι → ι → ℂ := fun i j => if blk i = blk j then ((w i * w j : ℝ) : ℂ) else 0
  have hK : ∀ i j, reflKernel blk w i j = (if i = j then 1 else 0) - A i j := fun _ _ => rfl
  simp_rw [hK, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, if_neg hij]
  by_cases hb : blk i = blk j
  · have hAij : A i j = ((w i * w j : ℝ) : ℂ) := if_pos hb
    have hsum : ∑ k, A i k * (φ k * A k j) =
        ((w i * w j : ℝ) : ℂ) * ∑ k, (if blk k = blk j then ((w k ^ 2 : ℝ) : ℂ) * φ k else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : blk k = blk j
      · simp only [A, if_pos (hb.trans hk.symm), if_pos hk]
        push_cast
        ring
      · have hk' : blk i ≠ blk k := fun h => hk (h.symm.trans hb)
        simp [A, hk, hk']
    rw [if_pos hb, hsum, hAij]
    ring
  · have hAij : A i j = 0 := if_neg hb
    have hsum : ∑ k, A i k * (φ k * A k j) = 0 := Finset.sum_eq_zero fun k _ => by
      by_cases hk : blk i = blk k
      · have : blk k ≠ blk j := fun h => hb (hk.trans h)
        simp [A, this]
      · simp [A, hk]
    rw [if_neg hb, hsum, hAij]
    ring

/-- A block-diagonal matrix `K (r', s') (r, s) = [r' = r] M r s' s` with self-adjoint involutive
blocks is self-adjoint and involutive. -/
theorem blockKernel_symm {R S : Type*} [DecidableEq R] (M : R → S → S → ℂ)
    (hsym : ∀ r i j, M r j i = star (M r i j)) (b b' : R × S) :
    (if b.1 = b'.1 then M b'.1 b.2 b'.2 else 0) = star (if b'.1 = b.1 then M b.1 b'.2 b.2 else 0) := by
  by_cases h : b.1 = b'.1
  · rw [if_pos h, if_pos h.symm, h, hsym]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem blockKernel_inv {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (M : R → S → S → ℂ) (hinv : ∀ r i k, ∑ j, M r i j * M r j k = if i = k then 1 else 0)
    (b b' : R × S) :
    ∑ c : R × S, (if b.1 = c.1 then M c.1 b.2 c.2 else 0) * (if c.1 = b'.1 then M b'.1 c.2 b'.2 else 0) =
      if b = b' then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single b.1 (fun r _ hr => by simp [Ne.symm hr]) (by simp)]
  by_cases h : b.1 = b'.1
  · simp only [if_true, h]
    rw [hinv b'.1 b.2 b'.2]
    obtain ⟨b1, b2⟩ := b
    obtain ⟨c1, c2⟩ := b'
    simp only at h ⊢
    subst h
    simp
  · have : b ≠ b' := fun e => h (e ▸ rfl)
    simp [h, this]

/-! ### Relabelled bases and product states -/

section Relabel

variable {κ : Type*} [Fintype κ]

/-- The unitary `|i⟩ ↦ |σ i⟩` between the state spaces of two bases in bijection. -/
noncomputable def relabel (σ : ι ≃ κ) : QState ι ≃ₗᵢ[ℂ] QState κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ

@[simp]
theorem relabel_apply (σ : ι ≃ κ) (v : QState ι) (j : κ) : relabel σ v j = v (σ.symm j) :=
  rfl

@[simp]
theorem relabel_symm (σ : ι ≃ κ) : (relabel σ).symm = relabel σ.symm :=
  LinearIsometryEquiv.piLpCongrLeft_symm σ

/-- The Born distribution of a relabelled state is the relabelled Born distribution. -/
theorem born_relabel (σ : ι ≃ κ) (v : QState ι) (hv : ‖v‖ = 1) :
    born (relabel σ v) (by rw [LinearIsometryEquiv.norm_map, hv]) = (born v hv).map σ := by
  ext j
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (σ.symm j)]
  · simp [born]
  · intro i _ hi
    rw [if_neg]
    rintro rfl
    exact hi (σ.symm_apply_apply i).symm
  · simp

/-- The Born distribution of a permuted state is the permuted Born distribution. -/
theorem born_permOp (π : Equiv.Perm ι) (v : QState ι) (hv : ‖v‖ = 1) :
    born (permOp π v) (by rw [LinearIsometryEquiv.norm_map, hv]) = (born v hv).map π :=
  born_relabel π v hv

/-- The product state `v ⊗ |r⟩` with a basis state of a second register. -/
def tensorKet {R : Type*} [Fintype R] [DecidableEq R] (v : QState ι) (r : R) :
    QState (ι × R) :=
  WithLp.toLp 2 fun p => v p.1 * if p.2 = r then 1 else 0

variable {R : Type*} [Fintype R] [DecidableEq R]

@[simp]
theorem tensorKet_apply (v : QState ι) (r : R) (p : ι × R) :
    tensorKet v r p = v p.1 * if p.2 = r then 1 else 0 :=
  rfl

theorem norm_tensorKet (v : QState ι) (r : R) : ‖tensorKet v r‖ = ‖v‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single r (fun r' _ h => by simp [h]) (by simp)]
  simp

/-- The Born distribution of `v ⊗ |r⟩` is that of `v`, with the second register `r`. -/
theorem born_tensorKet (v : QState ι) (hv : ‖v‖ = 1) (r : R) :
    born (tensorKet v r) (by rw [norm_tensorKet, hv]) = (born v hv).map fun i => (i, r) := by
  ext ⟨i, r'⟩
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single i]
  · by_cases h : r' = r
    · subst h
      simp [born]
    · simp [born, h]
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Prod.ext_iff.1 h).1.symm
  · simp

end Relabel

/-- The Born weight of a set is the squared norm of the state's mask on it. -/
theorem bornWeight_apply (v : QState ι) (S : Set ι) : bornWeight v S = ‖mask S v‖ₑ ^ 2 := by
  classical
  rw [bornWeight, OuterMeasure.sum_apply, tsum_fintype]
  have hm : ‖mask S v‖ₑ ^ 2 = ENNReal.ofReal (‖mask S v‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hm, norm_mask_sq, ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OuterMeasure.smul_apply, OuterMeasure.dirac_apply]
  by_cases h : i ∈ S
  · simp [h, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  · simp [h]

end GordieHowe.Quantum
