-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.Quantum.Core.Born

@[expose] public section

/-!
# Linear maps given by rectangular matrices

- `kernelMap K` is the linear map between state spaces with matrix `K`:
  `(kernelMap K v) a = ∑ j, K a j * v j`, so `kernelMap K |j⟩ = ∑ a, K a j |a⟩`. The square case
  is `kernelOp` (`GordieHowe/Model/Quantum/Core/Born.lean`).
- A matrix whose columns indexed by a set `S` are orthonormal preserves inner products and norms
  of vectors supported in `S` (`inner_kernelMap`, `norm_kernelMap`).
- `piKernel K` is the matrix of a tensor product over a finite index type `X`: the bases are
  functions on `X` and `piKernel K d F = ∏ x, K x (d x) (F x)`. Products multiply entrywise
  (`sum_piKernel_mul`), and the column inner products of `piKernel K` are the products of those
  of the `K x` (`sum_star_piKernel_mul`).
- `idLeft K` is the matrix on a product basis `R × ι` that leaves the first register unchanged
  and applies `K r` to the second on the branch `r`; `idRight Q` leaves the second register
  unchanged and applies `Q` to the first. Matrices of the two forms commute (`idRight_comm`), and
  so do `controlled` unitaries and `idLeft` matrices independent of the branch
  (`controlled_kernelMap_idLeft`).

Everything here is about Mathlib objects only.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

section KernelMap

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- **The linear map with matrix `K`**: `(kernelMap K v) a = ∑ j, K a j * v j`. -/
noncomputable def kernelMap (K : κ → ι → ℂ) : QState ι →L[ℂ] QState κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 fun a => ∑ j, K a j * v j
      map_add' := fun v w => by
        ext a
        simp [mul_add, sum_add_distrib]
      map_smul' := fun c v => by
        ext a
        simp [mul_sum, mul_left_comm] }

@[simp]
theorem kernelMap_apply (K : κ → ι → ℂ) (v : QState ι) (a : κ) :
    kernelMap K v a = ∑ j, K a j * v j :=
  rfl

theorem kernelOp_eq_kernelMap (K : ι → ι → ℂ) : kernelOp K = kernelMap K :=
  rfl

/-- Composing linear maps multiplies their matrices. -/
theorem kernelMap_kernelMap (K : μ → κ → ℂ) (L : κ → ι → ℂ) (v : QState ι) :
    kernelMap K (kernelMap L v) = kernelMap (fun a b => ∑ c, K a c * L c b) v := by
  ext a
  simp only [kernelMap_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- A matrix whose nonzero entries link only basis states on corresponding sides of two masks
intertwines the masks. -/
theorem kernelMap_mask {K : κ → ι → ℂ} {S : Set ι} {S' : Set κ}
    (hK : ∀ a j, K a j ≠ 0 → (a ∈ S' ↔ j ∈ S)) (v : QState ι) :
    kernelMap K (mask S v) = mask S' (kernelMap K v) := by
  ext a
  rw [kernelMap_apply, mask_apply]
  by_cases ha : a ∈ S'
  · rw [Set.indicator_of_mem ha, kernelMap_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hk : K a j = 0
    · rw [hk, zero_mul, zero_mul]
    · rw [mask_apply_of_mem _ ((hK a j hk).1 ha)]
  · rw [Set.indicator_of_notMem ha]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hk : K a j = 0
    · rw [hk, zero_mul]
    · rw [mask_apply_of_notMem _ (fun h => ha ((hK a j hk).2 h)), mul_zero]

/-- The mask of a smaller set has a smaller norm. -/
theorem norm_mask_le_norm_mask {A A' : Set ι} (h : A ⊆ A') (v : QState ι) :
    ‖mask A v‖ ≤ ‖mask A' v‖ := by
  have : mask A v = mask A (mask A' v) := by
    ext i
    simp only [mask_apply]
    by_cases hi : i ∈ A
    · simp [hi, h hi]
    · simp [hi]
  rw [this]
  exact norm_mask_le _ _

/-- Matrices that agree on the columns indexed by `S` agree on vectors supported in `S`. -/
theorem kernelMap_congr {K K' : κ → ι → ℂ} {S : Set ι} (h : ∀ a, ∀ j ∈ S, K a j = K' a j)
    {v : QState ι} (hv : Supported S v) : kernelMap K v = kernelMap K' v := by
  ext a
  simp only [kernelMap_apply]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · rw [h a j hj]
  · rw [hv j hj, mul_zero, mul_zero]

/-- A matrix whose columns indexed by `S` are orthonormal preserves the inner product of vectors
supported in `S`. -/
theorem inner_kernelMap [DecidableEq ι] {K : κ → ι → ℂ} {S : Set ι}
    (hK : ∀ i ∈ S, ∀ j ∈ S, ∑ a, star (K a i) * K a j = if i = j then 1 else 0)
    {v w : QState ι} (hv : Supported S v) (hw : Supported S w) :
    inner ℂ (kernelMap K v) (kernelMap K w) = inner ℂ v w := by
  simp only [PiLp.inner_apply, kernelMap_apply, RCLike.inner_apply]
  calc ∑ a, (∑ j, K a j * w j) * (starRingEnd ℂ) (∑ i, K a i * v i)
      = ∑ i, ∑ j, star (v i) * w j * ∑ a, star (K a i) * K a j := by
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => ?_
        simp only [RCLike.star_def]
        ring
    _ = ∑ i, w i * (starRingEnd ℂ) (v i) := by
        refine sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp), hK i hi i hi, if_pos rfl,
            mul_one, RCLike.star_def, mul_comm]
          by_cases hj' : j ∈ S
          · rw [hK i hi j hj', if_neg (Ne.symm hj), mul_zero]
          · rw [hw j hj', mul_zero, zero_mul]
        · simp [hv i hi]

/-- A matrix whose columns indexed by `S` are orthonormal preserves the norm of vectors supported
in `S`. -/
theorem norm_kernelMap [DecidableEq ι] {K : κ → ι → ℂ} {S : Set ι}
    (hK : ∀ i ∈ S, ∀ j ∈ S, ∑ a, star (K a i) * K a j = if i = j then 1 else 0)
    {v : QState ι} (hv : Supported S v) : ‖kernelMap K v‖ = ‖v‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_kernelMap hK hv hv]

/-- A matrix with orthonormal columns is an isometry. -/
theorem norm_kernelMap_univ [DecidableEq ι] {K : κ → ι → ℂ}
    (hK : ∀ i j, ∑ a, star (K a i) * K a j = if i = j then 1 else 0) (v : QState ι) :
    ‖kernelMap K v‖ = ‖v‖ :=
  norm_kernelMap (S := Set.univ) (fun i _ j _ => hK i j) fun _ h => absurd trivial h

/-- The image of a basis vector is the column of the matrix. -/
theorem kernelMap_single [DecidableEq ι] (K : κ → ι → ℂ) (j : ι) :
    kernelMap K (EuclideanSpace.single j 1) = WithLp.toLp 2 fun a => K a j := by
  ext a
  simp [PiLp.single_apply]

/-- Two continuous linear maps that agree on the basis vectors of `S` agree on vectors supported
in `S`. -/
theorem eq_of_supported [DecidableEq ι] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f g : QState ι →ₗ[ℂ] E) {S : Set ι}
    (h : ∀ j ∈ S, f (EuclideanSpace.single j 1) = g (EuclideanSpace.single j 1))
    {v : QState ι} (hv : Supported S v) : f v = g v := by
  have hsum : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
    ext i
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      PiLp.ofLp_single, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  rw [hsum, map_sum, map_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · rw [map_smul, map_smul, h j hj]
  · rw [hv j hj, zero_smul, map_zero, map_zero]

end KernelMap

/-! ### Tensor products over a finite index type -/

section Pi

variable {X : Type*} [Fintype X] [DecidableEq X] {O Y Z : Type*} [Fintype Y]

/-- **The matrix of a tensor product over `X`**: `piKernel K d F = ∏ x, K x (d x) (F x)`. -/
def piKernel (K : X → O → Y → ℂ) (d : X → O) (F : X → Y) : ℂ :=
  ∏ x, K x (d x) (F x)

/-- The product of two tensor-product matrices is the tensor product of the products. -/
theorem sum_piKernel_mul (K : X → O → Y → ℂ) (L : X → Y → Z → ℂ) (d : X → O) (h : X → Z) :
    ∑ F, piKernel K d F * piKernel L F h =
      piKernel (fun x o z => ∑ y, K x o y * L x y z) d h := by
  simp only [piKernel, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun x y => K x (d x) y * L x y (h x)).symm

variable [Fintype O]

omit [Fintype Y] in
/-- The column inner products of a tensor-product matrix are the products of those of its
factors. -/
theorem sum_star_piKernel_mul (K : X → O → Y → ℂ) (F F' : X → Y) :
    ∑ d, star (piKernel K d F) * piKernel K d F' =
      ∏ x, ∑ o, star (K x o (F x)) * K x o (F' x) := by
  simp only [piKernel, RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun x o => (starRingEnd ℂ) (K x o (F x)) * K x o (F' x)).symm

omit [Fintype Y] in
/-- A tensor product of matrices with orthonormal columns has orthonormal columns. -/
theorem piKernel_orthonormal [DecidableEq Y] {K : X → O → Y → ℂ}
    (hK : ∀ x i j, ∑ o, star (K x o i) * K x o j = if i = j then 1 else 0) (F F' : X → Y) :
    ∑ d, star (piKernel K d F) * piKernel K d F' = if F = F' then 1 else 0 := by
  rw [sum_star_piKernel_mul]
  simp only [hK]
  by_cases h : F = F'
  · simp [h]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

omit [DecidableEq X] [Fintype Y] in
/-- The tensor product of identity matrices is the identity matrix. -/
theorem piKernel_ite_eq [DecidableEq Y] (d F : X → Y) :
    piKernel (fun _ (o y : Y) => if o = y then (1 : ℂ) else 0) d F = if d = F then 1 else 0 := by
  by_cases h : d = F
  · simp [piKernel, h]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

end Pi

/-! ### Registers left unchanged -/

section Registers

variable {R ρ ι κ : Type*} [Fintype R] [Fintype ρ] [Fintype ι] [Fintype κ] [DecidableEq R]
  [DecidableEq ι]

/-- **The matrix that leaves the first register unchanged** and applies `K r` to the second on
the branch `r`. -/
def idLeft (K : R → κ → ι → ℂ) (b' : R × κ) (b : R × ι) : ℂ :=
  if b'.1 = b.1 then K b.1 b'.2 b.2 else 0

omit [DecidableEq ι] in
@[simp]
theorem kernelMap_idLeft_apply (K : R → κ → ι → ℂ) (v : QState (R × ι)) (r : R) (a : κ) :
    kernelMap (idLeft K) v (r, a) = ∑ j, K r a j * v (r, j) := by
  rw [kernelMap_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single r (fun r' _ h => by simp [idLeft, Ne.symm h]) (by simp)]
  simp [idLeft]

omit [Fintype ι] [DecidableEq ι] in
/-- The column inner products of `idLeft K`. -/
theorem sum_star_idLeft_mul (K : R → κ → ι → ℂ) (b c : R × ι) :
    ∑ b', star (idLeft K b' b) * idLeft K b' c =
      if b.1 = c.1 then ∑ a, star (K b.1 a b.2) * K b.1 a c.2 else 0 := by
  rw [Fintype.sum_prod_type,
    Finset.sum_eq_single b.1 (fun r _ h => by simp [idLeft, h]) (by simp)]
  by_cases h : b.1 = c.1
  · simp [idLeft, h]
  · simp [idLeft, h]

omit [Fintype ι] in
/-- If every `K r` has orthonormal columns on `S r`, then `idLeft K` has orthonormal columns on
the basis states `(r, j)` with `j ∈ S r`. -/
theorem idLeft_orthonormal {K : R → κ → ι → ℂ} {S : R → Set ι}
    (hK : ∀ r, ∀ i ∈ S r, ∀ j ∈ S r, ∑ a, star (K r a i) * K r a j = if i = j then 1 else 0) :
    ∀ b ∈ {b : R × ι | b.2 ∈ S b.1}, ∀ c ∈ {b : R × ι | b.2 ∈ S b.1},
      ∑ b', star (idLeft K b' b) * idLeft K b' c = if b = c then 1 else 0 := by
  rintro ⟨r, i⟩ hi ⟨r', j⟩ hj
  rw [sum_star_idLeft_mul]
  by_cases h : r = r'
  · subst h
    simp only [if_true]
    rw [hK r i hi j hj]
    simp
  · simp [h]

/-- The product state `|r⟩ ⊗ v` of a basis state of the first register and a vector of the
second. -/
def ketTensor (r : R) (v : QState ι) : QState (R × ι) :=
  WithLp.toLp 2 fun b => if b.1 = r then v b.2 else 0

omit [DecidableEq ι] in
/-- `idLeft K` maps `|r⟩ ⊗ v` to `|r⟩ ⊗ K r v`. -/
theorem kernelMap_idLeft_ketTensor (K : R → κ → ι → ℂ) (r : R) (v : QState ι) :
    kernelMap (idLeft K) (ketTensor r v) = ketTensor r (kernelMap (K r) v) := by
  ext ⟨r', a⟩
  rw [kernelMap_idLeft_apply]
  by_cases h : r' = r
  · subst h
    simp [ketTensor]
  · simp [ketTensor, h]

/-- The image of a basis vector under `idLeft K`. -/
theorem kernelMap_idLeft_single (K : R → κ → ι → ℂ) (r : R) (j : ι) :
    kernelMap (idLeft K) (EuclideanSpace.single (r, j) 1) =
      ketTensor r (WithLp.toLp 2 fun a => K r a j) := by
  ext ⟨r', a⟩
  rw [kernelMap_idLeft_apply]
  by_cases h : r' = r
  · subst h
    simp [ketTensor]
  · simp [ketTensor, h]

/-- **The matrix that leaves the second register unchanged** and applies `Q` to the first. -/
def idRight {L : Type*} [DecidableEq L] (Q : ρ → R → ℂ) (b' : ρ × L) (b : R × L) : ℂ :=
  if b'.2 = b.2 then Q b'.1 b.1 else 0

omit [DecidableEq R] in
@[simp]
theorem kernelMap_idRight_apply {L : Type*} [Fintype L] [DecidableEq L] (Q : ρ → R → ℂ)
    (v : QState (R × L)) (r : ρ) (s : L) :
    kernelMap (idRight Q) v (r, s) = ∑ r', Q r r' * v (r', s) := by
  rw [kernelMap_apply, Fintype.sum_prod_type]
  refine sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single s (fun s' _ h => by simp [idRight, Ne.symm h]) (by simp)]
  simp [idRight]

/-- A matrix acting on the first register commutes with a matrix acting on the second. -/
theorem idRight_comm [DecidableEq κ] (Q : R → R → ℂ) (C : κ → ι → ℂ) (v : QState (R × ι)) :
    kernelMap (idRight Q) (kernelMap (idLeft fun _ => C) v) =
      kernelMap (idLeft fun _ => C) (kernelMap (idRight Q) v) := by
  ext ⟨r, s⟩
  simp only [kernelMap_idRight_apply, kernelMap_idLeft_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

omit [DecidableEq ι] in
/-- A unitary on the first register commutes with a matrix on the second. -/
theorem controlled_kernelMap_idLeft (U : QState R ≃ₗᵢ[ℂ] QState R) (C : κ → ι → ℂ)
    (v : QState (R × ι)) :
    controlled (fun _ => U) (kernelMap (idLeft fun _ => C) v) =
      kernelMap (idLeft fun _ => C) (controlled (fun _ => U) v) := by
  ext ⟨r, a⟩
  rw [controlled_apply, kernelMap_idLeft_apply]
  have h : (WithLp.toLp 2 fun r' => kernelMap (idLeft fun _ => C) v (r', a) : QState R) =
      ∑ j, C a j • (WithLp.toLp 2 fun r' => v (r', j) : QState R) := by
    ext r'
    simp only [kernelMap_idLeft_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
  rw [h, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  rfl

end Registers

end GordieHowe.Quantum
