-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureRun
public import GordieHowe.Model.Quantum.Core.Dilation

@[expose] public section

/-!
# Unitary channels for tests

Unitary channels for the residual-state tests (`IAlg.QTest`,
`GordieHowe/Model/Quantum/Interactive/Test.lean`) that follow the pure run of an adversary (`IAlg.pureRun`,
`GordieHowe/Model/Quantum/Interactive/PureRun.lean`).

- `KrausChannel.ofUnitary U hU`: the channel with the one unitary operator `U`; `unitaryMat L`,
  the matrix of a unitary `L` of the state space; `rotateTo ψ hψ i₀`, a unitary that maps the unit
  vector `ψ` to the basis vector at `i₀` (from `extendUnitary`, `GordieHowe/Model/Quantum/Core/Dilation.lean`).
-/

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Unitary channels -/

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem matApply_mul (M N : Matrix ι ι ℂ) (v : QState ι) :
    matApply (M * N) v = matApply M (matApply N v) := by
  ext i
  simp only [matApply_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem matApply_submatrix_perm (M : Matrix ι ι ℂ) (π : Equiv.Perm ι) (v : QState ι) :
    matApply (M.submatrix π.symm (Equiv.refl ι)) v = permOp π (matApply M v) := by
  ext i
  simp [matApply_apply, permOp_apply]

theorem permMat_conjTranspose_mul (π : Equiv.Perm ι) :
    ((1 : Matrix ι ι ℂ).submatrix π.symm (Equiv.refl ι))ᴴ *
      (1 : Matrix ι ι ℂ).submatrix π.symm (Equiv.refl ι) = 1 := by
  rw [conjTranspose_submatrix, conjTranspose_one, submatrix_mul_equiv, one_mul]
  exact submatrix_id_id 1

/-- **The channel with one unitary operator** `U`. -/
def KrausChannel.ofUnitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) : KrausChannel Unit ι ι where
  op _ := U
  sum_conjTranspose_mul := by
    rw [Fintype.sum_unique]
    exact hU

theorem KrausChannel.ofUnitary_pureAt (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    (KrausChannel.ofUnitary U hU).toKrausMap.PureAt () U :=
  KrausChannel.pureAt_toKrausMap rfl fun r hr => absurd (Subsingleton.elim r ()) hr

/-- **The matrix of a unitary** `L` of the state space: column `j` is `L` of the basis vector
at `j`. -/
noncomputable def unitaryMat (L : QState ι ≃ₗᵢ[ℂ] QState ι) : Matrix ι ι ℂ :=
  fun i j => L (EuclideanSpace.single j 1) i

theorem matApply_unitaryMat (L : QState ι ≃ₗᵢ[ℂ] QState ι) (v : QState ι) :
    matApply (unitaryMat L) v = L v := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  ext i
  rw [matApply_apply]
  conv_rhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, unitaryMat]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem unitaryMat_conjTranspose_mul (L : QState ι ≃ₗᵢ[ℂ] QState ι) :
    (unitaryMat L)ᴴ * unitaryMat L = 1 := by
  ext j k
  have h := L.inner_map_map (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single k 1)
  rw [PiLp.inner_apply, EuclideanSpace.inner_single_left] at h
  simp only [RCLike.inner_apply, map_one, one_mul, PiLp.single_apply] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, unitaryMat, RCLike.star_def]
  rw [Finset.sum_congr rfl fun i _ => mul_comm _ _, h]

/-- **A unitary that maps the unit vector `ψ` to the basis vector at `i₀`**: on the line of `ψ`
the map `v ↦ ⟪ψ, v⟫ e_{i₀}`, extended to a unitary (`extendUnitary`). -/
noncomputable def rotateTo (ψ : QState ι) (hψ : ‖ψ‖ = 1) (i₀ : ι) : QState ι ≃ₗᵢ[ℂ] QState ι :=
  extendUnitary (ℂ ∙ ψ) ((innerₛₗ ℂ ψ).smulRight (EuclideanSpace.single i₀ (1 : ℂ)))
    fun v hv => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp [innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K, hψ, norm_smul]

theorem rotateTo_apply_self (ψ : QState ι) (hψ : ‖ψ‖ = 1) (i₀ : ι) :
    rotateTo ψ hψ i₀ ψ = EuclideanSpace.single i₀ 1 := by
  rw [rotateTo, extendUnitary_apply_of_mem _ _ _ (Submodule.mem_span_singleton_self ψ)]
  simp [inner_self_eq_norm_sq_to_K, hψ]

end Unitary

end GordieHowe.Quantum
