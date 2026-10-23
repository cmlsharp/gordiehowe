-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.Decoder
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.LinearMap.End

@[expose] public section

/-! # Linear combinations of received Reed–Solomon rows -/
namespace GordieHowe.RSCode
open scoped Classical
variable {F : Type*} [Field F] {R N : ℕ}

/-- The rows are fixed data; the coefficient vector is unrestricted. -/
def combination (U : Matrix F R N) : (Fin R → F) →ₗ[F] (Fin N → F) :=
  ∑ i, (LinearMap.proj i).smulRight (U i)

@[simp] theorem combination_apply (U : Matrix F R N) (r : Fin R → F) (j : Fin N) :
    combination U r j = ∑ i, r i * U i j := by
  simp [combination, LinearMap.smulRight_apply, Finset.sum_apply]

@[simp] theorem combination_single (U : Matrix F R N) (i : Fin R) :
    combination U (Pi.single i 1) = U i := by
  ext j
  simp [combination_apply, Pi.single_apply]

@[simp] theorem combination_cons (U : Matrix F (R+1) N) (s : F) (r : Fin R → F) :
    combination U (Fin.cons s r) = s • U 0 + combination (fun i => U i.succ) r := by
  ext j
  simp [combination_apply, Fin.sum_univ_succ]

end GordieHowe.RSCode
