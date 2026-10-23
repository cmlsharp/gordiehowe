-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskedConstraintTest

@[expose] public section

/-!
# Several scalar checks of one masked polynomial response

All functionals share one coefficient vector, one committed arbitrary mask,
and one response polynomial. A false claim selects a violated functional from
the source equations before either challenge or response. Thus the algebraic
error remains `1 / |F|`, without a factor for the number of functionals.
-/

namespace GordieHowe.Ligero.MaskedConstraintFamily

open Polynomial
open scoped Classical

variable {F : Type} [Field F] {N n m : ℕ}

/-- All source equations tested by the family of scalar functionals. -/
def Claim (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) : Prop :=
  ∀ j i, check j (g i) = target j i

theorem exists_violated (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) (hfalse : ¬ Claim check g target) :
    ∃ j, ∃ i, check j (g i) ≠ target j i := by
  simpa only [Claim, not_forall] using hfalse

/-- This choice depends only on the fixed source claim, not on the mask,
random coefficients, response, or queries. -/
noncomputable def chosenCheck (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) (hfalse : ¬ Claim check g target) : Fin m :=
  Classical.choose (exists_violated check g target hfalse)

theorem chosenCheck_violated (check : Fin m → (F[X] →ₗ[F] F)) (g : Fin n → F[X])
    (target : Fin m → Fin n → F) (hfalse : ¬ Claim check g target) :
    ∃ i, check (chosenCheck check g target hfalse) (g i) ≠
      target (chosenCheck check g target hfalse) i :=
  Classical.choose_spec (exists_violated check g target hfalse)

end GordieHowe.Ligero.MaskedConstraintFamily
