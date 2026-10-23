-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.FieldSkip

@[expose] public section

/-!
# Event degrees and operand evaluation for the field-generic skip zerocheck

Facts about the skip zerocheck of `Sumcheck.FieldSkip` (`lib/gordiehowe/compiler/field_skip.h`):

* **The events' degrees** (`rEvent_deg`, `roundEvent_deg`, `uEvent_deg`): the skip event has
  degree `D * (w - 1)`, each round event degree `D + 1` and the terminal event degree `1`.
* **Operand evaluation by field operations** (`opEvalDec`): operand `j`'s multilinear extension
  at `(s, r)` computed through `SkipPoints.interpEval`, equal to `opEval` (`opEvalDec_eq`). With
  `X` substituted at coordinate `i`, an operand's multilinear extension is the line through its
  values at `0` and `1` there (`eval₂_mle_opTable`).
* **Batching is linear** (`batch_sub`): `batch u (x - y) = batch u x - batch u y`.
-/

namespace GordieHowe.Sumcheck.FieldSkip

open Polynomial

variable {K : Type} [Field K] {k m : ℕ}

/-! ### The events' degrees

Facts about `FieldSkip`'s events, stated here because `GordieHowe/ProofSystem/Zerocheck/FieldSkip.lean` is imported by
the whole hash stack. -/

section Degrees

variable {w D n k : ℕ} (R : Relation K k D) (ops : Operands K w n k) (dom : SkipPoints K w D)

theorem rEvent_deg [NeZero D] (ρ : Fin n → K) (skip : Fin ((D - 1) * (w - 1)) → K) :
    (rEvent R ops dom ρ skip).deg = D * (w - 1) := rfl

theorem roundEvent_deg (ρ : Fin n → K) (r : K) (skip : Fin ((D - 1) * (w - 1)) → K)
    (msg : Fin n → Fin D → K) (s : Fin n → K) (i : Fin n) :
    (roundEvent R ops dom ρ r skip msg s i).deg = D + 1 := rfl

theorem uEvent_deg (s : Fin n → K) (r : K) (x : Fin k → K) : (uEvent ops dom s r x).deg = 1 :=
  rfl

end Degrees

/-! ### Operand evaluation by field operations

`opEvalDec` computes an operand's multilinear extension at `(s, r)` by field operations, the value
the C++ prover computes (`MaskedFieldSkip::prove`); it equals `opEval` (`opEvalDec_eq`). -/

section Executable

open GKR.ClaimEvaluation (evalTable mle value)

section AnyDegree

variable {w n k D : ℕ} (ops : Operands K w n k) (dom : SkipPoints K w D)

/-- Operand `j`'s multilinear extension at `(s, r)` by field operations (`SkipPoints.interpEval`),
equal to `opEval` (`opEvalDec_eq`). -/
def opEvalDec (j : Fin k) (s : Fin n → K) (r : K) : K :=
  evalTable (fun row => dom.interpEval (fun z => ops row z j) r) s

theorem opEvalDec_eq (j : Fin k) (s : Fin n → K) (r : K) :
    opEvalDec ops dom j s r = opEval ops dom j s r := by
  simp only [opEvalDec, opEval, SkipPoints.eval_interp]

/-- An operand's multilinear extension with `X` substituted at coordinate `i` is the line through
its values at `0` and `1` there. -/
theorem eval₂_mle_opTable (i : Fin n) (e : Fin n → K) (j : Fin k) (r : K) :
    MvPolynomial.eval₂ Polynomial.C (Function.update (Polynomial.C ∘ e) i Polynomial.X)
        (mle (opTable ops dom j r)) =
      Polynomial.C (opEvalDec ops dom j (Function.update e i 0) r) +
        Polynomial.C (opEvalDec ops dom j (Function.update e i 1) r -
          opEvalDec ops dom j (Function.update e i 0) r) * Polynomial.X := by
  rw [GKR.LayerSumcheck.eval₂_update_X_of_degreeOf_le_one _ _ _
    (GKR.ClaimEvaluation.mle_degreeOf_le _ i)]
  simp only [GKR.ClaimEvaluation.eval_mle, value_opTable, opEvalDec_eq]

end AnyDegree

end Executable

end GordieHowe.Sumcheck.FieldSkip

namespace GordieHowe.Sumcheck.FieldSkipPads

open FieldSkip

variable {K : Type} [Field K] {w n k m : ℕ}

theorem batch_sub (u x y : Fin k → K) : batch u (x - y) = batch u x - batch u y := by
  simp [batch, mul_sub, Finset.sum_sub_distrib]

end GordieHowe.Sumcheck.FieldSkipPads
