-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# Finite systems of quadratic equations

The generic Ligero constraint-test boundary consumes actual multivariate polynomials of total degree
at most two. A predicate supplied by a caller is not a substitute for this representation.
-/

namespace GordieHowe

open MvPolynomial

/-- A finite family of polynomial equations, each of total degree at most two. -/
structure QuadraticSystem (F ι : Type) [CommRing F] where
  Eq : Type
  [finiteEq : Fintype Eq]
  polynomial : Eq → MvPolynomial ι F
  degree : ∀ e, (polynomial e).totalDegree ≤ 2

attribute [instance] QuadraticSystem.finiteEq

namespace QuadraticSystem

variable {F ι : Type} [CommRing F]

/-- Every equation vanishes on the same assignment. -/
def Holds (S : QuadraticSystem F ι) (w : ι → F) : Prop :=
  ∀ e, MvPolynomial.eval w (S.polynomial e) = 0

/-- Combine two finite equation families without changing their variables. -/
def and (S T : QuadraticSystem F ι) : QuadraticSystem F ι where
  Eq := S.Eq ⊕ T.Eq
  polynomial := Sum.elim S.polynomial T.polynomial
  degree := by rintro (e | e); exact S.degree e; exact T.degree e

@[simp] theorem holds_and (S T : QuadraticSystem F ι) (w : ι → F) :
    (S.and T).Holds w ↔ S.Holds w ∧ T.Holds w := by
  simp [Holds, and, Sum.forall]

/-- Reindex every equation's variables along `f`, without changing the
equations themselves. `MvPolynomial.rename` cannot raise total degree. -/
noncomputable def rename (S : QuadraticSystem F ι) {ι' : Type} (f : ι → ι') :
    QuadraticSystem F ι' where
  Eq := S.Eq
  polynomial e := MvPolynomial.rename f (S.polynomial e)
  degree e := (MvPolynomial.totalDegree_rename_le f (S.polynomial e)).trans (S.degree e)

@[simp] theorem holds_rename (S : QuadraticSystem F ι) {ι' : Type} (f : ι → ι') (w : ι' → F) :
    (S.rename f).Holds w ↔ S.Holds (w ∘ f) := by
  simp [Holds, rename, MvPolynomial.eval_rename]

/-- A single quadratic equation. -/
def single (p : MvPolynomial ι F) (h : p.totalDegree ≤ 2) : QuadraticSystem F ι where
  Eq := Unit
  polynomial _ := p
  degree _ := h

@[simp] theorem holds_single (p : MvPolynomial ι F) (h : p.totalDegree ≤ 2)
    (w : ι → F) : (single p h).Holds w ↔ MvPolynomial.eval w p = 0 := by
  simp [Holds, single]

end QuadraticSystem

end GordieHowe
