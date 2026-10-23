-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State

@[expose] public section

/-!
# Quantum-accessible oracles with parallel queries

The registers of an algorithm with `n` parallel queries are a work register `W` and `n` pairs of
a query input register `X` and a query output register `Y`; the computational basis is
`QueryReg W n X Y = W × (Fin n → X × Y)`.

For `f : X → Y`, `queryPerm f` maps the basis state `|w, (x_j, y_j)_j⟩` to
`|w, (x_j, y_j + f x_j)_j⟩`: AHU19's `U_f : |q, r⟩ ↦ |q, r ⊕ f(q)⟩` applied to every pair
`Q_j, R_j` at once (AHU19, ePrint 2018/904, pp. 8–9). AHU take `⊕` to be "some involutive group
operation (e.g., XOR if Y is a set of bitstrings)". Here `Y` is any additive group: `U_f` is a
basis permutation for every group operation, with inverse `y ↦ y - f x`, and the proofs never
use that it is its own inverse. For bit strings with XOR, `y + y = 0` and `U_f` is involutive.

- `queryPerm_eq_of_notMem_queried`: if `f` and `g` agree outside `S`, then `queryPerm f` and
  `queryPerm g` agree on every basis state outside `queried S`, the basis states with some
  query input in `S`.
- `queryPermOf f` applies the function `f w` chosen by the content `w` of the work register, and
  `queriedOf S` is the set of basis states with some query input in `S w`; with constant `f` and
  `S` they are `queryPerm` and `queried` (`queryPermOf_const`, `queriedOf_const`).
- `prob_queried`: the Born probability of `queried S` is the probability that measuring all
  query input registers in the computational basis gives a tuple `t` with some `t j ∈ S`.
  This is AHU19's event `S ∩ T ≠ ∅` for the set `T` of measurement outcomes (Theorem 3, p. 11).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- The computational basis of an algorithm with work register `W` and `n` parallel query
registers, each a query input in `X` and a query output in `Y`. -/
abbrev QueryReg (W : Type*) (n : ℕ) (X Y : Type*) := W × (Fin n → X × Y)

variable {W X Y : Type*} {n : ℕ}

/-- The oracle for `f`: `|w, (x_j, y_j)_j⟩ ↦ |w, (x_j, y_j + f x_j)_j⟩`. -/
def queryPerm [AddGroup Y] (f : X → Y) : Equiv.Perm (QueryReg W n X Y) :=
  Equiv.prodCongrRight fun _ =>
    Equiv.piCongrRight fun _ => Equiv.prodShear (Equiv.refl X) fun x => Equiv.addRight (f x)

@[simp]
theorem queryPerm_apply [AddGroup Y] (f : X → Y) (r : QueryReg W n X Y) :
    queryPerm f r = (r.1, fun j => ((r.2 j).1, (r.2 j).2 + f (r.2 j).1)) :=
  rfl

/-- The query inputs of a basis state. -/
def queryInputs (r : QueryReg W n X Y) : Fin n → X :=
  fun j => (r.2 j).1

/-- The basis states with some query input in `S`. -/
def queried (S : Set X) : Set (QueryReg W n X Y) :=
  {r | ∃ j, (r.2 j).1 ∈ S}

theorem queried_eq_preimage (S : Set X) :
    queried (W := W) (Y := Y) (n := n) S = queryInputs ⁻¹' {t | ∃ j, t j ∈ S} :=
  rfl

/-- Oracles for functions that agree outside `S` agree on every basis state with no query input
in `S`. -/
theorem queryPerm_eq_of_notMem_queried [AddGroup Y] {S : Set X} {f g : X → Y}
    (h : ∀ x ∉ S, f x = g x) :
    ∀ r ∉ queried (W := W) (n := n) S, queryPerm f r = queryPerm g r := by
  intro r hr
  simp only [queried, Set.mem_ofPred_eq, not_exists] at hr
  simp [h _ (hr _)]

/-! ### Oracles chosen by the work register -/

/-- The oracle for a function `f w` chosen by the work register:
`|w, (x_j, y_j)_j⟩ ↦ |w, (x_j, y_j + f w x_j)_j⟩`. It is a basis permutation that leaves the work
register unchanged; the oracle of a game whose oracle depends on classical data held in the
work register (the logged requests of `GordieHowe/Model/Quantum/Pure/Game.lean`) is of this form. -/
def queryPermOf [AddGroup Y] (f : W → X → Y) : Equiv.Perm (QueryReg W n X Y) :=
  Equiv.prodShear (Equiv.refl W) fun w =>
    Equiv.piCongrRight fun _ => Equiv.prodShear (Equiv.refl X) fun x => Equiv.addRight (f w x)

@[simp]
theorem queryPermOf_apply [AddGroup Y] (f : W → X → Y) (r : QueryReg W n X Y) :
    queryPermOf f r = (r.1, fun j => ((r.2 j).1, (r.2 j).2 + f r.1 (r.2 j).1)) :=
  rfl

/-- With a function that does not depend on the work register, `queryPermOf` is `queryPerm`. -/
theorem queryPermOf_const [AddGroup Y] (f : X → Y) :
    queryPermOf (W := W) (n := n) (fun _ => f) = queryPerm f :=
  Equiv.ext fun _ => rfl

/-- The basis states with some query input in `S w`, for the work register content `w`. -/
def queriedOf (S : W → Set X) : Set (QueryReg W n X Y) :=
  {r | ∃ j, (r.2 j).1 ∈ S r.1}

/-- With a set that does not depend on the work register, `queriedOf` is `queried`. -/
theorem queriedOf_const (S : Set X) :
    queriedOf (W := W) (n := n) (Y := Y) (fun _ => S) = queried S :=
  rfl

/-- Oracles for functions that agree outside `S w` agree on every basis state with no query
input in `S w`. -/
theorem queryPermOf_eq_of_notMem_queriedOf [AddGroup Y] {S : W → Set X} {f g : W → X → Y}
    (h : ∀ w, ∀ x ∉ S w, f w x = g w x) :
    ∀ r ∉ queriedOf (n := n) S, queryPermOf f r = queryPermOf g r := by
  intro r hr
  simp only [queriedOf, Set.mem_ofPred_eq, not_exists] at hr
  simp [h _ _ (hr _)]

/-- The Born probability of `queried S` is the probability that measuring the query input
registers in the computational basis gives a tuple `t` of inputs with some `t j ∈ S`. -/
theorem prob_queried [Fintype W] [Fintype X] [Fintype Y] (S : Set X) [DecidablePred (· ∈ S)]
    (v : QState (QueryReg W n X Y)) :
    prob (queried S) v = ∑ t with ∃ j, t j ∈ S, prob (queryInputs ⁻¹' {t}) v := by
  rw [queried_eq_preimage, prob_preimage]
  rfl

/-! ### Outcomes in the random-oracle model -/

/-- **The outcome of a run in the random-oracle model**: the adversary's output and the random
oracle, read through an equivalence of its range (CMS19 p. 14, the pair of `A^h`'s output and
`h`). -/
structure Outcome (O X B : Type*) where
  /-- The adversary's output. -/
  out : O
  /-- The random oracle. -/
  oracle : X → B

/-- The outcome with its output read through `g`. -/
def Outcome.mapOut {O O' X B : Type*} (g : O → O') (p : Outcome O X B) : Outcome O' X B :=
  ⟨g p.out, p.oracle⟩

end GordieHowe.Quantum
