-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Rules

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Solve`

The definitions of `GordieHowe.Language.Realizations.Derivation.Solve` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Solve.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The integer linear form of an expression** at the characteristic `p`: its constant and its
terms, sums, differences and constant multiples (read centred) expanded, any other node a term of
coefficient `1`. -/
def ilin (p : ℕ) : Expr → ℤ × List (ℤ × Expr)
  | .add a b =>
    let x := ilin p a
    let y := ilin p b
    (x.1 + y.1, x.2 ++ y.2)
  | .sub a b =>
    let x := ilin p a
    let y := ilin p b
    (x.1 - y.1, x.2 ++ y.2.map fun t => (-t.1, t.2))
  | .scale (.const c) a =>
    let x := ilin p a
    (centeredZ p c * x.1, x.2.map fun t => (centeredZ p c * t.1, t.2))
  | e => (0, [(1, e)])

/-- **The premises of `ivlSolve`**: the `ivl` facts of domain `d` at `ks`, each of an expression
at least `n` long. -/
def solvePrem (fs : List Fact) (d n : ℕ) : List ℕ → Option (List (Expr × Ivl))
  | [] => some []
  | k :: ks =>
    match fs[k]? with
    | some (.ivl d' x a b) =>
      if d' = d ∧ n ≤ ir.exprLen x then (solvePrem fs d n ks).map ((x, ⟨a, b⟩) :: ·) else none
    | _ => none

end

/-- **The coefficient of `a` and the interval of the other terms** of a linear form, the other
terms' intervals the premises `ps` consumed in order. -/
def solveIvl (a : Expr) : List (ℤ × Expr) → List (Expr × Ivl) → Option (ℤ × Ivl)
  | [], [] => some (0, ⟨0, 0⟩)
  | [], _ :: _ => none
  | (c, t) :: ts, ps =>
    if t.beq a = true then (solveIvl a ts ps).map fun r => (r.1 + c, r.2)
    else
      match ps with
      | (x, K) :: ps' =>
        if x.beq t = true then (solveIvl a ts ps').map fun r => (r.1, r.2.add (K.smul c))
        else none
      | [] => none

section

variable (ir : RealizedProgram)

/-- **`ivlSolve k ks a j lo hi`** in domain `d`: from `intEq d e₁ e₂` (`k`), the `ivl` facts `ks`
of the other atoms of `e₁ − e₂` and an `ivl` fact of `a` (`j`): `ivl d a lo hi`. -/
def ivlSolveFact (fs : List Fact) (d k : ℕ) (ks : List ℕ) (a : Expr) (j : ℕ) (lo hi : ℤ) :
    Option Fact :=
  match fs[k]?, fs[j]? with
  | some (.intEq d₀ e₁ e₂), some (.ivl d₁ a' _ _) =>
    if d₀ = d ∧ d₁ = d ∧ d < ir.domains.length ∧ a'.beq a = true ∧
        ir.exprLen a ≤ ir.exprLen e₁ then
      match solvePrem ir fs d (ir.exprLen a) ks with
      | some ps =>
        match solveIvl a (ilin (ir.charOf (ir.domainField d)) (.sub e₁ e₂)).2 ps with
        | some (s, J) =>
          let c := (ilin (ir.charOf (ir.domainField d)) (.sub e₁ e₂)).1
          if s = 1 ∧ lo ≤ -(c + J.hi) ∧ -(c + J.lo) ≤ hi ∨
              s = -1 ∧ lo ≤ c + J.lo ∧ c + J.hi ≤ hi then
            some (.ivl d a lo hi)
          else none
        | none => none
      | none => none
    else none
  | _, _ => none

end

end GordieHowe.RealizedProgram
