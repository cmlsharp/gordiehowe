-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Mac`

The definitions of `GordieHowe.Language.Realizations.Derivation.Mac` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Mac.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **Fact `k` reads `e` within `[0, 1]` in domain `d`.** -/
def bitsAtB (fs : List Fact) (k d : ℕ) (e : Expr) : Bool :=
  match fs[k]? with
  | some f => f.beq (.ivl d e 0 1)
  | none => false

/-- **The H predicate cited is the record's**, of smaller rank. -/
def macHCiteB (ctx : DerivCtx) (self : ℕ) (real : MacRealization) (h : Option ℕ) : Bool :=
  match real.hPredicate, h with
  | none, none => true
  | some p, some q => p == q && decide (q < ir.predicates.length) && decide (ctx.rank q < self)
  | _, _ => false

/-- **A tail of a check over a field**: `macTailAtB` at odd characteristic or `macTailTwoB`. -/
def sideTailB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) : Bool :=
  (ir.macTailAtB pid d z b real t && decide (2 < ir.charOf (ir.domainField d))) ||
    ir.macTailTwoB pid d z b real t

/-- **`mac ts h ivs`** for predicate `pid` of body `body`, at rank `self`. -/
def macFact (primeNodes : ℕ → List String) (ctx : DerivCtx) (self pid : ℕ) (body : PredBody)
    (fs : List Fact) (ts : List ℕ) (h : Option ℕ) (ivs : List ℕ) : Option Fact :=
  match body with
  | .cross dx x dy y k real =>
    if ir.macHCiteB ctx self real h then
      match real.blindX, real.blind, ts, ivs with
      | none, some b, [t], [iy, ib] =>
        if ir.macHostedCoreB pid dx x dy y k real = true ∧
            ir.valueField b = ir.domainField dy ∧ (ir.value b).size = real.width ∧
            t < ir.predicates.length ∧ ctx.rank t < self ∧ ir.macTailB pid dy y real t = true ∧
            bitsAtB fs iy dy y = true ∧ bitsAtB fs ib dy (.leaf b) = true then
          some (.holds pid)
        else none
      | some bx, some b, [tx, ty], [ix, ibx, iy, ib] =>
        if ir.macTwoCoreB pid x y k real = true ∧
            ir.valueField bx = ir.domainField dx ∧ (ir.value bx).size = real.width ∧
            ir.valueField b = ir.domainField dy ∧ (ir.value b).size = real.width ∧
            tx < ir.predicates.length ∧ ctx.rank tx < self ∧ ty < ir.predicates.length ∧
            ctx.rank ty < self ∧ ir.sideTailB pid dx x bx real tx = true ∧
            ir.sideTailB pid dy y b real ty = true ∧
            bitsAtB fs ix dx x = true ∧ bitsAtB fs ibx dx (.leaf bx) = true ∧
            bitsAtB fs iy dy y = true ∧ bitsAtB fs ib dy (.leaf b) = true then
          some (.holds pid)
        else none
      | _, _, _, _ => none
    else none
  | _ => none

end

end GordieHowe.RealizedProgram
