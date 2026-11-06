-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Foundations.Algebra.BitReverse
public import GordieHoweNative.Foundations.Algebra.ConvMatrix
public import GordieHoweNative.Language.RealizedProgram

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Semantics`

The definitions of `GordieHowe.Language.RealizedProgram.Semantics` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Semantics.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

namespace NamedOp

variable (ir : RealizedProgram)

/-- **The block width of a named operator**: the coordinates of one block of its operand
(`n` for the transforms and convolutions, `L·n` for `polyMatVec`, `nch·w` for `macConv`, `w` for
`sum`, `k` for `fromDigits`, `1` for `scale`). -/
def cols : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.value h).size
  | .polyMatVec a K L _ => L * ((ir.value a).size / (K * L))
  | .polyBroadcast t K _ => (ir.value t).size / K
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ _ W => W
  | .macConv _ w nch _ => nch * w
  | .acyclicConv _ lx => lx
  | .diagonal d => (ir.value d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.value d).size
  | .sum w => w
  | .fromDigits k _ => k
  | .batched b op => b * cols op

/-- **The output width of a named operator** on one block. -/
def rows : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.value h).size
  | .polyMatVec a K L _ => K * ((ir.value a).size / (K * L))
  | .polyBroadcast t _ _ => (ir.value t).size
  | .ntt n _ _ => n
  | .inverseNtt n _ => n
  | .nttTranspose n _ => n
  | .rowDot _ R _ => R
  | .macConv _ w _ _ => w
  | .acyclicConv h lx => lx + (ir.value h).size - 1
  | .diagonal d => (ir.value d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.value d).size
  | .sum _ => 1
  | .fromDigits _ _ => 1
  | .batched b op => b * rows op

end NamedOp

variable (ir : RealizedProgram)

mutual

/-- **The length of an expression** (its number of coordinates), the shared expressions having
lengths `rl`. -/
def Expr.len (rl : ℕ → ℕ) : Expr → ℕ
  | .leaf v => (ir.value v).size
  | .add e _ => Expr.len rl e
  | .sub e _ => Expr.len rl e
  | .scale _ e => Expr.len rl e
  | .mul e _ => Expr.len rl e
  | .reindex idx _ => idx.size
  | .concat e e' => Expr.len rl e + Expr.len rl e'
  | .linear rows _ => rows.length
  | .prod n e => Expr.len rl e / n
  | .mux _ t _ => Expr.len rl t
  | .apply op e => Expr.len rl e / NamedOp.cols ir op * NamedOp.rows ir op
  | .ref k => rl k
  | .logic _ w args => (Expr.lenList rl args).headD 0 / w

/-- The lengths of a list of expressions. -/
def Expr.lenList (rl : ℕ → ℕ) : List Expr → List ℕ
  | [] => []
  | e :: es => Expr.len rl e :: Expr.lenList rl es

end

section

/-- **A late value node** of a phase the program has. -/
def IsLate (v : ℕ) : Prop :=
  (ir.value v).kind.isLate = true ∧ 1 ≤ (ir.value v).phase ∧ (ir.value v).phase ≤ ir.phases

/-- A phase-zero value cannot be a late value. -/
theorem not_IsLate_of_phase_zero {v : Nat} (h : (ir.value v).phase = 0) : ¬ ir.IsLate v := by
  intro hv
  have hp := hv.2.1
  rw [h] at hp
  exact Nat.not_succ_le_zero 0 hp

instance (v : ℕ) : Decidable (ir.IsLate v) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The lengths of the shared expressions**, with `n` levels (`0`: every length `0`). -/
def refLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => Expr.len ir (refLen n) (ir.expr k)

/-- **The length of an expression**, its shared expressions' lengths at the program's depth (the
number of shared expressions, enough when each reads only entries of smaller index). -/
def exprLen (e : Expr) : ℕ := Expr.len ir (ir.refLen ir.exprs.length) e

variable {I}

/-- **The fuel of the program**: one more than its number of values. -/
def fuel : ℕ := ir.values.length + 1

/-- Whether a value's kind is read from the statement as given: a statement input or an opaque
statement value with no arguments. -/
def isStmtLeaf : Kind → Bool
  | .pub .input => true
  | .pub (.opaque _ []) => true
  | _ => false

/-- Whether a value's kind is computed from the statement: an opaque statement value whose
arguments are all read from the statement as given (`isStmtLeaf`). -/
def isStmtComputed : Kind → Bool
  | .pub (.opaque _ (a :: as)) => (a :: as).all fun u => isStmtLeaf (ir.value u).kind
  | _ => false

/-- Whether value `v` is a statement value: read from the statement as given (`isStmtLeaf`) or
computed from such values (`isStmtComputed`). -/
def isStmtValue (v : ℕ) : Bool :=
  isStmtLeaf (ir.value v).kind || ir.isStmtComputed (ir.value v).kind

/-- **The declared statement bounds** (`Value.bound`): `(v, N)` for every statement value
(`isStmtValue`) that declares the bound `N`. The verifier checks them on the statement before the
transcript starts, a computed value's at its computation, as the C++ verifier's setup does. -/
def declaredRanges : List (ℕ × ℕ) :=
  (List.range ir.values.length).filterMap fun v =>
    if ir.isStmtValue v then (ir.value v).bound.map (v, ·) else none

/-- **`declaredRanges`, each value read from an array of the values**: the code compiled for
`declaredRanges` (`declaredRanges_csimp`). Compiled checkers evaluate `declaredRanges` inside
per-value lookups (`srcLeafIvl`), and a walk of the list per value would make each evaluation
quadratic in the number of values. -/
def declaredRangesC : List (ℕ × ℕ) :=
  let a := ir.values.toArray
  (List.range a.size).filterMap fun v =>
    let x := a[v]?.getD default
    if isStmtLeaf x.kind || ir.isStmtComputed x.kind then x.bound.map (v, ·) else none

@[csimp] theorem declaredRanges_csimp : @declaredRanges = @declaredRangesC := by
  funext ir
  simp only [declaredRanges, declaredRangesC, isStmtValue, value_eq_getD, List.size_toArray,
    List.getElem?_toArray, List.getD_eq_getElem?_getD]

end

end GordieHowe.RealizedProgram
