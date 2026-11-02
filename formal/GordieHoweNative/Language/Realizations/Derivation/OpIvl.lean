-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.LinOp
public import GordieHoweNative.Language.Realizations.Derivation.Rules

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.OpIvl`

The definitions of `GordieHowe.Language.Realizations.Derivation.OpIvl` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/OpIvl.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The centred weights of a number from `k` digits in base `b`** at the characteristic `p`:
`bˡ mod p` read centred, `l < k`. -/
def digitWeights (p b k : ℕ) : List ℤ := (List.range k).map fun l => centeredZ p (b ^ l % p)

section

variable (ir : RealizedProgram)

/-- **The interval of an operator application** at the characteristic `p`, the operand's interval
`J` and the public operand `pub` an interval premise names (`ivlApply`). -/
def specialIvl (p : ℕ) (J : Ivl) (pub : Option (ℕ × Ivl)) : NamedOp → Option Ivl
  | .batched B (.fromDigits k b) =>
    if 0 < p ∧ b < p ∧ 0 < B then some (groupSumIvl J (digitWeights p b k)) else none
  | .negacyclicConv h .coefficients =>
    match pub with
    | some (v, A) =>
      if v = h ∧ 2 * A.mag < p then some (Ivl.sym ((ir.value h).size * A.mag * J.mag)) else none
    | none => none
  | .negacyclicConv h (.ntt psi) =>
    if (pub.map (·.1)) = some h ∧ psi < p then
      some (Ivl.sym ((ir.value h).size * p * J.mag))
    else none
  | _ => none

/-- **The public operand's interval as values' intervals**: `A` for the named value, none
elsewhere. -/
def pubLeafI : Option (ℕ × Ivl) → ℕ → Option Ivl
  | some (v, A), u => if u = v then some A else none
  | none, _ => none

/-- **The interval of an operator application**: the transform-form and digit cases
(`specialIvl`), else the public polynomial and row-form operators' interval at the public
operand's interval (`NamedOp.polyIvl`: `polyBroadcast`, `polyMatVec` and `negacyclicConv` in
coefficient form, `rowDot` by a constant matrix, `acyclicConv`, and their batched forms). -/
def opIvl (p : ℕ) (J : Ivl) (pub : Option (ℕ × Ivl)) (op : NamedOp) : Option Ivl :=
  match ir.specialIvl p J pub op with
  | some J' => some J'
  | none => NamedOp.polyIvl ir (pubLeafI pub) p J op

/-- **The public operand an interval premise names**: the value `v` of field `d`'s and the
interval of the premise `a`'s fact `ivl d (leaf v) …`. -/
def pubOf (fs : List Fact) (d : ℕ) : Option ℕ → Option (ℕ × Ivl)
  | some j =>
    match fs[j]? with
    | some (.ivl d'' (.leaf v) lo hi) =>
      if d'' = d ∧ ir.valueField v = ir.domainField d then some (v, ⟨lo, hi⟩) else none
    | _ => none
  | none => none

/-- **`ivlApply k a e lo hi`** in domain `d`: `e = .apply op x`, `ivl d x` at premise `k`, the
public operand's interval at premise `a`: `ivl d e lo hi` for the operator's interval (`opIvl`)
within `[lo, hi]`. -/
def ivlApplyFact (fs : List Fact) (d k : ℕ) (a : Option ℕ) (e : Expr) (lo hi : ℤ) :
    Option Fact :=
  match e, fs[k]? with
  | .apply op x, some (.ivl d' x' l h) =>
    if d' = d ∧ x'.beq x = true ∧ d < ir.domains.length ∧
        2 < ir.charOf (ir.domainField d) then
      match opIvl ir (ir.charOf (ir.domainField d)) ⟨l, h⟩ (ir.pubOf fs d a) op with
      | some J => if J.Within lo hi then some (.ivl d e lo hi) else none
      | none => none
    else none
  | _, _ => none

/-- **The bit premises of a Logic builder's arguments**: each argument `args[i]` has an interval
within `[0, 1]` at premise `ks[i]`, of the first argument's length. -/
def logicPremOk (fs : List Fact) (d L : ℕ) : List ℕ → List Expr → Bool
  | [], [] => true
  | k :: ks, x :: xs =>
    (match fs[k]? with
      | some (.ivl d' x' lo hi) =>
        decide (d' = d) && x'.beq x && decide (0 ≤ lo) && decide (hi ≤ 1) &&
          decide (ir.exprLen x = L)
      | _ => false) && logicPremOk fs d L ks xs
  | _, _ => false

/-- **`ivlLogic ks e`** in domain `d`: `e = .logic op w args`, each argument within `[0, 1]`
(`logicPremOk`): `ivl d e 0 1`. -/
def ivlLogicFact (fs : List Fact) (d : ℕ) (ks : List ℕ) (e : Expr) : Option Fact :=
  match e with
  | .logic op w (x :: xs) =>
    if 0 < w ∧ ir.logicPremOk fs d (ir.exprLen x) ks (x :: xs) = true then
      some (.ivl d e 0 1)
    else none
  | _ => none

end

end GordieHowe.RealizedProgram
