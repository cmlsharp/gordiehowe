-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realize
public import GordieHoweNative.Language.Realizations.Derivation.Basic

@[expose] public section

/-!
# GordieHowe: derivations, the facts and the steps

The facts a derivation establishes (`GordieHowe.RealizedProgram.Fact`, `GordieHowe.RealizedProgram.Fact.HoldsWith`), the rule set
(`GordieHowe.RealizedProgram.Step`, every constructor), and the model facts the rules read
(`GordieHowe.RealizedProgram.DerivModel`). The rules' checkers and soundness lemmas are in
`GordieHowe/Language/Realizations/Derivation/*.lean`; the dispatcher and the theorems in
`GordieHowe/Language/Realizations/Derivation.lean`. A new rule adds a constructor here, a file of
its own with `<rule>Fact` and `<rule>Fact_sound`, and one line each in `stepFact` and
`stepFact_sound`.

The fact `real rc` (a realization circuit holds) and the steps `circuitAssert` and `inputPremise`
belong to the derivations of a GKR circuit's entries
(`GordieHowe/Language/Realizations/Derivation/Circuit.lean`): the two steps cite the facts of the
circuit's template instances and input premises, and the program's derivations conclude nothing
from them.

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/Basic.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP


/-! ## Facts and steps -/

/-- **A derivation**: its steps in order. -/
abbrev Derivation : Type := List Step

/-- **The derivation of an unlisted predicate**: a field `equal` realized as written. -/
def defaultSteps (pid : ℕ) : List Step := [.realized pid, .conclude 0]

/-- **The steps of predicate `pid` in a sparse derivation list**: its listed steps, else
`defaultSteps`. -/
def sparseSteps : List (ℕ × List Step) → ℕ → List Step
  | [], pid => defaultSteps pid
  | d :: ds, pid => if d.1 = pid then d.2 else sparseSteps ds pid

/-- **The steps of predicate `pid`** (`sparseSteps`). -/
def Derivations.stepsOf (D : Derivations) (pid : ℕ) : List Step := sparseSteps D.derivs pid

theorem sparseSteps_of_lt : ∀ {ds : List (ℕ × List Step)} {pid : ℕ}, (∀ d ∈ ds, pid < d.1) →
    sparseSteps ds pid = defaultSteps pid
  | [], _, _ => rfl
  | d :: ds, pid, h => by
    have h1 := h d (by simp)
    simp only [sparseSteps, if_neg (Nat.ne_of_gt h1)]
    exact sparseSteps_of_lt fun d' hd' => h d' (by simp [hd'])

theorem Expr.beq_iff {e e' : Expr} : e.beq e' = true ↔ e = e' :=
  ⟨Expr.eq_of_beq, fun h => h ▸ Expr.beq_self e⟩

/-- **Structurally equal facts are equal.** -/
theorem Fact.eq_of_beq {f g : Fact} (h : f.beq g = true) : f = g := by
  cases f <;> cases g <;> simp_all [Fact.beq, Expr.beq_iff]

section

variable (ir : RealizedProgram) {I : Interp}

/-- **A fact holds** at the reader `rd`. -/
def Fact.HoldsWith (rd : ir.Valuation I) : Fact → Prop
  | .eq d e₁ e₂ => ∀ i < ir.exprLen e₁, ir.evalWith rd d e₁ i = ir.evalWith rd d e₂ i
  | .nat d e N => ∀ i < ir.exprLen e, IsNatBelow N (ir.evalWith rd d e i)
  | .ivl d e lo hi => ∀ i < ir.exprLen e, lo ≤ ir.evalIntWith rd d e i ∧
      ir.evalIntWith rd d e i ≤ hi ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i
  | .intEq d e₁ e₂ => ∀ i < ir.exprLen e₁, ir.evalIntWith rd d e₁ i = ir.evalIntWith rd d e₂ i
  | .dvd d e q => ∀ i < ir.exprLen e, (q : ℤ) ∣ ir.evalIntWith rd d e i
  | .inRows t e => ∀ i < ir.exprLen e, ∃ j, ir.tableRow rd (ir.chalField (ir.alphaOf t)) t j =
      ir.evalE rd (ir.chalField (ir.alphaOf t)) e i
  | .holds p => ir.HoldsWith rd (ir.predicate p).body
  | .real rc => ir.RealHolds rd rc

variable {ir} in
/-- **A fact holds in the environment `e`**: at its reader. -/
def Fact.Holds (e : ir.Env I) (f : Fact) : Prop := f.HoldsWith ir (ir.reader e)


variable {ir} in
/-- **What a derivation of rank `self` may cite holds**: every predicate and every shared entry of
smaller rank. -/
def CitesHold (e : ir.Env I) (ctx : DerivCtx) (self : ℕ) : Prop :=
  (∀ q < ir.predicates.length, ctx.rank q < self → ir.HoldsAt e (ir.predicate q).body) ∧
    ∀ k f, ctx.srank k < self → ctx.sfact k = some f → f.Holds e

/-- **The body a derivation is checked against** is its predicate's or a shared entry's. -/
def OwnBody (pid : ℕ) (body : PredBody) : Prop :=
  (pid < ir.predicates.length ∧ (ir.predicate pid).body = body) ∨ ∃ d, body = entryBody d

variable (I) in
/-- **The model facts the rules read**: the program is well formed, the interpretation registered
and lawful, and every table valid (`TableOk`). -/
structure DerivModel (primeNodes : ℕ → List String) : Prop where
  /-- The program is well formed. -/
  wf : ir.WellFormed
  /-- The interpretation is registered. -/
  registered : I.Registered ir
  /-- The integer readings are lawful. -/
  lawful : I.Lawful ir primeNodes
  /-- Every table is valid. -/
  tables : ∀ t < ir.tables.length, ir.TableOk t
  /-- The MAC fields are modelled (`Interp.MacModel`). -/
  mac : I.MacModel ir


end

end GordieHowe.RealizedProgram
