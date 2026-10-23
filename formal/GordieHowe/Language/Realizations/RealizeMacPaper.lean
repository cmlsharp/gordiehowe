-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeMac
public import GordieHowe.Foundations.Probability.ChallengeEventCount
public import GordieHowe.Headline

@[expose] public section

/-!
# The MAC's soundness, in the form of the paper's lemma

The paper's lemma on the MAC of a cross-field `equal` (Lemma 4.6, `lem:core-mac`): (1) the checks over two fields
whose masked MACs give the same target agree, or the key is a root of the nonzero binding polynomial
`G`; (2) a nonzero `G` has the key as a root with probability at most `nch/2^w`.

* Part (1) in the field `GF(2^w)` is `MAC.binding`; at a realized program it is
  `GordieHowe.RealizedProgram.crossHolds_or_macBad` (the `x` domain hosts the MAC) and
  `GordieHowe.RealizedProgram.crossHolds_or_macBad_twoTail` (no domain hosts it), which read each side's masked MAC
  from its tail (the integer accumulator modulo `2`). This file restates those two with their
  hypotheses bundled: the facts about the program, its model and the environment (`MacFacts`),
  the predicate's shape (`CrossAt`) and the tails (`MacTailsHold`, `MacHHoldsAtKey`,
  `NonCrossHold`).
* Part (2) is `MAC.probUniform_bindingEvent_le`.
-/

namespace GordieHowe

open scoped NNReal ENNReal IOP
open IOP

namespace MAC

/-- **Paper `lem:core-mac`, part (2)**: the binding event of `k` chunks has the key as a root with
probability at most `k/|K|` over a uniform key (`ChallengeEvent.probUniform_badAt_le`; `k/2^w` in
`GF(2^w)`). -/
@[headline]
theorem probUniform_bindingEvent_le {K : Type} [Field K] [Fintype K] [DecidableEq K] {k : ℕ}
    (XH XA : Fin k → K) (PH PA : K) :
    Pr[κ ← K : (bindingEvent XH XA PH PA).BadAt κ] ≤ ((k / Fintype.card K : ℝ≥0) : ℝ≥0∞) :=
  ChallengeEvent.probUniform_badAt_le (bindingEvent XH XA PH PA)

end MAC

-- Paper `lem:core-mac`, part (1), in the field `GF(2^w)`.
attribute [headline] MAC.binding

namespace RealizedProgram

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir I primeNodes) in
/-- **The facts the MAC's soundness reads** about the program `ir`, its interpretation `I` and the
environment `e`: well-formedness, registration and lawfulness of the interpretation, the MAC model
(`Interp.MacModel`, a property of the model), and the leaf and shift facts of the environment's
reader. -/
structure MacFacts (e : ir.Env I) : Prop where
  /-- The program is well formed. -/
  wf : ir.WellFormed
  /-- The interpretation registers the program's fields. -/
  registered : I.Registered ir
  /-- The interpretation is lawful. -/
  lawful : I.Lawful ir primeNodes
  /-- The MAC model. -/
  model : I.MacModel ir
  /-- The leaf facts of the reader. -/
  leaf : ir.LeafFacts (ir.reader e)
  /-- The shift facts of the reader. -/
  shift : ir.ShiftFacts (ir.reader e)

variable (ir) in
/-- **Predicate `pid` is the cross-field `equal` `x = y`** of kind `k` with the MAC realization
`real`. -/
structure CrossAt (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind)
    (real : MacRealization) : Prop where
  /-- The predicate exists. -/
  lt : pid < ir.predicates.length
  /-- Its body is the cross-field `equal`. -/
  body : (ir.predicate pid).body = .cross dx x dy y k real

variable (ir) in
/-- **The MAC's tail predicates hold** in the environment `e`. -/
def MacTailsHold (e : ir.Env I) (pid dy : ℕ) (y : Expr) (real : MacRealization) : Prop :=
  ∀ t < ir.predicates.length, ir.macTailB pid dy y real t = true →
    ir.HoldsWith (ir.reader e) (ir.predicate t).body

variable (ir) in
/-- **The H half holds at the key where the compiler states it by its own circuit** (no H
predicate `<mac>.H`). -/
def MacHHoldsAtKey (e : ir.Env I) (dx : ℕ) (x : Expr) (real : MacRealization) : Prop :=
  real.hPredicate = none → ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0))

variable (ir) in
/-- **Every predicate other than a cross-field `equal` holds** in the environment `e`. -/
def NonCrossHold (e : ir.Env I) : Prop :=
  ∀ t < ir.predicates.length,
    (∀ dx' x' dy' y' k' real', (ir.predicate t).body ≠ .cross dx' x' dy' y' k' real') →
      ir.HoldsWith (ir.reader e) (ir.predicate t).body

/-- **Paper `lem:core-mac`, part (1), at a realized program, hosted MAC** (`crossHolds_or_macBad`):
for a cross-field `equal` whose `x` domain hosts the MAC (`MacShapeOk`), where the MAC's tails hold
and the H half holds, either the cross-field `equal` holds (in the compiler's contract, `HoldsWith`)
or the key is a root of the MAC's binding polynomial (`macEvent`). -/
@[headline]
theorem crossHolds_or_macBad_of {e : ir.Env I} (hF : MacFacts ir I primeNodes e) {pid dx : ℕ}
    {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization}
    (hc : ir.CrossAt pid dx x dy y k real) (hok : ir.MacShapeOk primeNodes pid dx x dy y k real)
    (htail : ir.MacTailsHold e pid dy y real) (hH : ir.MacHHoldsAtKey e dx x real) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) :=
  crossHolds_or_macBad hF.wf hF.registered hF.lawful hF.model e hF.leaf hF.shift hc.lt hc.body hok
    htail hH

/-- **Paper `lem:core-mac`, part (1), at a realized program, MAC hosted by no domain**
(`crossHolds_or_macBad_twoTail`): for a cross-field `equal` with blinds `bx` and `b` whose MAC no
domain hosts (`MacTwoTailOk`), where every predicate other than a cross-field `equal` holds, either
the cross-field `equal` holds (in the compiler's contract) or the key is a root of the MAC's binding
polynomial (`macEvent`). -/
@[headline]
theorem crossHolds_or_macBad_twoTail_of {e : ir.Env I} (hF : MacFacts ir I primeNodes e)
    {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization} {bx b : ℕ}
    (hc : ir.CrossAt pid dx x dy y k real) (hbx : real.blindX = some bx)
    (hbl : real.blind = some b) (hok : ir.MacTwoTailOk primeNodes pid dx x dy y k real bx b)
    (hnc : ir.NonCrossHold e) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) :=
  crossHolds_or_macBad_twoTail hF.wf hF.registered hF.lawful hF.model e hF.leaf hF.shift hc.lt
    hc.body hbx hbl hok hnc

end RealizedProgram

end GordieHowe
