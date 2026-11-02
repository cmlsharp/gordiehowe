-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Pure`

The definitions of `GordieHowe.Language.Realizations.Derivation.Pure` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Pure.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The reader-generic interval sources**: a constant's entries, a declared bound, a `nat`
premise (`srcFact`); none for the others. -/
def pureSrcFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (fs : List Fact) (d v : ℕ) :
    IvlSrc → Option Fact
  | .const => ir.srcFact primeNodes sr fs d v .const
  | .declared k => ir.srcFact primeNodes sr fs d v (.declared k)
  | .nat k => ir.srcFact primeNodes sr fs d v (.nat k)
  | _ => none

/-- **The conclusion of a reader-generic step** (`stepFact` on the rules whose soundness reads only
their premises), for a derivation of body `body` from the facts `fs`; `none` for every other
step. -/
def pureStepFact (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (body : PredBody)
    (fs : List Fact) : Step → Option Fact
  | .subst e₁ e₂ => ir.substFact body.dom e₁ e₂
  | .linear cs e₁ e₂ => ir.linearFact fs body.dom cs e₁ e₂
  | .rangeNat k => ir.rangeNatFact fs body.dom k
  | .src v s =>
    if ir.srcGuard body.dom v = true then ir.pureSrcFact primeNodes sr fs body.dom v s else none
  | .ivlNat k => ir.ivlNatFact fs body.dom k
  | .ivlExpr ks x lo hi => ir.ivlExprFact fs body.dom ks x lo hi
  | .ivlSolve k ks a j lo hi => ir.ivlSolveFact fs body.dom k ks a j lo hi
  | .ivlApply k a e lo hi => ir.ivlApplyFact fs body.dom k a e lo hi
  | .ivlLogic ks e => ir.ivlLogicFact fs body.dom ks e
  | .ivlMeet a b => ivlMeetFact fs a b
  | .ivlDisjoint a b => ir.ivlDisjointFact fs body.dom a b
  | .fieldDvd k a b => ir.fieldDvdFact fs body.dom k a b
  | .natIvl k => natIvlFact fs k
  | .transport k j => ir.transportFact fs k j
  | .natComp k j => ir.natCompFact fs body.dom k j
  | .natLin k ks => ir.natLinFact fs body.dom k ks
  | .liftConst k a => ir.liftConstFact fs body k a
  | .lift k a b => ir.liftFact fs k a b
  | .digits k ds T => ir.digitsFact fs body.dom k ds T
  | .linop s => ir.linopFact fs body.dom s
  | .inDom d s => pureStepFact primeNodes sr (entryBody d) fs s
  | _ => none

end

end GordieHowe.RealizedProgram
