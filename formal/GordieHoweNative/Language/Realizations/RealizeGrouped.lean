-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeMac

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.RealizeGrouped`

The definitions of `GordieHowe.Language.Realizations.RealizeGrouped` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/RealizeGrouped.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **A group's accumulator row, without its interval** (`groupRowB` but the interval of its
convolution, which a derivation states as a fact). -/
def groupRowCoreB (d : ℕ) (u : MacUnits) (G : GroupedMod) (acc g : ℕ) (fc : ℕ × ℕ) (b : PredBody) :
    Bool :=
  match b with
  | .equal d' (.add (.reindex ia (.leaf acc')) (.scale (.const c)
      (.apply (.macConv rg w cnt taps) Yv))) (.leaf z) _ =>
    d' == d && acc' == acc && c + 1 == ir.charOf (ir.domainField d) && w == u.width &&
      cnt == fc.2 && taps == u.taps && ia.toList == runList (g * u.width) u.width &&
      ir.subPowersB rg u.powers (fc.1 - 1) fc.2 &&
      (match ir.deref Yv with
        | .reindex iy y' => y'.beq u.operand &&
          iy.toList == runList ((fc.1 - 1) * u.width) (fc.2 * u.width)
        | _ => false) &&
      ir.constAll z 0 u.width (ir.domainField d) &&
      decide (ir.exprLen (.apply (.macConv rg w cnt taps) Yv) = u.width) &&
      ir.exprShapeOk (.apply (.macConv rg w cnt taps) Yv) &&
      Yv.refs.all (· < ir.exprs.length)
  | _ => false

/-- **The convolution term of a group's accumulator row** `acc_view + c · E = z`. -/
def groupRowExpr? : PredBody → Option Expr
  | .equal _ (.add (.reindex _ (.leaf _)) (.scale (.const _) E)) (.leaf _) _ => some E
  | _ => none

end

end GordieHowe.RealizedProgram
