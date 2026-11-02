-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Committed

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Spectral`

The definitions of `GordieHowe.Language.Completeness.Spectral` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Spectral.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {S : Structure}

variable (ir primeNodes) in
/-- **The honest facts of the spectrally realized convolution `k`** at the certificate's generators
`G`, as a check: `k` is a convolution of the program
whose products predicate is a field `equal` `NTT_M(P_a) · NTT_M(P_b) = z` of a domain `d` where it
is realized (`ConvOkAt`); the operand views are well formed and have intervals from the source
values (`srcIvl`); every value the products' left side reads is a source value reading no challenge
and no late value, or a constant; and `z` is a committed cell generated as `k`'s transformed value,
no source value. -/
def specHonestCB (S : Structure) (G : Gens) (k : ℕ) : Bool :=
  match ir.convs[k]? with
  | none => false
  | some cv =>
    match (ir.predicate cv.products).body with
    | .equal d (.mul (.apply op pa) (.apply op' pb)) (.leaf z) _ =>
      decide (ir.ConvOkAt d cv) && decide (ir.ExprOk (ir.domainField d) pa) &&
        decide (ir.ExprOk (ir.domainField d) pb) &&
        (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) pa).isSome &&
        (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) pb).isSome &&
        (ir.exprNodes (.mul (.apply op pa) (.apply op' pb))).all (fun w =>
          (decide (ir.IsSourceValue w) && (ir.readsT.getD w []).isEmpty) || ir.isConstant w) &&
        decide (G.at z = .spec k) && ir.privCellB z && !decide (ir.IsSourceValue z)
    | _ => false

variable (ir primeNodes) in
/-- **Predicate `q` realizes the field equation of the source predicate `m`**, as a check:
every spectrally realized convolution has its honest
facts (`specHonestCB`), and `m` is a source field `equal` or `mod_0` with the target `realized q`
admitted at the structure records' route of `m` (`realizedAtS`, giving `RealizedAdmits`), a
`mod_0` with the intervals of its sides from the source values within
the exported ones (`srcIvl`) in a field of characteristic above `2`. -/
def specRowCB (S : Structure) (G : Gens) (m q : ℕ) : Bool :=
  (List.range ir.convs.length).all (ir.specHonestCB primeNodes S G) &&
    ir.inSource (ir.predicate m) &&
      match (ir.predicate m).body with
      | .equal d e e' (.realized q') => q' == q && ir.realizedAtS S m d e e' q
      | .mod d 0 e e' real =>
        real.target == some (.realized q) && ir.realizedAtS S m d e e' q &&
          decide (IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) e)
            real.lhsLo real.lhsHi) &&
          decide (IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) e')
            real.rhsLo real.rhsHi) &&
          decide (2 < ir.charOf (ir.domainField d))
      | _ => false

end

end GordieHowe.RealizedProgram
