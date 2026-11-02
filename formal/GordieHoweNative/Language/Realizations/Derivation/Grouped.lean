-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Grouped`

The definitions of `GordieHowe.Language.Realizations.Derivation.Grouped` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Grouped.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The rows and the groups' intervals of a `groupedMod` step check.** -/
def groupRowsB (ctx : DerivCtx) (self d : ℕ) (u : MacUnits) (G : GroupedMod) (acc : ℕ)
    (fs : List Fact) (rows ivs : List ℕ) : Bool :=
  (List.range G.groups.length).all fun g =>
    decide (rows.getD g 0 < ir.predicates.length) && decide (ctx.rank (rows.getD g 0) < self) &&
      ir.groupRowCoreB d u G acc g (G.groups.getD g default) (ir.predicate (rows.getD g 0)).body &&
      match groupRowExpr? (ir.predicate (rows.getD g 0)).body with
      | some Eg => (fs[ivs.getD g 0]?).any fun f => f.beq (.ivl d Eg 0 (G.groupBound : ℤ))
      | none => false

/-- **The numbers a `groupedMod` step reads**: the residues', digits' and final quotient's bounds and
the blind's and the right side's intervals, from the facts `ivs[#groups ..]`. -/
def groupedNums (fs : List Fact) (d : ℕ) (E' : Expr) (G : GroupedMod) (u : MacUnits)
    (real : ModRealization) (rest : List ℕ) : Option (ℕ × ℕ × ℕ × ℤ × ℤ × ℤ × ℤ) :=
  match rest with
  | [ires, idig, iq, ib, irhs] =>
    match fs[ires]?, fs[idig]?, fs[iq]?, fs[ib]?, fs[irhs]? with
    | some (.nat d1 R Rb), some (.nat d2 D Nd), some (.nat d3 Qx N), some (.ivl d4 B lob hib),
        some (.ivl d5 Xr lo' hi') =>
      if d1 = d ∧ d2 = d ∧ d3 = d ∧ d4 = d ∧ d5 = d ∧ R.beq G.residues = true ∧
          D.beq G.groupDigits = true ∧ Qx.beq real.quotExpr = true ∧
          B.beq (.leaf u.blind) = true ∧ Xr.beq E' = true then
        some (Rb, Nd, N, lob, hib, lo', hi')
      else none
    | _, _, _, _, _ => none
  | _ => none

/-- **`groupedMod rows ivs`** for predicate `pid` of body `body`, at rank `self`. -/
def groupedFact (ctx : DerivCtx) (self pid : ℕ) (body : PredBody) (fs : List Fact)
    (rows ivs : List ℕ) : Option Fact :=
  match body with
  | .mod d q E E' real =>
    match real.grouped, macUnits? E with
    | some G, some u =>
      match G.accumulators with
      | some (.leaf acc) =>
        match groupedNums fs d E' G u real (ivs.drop G.groups.length) with
        | some (Rb, Nd, N, lob, hib, lo', hi') =>
          if real.form.isProduct = false ∧ 0 < q ∧ 2 < ir.charOf (ir.domainField d) ∧
              ir.macUnitsOkB d u G = true ∧
              ir.residuesB d q u G acc = true ∧ ir.finalQuotB d q E' u G real = true ∧
              ir.groupRowsB ctx self d u G acc fs rows ivs = true ∧
              ir.exprLen E ≤ ir.exprLen real.quotExpr ∧
              G.groupBound < ir.charOf (ir.domainField d) ∧
              Rb - 1 + q * groupQuotMax G.base G.digitCount Nd < ir.charOf (ir.domainField d) ∧
              hib + ((G.groups.length * (Rb - 1) : ℕ) : ℤ) - lo' < ir.charOf (ir.domainField d) ∧
              ((q * (N - 1) : ℕ) : ℤ) + hi' - lob < ir.charOf (ir.domainField d) then
            some (.holds pid)
          else none
        | none => none
      | _ => none
    | _, _ => none
  | _ => none

end

end GordieHowe.RealizedProgram
