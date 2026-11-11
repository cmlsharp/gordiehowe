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
/-- **The honest facts of a convolution's committed `C`**, read as the shared expression `kc`,
of the convolution `k` of domain `d` (`cv`), as a check: `kc` (one of the program's shared
expressions) is the leaf of a value `C`, a committed cell of the domain's field and of the
source's length, generated as `k`'s committed `C` (`Gen.specC k`), no source value; the source is
well formed, has an interval from the source values (`srcIvl`), and every value it reads is a
source value reading no challenge and no late value, or a constant. -/
def cHonestB (S : Structure) (G : Gens) (k d : ℕ) (cv : SpectralConv) (kc : ℕ) : Bool :=
  match ir.expr kc with
  | .leaf C =>
    decide (kc < ir.exprs.length) && decide (G.at C = .specC k) && ir.privCellB C && !decide (ir.IsSourceValue C) &&
      decide (ir.valueField C = ir.domainField d) &&
      decide ((ir.value C).size = ir.exprLen (.ref cv.source)) &&
      decide (ir.ExprOk (ir.domainField d) (.ref cv.source)) &&
      (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) (.ref cv.source)).isSome &&
      (ir.exprNodes (.ref cv.source)).all (fun w =>
        (decide (ir.IsSourceValue w) && (ir.readsT.getD w []).isEmpty) || ir.isConstant w)
  | _ => false

variable (ir primeNodes) in
/-- **The honest facts of the committed reading of the spectrally realized convolution `k`** of
domain `d` (`cv`), as a check: none without one; otherwise its `C`'s (`cHonestB`). -/
def specCHonestB (S : Structure) (G : Gens) (k d : ℕ) (cv : SpectralConv) : Bool :=
  match cv.committed with
  | none => true
  | some (kc, _) => ir.cHonestB primeNodes S G k d cv kc

variable (ir primeNodes) in
/-- **The honest facts of the spectrally realized convolution `k`** at the certificate's generators
`G`, as a check: `k` is a convolution of the program
whose products predicate is a field `equal` `NTT_M(P_a) · NTT_M(P_b) = z` of a domain `d` where it
is realized (`ConvOkAt`); the operand views are well formed and have intervals from the source
values (`srcIvl`); every value the products' left side reads is a source value reading no challenge
and no late value, or a constant; and `z` is a committed cell generated as `k`'s transformed value,
no source value. A committed reading's `C` (`specCHonestB`) is a committed cell of the domain's
field generated as `k`'s source, no source value, of the source's length, and the source has an
interval from the source values. A directly realized convolution's facts are `DirectOkAt` at
the domain of its products predicate and its reading `C`'s honest facts (`cHonestB`). -/
def specHonestCB (S : Structure) (G : Gens) (k : ℕ) : Bool :=
  match ir.convs[k]? with
  | none => false
  | some cv =>
    if cv.direct then
      match (ir.predicate cv.products).body with
      | .equal d _ _ _ => decide (ir.DirectOkAt d cv) && ir.cHonestB primeNodes S G k d cv cv.read
      | _ => false
    else
      match (ir.predicate cv.products).body with
      | .equal d (.mul (.apply op pa) (.apply op' pb)) (.leaf z) _ =>
        decide (ir.ConvOkAt d cv) && decide (ir.ExprOk (ir.domainField d) pa) &&
          decide (ir.ExprOk (ir.domainField d) pb) &&
          (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) pa).isSome &&
          (ir.srcIvl (ir.srcLeafIvl primeNodes S) (ir.domainField d) pb).isSome &&
          (ir.exprNodes (.mul (.apply op pa) (.apply op' pb))).all (fun w =>
            (decide (ir.IsSourceValue w) && (ir.readsT.getD w []).isEmpty) || ir.isConstant w) &&
          decide (G.at z = .spec k) && ir.privCellB z && !decide (ir.IsSourceValue z) &&
          ir.specCHonestB primeNodes S G k d cv
      | _ => false

variable (ir primeNodes) in
/-- **Predicate `q` realizes the field equation of the predicate `m`**, as a check:
every spectrally realized convolution has its honest
facts (`specHonestCB`), and `m` is a field `equal` or `mod_0` with the target `realized q`
admitted at the structure records' route of `m` (`realizedAtS`, giving `RealizedAdmits`), a
`mod_0` with the intervals of its sides from the source values within
the exported ones (`srcIvl`) in a field of characteristic above `2`. Where `m`'s field equation
holds, so does `q` (the completeness step `specRow` reads it from `m` a source predicate, or of
smaller rank). -/
def specRowCB (S : Structure) (G : Gens) (m q : ℕ) : Bool :=
  (List.range ir.convs.length).all (ir.specHonestCB primeNodes S G) &&
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
