-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Committed

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.CommDigits`

The definitions of `GordieHowe.Language.Completeness.CommDigits` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/CommDigits.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {S : Structure}
  {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **The facts of a digit lookup whose record is a committed-digits `mod_q`'s quotient digit** at
the certificate's generators `G`, at the `in`
predicate `lk` with body `mem d [rec] (range N) (lookup r)` whose record is digit `j` of the
`mod_q` `m` with body `mod d q e e' real`: a digit lookup of a domain with `k` digit values and no
second digits, each generated as the committed digit `⟨m, j, lk, k⟩` at its position, a committed
cell of the record's length in the domain's field that is no source value; the base above `1`; the
record the number of its digits (`digitsExprOk`) and digit `j` of the `mod_q`, of the sides'
length; the radix `R` with `R ≤ N` (the honest quotient digit lies in the range) and `R ≤ T^k`
(the digits hold it); the range within the characteristic. -/
structure CommLookupFactsC (G : Gens) (lk d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization)
    (m j : ℕ) (q : ℕ) (e e' : Expr) (real : ModRealization) : Prop where
  /-- A digit lookup. -/
  kind : r.kind = .digits
  /-- A domain of the program. -/
  domain : d < ir.domains.length
  /-- `k` digit values. -/
  len : r.digitValues.length = r.digits
  /-- No second digits. -/
  second : r.second = []
  /-- The digit values are generated as the committed digits at their positions. -/
  own : ∀ k (hk : k < r.digitValues.length), G.at r.digitValues[k] = .commDigit m j lk k
  /-- The digits are committed cells of the record's length in the domain's field, no source
  values. -/
  cells : ∀ u ∈ r.digitValues, ir.privCellB u = true ∧ (ir.value u).size = ir.exprLen rec ∧
    ir.valueField u = ir.domainField d ∧ ¬ ir.IsSourceValue u
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- The record, through a shared expression (`unref`), is the number of its digits. -/
  expr : digitsExprOk (ir.charOf (ir.domainField d)) r.base (ir.unref rec) r.digitValues = true
  /-- The record is digit `j` of the `mod_q`. -/
  isDigit : (real.digits[j]?.map fun D => D.beq rec) = some true
  /-- The record has the sides' length. -/
  recLen : ir.exprLen rec = ir.exprLen e
  /-- The honest quotient digit lies in the range. -/
  radixLe : real.radix ≤ N
  /-- The digits hold the honest quotient digit. -/
  radixDigits : real.radix ≤ r.base ^ r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : N ≤ ir.charOf (ir.domainField d)

instance (G : Gens) (lk d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) (m j q : ℕ)
    (e e' : Expr) (real : ModRealization) :
    Decidable (ir.CommLookupFactsC G lk d rec N r m j q e e' real) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩,
     fun h => ⟨h.kind, h.domain, h.len, h.second, h.own, h.cells, h.baseGt, h.expr, h.isDigit,
      h.recLen, h.radixLe, h.radixDigits, h.rangeLe⟩⟩

variable (ir) in
/-- **The facts of the committed-digits lookup `lk` at digit `j` of the `mod_q` `m`, as a check**
(`CommLookupFactsC`): `lk` has one record and a range,
`m` is a `mod_q` of the same domain. -/
def commLookupCB (G : Gens) (lk m j : ℕ) : Bool :=
  match (ir.predicate lk).body, (ir.predicate m).body with
  | .mem d [rec] (.range N) (.lookup r), .mod d' q e e' real =>
    decide (d' = d) && decide (ir.CommLookupFactsC G lk d rec N r m j q e e' real)
  | _, _ => false

variable (ir L) in
/-- **The honest-quotient facts of a source committed-digits `mod_q`** `m` with body
`mod d q e e' real`: `q > 0`, `p > 2`; the sides' intervals from the source values
(`srcIvl`) within the exported `[lhsLo, lhsHi]` and `[rhsLo, rhsHi]`; the honest quotient
`(e − e')/q` at least `qlo` and below `qlo + R^K`; the sides read no challenge. -/
structure CommModFactsC (m d q : ℕ) (e e' : Expr) (real : ModRealization) : Prop where
  /-- A source predicate. -/
  source : ir.inSource (ir.predicate m) = true
  /-- The committed-digits form. -/
  form : real.form = .committedDigits
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.srcIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.srcIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The honest quotient is at least `qlo`. -/
  lo : (q : ℤ) * (real.quotientLo - 1) < real.lhsLo - real.rhsHi
  /-- The honest quotient lies below `qlo + R^K`. -/
  hi : real.lhsHi - real.rhsLo <
    (q : ℤ) * (real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ))
  /-- The radix is positive. -/
  radixPos : 0 < real.radix
  /-- The sides read no challenge and no late value. -/
  noChal : ∀ w ∈ ir.exprNodes e ++ ir.exprNodes e', (ir.readsT.getD w []).isEmpty = true

instance (m d q : ℕ) (e e' : Expr) (real : ModRealization) :
    Decidable (ir.CommModFactsC L m d q e e' real) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩,
     fun h => ⟨h.source, h.form, h.qpos, h.char, h.lhs, h.rhs, h.lo, h.hi, h.radixPos,
      h.noChal⟩⟩

variable (ir primeNodes) in
/-- **Predicate `m` is a source committed-digits `mod_q` with its honest-quotient facts**
(`CommModFactsC` at the values' intervals `srcLeafIvl`), as a check. -/
def commModCB (S : Structure) (m : ℕ) : Bool :=
  match (ir.predicate m).body with
  | .mod d q e e' real => decide (ir.CommModFactsC (ir.srcLeafIvl primeNodes S) m d q e e' real)
  | _ => false

variable (L) in
/-- **Predicate `m` is a source committed-digits `mod_q` with its honest-quotient facts**
(`CommModFactsC` at the values' intervals `L`), as a check at a program reader: the facts' decisions
in their order, the intervals and the reads through the reader (`commModCB_ofProgram`). -/
def PReader.commModCB (ir : RealizedProgram) [r : PReader] (m : ℕ) : Bool :=
  match (r.predicate m).body with
  | .mod d q e e' real =>
    ir.inSource (r.predicate m) && decide (real.form = .committedDigits) && decide (0 < q) &&
      decide (2 < ir.charOf (ir.domainField d)) &&
      decide (IvlWithin (PReader.srcIvl L ir (ir.domainField d) e) real.lhsLo real.lhsHi) &&
      decide (IvlWithin (PReader.srcIvl L ir (ir.domainField d) e') real.rhsLo real.rhsHi) &&
      decide ((q : ℤ) * (real.quotientLo - 1) < real.lhsLo - real.rhsHi) &&
      decide (real.lhsHi - real.rhsLo <
        (q : ℤ) * (real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ))) &&
      decide (0 < real.radix) &&
      (ir.exprNodes e ++ ir.exprNodes e').all fun w => (r.reads w).isEmpty
  | _ => false

end

end GordieHowe.RealizedProgram
