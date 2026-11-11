-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Library.Table
public import GordieHoweNative.Language.RealizedProgram.Shapes

/-!
# GordieHowe: the compiled check of a program's table selections

The check the frontends' table selections (`GordieHowe.RealizedProgram.TableSelect`) read, in the
Mathlib-free library `GordieHoweNative`. The compiler emits one certificate per `select_row`
(`lib/gordiehowe/lib/table.h`): the selection's fingerprint predicate and the gadget's identifiers
(`SelCert`). The check confirms each certificate's gadget facts (`TableShape.selectB`: the facts
`TableSelect` states). Their lemmas are in `GordieHowe/Language/Realizations/SelectionCheck.lean`,
which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A table-selection certificate** (`select_row`): predicate `q` is the fingerprint equation of
the gadget `table`. -/
structure SelCert where
  /-- The selection's fingerprint predicate. -/
  q : ℕ
  /-- The gadget's identifiers and row map. -/
  table : TableShape

section

variable (ir : RealizedProgram)

namespace TableShape

variable (t : TableShape)

/-- **The gadget's facts** (the fields of `GordieHowe.RealizedProgram.TableSelect`): the matchers
(`okB`), the powers and the digests public expressions, the index bits' check, the selection's two
predicates source predicates, the constants `1` and `0`, `γ` its challenge of one full coordinate
in the domain's field, the values read in the domain's field and of their sizes, the index bits
committed, the record reading only committed values and constants, the rows only the statement. -/
def selectB : Bool :=
  t.okB ir && decide (0 < ir.exprs.length) && decide (0 < ir.values.length) &&
    (ir.value t.pow).kind.isExprB && (ir.value t.dig).kind.isExprB &&
    (ir.predicate t.idxPred).body.isEqualB t.dom (.mul (.leaf t.idx) (.leaf t.idx)) (.leaf t.idx) &&
    [t.pred, t.idxPred].all (fun p => decide (p < ir.predicates.length) &&
      ir.inSource (ir.predicate p)) &&
    ir.isConstant t.one && (ir.constEntries t.one).getD 0 0 == 1 &&
    ir.isConstant t.zero && (ir.constEntries t.zero).getD 0 0 == 0 &&
    (ir.value t.gamma).kind.isChallengeB t.chal &&
    (ir.challenge t.chal).size == 1 && (ir.challenge t.chal).isFullB &&
    ir.chalField t.chal == ir.domainField t.dom &&
    (([t.one, t.zero, t.gamma, t.pow, t.dig, t.idx] ++ t.parts.map (·.1)).all fun v =>
      ir.valueField v == ir.domainField t.dom) &&
    (ir.value t.one).size == 1 && (ir.value t.gamma).size == 1 &&
    (ir.value t.idx).size == t.bits && (ir.value t.dig).size == 2 ^ t.bits &&
    (ir.value t.pow).size == (powerExps t.map).length &&
    (ir.value t.idx).kind.isPrivB &&
    (ir.exprNodes t.record).all (fun v => (ir.nodeReads ir.fuel v).isEmpty) &&
    t.parts.all (fun p => (ir.nodeReads ir.values.length p.1).isEmpty)

end TableShape

/-- **The program's table selections**: every certificate's gadget facts hold. -/
def selectionsB (cs : List SelCert) : Bool :=
  cs.all (fun c => c.table.selectB ir)

end

end GordieHowe.RealizedProgram
