-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.TableSelect
public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.RealizedProgram.Shapes
public import GordieHoweNative.Language.Realizations.SelectionCheck

@[expose] public section

/-!
# GordieHowe: the table selections from the program check

The check `selectionsB` (`GordieHoweNative/Language/Realizations/SelectionCheck.lean`) gives the
table selection of every certificate (`TableSelect.ofCheck`, `TableSelect.ofSelections`): the
gadget's facts (`TableShape.selectB`) are the fields of `GordieHowe.RealizedProgram.TableSelect`,
so a frontend reads its selection from the check.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-! ## The gadget's facts -/

section Gadget

variable {ir : RealizedProgram} {t : TableShape}

theorem isExprB_spec {k : Kind} (h : k.isExprB = true) : ∃ e, k = .pub (.expr e) := by
  revert h
  rcases k with _ | (_ | _ | e) | _ | _ | _ | _ | _ | _ | _ <;> simp [Kind.isExprB]

theorem isPrivB_spec {k : Kind} (h : k.isPrivB = true) : k = .priv := by
  revert h
  cases k <;> simp [Kind.isPrivB]

theorem isChallengeB_spec {k : Kind} {c : ℕ} (h : k.isChallengeB c = true) : k = .challenge c := by
  revert h
  cases k <;> simp [Kind.isChallengeB]

theorem isEqualB_spec {b : PredBody} {d : ℕ} {lhs rhs : Expr} (h : b.isEqualB d lhs rhs = true) :
    ∃ tg, b = .equal d lhs rhs tg := by
  revert h
  rcases b with ⟨d', l, r, tg⟩ | _ | _ | _ <;> simp only [PredBody.isEqualB,
    Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, false_implies]
  rintro ⟨⟨rfl, hl⟩, hr⟩
  exact ⟨tg, by rw [Expr.eq_of_beq hl, Expr.eq_of_beq hr]⟩

theorem isFullB_spec {c : Challenge} (h : c.isFullB = true) : c.sampler = .full := by
  revert h
  unfold Challenge.isFullB
  split <;> simp_all

/-- **The gadget's facts a passing certificate states** (`TableShape.selectB`): the fields of
`TableSelect` at the shape `t`, apart from the shared expressions' order. -/
structure TableShape.SelectFacts (ir : RealizedProgram) (t : TableShape) : Prop where
  exprs_pos : 0 < ir.exprs.length
  values_pos : 0 < ir.values.length
  mapWf : mapWfFrom 0 t.map = true
  width : mapWidth t.map = (t.parts.map (·.2)).sum
  powOk : ir.powSym ⟨onePub t.one t.gamma, none⟩ powFuel (t.powExpr ir) = some (powerExps t.map)
  digOk : ir.digestsOk (t.pubCtx ir) t.map t.parts t.rows (2 ^ t.bits) (t.digExpr ir) = true
  bodyOk : t.bodyOk ir (ir.predicate t.pred).body = true
  powKind : (ir.value t.pow).kind = .pub (.expr (t.powExpr ir))
  digKind : (ir.value t.dig).kind = .pub (.expr (t.digExpr ir))
  idxBool : ∃ tg, (ir.predicate t.idxPred).body =
    .equal t.dom (.mul (.leaf t.idx) (.leaf t.idx)) (.leaf t.idx) tg
  inSource : ∀ p ∈ [t.pred, t.idxPred],
    p < ir.predicates.length ∧ ir.inSource (ir.predicate p) = true
  consts : ir.isConstant t.one = true ∧ (ir.constEntries t.one).getD 0 0 = 1 ∧
    ir.isConstant t.zero = true ∧ (ir.constEntries t.zero).getD 0 0 = 0
  gammaKind : (ir.value t.gamma).kind = .challenge t.chal
  chalOk : (ir.challenge t.chal).size = 1 ∧ (ir.challenge t.chal).sampler = .full ∧
    ir.chalField t.chal = ir.domainField t.dom
  fields : ∀ v ∈ [t.one, t.zero, t.gamma, t.pow, t.dig, t.idx] ++ t.parts.map (·.1),
    ir.valueField v = ir.domainField t.dom
  sizes : (ir.value t.one).size = 1 ∧ (ir.value t.gamma).size = 1 ∧
    (ir.value t.idx).size = t.bits ∧ (ir.value t.dig).size = 2 ^ t.bits ∧
    (ir.value t.pow).size = (powerExps t.map).length
  idxPriv : (ir.value t.idx).kind = .priv
  recordReads : ∀ v ∈ ir.exprNodes t.record, ir.nodeReads ir.fuel v = []
  rowReads : ∀ p ∈ t.parts, ir.nodeReads ir.values.length p.1 = []

/-- **`TableShape.selectB` decides the gadget's facts.** -/
theorem TableShape.selectFacts_of_selectB (h : t.selectB ir = true) : t.SelectFacts ir := by
  unfold TableShape.selectB TableShape.okB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩, a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩, a21⟩, a22⟩, a23⟩, a24⟩, a25⟩, a26⟩, a27⟩, a28⟩ := h
  exact ⟨a6, a7, a1, a2, a3, a4, a5, TableShape.powKind_of_exists (isExprB_spec a8),
    TableShape.digKind_of_exists (isExprB_spec a9), isEqualB_spec a10, a11, ⟨a12, a13, a14, a15⟩,
    isChallengeB_spec a16, ⟨a17, isFullB_spec a18, a19⟩, a20, ⟨a21, a22, a23, a24, a25⟩,
    isPrivB_spec a26, a27, a28⟩

/-- **The table selection a passing certificate states** (`TableShape.selectB`): its gadget's
facts are the fields of `TableSelect`. -/
@[instance_reducible] def TableSelect.ofCheck (hwf : ir.WellFormed) (h : t.selectB ir = true) :
    TableSelect ir :=
  have F := TableShape.selectFacts_of_selectB h
  { shape := t
    refsOrdered := hwf.refsOrdered
    exprs_pos := F.exprs_pos
    values_pos := F.values_pos
    mapWf := F.mapWf
    width := F.width
    powOk := F.powOk
    digOk := F.digOk
    bodyOk := F.bodyOk
    powKind := F.powKind
    digKind := F.digKind
    idxBool := F.idxBool
    inSource := F.inSource
    consts := F.consts
    gammaKind := F.gammaKind
    chalOk := F.chalOk
    fields := F.fields
    sizes := F.sizes
    idxPriv := F.idxPriv
    recordReads := F.recordReads
    rowReads := F.rowReads }

/-- **The certificate's table selection has the certificate's shape.** -/
theorem TableSelect.ofCheck_shape (hwf : ir.WellFormed) (h : t.selectB ir = true) :
    @TableSelect.shape ir (TableSelect.ofCheck hwf h) = t := rfl

end Gadget

/-- **Every certificate of a passing check states its gadget's facts** (`TableShape.selectB`). -/
theorem selectB_of_selectionsB {ir : RealizedProgram} {cs : List SelCert}
    (h : ir.selectionsB cs = true) {c : SelCert} (hc : c ∈ cs) : c.table.selectB ir = true := by
  unfold selectionsB at h
  rw [List.all_eq_true] at h
  exact h c hc

/-- **The table selection of certificate `i` of a passing check** (`TableSelect.ofCheck`): a
frontend's `TableSelect` from the program check, its shape the certificate's. -/
@[instance_reducible] def TableSelect.ofSelections {ir : RealizedProgram} (hwf : ir.WellFormed)
    {cs : List SelCert} (h : ir.selectionsB cs = true) (i : Fin cs.length) : TableSelect ir :=
  TableSelect.ofCheck hwf (selectB_of_selectionsB h (List.get_mem cs i))

end GordieHowe.RealizedProgram
