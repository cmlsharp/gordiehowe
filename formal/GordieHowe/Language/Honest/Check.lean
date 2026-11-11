-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Realizations.Derivation.Events
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.Honest.Check

@[expose] public section

/-!
# GordieHowe: the MAC sites and the Boolean checks on a program's values and groups

The pieces of a program the completeness certificate's checks read
(`GordieHowe/Language/Completeness/Check.lean`), each stated for any realized program:

* **the MAC sites** (`MacSite`, read at a `macSite` structure record by `macSiteAt`): the MAC check
  over `y`'s field for every cross-field `equal` its `x` domain hosts, and the checks over both
  fields for every cross-field `equal` no domain hosts (compiler/mac.h, `mac_odd`), each with its
  tail named by the record (`macTail`, `twoTail`), the parts of the tail (`macTailParts`,
  `macGrouping`, `macLow`, `macTop`) and the site's check over a field (`macFieldCheckB`);
* **the predicates' roles** in a MAC (`MacRole`), which the completeness steps name;
* **the groups** (`staticGroupNoLateB`, `allGroupsB`): a late histogram the only one of its group or
  beside a static one;
* **the values** (`allValuesB`, `typedNoLateB`, `blindsB`, `noGenReadB`, `srcNoPadCopyB`,
  `srcNoMessageB`, `srcLatePadB`, `cellB`, `realTypeB`), each with its soundness
  lemma.

The definitions are in `GordieHoweNative/Language/Honest/Check.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

/-! ## The parts of a cross-field `equal` and of a `mod_q` -/

theorem PredBody.eq_of_crossParts? {b : PredBody} {c : CrossParts} (h : b.crossParts? = some c) :
    b = .cross c.dx c.x c.dy c.y c.k c.real := by
  unfold crossParts? at h
  split at h
  · cases h
    rfl
  · cases h

theorem PredBody.eq_of_modParts? {b : PredBody} {m : ModParts} (h : b.modParts? = some m) :
    b = .mod m.d m.q m.lhs m.rhs m.real := by
  unfold modParts? at h
  split at h
  · cases h
    rfl
  · cases h

theorem Expr.eq_leaf_of_isLeaf {e : Expr} (h : e.isLeaf = true) : ∃ v, e = .leaf v := by
  cases e <;> simp_all [isLeaf]

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}
  {L : ℕ → ℕ → Option Ivl}

/-! ## The MAC of a cross-field `equal` -/

/-- **A cross-field `equal` is its parts** (`macCross`). -/
theorem body_eq_macCross {pid : ℕ} (h : ir.isCrossB pid = true) :
    (ir.predicate pid).body = .cross (ir.macCross pid).dx (ir.macCross pid).x (ir.macCross pid).dy
      (ir.macCross pid).y (ir.macCross pid).k (ir.macCross pid).real := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  have hm : ir.macCross pid = c := by simp [macCross, hc]
  rw [hm, ← predicateT_eq]
  exact PredBody.eq_of_crossParts? hc

/-- **The MAC convolution's largest entry is `macConvMaxAt`** where `macConvMax?` succeeds. -/
theorem convMax_eq_macConvMaxAt {st : MacSite}
    (h : (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome = true) :
    Conv.convMax (ir.macUnitsAt st).width (ir.macUnitsAt st).taps.toFinset = ir.macConvMaxAt st := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [convMax_of_macConvMax? hc]
  simp [macConvMaxAt, hc]

/-! ## The MAC checks over the fields of characteristic `2` -/

theorem isCrossB_of_body {pid dx dy : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hb : (ir.predicate pid).body = .cross dx x dy y k real) : ir.isCrossB pid = true := by
  simp [isCrossB, predicateT_eq, hb, PredBody.crossParts?]

/-! ## The groups and their histograms -/

theorem of_allGroupsB {P : ℕ → ℕ → Bool} (h : ir.allGroupsB P = true) {t g : ℕ}
    (ht : t < ir.tables.length) (hg : g < ir.groupCountOf t) : P t g = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h t (List.mem_range.2 ht)) g (List.mem_range.2 hg)

/-- **The table's entries are distinct in the challenge's field** below its characteristic. -/
theorem natCast_inj_of_le_char (hI : I.Registered ir) {f n : ℕ} (hf : f < ir.fields.length)
    (hn : n ≤ ir.charOf f) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : ((a : ℕ) : (I f).K) = (b : ℕ)) : a = b := by
  have := charP_field hI hf
  exact ((CharP.natCast_eq_natCast (I f).K (ir.field f).characteristic).1 h).eq_of_lt_of_lt
    (lt_of_lt_of_le ha hn) (lt_of_lt_of_le hb hn)

variable (ir) in
/-- **`staticGroupNoLateB` at the program.** -/
theorem staticGroupNoLateB_eq (t g : ℕ) :
    ir.staticGroupNoLateB t g =
      match (ir.groupOf t g).lateMult with
      | none => (ir.members t g).all (fun m =>
            (ir.exprNodes (ir.needleExpr m.pred m.needle)).all ir.noLateReadB) &&
          (ir.groupOf t g).staticMult.toList.all ir.noLateReadB &&
          (ir.tableRowReads t).all ir.noLateReadB
      | some _ => true :=
  rfl

theorem staticGroups_of_B (hwf : ir.WellFormed) (h : ir.allGroupsB ir.staticGroupNoLateB = true) :
    ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t,
      (ir.groupOf t g).lateMult = none →
        (∀ m ∈ ir.members t g, ∀ w ∈ ir.exprNodes (ir.needleExpr m.pred m.needle),
          ir.NoLateRead w) ∧ (∀ v ∈ (ir.groupOf t g).staticMult.toList, ir.NoLateRead v) ∧
          ∀ w ∈ ir.tableRowReads t, ir.NoLateRead w := by
  intro t ht g hg hv
  have hB := of_allGroupsB h ht hg
  rw [staticGroupNoLateB_eq] at hB
  rw [hv] at hB
  simp only [Bool.and_eq_true, List.all_eq_true] at hB
  exact ⟨fun m hm w hw => noLateRead_of_B hwf (hB.1.1 m hm w hw),
    fun v hv => noLateRead_of_B hwf (hB.1.2 v hv), fun w hw => noLateRead_of_B hwf (hB.2 w hw)⟩

/-! ## The values -/

section Values

variable (ir)

/-- **A property of every value of the program**, as a check. -/
def allValuesB (P : ℕ → Bool) : Bool := (List.range ir.values.length).all P

/-- **The pad space of value `v` contains the naturals by a listed node**, as a check: the whole
field, or a node of `L` in the value's field. -/
def padNatB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  match (ir.value v).padSpace with
  | .full => true
  | .node S => L.contains (ir.valueField v, S)

/-- **A node-typed value that is not late reads no late value** (`CompletionFacts.typedNoLate`), as
a check at value `v`. -/
def typedNoLateB (v : ℕ) : Bool :=
  !((ir.value v).typeSource == .node) || decide (ir.IsLate v) || ir.noLateReadB v

end Values

theorem of_allValuesB {P : ℕ → Bool} (h : ir.allValuesB P = true) {v : ℕ}
    (hv : v < ir.values.length) : P v = true :=
  List.all_eq_true.1 h v (List.mem_range.2 hv)

theorem of_allPredsB {P : ℕ → Bool} (h : ir.allPredsB P = true) {q : ℕ}
    (hq : q < ir.predicates.length) : P q = true :=
  List.all_eq_true.1 h q (List.mem_range.2 hq)

theorem noGenRead_of_B (hwf : ir.WellFormed) {w : ℕ} (h : ir.noGenReadB w = true) :
    ir.NoGenRead w := by
  intro u hu hlt hl
  have := List.all_eq_true.1 h _ ((mem_readsT hwf w _).1 hu)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    not_and] at this
  rcases this with h1 | h1
  · exact absurd hl (h1 hlt)
  · exact h1

theorem noGenPred_of_B (hwf : ir.WellFormed) {b : PredBody}
    (hr : ir.BodyRefsOk b) (h : ir.noGenPredB b = true) :
    ir.NoGenPred b := fun w hw =>
  noGenRead_of_B hwf (List.all_eq_true.1 h w ((mem_predNodesM hwf.refsOrdered hr w).2 hw))

theorem typedNoLate_of_B (hwf : ir.WellFormed) (h : ir.allValuesB ir.typedNoLateB = true) :
    ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v → ir.NoLateRead v := by
  intro v hv hts hl
  have hB := of_allValuesB h hv
  unfold typedNoLateB at hB
  simp only [hts, beq_self_eq_true, Bool.not_true, Bool.false_or, hl, decide_false] at hB
  exact noLateRead_of_B hwf hB

theorem blinds_of_B (h : ir.allPredsB ir.blindsB = true) : ir.BlindsArePadCopies := by
  intro p hp dx x dy y k real hb b hbm
  obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
  have hB := of_allPredsB h hq
  unfold blindsB at hB
  rw [predicateT_eq, hb] at hB
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hB b hbm
  exact ⟨kind_of_isPadCopyB h1, h2, fun i hi => (ir.mem_cellKeys_val).2 ⟨h3, h4, by omega⟩, h6,
    (ir.mem_cellKeys_pad).2 ⟨h7, h8, h9, h10⟩⟩

/-! ## The value facts -/

section Honest

variable (ir)

/-- **No source value is a pad copy** (`CommittedFacts.srcNoPadCopy`), as a check at value `u`. -/
def srcNoPadCopyB (u : ℕ) : Bool := !decide (ir.IsSourceValue u) || !(ir.value u).kind.isPadCopy

/-- **No source value is a message** (`SrcNoMessage`), as a check at value `v`. -/
def srcNoMessageB (v : ℕ) : Bool := !decide (ir.IsSourceValue v) || !(ir.value v).kind.isMessage

/-- **A source late value's pad space contains its type** (`CommittedFacts.srcLatePads`), as a check
at value `v`. -/
def srcLatePadB (v : ℕ) : Bool :=
  !decide (ir.IsSourceValue v) || !decide (ir.IsLate v) || ir.latePadTypeB v

/-- **A committed cell is at a node of its source value's type, a node of `L`**
(`CommittedFacts.cellNodes`, `CommittedFacts.oneMem`), as a check at value `v`. -/
def cellB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  !ir.isCellValue (ir.value v).domain v || (ir.cellNodeB v && ir.cellNodeInB L v)

/-- A checked committed cell lies at one of the listed nodes. -/
theorem cellNodeInB_of_cellB {L : List (ℕ × String)} {v : ℕ}
    (h : ir.cellB L v = true) (hc : ir.isCellValue (ir.value v).domain v = true) :
    ir.cellNodeInB L v = true := by
  simp only [cellB, hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.2

/-- **A node-typed value that is no source value and no late value is a committed cell whose type
contains the naturals by a node of `L`** (`CommittedFacts.realTypes`), as a check at value `v`. -/
def realTypeB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  !((ir.value v).typeSource == .node) || decide (ir.IsLate v) || decide (ir.IsSourceValue v) ||
    (ir.privCellB v && ir.natTypedInB L v)

/-- A checked node-typed realization value that is not late has committed cells. -/
theorem privCellB_of_realTypeB {L : List (ℕ × String)} {v : ℕ}
    (h : ir.realTypeB L v = true) (ht : (ir.value v).typeSource = .node)
    (hl : ¬ ir.IsLate v) (hs : ¬ ir.IsSourceValue v) : ir.privCellB v = true := by
  simp only [realTypeB, ht, beq_self_eq_true, Bool.not_true, decide_eq_false hl,
    decide_eq_false hs, Bool.false_or, Bool.and_eq_true] at h
  exact h.1

end Honest

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

end

end GordieHowe.RealizedProgram
