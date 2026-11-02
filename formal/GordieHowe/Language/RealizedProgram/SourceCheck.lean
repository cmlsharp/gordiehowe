-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Source
public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the source part's checks through the tables

The well-formedness of the source part (`GordieHowe.RealizedProgram.SourceValid`) from Boolean checks
that read the values' dependencies and run reads through the memoized tables
(`GordieHowe.RealizedProgram.nodesOf`, `GordieHowe.RealizedProgram.readsT`) instead of the recursions
`exprNodes` and `nodeReads`, for programs whose recursions are too deep to decide directly:

* **the dependencies through the table** (`valueDepsM`, `mem_valueDepsM`): `valueDeps` with a public
  expression's values read through `nodesOf`, the same members in a well-formed program;
* **the source values as a bit set** (`nonSourceBits`, `srcB`, `srcB_iff`): the positions of the
  values of another role, built in one walk of the values, so a test of a value is one
  `Nat.testBit`, where `IsSourceValue` looks the value up in the values' trie;
* **the checks** (`SourceValid.of_checks`): the four fields of `SourceValid`, each a Boolean `all`
  over the challenges, the predicates or the values; the values' checks walk the values (zipped
  with their reads, `readsL`) instead of looking each up, and every value read is tested by `srcB`.
-/

namespace GordieHowe.RealizedProgram

open Export

variable (ir : RealizedProgram)

/-- **The values the definition of value `v` reads, through the table**: `valueDeps`, a public
expression's values read through `nodesOf`. -/
def valueDepsM (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .pub (.expr e) => ir.nodesOf e
  | .pub (.opaque _ args) => args
  | .bits w _ => [w]
  | _ => []

/-- **The values the definition of a value `x` reads, through the table**: `valueDepsM` at a
value read from the walk (`valueDepsM_eq`). -/
def valueDepsOf (x : Value) : List ℕ :=
  match x.kind with
  | .pub (.expr e) => ir.nodesOf e
  | .pub (.opaque _ args) => args
  | .bits w _ => [w]
  | _ => []

theorem valueDepsM_eq (v : ℕ) : ir.valueDepsM v = ir.valueDepsOf (ir.value v) := rfl

/-- **The values of another role than `source`**, as a bit set (`failBits`): bit `v` set when value
`v` exists and its role is not `source`. -/
def nonSourceBits : ℕ := failBits (fun _ (x : Value) => x.role == .source) ir.values 0

/-- **Value `v` is a source value, as a test**: its bit is clear in `nonSourceBits` (`srcB_iff`). A
value past the end is the default value, of role `source`, as `IsSourceValue` reads it. -/
def srcB (v : ℕ) : Bool := bitTest ir.nonSourceBits ir.values.length true v

/-- **`inSource` with the value read by `srcB`** (`inSourceB_eq`). -/
def inSourceB (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => ir.srcB v
  | .realization _ => false

/-- **`SourceRead` as a test**, a late value read by `srcB` (`srcReadB_iff`). -/
def srcReadB : Read → Bool
  | .chal c => ir.chalIsSource c
  | .late u => ir.srcB u
  | .pad _ => false

variable {ir}

theorem srcB_iff (v : ℕ) : ir.srcB v = true ↔ ir.IsSourceValue v := by
  have h := bitTest_eq (fun _ (x : Value) => x.role == .source) ir.values v
  change ir.srcB v = _ at h
  rw [h, IsSourceValue, value_eq_getD, beq_iff_eq]

theorem srcB_eq (v : ℕ) : ir.srcB v = decide (ir.IsSourceValue v) := by
  by_cases h : ir.IsSourceValue v
  · rw [decide_eq_true h, (srcB_iff v).2 h]
  · rw [decide_eq_false h, Bool.eq_false_iff, Ne, srcB_iff]
    exact h

theorem inSourceB_eq (p : Predicate) : ir.inSourceB p = ir.inSource p := by
  unfold inSourceB inSource
  rcases p.role with _ | _ | v <;> simp only [srcB_eq]

theorem srcReadB_iff (rd : Read) : ir.srcReadB rd = true ↔ ir.SourceRead rd := by
  cases rd <;> simp [srcReadB, SourceRead, srcB_iff]

/-- **The dependencies through the table are the dependencies** in a well-formed program. -/
theorem mem_valueDepsM (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length) (u : ℕ) :
    u ∈ ir.valueDepsM v ↔ u ∈ ir.valueDeps v := by
  unfold valueDepsM valueDeps
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    try exact Iff.rfl
  exact mem_nodesOf hwf.refsOrdered (hwf.pubExpr_refs hv hk) u

/-- **The source part is well formed from its checks through the tables**: the challenges' roles,
the source predicates' values (each expression's through the flags' table `closFlag`), the source values' dependencies (`valueDepsOf`) and
run reads (`readsL`), each a Boolean `all`, every value read tested by `srcB`; the values' checks
are walks of the values. -/
theorem SourceValid.of_checks (hwf : ir.WellFormed)
    (hr : (List.range ir.challenges.length).all ir.chalRoleOk = true)
    (hp : ir.predicates.all (fun p => !ir.inSourceB p ||
      (p.body.exprs.all (ir.closFlag Expr.directNodes ir.srcB ·.2) &&
        (ir.tableCols p.body).all ir.srcB)) = true)
    (hv : allIdx (fun _ x => !(x.role == .source) || (ir.valueDepsOf x).all ir.srcB) ir.values 0 =
      true)
    (hd : allIdx (fun _ xr => !(xr.1.role == .source) || xr.2.all ir.srcReadB)
      (ir.values.zip ir.readsL) 0 = true) :
    ir.SourceValid where
  roles j hj := List.all_eq_true.1 hr j (List.mem_range.2 hj)
  preds p hp' hs u hu := by
    have h := List.all_eq_true.1 hp p hp'
    rw [inSourceB_eq, hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
      List.all_eq_true] at h
    refine (srcB_iff u).1 ?_
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨de, hde, hu⟩ := List.mem_flatMap.1 hu
      have := h.1 de hde
      rw [closFlag_eq hwf.refsOrdered _ _ (hwf.bodyRefsOk hp' de hde), List.all_eq_true] at this
      exact this u hu
    · exact h.2 u hu
  values v hv' hs u hu := by
    have h := (allIdx_iff _ ir.values 0).1 hv v hv'
    rw [← value_eq_getD, show ((ir.value v).role == .source) = true from beq_iff_eq.2 hs,
      Bool.not_true, Bool.false_or, ← valueDepsM_eq, List.all_eq_true] at h
    exact (srcB_iff u).1 (h u ((mem_valueDepsM hwf hv' u).2 hu))
  reads v hv' hs rd hrd := by
    have hlen : (ir.values.zip ir.readsL).length = ir.values.length := by
      rw [List.length_zip, readsL, memoList, length_memoAuxL_snd, Nat.min_self]
    have h := (allIdx_iff _ (ir.values.zip ir.readsL) 0).1 hd v (hlen ▸ hv')
    have hz : (ir.values.zip ir.readsL).getD v default = (ir.value v, ir.readsT.getD v []) := by
      have hl : v < ir.readsL.length := by
        rw [readsL, memoList, length_memoAuxL_snd]
        exact hv'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hv'), Option.getD_some,
        List.getElem_zip, value_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv',
        Option.getD_some, ← getD_readsL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
        Option.getD_some]
    rw [hz, show ((ir.value v).role == .source) = true from beq_iff_eq.2 hs,
      Bool.not_true, Bool.false_or, List.all_eq_true] at h
    exact (srcReadB_iff rd).1 (h rd ((mem_readsT hwf v rd).1 hrd))

end GordieHowe.RealizedProgram
