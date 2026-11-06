-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldTree
public import GordieHowe.Language.RealizedProgram.InputLayout
public import GordieHowe.Language.RealizedProgram.CellsLowering
public import GordieHowe.Language.Realizations.CircuitInput
public import GordieHoweNative.ProofSystem.Program.FieldInput

@[expose] public section

/-!
# GordieHowe: a domain's GKR circuits on its tree's coordinates

Every GKR circuit `c` of domain `d` read on the logical coordinates of `d`'s packing tree
(`GordieHowe.RealizedProgram.TLog`), and the compiler correspondence's soundness direction, for any number of circuits
in the domain:

* **The input layout** (`GordieHowe.RealizedProgram.InputsT`, decided by `inputsTB` in a well-formed
  program): contiguous blocks; committed blocks holding
  every coordinate of a committed value of `d`, pad blocks of its late values, view blocks of its
  bit views, filler, all among the private inputs; public blocks of values of the circuit's field
  reading nothing of the committed assignment, or late values (read as their messages); the batch
  pads after the private block; every committed value and every late value of `d` has a block, and
  so do the words every view block reads.
* **The viewed words** (`GordieHowe.RealizedProgram.ViewsOk`, decidable): every bit view of `d` reads words of a value
  whose node has a view child (`viewChild`), the value's type named after its node.
* **The input forms** (`GordieHowe.RealizedProgram.treeInputForms`): the public inputs the verifier's
  (`GordieHowe.RealizedProgram.publicInput`), private input `q` the coordinate its block holds (`GordieHowe.RealizedProgram.inputCoord`:
  a committed or pad coordinate's cell `place`, a bit view's word bit `viewPlace`, a filler cell),
  zero after the private block (the batch pads, which no gate reads).
* **The proof system's premises** (`GordieHowe.RealizedProgram.inputPremises_treeInput`): on the input of the
  logical assignment of any committed cells, every view input is the bit of the committed word it
  aliases, so the decoded valuation reads the bit views as the semantics does (`InputPremises`).
* **Soundness** (`GordieHowe.RealizedProgram.circuitHolds_of_treeInput`): the trust bundle `CircuitsEnforce` turns the
  source's satisfaction on the input of the logical assignment of any committed cells into the
  circuit's meaning at the decoded cells' valuation: the valuation the bundle decodes is the
  decoded cells' valuation (`inputValuation_treeInput`), the view inputs being the decoded words'
  bits (`treeBits_eq`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge

section

variable (ir : RealizedProgram) {I : Interp} (d : ℕ) {Pk : (I (ir.domainField d)).Packing}
  (rs : List (REdge (I (ir.domainField d)) Pk)) (Pads : Type)

/-! ## The input layout -/

/-- **Block `b` of circuit `c` of domain `d` is plain** (see the module docstring). -/
def blockOkT (c : ℕ) : InputBlock → Bool
  | .committed u a n => decide (u < ir.values.length) && ir.isCellValue d u &&
      decide (n = (ir.value u).size) && decide ((ir.circuit c).publicInputs ≤ a) &&
      decide (a + n ≤ ir.privEnd c)
  | .pad u a n => decide (u < ir.values.length) && !ir.isCellValue d u &&
      ir.isLateOf d u && decide (n = (ir.value u).size) &&
      decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .pub u a n => decide (ir.valueField u = ir.circField c) &&
      (decide (ir.IsLate u) || ir.pubB ir.fuel u) && decide (1 ≤ a) &&
      decide (a + n ≤ (ir.circuit c).publicInputs)
  | .realizationPub _ a n => decide (1 ≤ a) && decide (a + n ≤ (ir.circuit c).publicInputs)
  | .filler a n => decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .view u a n => ir.bitViewOk d u && decide (n ≤ (ir.value u).size) &&
      decide ((ir.circuit c).publicInputs ≤ a) && decide (a + n ≤ ir.privEnd c)
  | .batchPads _ a n => decide (ir.privEnd c ≤ a) && decide (a + n ≤ (ir.circuit c).inputCount)

/-- **`blockOkT`, decided**: a public block's value read through the table `pubT`. -/
def blockOkB (c : ℕ) : InputBlock → Bool
  | .pub u a n => decide (ir.valueField u = ir.circField c) &&
      (decide (ir.IsLate u) || ir.pubT.getD u false) && decide (1 ≤ a) &&
      decide (a + n ≤ (ir.circuit c).publicInputs)
  | b => ir.blockOkT d c b

/-- **The values entry `e` reads**, through the tables: a placed predicate's (`predNodesM`), a
LogUp identity's (`logupNodes`), an H half's (`macHNodes`); nothing for an alignment or another
realization circuit. -/
def entryNodesM : CircuitEntry → List ℕ
  | .pred p => ir.predNodesM (ir.predicate p).body
  | .typeCheck p => ir.predNodesM (ir.predicate p).body
  | .realization (.logup t g) => ir.logupNodes t g
  | .realization (.macH p) => ir.macHNodes p
  | _ => []

/-- **The values circuit `c`'s entries read** (`entryNodesM`). -/
def circValues (c : ℕ) : List ℕ := (ir.circuit c).entries.flatMap ir.entryNodesM

/-- **What circuit `c` reads of the committed assignment**: what its entries' values read
(`asgReadsT`). -/
def circReadsT (c : ℕ) : List ℕ := (ir.circValues c).flatMap fun v => ir.asgReadsT.getD v []

/-- **The words a view block of circuit `c` reads have a committed block**: the view's words' value
(`InputBlock.view` of a bit view of the words of `w`) has a committed block in `c`; true at every
other block. -/
def viewWordsCommittedB (c : ℕ) : InputBlock → Bool
  | .view u _ _ =>
    match (ir.value u).kind with
    | .bits w _ => (ir.circuit c).inputs.any (·.isCommittedOf w)
    | _ => true
  | _ => true

/-- **Circuit `c` has a plain input layout covering the values of domain `d` it reads** (see the
module docstring). -/
structure InputsT (c : ℕ) : Prop where
  /-- The blocks are contiguous from input `1` to the input count. -/
  layout : InputBlock.layoutEnd 1 (ir.circuit c).inputs = some (ir.circuit c).inputCount
  /-- The public inputs include the constant one. -/
  one_le : 1 ≤ (ir.circuit c).publicInputs
  /-- The public inputs end by the private block's end. -/
  pubEnd : (ir.circuit c).publicInputs ≤ ir.privEnd c
  /-- Every block is plain. -/
  blocks : ∀ b ∈ (ir.circuit c).inputs, ir.blockOkT d c b = true
  /-- Every entry names a predicate of the program, when it names one. -/
  entries : ∀ e ∈ (ir.circuit c).entries, ir.entryPredOkB e = true
  /-- The entries read values of the program. -/
  valuesLt : ∀ v ∈ ir.circValues c, v < ir.values.length
  /-- Every committed value the circuit reads has a committed block. -/
  coverVal : ∀ v ∈ ir.circReadsT c, ir.isCellValue d v = true →
    (ir.circuit c).inputs.any (·.isCommittedOf v) = true
  /-- Every late value the circuit reads has a pad block. -/
  coverPad : ∀ v ∈ ir.circReadsT c, ir.isLateOf d v = true →
    (ir.circuit c).inputs.any (·.isPadOf v) = true
  /-- The words every view block reads have a committed block. -/
  coverView : ∀ b ∈ (ir.circuit c).inputs, ir.viewWordsCommittedB c b = true

theorem inputsT_iff (c : ℕ) : ir.InputsT d c ↔
    InputBlock.layoutEnd 1 (ir.circuit c).inputs = some (ir.circuit c).inputCount ∧
      1 ≤ (ir.circuit c).publicInputs ∧ (ir.circuit c).publicInputs ≤ ir.privEnd c ∧
      (∀ b ∈ (ir.circuit c).inputs, ir.blockOkT d c b = true) ∧
      (∀ e ∈ (ir.circuit c).entries, ir.entryPredOkB e = true) ∧
      (∀ v ∈ ir.circValues c, v < ir.values.length) ∧
      (∀ v ∈ ir.circReadsT c, ir.isCellValue d v = true →
        (ir.circuit c).inputs.any (·.isCommittedOf v) = true) ∧
      (∀ v ∈ ir.circReadsT c, ir.isLateOf d v = true →
        (ir.circuit c).inputs.any (·.isPadOf v) = true) ∧
      (∀ b ∈ (ir.circuit c).inputs, ir.viewWordsCommittedB c b = true) :=
  ⟨fun h => ⟨h.layout, h.one_le, h.pubEnd, h.blocks, h.entries, h.valuesLt, h.coverVal,
      h.coverPad, h.coverView⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

/-! ### The input layout, decided -/

/-- **The values entry `e` reads other than the challenges' values** (`entryNodesM` without the
value holding a LogUp identity's or an H half's challenge; that value reads nothing of the
committed assignment). -/
def entryNodesC : CircuitEntry → List ℕ
  | .pred p => ir.predNodesM (ir.predicate p).body
  | .typeCheck p => ir.predNodesM (ir.predicate p).body
  | .realization (.logup t g) => ir.logupNodesWith (fun _ => none) t g
  | .realization (.macH p) => ir.macHNodesWith (fun _ => none) p
  | _ => []

/-- **The values circuit `c`'s entries read, other than the challenges' values** (`entryNodesC`). -/
def circValuesC (c : ℕ) : List ℕ := (ir.circuit c).entries.flatMap ir.entryNodesC

/-- **What circuit `c` reads of the committed assignment**, from `circValuesC`. -/
def circReadsC (c : ℕ) : List ℕ := (ir.circValuesC c).flatMap fun v => ir.asgReadsT.getD v []

/-- **The words a view block reads have a committed block**, through the circuit's sets
(`viewWordsCommittedB`). -/
def viewWordsSetB (S : CircuitSets) : InputBlock → Bool
  | .view u _ _ =>
    match (ir.value u).kind with
    | .bits w _ => natMem S.committed w
    | _ => true
  | _ => true

/-- **`InputsT`, decided**: the blocks' coverage read through the circuit's sets
(`circuitSets`), the values the entries read without the challenges' values (`circReadsC`). -/
def inputsTB (c : ℕ) : Bool :=
  let S := circuitSets (ir.circuit c)
  decide (InputBlock.layoutEnd 1 (ir.circuit c).inputs = some (ir.circuit c).inputCount) &&
    decide (1 ≤ (ir.circuit c).publicInputs) &&
    decide ((ir.circuit c).publicInputs ≤ ir.privEnd c) &&
    (ir.circuit c).inputs.all (ir.blockOkB d c) && (ir.circuit c).entries.all ir.entryPredOkB &&
    (ir.circValuesC c).all (· < ir.values.length) &&
    (ir.circReadsC c).all (fun v => (!ir.isCellValue d v || natMem S.committed v) &&
      (!ir.isLateOf d v || natMem S.pad v)) &&
    (ir.circuit c).inputs.all (ir.viewWordsSetB S)

/-- **No value of a challenge reads the committed assignment** (`asgReadsT`). -/
theorem asgReadsT_getD_of_challenge {u j : ℕ} (hk : (ir.value u).kind = .challenge j) :
    ir.asgReadsT.getD u [] = [] := by
  have hF : ∀ r, ir.asgStep r u (ir.values.getD u default) = [] := fun r => by
    rw [← value_eq_getD]
    change ir.asgStep r u (ir.value u) = []
    simp [asgStep, hk]
  have key : ∀ (xs : List Value) (i : ℕ) (t : NatTrie (List ℕ)), ir.values.drop i = xs →
      t.getD u [] = [] → (memoAux ir.asgStep [] xs i t).getD u [] = [] := by
    intro xs
    induction xs with
    | nil => exact fun _ _ _ ht => ht
    | cons x xs ih =>
      intro i t hxs ht
      refine ih (i + 1) _ (by rw [← List.drop_drop, hxs]; rfl) ?_
      rw [NatTrie.getD_set]
      split
      · rename_i hui
        subst hui
        have hx : ir.values[u]? = some x := by
          have := congrArg List.head? hxs
          rwa [List.head?_drop] at this
        have : ir.values.getD u default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
        rw [← this]
        exact hF _
      · exact ht
  rw [asgReadsT, memo_eq]
  exact key ir.values 0 .nil (by simp) (by simp [NatTrie.getD, NatTrie.get?_nil])

/-- **The value holding a challenge** is a value of the program of the challenge's kind. -/
theorem chalNode_spec {j v : ℕ} (h : ir.chalNode j = some v) :
    v < ir.values.length ∧ (ir.value v).kind = .challenge j := by
  unfold chalNode at h
  rw [List.find?_range_eq_some] at h
  obtain ⟨hp, hv, -⟩ := h
  refine ⟨List.mem_range.1 hv, ?_⟩
  revert hp
  cases (ir.value v).kind <;> simp

/-- **The values `entryNodesC` lists are values the entry reads.** -/
theorem mem_entryNodesM_of_C {e : CircuitEntry} {v : ℕ} (h : v ∈ ir.entryNodesC e) :
    v ∈ ir.entryNodesM e := by
  cases e with
  | realization rc =>
    cases rc with
    | logup t g =>
      simp only [entryNodesM, entryNodesC, logupNodes, logupNodesWith, List.mem_append,
        Option.toList_none, List.not_mem_nil, false_or] at h ⊢
      rcases h with ((h | h) | h) | h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
    | macH p =>
      simp only [entryNodesM, entryNodesC, macHNodes, macHNodesWith] at h ⊢
      split at h
      · simp only [List.mem_append, Option.toList_none, List.nil_append] at h ⊢
        exact .inr h
      · simp at h
    | _ => simp [entryNodesC] at h
  | _ => simpa [entryNodesM, entryNodesC] using h

/-- **The values an entry reads are those `entryNodesC` lists, or values holding a challenge.** -/
theorem mem_entryNodesC_or_chal {e : CircuitEntry} {v : ℕ} (h : v ∈ ir.entryNodesM e) :
    v ∈ ir.entryNodesC e ∨ ∃ j, ir.chalNode j = some v := by
  cases e with
  | realization rc =>
    cases rc with
    | logup t g =>
      simp only [entryNodesM, entryNodesC, logupNodes, logupNodesWith, List.mem_append,
        Option.mem_toList, Option.toList_none, List.not_mem_nil, false_or] at h ⊢
      rcases h with (((h | h) | h) | h) | h
      · exact .inr ⟨_, h⟩
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
    | macH p =>
      simp only [entryNodesM, entryNodesC, macHNodes, macHNodesWith] at h ⊢
      split at h
      · simp only [List.mem_append, Option.mem_toList, Option.toList_none, List.nil_append]
          at h ⊢
        rcases h with h | h
        · exact .inr ⟨_, h⟩
        · exact .inl h
      · simp at h
    | _ => simp [entryNodesM] at h
  | _ => exact .inl (by simpa [entryNodesM, entryNodesC] using h)

theorem mem_circValues_of_C {c v : ℕ} (h : v ∈ ir.circValuesC c) : v ∈ ir.circValues c := by
  obtain ⟨e, he, hv⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨e, he, ir.mem_entryNodesM_of_C hv⟩

theorem mem_circValues_cases {c v : ℕ} (h : v ∈ ir.circValues c) :
    v ∈ ir.circValuesC c ∨ ∃ j, ir.chalNode j = some v := by
  obtain ⟨e, he, hv⟩ := List.mem_flatMap.1 h
  rcases ir.mem_entryNodesC_or_chal hv with h1 | h1
  · exact .inl (List.mem_flatMap.2 ⟨e, he, h1⟩)
  · exact .inr h1

/-- **What a circuit reads of the committed assignment is what `circReadsC` lists.** -/
theorem mem_circReadsT_iff {c v : ℕ} : v ∈ ir.circReadsT c ↔ v ∈ ir.circReadsC c := by
  simp only [circReadsT, circReadsC, List.mem_flatMap]
  constructor
  · rintro ⟨u, hu, hv⟩
    rcases ir.mem_circValues_cases hu with hu | ⟨j, hj⟩
    · exact ⟨u, hu, hv⟩
    · rw [ir.asgReadsT_getD_of_challenge (ir.chalNode_spec hj).2] at hv
      cases hv
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, ir.mem_circValues_of_C hu, hv⟩

/-- **`blockOkB` is `blockOkT`** in a well-formed program (`pubB_fuel_eq_pubT`). -/
theorem blockOkB_eq (hwf : ir.WellFormed) (c : ℕ) : ir.blockOkB d c = ir.blockOkT d c := by
  funext b
  cases b <;> simp only [blockOkB, blockOkT, pubB_fuel_eq_pubT hwf]

theorem inputsTB_iff (hwf : ir.WellFormed) (c : ℕ) : ir.inputsTB d c = true ↔ ir.InputsT d c := by
  rw [inputsT_iff]
  simp only [inputsTB, ir.blockOkB_eq d hwf c, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', circuitSets]
  have hv : (∀ v ∈ ir.circValuesC c, v < ir.values.length) ↔
      ∀ v ∈ ir.circValues c, v < ir.values.length :=
    ⟨fun h v hv => (ir.mem_circValues_cases hv).elim (h v) fun ⟨_, hj⟩ =>
      (ir.chalNode_spec hj).1, fun h v hv => h v (ir.mem_circValues_of_C hv)⟩
  have hw : ∀ b ∈ (ir.circuit c).inputs, ir.viewWordsSetB (circuitSets (ir.circuit c)) b =
      ir.viewWordsCommittedB c b := by
    intro b _
    cases b with
    | view u a n =>
      simp only [viewWordsSetB, viewWordsCommittedB]
      split
      · rename_i w sel _
        exact Bool.eq_iff_iff.2 (any_isCommittedOf_iff _ w).symm
      · rfl
    | _ => rfl
  have hc : ∀ v, ((ir.isCellValue d v = false ∨
        natMem (natSet ((ir.circuit c).inputs.filterMap InputBlock.committedOf?)) v = true) ∧
      (ir.isLateOf d v = false ∨
        natMem (natSet ((ir.circuit c).inputs.filterMap InputBlock.padOf?)) v = true)) ↔
      ((ir.isCellValue d v = true → (ir.circuit c).inputs.any (·.isCommittedOf v) = true) ∧
        (ir.isLateOf d v = true → (ir.circuit c).inputs.any (·.isPadOf v) = true)) := by
    intro v
    rw [any_isCommittedOf_iff, any_isPadOf_iff]
    cases ir.isCellValue d v <;> cases ir.isLateOf d v <;> simp
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    refine ⟨h1, h2, h3, h4, h5, hv.1 h6, fun v hv' => ((hc v).1 (h7 v (mem_circReadsT_iff ir |>.1
      hv'))).1, fun v hv' => ((hc v).1 (h7 v (mem_circReadsT_iff ir |>.1 hv'))).2,
      fun b hb => (hw b hb) ▸ h8 b hb⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hv.2 h6⟩, fun v hv' => (hc v).2
      ⟨h7 v ((mem_circReadsT_iff ir).2 hv'), h8 v ((mem_circReadsT_iff ir).2 hv')⟩⟩,
      fun b hb => (hw b hb).symm ▸ h9 b hb⟩

/-- **Value `w` has the blocks circuit `c` needs to decode it**: a committed block when it is a
committed value of `d`, a pad block when it is a late value of `d`. -/
def CoveredT (c w : ℕ) : Prop :=
  (ir.isCellValue d w = true → (ir.circuit c).inputs.any (·.isCommittedOf w) = true) ∧
    (ir.isLateOf d w = true → (ir.circuit c).inputs.any (·.isPadOf w) = true)

/-- **The sweep is the lookup**: value `w` is viewed iff its node is the child of the edge
`nodeIdx` names, that node has a view child, and its type is named after that edge's child. -/
theorem viewableB_iff {es : List PackingEdge} {w : ℕ} :
    ir.viewableB es w = true ↔ ∃ nr a, (ir.value w).node = some nr ∧ nodeIdx es nr.name = some a ∧
      (viewChild es a).isSome ∧ (ir.value w).type.nodeName.getD "" = (es.getD a noEdge).child := by
  -- the parent edge of an edge whose parent is `s` is the edge `nodeIdx` names for `s`
  have hpar : ∀ {b : ℕ} {s : String} (hb : b < es.length), es[b].parent = s →
      parentIdx es b = nodeIdx es s := by
    intro b s hb hs
    simp only [parentIdx, nodeIdx, List.getD_eq_getElem _ _ hb, hs]
  unfold viewableB
  constructor
  · intro h
    rcases hnr : (ir.value w).node with _ | nr
    · simp only [hnr] at h
      cases h
    · simp only [hnr, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
      obtain ⟨⟨htype, x, hx, hxc⟩, e, he, hbit, hpe⟩ := h
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem he
      have hpb := hpar hb hpe
      obtain ⟨a, ha⟩ : ∃ a, nodeIdx es nr.name = some a := by
        refine Option.isSome_iff_exists.1 ?_
        rw [nodeIdx, List.findIdx?_isSome, List.any_eq_true]
        exact ⟨x, hx, beq_iff_eq.2 hxc⟩
      obtain ⟨ha', hac⟩ := nodeIdx_spec ha
      refine ⟨nr, a, rfl, ha, ?_, ?_⟩
      · rw [viewChild, List.find?_isSome]
        refine ⟨b, List.mem_range.2 hb, ?_⟩
        simp only [hpb, ha, beq_self_eq_true, Bool.true_and, isView,
          List.getD_eq_getElem _ _ hb, Option.isSome_some, Bool.and_true]
        simpa [isBitEdge] using hbit
      · rw [htype, List.getD_eq_getElem _ _ ha', hac]
  · rintro ⟨nr, a, hnr, ha, hv, htype⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hv
    obtain ⟨hbl, hpb, hview⟩ := viewChild_spec hb
    obtain ⟨ha', hac⟩ := nodeIdx_spec ha
    rw [hnr]
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
    refine ⟨⟨by rw [htype, List.getD_eq_getElem _ _ ha', hac], es[a], List.getElem_mem ha',
      by simp [hac]⟩, es[b], List.getElem_mem hbl, ?_⟩
    simp only [isView, List.getD_eq_getElem _ _ hbl, Bool.and_eq_true] at hview
    -- the parent edge of `b` is `a`, so `b`'s parent is `a`'s child
    have hp : es[a].child = es[b].parent := by
      unfold parentIdx at hpb
      obtain ⟨_, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hpb
      simpa [List.getElem?_eq_getElem hbl] using hp
    simp [isBitEdge, hview.1.1.1, hview.1.1.2, hview.1.2, ← hp, hac]

/-- **Every bit view of domain `d` reads viewed words** (see the module docstring). -/
def ViewsOk (es : List PackingEdge) : Prop :=
  ∀ u w sel, (ir.value u).kind = .bits w sel → (ir.value u).domain = d → ir.viewableB es w = true

/-- **The viewed words as a test.** -/
def viewsOkB (es : List PackingEdge) : Bool :=
  (List.range ir.values.length).all fun u =>
    match (ir.value u).kind with
    | .bits w _ => (ir.value u).domain != d || ir.viewableB es w
    | _ => true

theorem ViewsOk.of_viewsOkB {es : List PackingEdge} (h : ir.viewsOkB d es = true) :
    ir.ViewsOk d es := by
  intro u w sel hk hd
  have hu := lt_of_kind_bits hk
  have := List.all_eq_true.1 h u (List.mem_range.2 hu)
  simp only [hk, hd, bne_self_eq_false, Bool.false_or] at this
  exact this

/-! ## The input forms -/

variable {d}

/-- **The coordinate of a cell key**: its cell's coordinate (`place`), none off the cells. -/
def keyCoord (k : CellKey) : Option (ir.TLog d rs Pads) :=
  if h : k ∈ ir.cellKeys d then some (ir.place d rs Pads ⟨k, h⟩) else none

/-- **The coordinate of coordinate `i` of a bit view** `u` of words `sel` of `w`: bit `i mod 16`
of word `sel[i / 16]` (`viewPlace`), none off the cells. -/
def viewCoord (u i : ℕ) : Option (ir.TLog d rs Pads) :=
  match (ir.value u).kind with
  | .bits w sel =>
    if h : CellKey.val w (sel.entry (i / 16)) ∈ ir.cellKeys d then
      some (ir.viewPlace d rs Pads ⟨_, h⟩ (bitPos i))
    else none
  | _ => none

/-- **The coordinate of private input `q`** held by block `b` of circuit `c` (the outer option: the
block holds `q`): a committed or pad coordinate's cell, a bit view's word bit, a filler cell. -/
def blockCoord (c q : ℕ) : InputBlock → Option (Option (ir.TLog d rs Pads))
  | .committed u a n => if a ≤ q ∧ q < a + n then some (ir.keyCoord rs Pads (.val u (q - a))) else none
  | .pad u a n => if a ≤ q ∧ q < a + n then some (ir.keyCoord rs Pads (.pad u (q - a))) else none
  | .view u a n => if a ≤ q ∧ q < a + n then some (ir.viewCoord rs Pads u (q - a)) else none
  | .filler a n => if a ≤ q ∧ q < a + n then some (ir.keyCoord rs Pads (.filler c q)) else none
  | _ => none

/-- **The coordinate of private input `q`** of circuit `c`: its block's (`blockCoord`). -/
def inputCoord (c q : ℕ) : Option (ir.TLog d rs Pads) :=
  ((ir.circuit c).inputs.findSome? (ir.blockCoord rs Pads c q)).bind id

theorem holds_of_blockCoord {c q : ℕ} {b : InputBlock} (h : ir.blockCoord rs Pads c q b ≠ none) :
    b.Holds q := by
  cases b <;> simp only [blockCoord, ne_eq, not_true_eq_false] at h <;>
    split_ifs at h with h' <;> simp_all [InputBlock.Holds, InputBlock.first, InputBlock.len]

/-- **The coordinate of a private input is its block's**, in a contiguous layout. -/
theorem inputCoord_eq {c : ℕ} (hc : ir.InputsT d c) {q : ℕ} {b : InputBlock}
    (hb : b ∈ (ir.circuit c).inputs) (hq : b.Holds q) :
    ir.inputCoord rs Pads c q = (ir.blockCoord rs Pads c q b).bind id := by
  unfold inputCoord
  rw [InputBlock.findSome?_eq_of_holds hc.layout hb hq fun b' => ir.holds_of_blockCoord rs Pads]

/-- **The value of an optional coordinate**, `0` at none. -/
def optVal {α K : Type} [Zero K] (z : α → K) : Option α → K
  | some c => z c
  | none => 0

/-- **The input forms of circuit `c` on domain `d`'s tree's coordinates** (see the module
docstring). -/
def treeInputForms (c dd : ℕ) :
    GKR.SourceInput.InputForms (I (ir.domainField d)).K (ir.TLog d rs Pads) (ir.DomainPub I) dd where
  form p x :=
    if (x : ℕ) < (ir.circuit c).publicInputs then
      .ofConst (castElt (ir.publicInput I c p.stmt p.run x))
    else if (x : ℕ) < ir.privEnd c then
      match ir.inputCoord rs Pads c x with
      | some z => .var z
      | none => 0
    else 0

theorem treeInputForms_input {c dd : ℕ} (p : ir.DomainPub I)
    (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) (x : Fin (2 ^ dd)) :
    (ir.treeInputForms rs Pads c dd).input p z x =
      if (x : ℕ) < (ir.circuit c).publicInputs then castElt (ir.publicInput I c p.stmt p.run x)
      else if (x : ℕ) < ir.privEnd c then optVal z (ir.inputCoord rs Pads c x)
      else 0 := by
  simp only [GKR.SourceInput.InputForms.input, treeInputForms]
  split_ifs
  · exact AffineForm.eval_ofConst _ _
  · cases ir.inputCoord rs Pads c x <;> simp [optVal]
  · exact AffineForm.eval_zero _

/-! ## Soundness -/

variable {ir rs Pads}

theorem blockOkT_committed {c u a n : ℕ} (h : ir.blockOkT d c (.committed u a n) = true) :
    u < ir.values.length ∧ ir.isCellValue d u = true ∧ n = (ir.value u).size ∧
      (ir.circuit c).publicInputs ≤ a ∧ a + n ≤ ir.privEnd c := by
  simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem blockOkT_pad {c u a n : ℕ} (h : ir.blockOkT d c (.pad u a n) = true) :
    u < ir.values.length ∧ ir.isCellValue d u = false ∧ ir.isLateOf d u = true ∧
      n = (ir.value u).size ∧ (ir.circuit c).publicInputs ≤ a ∧ a + n ≤ ir.privEnd c := by
  simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem blockOkT_view {c u a n : ℕ} (h : ir.blockOkT d c (.view u a n) = true) :
    ir.bitViewOk d u = true ∧ n ≤ (ir.value u).size ∧ (ir.circuit c).publicInputs ≤ a ∧
      a + n ≤ ir.privEnd c := by
  simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The public and pad blocks of a plain layout are placed as the plan places them.** -/
theorem InputsT.inputLayoutOk {c : ℕ} (hc : ir.InputsT d c) : ir.InputLayoutOk c where
  layout := hc.layout
  pubLe := hc.pubEnd.trans (Nat.sub_le _ _)
  pub u a n hb := by
    have h := hc.blocks _ hb
    simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  pad u a n hb := by
    obtain ⟨h1, -, h3, h4, -, -⟩ := blockOkT_pad (hc.blocks _ hb)
    exact ⟨h1, ir.isLateOf_isLate h3, h4.le⟩

/-- **A value the circuit reads has the blocks to decode it** (`InputsT.coverVal`,
`InputsT.coverPad`). -/
theorem InputsT.coveredT {c : ℕ} (hc : ir.InputsT d c) {w : ℕ} (hw : w ∈ ir.circReadsT c) :
    ir.CoveredT d c w :=
  ⟨hc.coverVal w hw, hc.coverPad w hw⟩

/-- **A committed cell has a committed input**: its value's committed block holds it. -/
theorem committedPos_ne_none_T {c : ℕ} (hc : ir.InputsT d c) {u i : ℕ}
    (hr : ir.isCellValue d u = true → (ir.circuit c).inputs.any (·.isCommittedOf u) = true)
    (hk : CellKey.val u i ∈ ir.cellKeys d) : (ir.circuit c).committedPos u i ≠ none := by
  obtain ⟨-, hcv, hi⟩ := (ir.mem_cellKeys_val).1 hk
  obtain ⟨b, hb, hbP⟩ := List.any_eq_true.1 (hr hcv)
  cases b <;> simp only [InputBlock.isCommittedOf, beq_iff_eq, Bool.false_eq_true] at hbP
  rename_i u' a n
  subst hbP
  have hp := blockOkT_committed (hc.blocks _ hb)
  intro hnone
  have := List.findSome?_eq_none_iff.1 hnone _ hb
  simp only [InputBlock.committedPos, true_and] at this
  rw [if_pos (by omega)] at this
  cases this

/-- **A pad cell has a pad input**: its late value's pad block holds it. -/
theorem padPos_ne_none_T {c : ℕ} (hc : ir.InputsT d c) {u i : ℕ}
    (hr : ir.isLateOf d u = true → (ir.circuit c).inputs.any (·.isPadOf u) = true)
    (hk : CellKey.pad u i ∈ ir.cellKeys d) : (ir.circuit c).padPos u i ≠ none := by
  obtain ⟨-, -, hl, hi⟩ := (ir.mem_cellKeys_pad).1 hk
  obtain ⟨b, hb, hbP⟩ := List.any_eq_true.1 (hr hl)
  cases b <;> simp only [InputBlock.isPadOf, beq_iff_eq, Bool.false_eq_true] at hbP
  rename_i u' a n
  subst hbP
  have hp := blockOkT_pad (hc.blocks _ hb)
  intro hnone
  have := List.findSome?_eq_none_iff.1 hnone _ hb
  simp only [InputBlock.padPos, true_and] at this
  rw [if_pos (by omega)] at this
  cases this

/-- **The coordinate of a cell key read from the logical assignment** is the decoded cell. -/
theorem optVal_keyCoord {x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K} {k : CellKey}
    (hk : k ∈ ir.cellKeys d) :
    optVal ((ir.treeLevel d rs Pads).view x) (ir.keyCoord rs Pads k) =
      ir.treeDecode d rs Pads x ⟨k, hk⟩ := by
  simp only [keyCoord, dif_pos hk, optVal, treeDecode]

/-- **The coordinate of a bit view's coordinate read from the logical assignment** is the word bit
of the decoded bits, the bit of `0` being `0`. -/
theorem optVal_viewCoord (hadd : (I (ir.domainField d)).BitsAdditive)
    {x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K} {u w : ℕ} {sel : IndexMap}
    (hk : (ir.value u).kind = .bits w sel) (i : ℕ) :
    optVal ((ir.treeLevel d rs Pads).view x) (ir.viewCoord rs Pads u i) =
      ir.wordBit I d (ir.treeBits d rs Pads x) w (sel.entry (i / 16)) (bitPos i) := by
  simp only [viewCoord, hk, wordBit]
  split_ifs with h
  · rfl
  · rw [hadd.ofBool_zero]
    rfl

variable [Fintype Pads]

/-- **The bits of viewed words read from the committed cells are the decoded cells' bits**
(`treeBits_eq`). -/
theorem wordBit_treeBits (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) {w : ℕ}
    (hw : ir.viewableB (rs.map REdge.plan) w = true) (k : ℕ) (j : Fin 16) :
    ir.wordBit I d (ir.treeBits d rs Pads x) w k j =
      ir.wordBit I d (ir.cellBits I d (ir.treeDecode d rs Pads x)) w k j := by
  unfold wordBit
  split_ifs with hmem
  · obtain ⟨nr, a, hnr, ha, hv, hkey⟩ := (ir.viewableB_iff).1 hw
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hv
    have hn : ir.cellNode (rs.map REdge.plan) (CellKey.val w k) = some a := by
      simp only [cellNode, cellName, hnr, Option.map_some, Option.bind_some, ha]
    rw [treeBits_eq ir ht hp hr x (k := ⟨_, hmem⟩) hn hb (by simp only [keyNode]; exact hkey) j]
    rfl
  · rfl

/-- **A private input of the forms** read as an input vector: its coordinate. -/
theorem vecRead_treeInput {c dd : ℕ} (hfit : (ir.circuit c).inputCount ≤ 2 ^ dd)
    (p : ir.DomainPub I) (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) {q : ℕ}
    (h1 : (ir.circuit c).publicInputs ≤ q) (h2 : q < ir.privEnd c) :
    vecRead ((ir.treeInputForms rs Pads c dd).input p z) q = optVal z (ir.inputCoord rs Pads c q) := by
  have hpe : ir.privEnd c ≤ (ir.circuit c).inputCount := Nat.sub_le _ _
  rw [vecRead, dif_pos (by omega), treeInputForms_input]
  simp only [if_neg (show ¬ q < (ir.circuit c).publicInputs by omega), if_pos h2]

end

section

variable {ir : RealizedProgram} {I : Interp} {c : ℕ}
  {Pk : (I (ir.circField c)).Packing} {rs : List (REdge (I (ir.circField c)) Pk)}
  {Pads : Type} [Fintype Pads]

/-- **An entry's truth depends only on the values it reads** (`entryNodesM`; `placedHolds_congr`,
`logupHoldsAt_congr`, `macHHolds_congr`), for a well-formed program. -/
theorem entryHolds_congr {ir : RealizedProgram} {I : Interp} (hwf : ir.WellFormed)
    {rd rd' : ir.Valuation I} {e : CircuitEntry} (he : ir.entryPredOkB e = true)
    (h : ∀ v ∈ ir.entryNodesM e, rd v = rd' v) : ir.EntryHolds rd e ↔ ir.EntryHolds rd' e := by
  have hpred : ∀ q, q < ir.predicates.length →
      (∀ v ∈ ir.predNodesM (ir.predicate q).body, rd v = rd' v) →
      (ir.PlacedHolds rd (ir.predicate q).body ↔ ir.PlacedHolds rd' (ir.predicate q).body) := by
    intro q hq hn
    have hmem : ir.predicate q ∈ ir.predicates := by
      rw [predicate_eq_getD, List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    exact placedHolds_congr fun v hv =>
      hn v ((mem_predNodesM hwf.refsOrdered (hwf.bodyRefsOk hmem) v).2 hv)
  cases e with
  | typeCheck q => exact hpred q (by simpa [entryPredOkB] using he) h
  | pred q => exact hpred q (by simpa [entryPredOkB] using he) h
  | alignment _ => exact Iff.rfl
  | realization rc =>
    cases rc with
    | logup t g => exact logupHoldsAt_congr h
    | macH q => exact macHHolds_congr h
    | named _ => exact Iff.rfl
    | unmodeled _ => exact Iff.rfl

/-- **The committed assignment the bundle decodes from the input of the logical assignment agrees
with the decoded cells' at every value with the blocks to decode it** (`CoveredT`; `inputCoord` at
every committed and pad input), and off the late values' pad coordinates. -/
theorem inputAssignment_treeInput (hc : ir.InputsT (ir.circuit c).domain c) {dd : ℕ}
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ dd) (p : ir.DomainPub I)
    (x : ir.TreeCell (ir.circuit c).domain Pk rs Pads → (I (ir.circField c)).K) :
    ir.AsgAgree I (ir.CoveredT (ir.circuit c).domain c) (ir.inputAssignment I c (vecRead
      ((ir.treeInputForms rs Pads c dd).input p ((ir.treeLevel (ir.circuit c).domain rs Pads).view x))))
      (ir.ofCells I (ir.circuit c).domain (ir.treeDecode (ir.circuit c).domain rs Pads x)) := by
  have hval : ∀ u i, (CellKey.val u i ∈ ir.cellKeys (ir.circuit c).domain →
      (ir.circuit c).committedPos u i ≠ none) →
      (ir.inputAssignment I c (vecRead ((ir.treeInputForms rs Pads c dd).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)))).val u i =
      (ir.ofCells I (ir.circuit c).domain (ir.treeDecode (ir.circuit c).domain rs Pads x)).val u i := by
    intro u i hcov
    simp only [inputAssignment, ofCells]
    cases hq : (ir.circuit c).committedPos u i with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      rw [dif_neg fun hk => hcov hk hq]
    | some q =>
      obtain ⟨a, n, hb, hi, rfl⟩ := exists_committed_block hq
      have hp := blockOkT_committed (hc.blocks _ hb)
      have hk : CellKey.val u i ∈ ir.cellKeys (ir.circuit c).domain :=
        (ir.mem_cellKeys_val).2 ⟨hp.1, hp.2.1, by omega⟩
      simp only [Option.map_some, Option.getD_some, dif_pos hk]
      rw [vecRead_treeInput hfit p _ (by omega) (by omega),
        ir.inputCoord_eq rs Pads hc hb (by simp only [InputBlock.Holds, InputBlock.first, InputBlock.len]; omega)]
      simp only [blockCoord, if_pos (show a ≤ a + i ∧ a + i < a + n by omega), Option.bind_some,
        id_eq, Nat.add_sub_cancel_left]
      rw [optVal_keyCoord hk]
  have hpad : ∀ u i, (CellKey.pad u i ∈ ir.cellKeys (ir.circuit c).domain →
      (ir.circuit c).padPos u i ≠ none) →
      (ir.inputAssignment I c (vecRead ((ir.treeInputForms rs Pads c dd).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)))).pad u i =
      (ir.ofCells I (ir.circuit c).domain (ir.treeDecode (ir.circuit c).domain rs Pads x)).pad u i := by
    intro u i hcov
    simp only [inputAssignment, ofCells]
    cases hq : (ir.circuit c).padPos u i with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      rw [dif_neg fun hk => hcov hk hq]
    | some q =>
      obtain ⟨a, n, hb, hi, rfl⟩ := exists_pad_block hq
      have hp := blockOkT_pad (hc.blocks _ hb)
      have hk : CellKey.pad u i ∈ ir.cellKeys (ir.circuit c).domain :=
        (ir.mem_cellKeys_pad).2 ⟨hp.1, hp.2.1, hp.2.2.1, by omega⟩
      simp only [Option.map_some, Option.getD_some, dif_pos hk]
      rw [vecRead_treeInput hfit p _ (by omega) (by omega),
        ir.inputCoord_eq rs Pads hc hb (by simp only [InputBlock.Holds, InputBlock.first, InputBlock.len]; omega)]
      simp only [blockCoord, if_pos (show a ≤ a + i ∧ a + i < a + n by omega), Option.bind_some,
        id_eq, Nat.add_sub_cancel_left]
      rw [optVal_keyCoord hk]
  refine ⟨fun u hu => funext fun i => hval u i (committedPos_ne_none_T hc hu.1),
    fun u hu => funext fun i => hpad u i (padPos_ne_none_T hc hu.2), fun u i hoff => hpad u i ?_⟩
  intro hk
  obtain ⟨h1, -, h3, h4⟩ := (ir.mem_cellKeys_pad).1 hk
  exact absurd ⟨h1, ir.isLateOf_isLate h3, h4⟩ hoff

/-- **The valuation the bundle decodes from the input of the logical assignment is the decoded
cells' valuation at every value reading only values with the blocks to decode them** (`CoveredT`;
every value the circuit reads has them, `InputsT.coveredT`): a committed value from its
block, a bit view from its view block (the decoded word's bit, `wordBit_treeBits`), a public value
from its public block (reading nothing of the committed assignment, `reader_eq_of_pubB`), every
other value read alike (`inputAssignment_treeInput`, `reader_bindAsg_congr`). -/
theorem inputValuation_treeInput (hc : ir.InputsT (ir.circuit c).domain c)
    (hv : ir.ViewsOk (ir.circuit c).domain (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk (ir.circuit c).domain Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk (ir.circuit c).domain rs) {dd : ℕ}
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ dd) (p : ir.DomainPub I)
    (x : ir.TreeCell (ir.circuit c).domain Pk rs Pads → (I (ir.circField c)).K) {u : ℕ}
    (hu : ∀ w ∈ ir.asgReads ir.fuel u, ir.CoveredT (ir.circuit c).domain c w) :
    ir.inputValuation I c p.stmt p.run ((ir.treeInputForms rs Pads c dd).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)) u =
      ir.cellValuation I (ir.circuit c).domain p.stmt p.run
        (ir.treeDecode (ir.circuit c).domain rs Pads x) u := by
  have hA := inputAssignment_treeInput hc hfit p x
  have hbase := reader_bindAsg_congr (x := p.stmt) (r := p.run) hA hu
  have hagree : ir.PadsAgreeOff I (ir.inputAssignment I c (vecRead ((ir.treeInputForms rs Pads c dd).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)))) ⟨0, 0⟩ := fun u i h =>
    (hA.off u i h).trans (padsAgreeOff_ofCells _ _ u i h)
  have hpub : ∀ j, j < (ir.circuit c).publicInputs →
      vecRead ((ir.treeInputForms rs Pads c dd).input p
        ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)) j =
        ir.publicInput I c p.stmt p.run j := fun j hj => by
    have := (hc.pubEnd.trans (Nat.sub_le _ _)).trans hfit
    rw [vecRead, dif_pos (by omega), treeInputForms_input, if_pos hj, castElt_self]
  funext i
  change _ = ir.reader (ir.layoutEnv I p.stmt (ir.bindAsg (ir.ofCells I (ir.circuit c).domain
    (ir.treeDecode (ir.circuit c).domain rs Pads x))) p.run) u i
  rw [← congrFun hbase i]
  unfold inputValuation
  rcases hk : (ir.value u).kind with _ | ⟨_ | ⟨name, args⟩ | e⟩ | es | ch | _ | ⟨w, sel⟩ | ⟨u', m⟩ | u'
  case priv =>
    simp only
    cases hq : (ir.circuit c).committedPos u i with
    | none => rfl
    | some q =>
      simp [reader_of_priv _ hk, layoutEnv, ir.bindAsg_val_of_isBound (v := u) _ (by rw [hk]; rfl),
        inputAssignment, hq]
  case padCopy =>
    simp only
    cases hq : (ir.circuit c).committedPos u i with
    | none => rfl
    | some q =>
      simp [reader_of_padCopy _ hk, layoutEnv,
        ir.bindAsg_val_of_isBound (v := u) _ (by rw [hk]; rfl), inputAssignment, hq]
  case late => rfl
  case bits =>
    simp only
    cases hq : (ir.circuit c).viewPos u i with
    | none => rfl
    | some q =>
      obtain ⟨a, n, hb, hi, rfl⟩ := exists_view_block hq
      have hpb := blockOkT_view (hc.blocks _ hb)
      obtain ⟨-, -, -, hud, -⟩ := bitViewOk_spec hpb.1
      have hw := hv u w sel hk hud
      simp only [Option.map_some, Option.getD_some]
      rw [vecRead_treeInput hfit p _ (by omega) (by omega),
        ir.inputCoord_eq rs Pads hc hb (by simp only [InputBlock.Holds, InputBlock.first, InputBlock.len]; omega)]
      simp only [blockCoord, if_pos (show a ≤ a + i ∧ a + i < a + n by omega), Option.bind_some,
        id_eq, Nat.add_sub_cancel_left]
      rw [optVal_viewCoord Pk.bitsAdditive hk, congrFun hbase i]
      change _ = ir.cellValuation I (ir.circuit c).domain p.stmt p.run
        (ir.treeDecode (ir.circuit c).domain rs Pads x) u i
      rw [← bitValuation_cellBits (show ir.bitViewOk (ir.circuit c).domain u = true from hpb.1)
        (ir.cellValuation I (ir.circuit c).domain p.stmt p.run
          (ir.treeDecode (ir.circuit c).domain rs Pads x)) p.stmt p.run]
      simp only [bitValuation, hk]
      rw [wordBit_treeBits ht hp hr x hw]
  all_goals
    simp only
    cases hq : (ir.circuit c).pubPos u i with
    | none => rfl
    | some q =>
      obtain ⟨b, hb, hbq⟩ := List.exists_of_findSome?_eq_some hq
      have hp := hc.blocks b hb
      cases b <;> simp only [InputBlock.pubPos, reduceCtorEq] at hbq
      rename_i u'' a n
      split_ifs at hbq with h'
      cases hbq
      obtain ⟨hu, hi⟩ := h'
      subst u''
      simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hp
      have hnl : ¬ ir.IsLate u := fun hl => by simp [IsLate, hk, Kind.isLate] at hl
      have hpb : ir.pubB ir.fuel u = true := hp.1.1.2.resolve_left hnl
      have hval : ((InputBlock.pub u a n).pubValue?
          (fun u i => (castElt (ir.reader (ir.layoutEnv I p.stmt ⟨0, 0⟩ p.run) u i) :
            (I (ir.circField c)).K))
          (ir.realPubValue I c p.run) (a + i)) =
            some (castElt (ir.reader (ir.layoutEnv I p.stmt ⟨0, 0⟩ p.run) u i)) := by
        simp only [InputBlock.pubValue?]
        rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      have hfind := InputBlock.findSome_pubValue? hc.layout _ hb hval
      have hne : a + i ≠ 0 := by omega
      simp only [Option.map_some, Option.getD_some]
      rw [hpub (a + i) (by omega), publicInput, if_neg hne, hfind, Option.getD_some,
        castElt_castElt_of_eq hp.1.1.1,
        reader_eq_of_pubB (a' := ir.bindAsg (ir.inputAssignment I c
          (vecRead ((ir.treeInputForms rs Pads c dd).input p
            ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)))))
          (fun u i hu => (hagree u i hu).symm) hpb]

/-- **The proof system's premises hold on the input of the logical assignment** (`InputPremises`):
a bit view's input is the bit of the committed word it reads (`viewCoord`, `wordBit_treeBits`), and
the word has a committed block (`InputsT.coverView`), so the decoded valuation and the semantics'
reading both read the decoded cells' bit there (`inputValuation_treeInput`,
`reader_bindAsg_congr`); a coordinate no view block holds is the semantics' reading by
definition. -/
theorem inputPremises_treeInput (hc : ir.InputsT (ir.circuit c).domain c)
    (hv : ir.ViewsOk (ir.circuit c).domain (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk (ir.circuit c).domain Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk (ir.circuit c).domain rs) {dd : ℕ}
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ dd) (p : ir.DomainPub I)
    (x : ir.TreeCell (ir.circuit c).domain Pk rs Pads → (I (ir.circField c)).K) :
    ir.InputPremises I c p.stmt p.run ((ir.treeInputForms rs Pads c dd).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x)) := by
  refine ⟨fun u w sel hk i => ?_⟩
  cases hq : (ir.circuit c).viewPos u i with
  | none =>
    unfold inputValuation inputBase
    simp only [hk, hq, Option.map_none, Option.getD_none]
  | some q =>
    obtain ⟨a, n, hb, -, -⟩ := exists_view_block hq
    obtain ⟨w', sel', hk', -, -, hwk, -, -⟩ := bitViewOk_spec (blockOkT_view (hc.blocks _ hb)).1
    rw [hk] at hk'
    injection hk' with hw hs
    subst hw hs
    have hcov : ir.CoveredT (ir.circuit c).domain c w := by
      refine ⟨fun _ => ?_, fun hl => ?_⟩
      · have := hc.coverView _ hb
        simpa only [viewWordsCommittedB, hk] using this
      · exfalso
        have := ir.isLateOf_isLate hl
        simp [IsLate, hwk, Kind.isLate] at this
    have hu : ∀ w' ∈ ir.asgReads ir.fuel u, ir.CoveredT (ir.circuit c).domain c w' := by
      intro w' hw'
      obtain ⟨m, hm⟩ : ∃ m, ir.fuel = m + 1 + 1 := ⟨ir.values.length - 1, by
        have := lt_of_kind_bits hk
        simp only [fuel]
        omega⟩
      rw [hm] at hw'
      simp only [asgReads, hk, hwk, List.mem_singleton] at hw'
      subst hw'
      exact hcov
    have h1 := congrFun (inputValuation_treeInput hc hv ht hp hr hfit p x hu) i
    have h2 := congrFun (reader_bindAsg_congr (x := p.stmt) (r := p.run)
      (inputAssignment_treeInput hc hfit p x) hu) i
    rw [h1]
    exact h2.symm

/-- **Soundness of the compiler correspondence on the tree's coordinates**: the trust bundle turns
the source's satisfaction on the input of the logical assignment of any committed cells into the
circuit's meaning at the decoded cells' valuation (`inputValuation_treeInput`), the proof system's
premises holding there (`inputPremises_treeInput`). -/
theorem circuitHolds_of_treeInput {src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c}
    (T : ir.CircuitsEnforce I src) {c : Fin ir.circuits.length}
    {Pk : (I (ir.circField c)).Packing} {rs : List (REdge (I (ir.circField c)) Pk)}
    (hc : ir.InputsT (ir.circuit c).domain c)
    (hv : ir.ViewsOk (ir.circuit c).domain (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk (ir.circuit c).domain Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk (ir.circuit c).domain rs) (hwf : ir.WellFormed) (p : ir.DomainPub I)
    (x : ir.TreeCell (ir.circuit c).domain Pk rs Pads → (I (ir.circField c)).K)
    (hsat : (src c).S.Satisfied ((ir.treeInputForms rs Pads c (src c).d).input p
      ((ir.treeLevel (ir.circuit c).domain rs Pads).view x))) :
    ir.CircuitHolds I c (ir.cellValuation I (ir.circuit c).domain p.stmt p.run
      (ir.treeDecode (ir.circuit c).domain rs Pads x)) := by
  have hv' := T.enforce c p.stmt p.run _ (fun j hj => by
    rw [treeInputForms_input, if_pos (show (j : ℕ) < (ir.circuit c).publicInputs from hj),
      castElt_self]) (inputPremises_treeInput hc hv ht hp hr (src c).hfit p x) hsat
  intro e he
  refine (entryHolds_congr hwf (hc.entries e he) fun v hve => ?_).1 (hv' e he)
  have hvc : v ∈ ir.circValues c := List.mem_flatMap.2 ⟨e, he, hve⟩
  exact inputValuation_treeInput hc hv ht hp hr (src c).hfit p x fun w hw =>
    hc.coveredT (List.mem_flatMap.2 ⟨v, hvc, (mem_asgReadsT hwf (hc.valuesLt v hvc) w).1 hw⟩)

end


end GordieHowe.RealizedProgram
