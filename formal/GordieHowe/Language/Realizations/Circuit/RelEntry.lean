-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelFamily
public import GordieHowe.Language.Realizations.ProductEquation
public import GordieHowe.Language.Realizations.SharedNorm
public import GordieHowe.Language.Realizations.Circuit.Load
public import GordieHowe.Language.Realizations.Circuit.LoadNative
public import GordieHoweNative.Language.Realizations.Circuit.RelEntry

@[expose] public section

/-!
# GordieHowe: the per-entry and per-circuit checks of a GKR circuit's certificate

* **An entry's meaning** (`GordieHowe.RealizedProgram.entryMeaningB`): the print `X` of the
  entry's asserted root is the printed predicate's `l − r` (or its negation) as normal forms
  (`nfUnitEqB`, coordinate by coordinate, over shared-expression atoms: `SharedNorm.lean`), a
  product form's asserted equation (`productEquationB`). An alignment or realization entry has no
  root; its family record (`RelFamily.lean`) states its meaning.
* **An entry** (`GordieHowe.RealizedProgram.entryCertB`): its block continues the previous one,
  its root's coordinates are asserted by its assertion pairs (`GKR.Rel.zeroOk`), its meaning holds,
  and every node of its block gives its cuts (`nodeCutsE`), which the relational check accepts; an
  alignment or realization entry instead meets its family record (`famHeadE`, `famSliceE`).
  The nodes check in parts (`entryNodesE`, `entryNodesB_append`), so one kernel check stays
  bounded.
* **The header** (`GordieHowe.RealizedProgram.headerB`): the scheduling certificate, the bridge's
  checks, the node table's check against the printed program, the codes, the partition of the
  table into the entries' blocks, every asserted DAG node an entry's, and every challenge's value
  in the challenge's field (`chalFieldsB`).
* **The circuit** (`GordieHowe.RealizedProgram.circuitCertB`): the header and every entry.

Every checker is its failure-reporting twin's success (`Twin.okB`).

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/RelEntry.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin GordieHowe.GKR.CertificateBridge
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert relOkE)

/-! ## Entries -/

section Entries

variable (ir : RealizedProgram) (c : ℕ) (ar : CodeArith) (cd : CircuitData)

/-- **The head of an entry with no root** is its family record's. -/
theorem famHead_of_entryHeadE {k : ℕ} (h : okB (ir.entryHeadE c ar cd k) = true)
    (hr : (cd.entries.getD k default).root = none) :
    ∃ f, (cd.entries.getD k default).fam = some f ∧ okB (ir.famHeadE c ar cd k f) = true := by
  unfold entryHeadE at h
  simp only [okB_seqE, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  simp only [List.getD_eq_getElem?_getD] at h hr ⊢
  revert h hr
  generalize cd.entries[k]?.getD default = en
  intro h hr
  rw [hr] at h
  revert h
  cases en.fam with
  | none => exact fun h => absurd h (by simp [okB])
  | some f => exact fun h => ⟨f, rfl, h⟩

/-- **Entry `k` checks**, as its failure-reporting twin: its head, its block's nodes, and its family
cuts. -/
def entryCertE (k : ℕ) : Except CertFailure Unit :=
  let en := cd.entries.getD k default
  seqE (ir.entryHeadE c ar cd k)
    (seqE (ir.entryNodesE c ar cd k en.lo (en.hi - en.lo)) (ir.famSliceE c ar cd k 0 0))

/-- **Entry `k` checks.** -/
def entryCertB (k : ℕ) : Bool := okB (ir.entryCertE c ar cd k)

/-! ## The header -/

/-- **Every asserted DAG node is some entry's** (merge-join against the sorted nonzero `Z`s). -/
def assertsCoveredB : Bool :=
  subsetSorted cd.dag.asserts
    (sortNat ((cd.entries.flatMap fun en => en.asserts.map (·.Z)).filter fun z => !(z == 0)))

/-- **Every asserted DAG node is an assertion `0 · 1 · U`**: one term, constant `0`, first operand
the constant one (node `0`). -/
def assertTermsB : Bool :=
  cd.dag.asserts.all fun z =>
    match nodeTerms cd.w cd.dag z with
    | [t] => Nat.beq t.k 0 && Nat.beq t.a 0
    | _ => false

/-- **The header of circuit `c`'s certificate**, as its twin: the circuit's index; the constant of
index `1` is the code `1`; the constant one is a public input; the scheduling
certificate (`check`) at the DAG's width; one assertion per gate and the shape at the circuit's
width and layers (the bridge); the layered circuit's inputs the circuit's input count; the node
table's check against the printed program; the environment's codes; one block per entry of the
circuit, the last ending at the table's size; every asserted DAG node an entry's; every challenge's
value in the challenge's field; no DAG output node; every asserted node an assertion `0 · 1 · U`. -/
def headerE : Except CertFailure Unit :=
  let env := cd.env ar
  let n := cd.entries.length
  seqE (guardE (Nat.beq cd.c c && Nat.beq cd.sched.width cd.w &&
      Nat.beq cd.layered.inputs (ir.circuit c).inputCount && Nat.beq (cd.consts.code 1) 1 &&
      Nat.blt 0 (ir.circuit c).publicInputs) ⟨0, 0, .header⟩)
    (seqE (guardE (check cd.dag cd.layered cd.sched) ⟨0, 1, .header⟩)
      (seqE (guardE (uniqueAssertsB cd.w cd.layered &&
          shapeB cd.layered (ir.circuitWidth c) (ir.circuit c).layers) ⟨0, 2, .header⟩)
        (seqE (guardE (ir.emitTableOkB env cd.table) ⟨0, 3, .header⟩)
          (seqE (guardE env.arithB ⟨0, 4, .header⟩)
            (seqE (guardE (Nat.beq n (ir.circuit c).entries.length &&
                Nat.beq (cond (Nat.beq n 0) 0 (cd.entries.getD (n - 1) default).hi) cd.table.size)
                ⟨0, 5, .partition⟩)
              (seqE (guardE (assertsCoveredB cd) ⟨0, 6, .header⟩)
                (seqE (guardE ir.chalFieldsB ⟨0, 7, .header⟩)
                  (seqE (guardE cd.dag.outputs.isEmpty ⟨0, 8, .header⟩)
                    (guardE (assertTermsB cd) ⟨0, 9, .header⟩)))))))))

/-- **The header checks.** -/
def headerB : Bool := okB (ir.headerE c ar cd)

/-- **Part `i` of the header** (`headerE`'s guards in order, `i < 10`): a large circuit's header is
checked part by part, the scheduling certificate (part `1`) layer by layer. -/
def headerPartB (i : ℕ) : Bool :=
  let env := cd.env ar
  let n := cd.entries.length
  match i with
  | 0 => Nat.beq cd.c c && Nat.beq cd.sched.width cd.w &&
      Nat.beq cd.layered.inputs (ir.circuit c).inputCount && Nat.beq (cd.consts.code 1) 1 &&
      Nat.blt 0 (ir.circuit c).publicInputs
  | 1 => check cd.dag cd.layered cd.sched
  | 2 => uniqueAssertsB cd.w cd.layered &&
      shapeB cd.layered (ir.circuitWidth c) (ir.circuit c).layers
  | 3 => ir.emitTableOkB env cd.table
  | 4 => env.arithB
  | 5 => Nat.beq n (ir.circuit c).entries.length &&
      Nat.beq (cond (Nat.beq n 0) 0 (cd.entries.getD (n - 1) default).hi) cd.table.size
  | 6 => assertsCoveredB cd
  | 7 => ir.chalFieldsB
  | 8 => cd.dag.outputs.isEmpty
  | 9 => assertTermsB cd
  | _ => true

/-- **The header from its parts**, one declaration each. -/
theorem headerB_of_parts (h0 : ir.headerPartB c ar cd 0 = true)
    (h1 : ir.headerPartB c ar cd 1 = true)
    (h2 : ir.headerPartB c ar cd 2 = true) (h3 : ir.headerPartB c ar cd 3 = true)
    (h4 : ir.headerPartB c ar cd 4 = true) (h5 : ir.headerPartB c ar cd 5 = true)
    (h6 : ir.headerPartB c ar cd 6 = true) (h7 : ir.headerPartB c ar cd 7 = true)
    (h8 : ir.headerPartB c ar cd 8 = true) (h9 : ir.headerPartB c ar cd 9 = true) :
    ir.headerB c ar cd = true := by
  simp only [headerPartB] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  simp only [headerB, headerE, okB_seqE, okB_guardE, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Bool.and_self]

/-- **The circuit's certificate checks**: its header and every entry. -/
def circuitCertB : Bool :=
  ir.headerB c ar cd && (List.range cd.entries.length).all (ir.entryCertB c ar cd)

/-- **The circuit check from its parts**, one declaration per entry. -/
theorem circuitCertB_of_entries (h0 : ir.headerB c ar cd = true)
    (he : ∀ k < cd.entries.length, ir.entryCertB c ar cd k = true) :
    ir.circuitCertB c ar cd = true := by
  simp only [circuitCertB, h0, Bool.true_and, List.all_eq_true, List.mem_range]
  exact he

/-! ## Entries in parts -/


theorem okB_entryNodesE (e lo n : ℕ) :
    okB (ir.entryNodesE c ar cd e lo n) = (List.range' lo n).all fun k => okB (ir.nodeOkE c ar cd e k) :=
  okB_allE (p := fun k => okB (ir.nodeOkE c ar cd e k)) (fun _ _ => rfl) 0 _

/-- **Two consecutive parts of an entry's nodes** check as one. -/
theorem entryNodesB_append {e a n m : ℕ} (h₁ : okB (ir.entryNodesE c ar cd e a n) = true)
    (h₂ : okB (ir.entryNodesE c ar cd e (a + n) m) = true) :
    okB (ir.entryNodesE c ar cd e a (n + m)) = true := by
  rw [okB_entryNodesE] at h₁ h₂ ⊢
  rw [← List.range'_append_1, List.all_append, h₁, h₂, Bool.true_and]

/-- **An entry from its head and its nodes' parts.** -/
theorem entryCertB_of_parts {k lo n : ℕ} (hlo : (cd.entries.getD k default).lo = lo)
    (hn : (cd.entries.getD k default).hi - (cd.entries.getD k default).lo = n)
    (h0 : okB (ir.entryHeadE c ar cd k) = true) (h1 : okB (ir.entryNodesE c ar cd k lo n) = true)
    (h2 : okB (ir.famSliceE c ar cd k 0 0) = true) :
    ir.entryCertB c ar cd k = true := by
  unfold entryCertB entryCertE
  simp only [okB_seqE, h0, h2, Bool.true_and, Bool.and_true]
  rw [hn, hlo]
  exact h1

/-- The relational check of cuts alone splits over a concatenation. -/
theorem relOk_nil_append {w : ℕ} {D : Dag} {Kc : Consts} {ar : CodeArith}
    (l₁ l₂ : List (Wire × TE)) :
    GKR.Rel.relOk w D Kc ar (l₁ ++ l₂) [] =
      (GKR.Rel.relOk w D Kc ar l₁ [] && GKR.Rel.relOk w D Kc ar l₂ []) := by
  simp [GKR.Rel.relOk, List.all_append, GKR.Rel.assertedNodes, subsetSorted]

/-- **A slice and the rest after it** check as the rest from the slice's start. -/
theorem nodeSliceB_cons {e k s n : ℕ} (hn : 0 < n) (h₁ : okB (ir.nodeSliceE c ar cd e k s n) = true)
    (h₂ : okB (ir.nodeSliceE c ar cd e k (s + n) 0) = true) :
    okB (ir.nodeSliceE c ar cd e k s 0) = true := by
  unfold nodeSliceE at h₁ h₂ ⊢
  generalize ir.nodeCutsE c (cd.env ar) cd.table k = rr at h₁ h₂ ⊢
  cases rr with
  | error r => cases h₁
  | ok cs =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hd : (cs.drop s).drop (m + 1) = cs.drop (s + (m + 1)) := by
      simp [List.drop_drop]
    simp only [okB_mapE, ← GKR.Rel.relOk_eq_okB] at h₁ h₂ ⊢
    change GKR.Rel.relOk _ _ _ _ ((cs.drop s).take (m + 1)) [] = true at h₁
    change GKR.Rel.relOk _ _ _ _ (cs.drop (s + (m + 1))) [] = true at h₂
    change GKR.Rel.relOk _ _ _ _ (cs.drop s) [] = true
    rw [← List.take_append_drop (m + 1) (cs.drop s), relOk_nil_append, h₁, hd, h₂]
    rfl

/-- **Two consecutive slices** check as one. -/
theorem nodeSliceB_append {e k s n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h₁ : okB (ir.nodeSliceE c ar cd e k s n) = true)
    (h₂ : okB (ir.nodeSliceE c ar cd e k (s + n) m) = true) :
    okB (ir.nodeSliceE c ar cd e k s (n + m)) = true := by
  unfold nodeSliceE at h₁ h₂ ⊢
  generalize ir.nodeCutsE c (cd.env ar) cd.table k = rr at h₁ h₂ ⊢
  cases rr with
  | error r => cases h₁
  | ok cs =>
    have hb : ∀ x, 0 < x → Nat.beq x 0 = false := fun x hx => by
      cases x with
      | zero => omega
      | succ => rfl
    have hd : (cs.drop s).drop n = cs.drop (s + n) := by simp [List.drop_drop]
    simp only [okB_mapE, ← GKR.Rel.relOk_eq_okB, hb n hn, hb m hm, hb (n + m) (by omega),
      Bool.cond_false] at h₁ h₂ ⊢
    rw [List.take_add, relOk_nil_append, h₁, hd, h₂]
    rfl

/-- **A family slice and the rest after it** check as the rest from the slice's start. -/
theorem famSliceB_cons {e s n : ℕ} (hn : 0 < n) (h₁ : okB (ir.famSliceE c ar cd e s n) = true)
    (h₂ : okB (ir.famSliceE c ar cd e (s + n) 0) = true) :
    okB (ir.famSliceE c ar cd e s 0) = true := by
  unfold famSliceE at h₁ h₂ ⊢
  generalize ir.famCuts c ar cd e = cs at h₁ h₂ ⊢
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : (cs.drop s).drop (m + 1) = cs.drop (s + (m + 1)) := by
    simp [List.drop_drop]
  simp only [okB_mapE, ← GKR.Rel.relOk_eq_okB] at h₁ h₂ ⊢
  change GKR.Rel.relOk _ _ _ _ ((cs.drop s).take (m + 1)) [] = true at h₁
  change GKR.Rel.relOk _ _ _ _ (cs.drop (s + (m + 1))) [] = true at h₂
  change GKR.Rel.relOk _ _ _ _ (cs.drop s) [] = true
  rw [← List.take_append_drop (m + 1) (cs.drop s), relOk_nil_append, h₁, hd, h₂]
  rfl

/-- **A node from its slices**: every cut from `0` on checks, so the node checks as one part. -/
theorem entryNodesB_of_slices {e k : ℕ} (h : okB (ir.nodeSliceE c ar cd e k 0 0) = true) :
    okB (ir.entryNodesE c ar cd e k 1) = true := by
  rw [okB_entryNodesE]
  simp only [List.range'_one, List.all_cons, List.all_nil, Bool.and_true]
  unfold nodeOkE
  unfold nodeSliceE at h
  generalize ir.nodeCutsE c (cd.env ar) cd.table k = rr at h ⊢
  cases rr with
  | error r => cases h
  | ok cs =>
    simp only [Nat.beq_refl, Bool.cond_true, List.drop_zero] at h
    exact h

end Entries

end GordieHowe.RealizedProgram
