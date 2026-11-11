-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelFamilySound
public import GordieHowe.Language.Realizations.Circuit.RelMeaning

@[expose] public section

/-!
# GordieHowe: a circuit's certificate enforces its entries

From an accepted certificate (`GordieHowe.RealizedProgram.circuitCertB`) and an input vector that
satisfies the source circuit, every entry of the circuit holds at the decoded valuation
(`GordieHowe.RealizedProgram.circuitHolds_of_circuitCertB`):

* **The header's facts** (`GordieHowe.RealizedProgram.HeaderFacts`): the scheduling certificate,
  the bridge's checks, the node table's check, the codes and the partition.
* **The DAG holds** at the inputs (`check_sound`, `toSource_satisfied`), so every accepted cut and
  assertion holds at the DAG's node values (`GKR.Rel.relOk_sound`).
* **Every node is in some entry's block** (`GordieHowe.RealizedProgram.exists_block`), so every
  node's cuts hold, and the node table is sound (`nodeTable_sound`).
* **Every entry's root is zero** by its assertions, so its meaning holds
  (`entryHolds_of_entryMeaningB`).
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.CertificateBridge
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert relOkE relOk relOk_eq_okB relOk_sound)

/-! ## The header -/

/-- **What an accepted header gives.** -/
structure HeaderFacts (ir : RealizedProgram) (c : ℕ) (ar : CodeArith) (cd : CircuitData) :
    Prop where
  /-- The schedule's width is the DAG's term width. -/
  width : cd.sched.width = cd.w
  /-- The layered circuit's inputs are the circuit's. -/
  inputs : cd.layered.inputs = (ir.circuit c).inputCount
  /-- The scheduling certificate checks. -/
  check : check cd.dag cd.layered cd.sched = true
  /-- One assertion per gate. -/
  unique : uniqueAssertsB cd.w cd.layered = true
  /-- The layered circuit's shape. -/
  shape : shapeB cd.layered (ir.circuitWidth c) (ir.circuit c).layers = true
  /-- The node table checks against the printed program. -/
  table : ir.EmitTableOk (cd.env ar) cd.table
  /-- The environment's codes. -/
  arith : (cd.env ar).arithB = true
  /-- One block per entry. -/
  count : cd.entries.length = (ir.circuit c).entries.length
  /-- The last block ends at the table's size. -/
  last : cond (Nat.beq cd.entries.length 0) 0 (cd.entries.getD (cd.entries.length - 1) default).hi =
    cd.table.size
  /-- The constant of index `1` is the code `1`. -/
  one : cd.consts.code 1 = 1
  /-- The constant one is a public input. -/
  pub : 0 < (ir.circuit c).publicInputs
  /-- Every challenge's value lies in the challenge's field. -/
  chal : ir.chalFieldsB = true
  /-- The DAG has no output node. -/
  noOutputs : cd.dag.outputs = []
  /-- Every asserted node is an assertion `0 · 1 · U`. -/
  assertTerms : assertTermsB cd = true

theorem headerFacts_of_headerB {ir : RealizedProgram} {c : ℕ} {ar : CodeArith} {cd : CircuitData}
    (h : ir.headerB c ar cd = true) : HeaderFacts ir c ar cd := by
  simp only [headerB, headerE, okB_seqE, okB_guardE, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h11⟩, h12⟩, h4, ⟨h5, h6⟩, h7, h8, ⟨h9, h10⟩, -, h13, h14, h15⟩ := h
  exact ⟨h2, h3, h4, h5, h6, emitTableOk_of_emitTableOkB h7, h8, h9, h10, h11, h12, h13,
    List.isEmpty_iff.1 h14, h15⟩

/-! ## Blocks -/

/-- **Consecutive blocks cover their union**: blocks starting at `0`, each starting where the
previous ends, cover every index below the end of block `j`. -/
theorem exists_block {n : ℕ} {lo hi : ℕ → ℕ} (h0 : 0 < n → lo 0 = 0)
    (hs : ∀ k, k + 1 < n → lo (k + 1) = hi k) :
    ∀ j < n, ∀ m < hi j, ∃ k ≤ j, lo k ≤ m ∧ m < hi k := by
  intro j
  induction j with
  | zero =>
    intro hj m hm
    exact ⟨0, le_rfl, by rw [h0 hj]; omega, hm⟩
  | succ j ih =>
    intro hj m hm
    by_cases hmj : m < hi j
    · obtain ⟨k, hk, hk'⟩ := ih (by omega) m hmj
      exact ⟨k, by omega, hk'⟩
    · exact ⟨j + 1, le_rfl, by rw [hs j hj]; omega, hm⟩

/-- **An accepted entry's head**: its block starts where the previous one ends and ends within the
table. -/
theorem entryHead_block {ir : RealizedProgram} {c : ℕ} {ar : CodeArith} {cd : CircuitData} {k : ℕ}
    (h : okB (ir.entryHeadE c ar cd k) = true) :
    (cd.entries.getD k default).lo =
        cond (Nat.beq k 0) 0 (cd.entries.getD (k - 1) default).hi ∧
      (cd.entries.getD k default).hi ≤ cd.table.size := by
  unfold entryHeadE at h
  simp only [okB_seqE, okB_guardE, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  exact ⟨h.1.1.1.2, h.1.2⟩

/-- **An accepted node's cuts** are the relational check's. -/
theorem nodeOkE_ok {ir : RealizedProgram} {c : ℕ} {ar : CodeArith} {cd : CircuitData} {e k : ℕ}
    (h : okB (ir.nodeOkE c ar cd e k) = true) :
    ∃ cs, ir.nodeCutsE c (cd.env ar) cd.table k = .ok cs ∧
      relOk cd.w cd.dag cd.consts ar cs [] = true := by
  unfold nodeOkE at h
  cases hn : ir.nodeCutsE c (cd.env ar) cd.table k with
  | error r =>
    rw [hn] at h
    cases h
  | ok cs =>
    rw [hn, okB_mapE] at h
    exact ⟨cs, rfl, by rw [relOk_eq_okB]; exact h⟩

/-- **The root's assertion item of coordinate `i`.** -/
theorem mem_rootItems {cd : CircuitData} {r i : ℕ} {as : List Assert} (hi : i < as.length)
    (hw : i < (cd.table.get r).wires.length) :
    (as.getD i default).item ((cd.table.get r).wires.getD i default) ∈ rootItems cd r as := by
  unfold rootItems
  have hl : i < (List.zipWith Assert.item as (cd.table.get r).wires).length := by
    simp [hi, hw]
  have hm := List.getElem_mem hl
  rw [List.getElem_zipWith] at hm
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hw]

/-! ## The circuit -/

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {c : ℕ}
  {ar : CodeArith} {cd : CircuitData}

/-- **A circuit's certificate enforces its entries** (the per-circuit core of
`circuitsEnforce_of_certs`): on an input vector whose public inputs are the verifier's, on which
the proof system's premises hold and which satisfies the source circuit of the certificate, every
entry of the circuit holds at the decoded valuation, where every bound value reads committed
values and constants (`hbd`). -/
theorem circuitHolds_of_circuitCertB (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w) (hL : ir.InputLayoutOk c)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (h : ir.circuitCertB c ar cd = true)
    {x : ir.Valuation I} {r : (ir.layout I).Run} {d : ℕ} {v : Fin (2 ^ d) → (I (ir.circField c)).K}
    (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hpub : ∀ j : Fin (2 ^ d), (ir.circuit c).IsPublicPos j → v j = ir.publicInput I c x r j)
    (hP : ir.InputPremises I c x r v)
    (hsat : (toSource cd.layered cd.w (cd.consts.decode (I (ir.circField c)).decode) d).Satisfied
      v) :
    ir.CircuitHolds I c (ir.inputValuation I c x r v) := by
  simp only [circuitCertB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hH, hE⟩ := h
  have hF := headerFacts_of_headerB hH
  have := hC.charP
  have hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode :=
    TEnv.arithOk_of_arithB hC.hom hF.arith
  -- the DAG holds at the inputs
  have hx : vecRead v 0 = 1 := by
    have h2 : 0 < 2 ^ d := Nat.two_pow_pos d
    simp only [vecRead, h2, ↓reduceDIte]
    rw [hpub ⟨0, h2⟩ hF.pub]
    simp [publicInput]
  have hκ1 : cd.consts.decode (I (ir.circField c)).decode 1 = 1 := by
    simp only [Consts.decode, hF.one, hC.hom.one]
  have hsatC := toSource_satisfied hF.unique (by rw [hF.inputs]; exact hfit)
    (by have := readsBelow_of_check hF.check; rwa [hF.width] at this) hsat
  have hD : cd.dag.Holds cd.w (cd.consts.decode (I (ir.circField c)).decode) (vecRead v) := by
    have := check_sound hF.check hκ1 hx (by rw [hF.width]; exact hsatC)
    rwa [hF.width] at this
  have hchk := hF.check
  simp only [GKR.Certificate.check, Bool.and_eq_true, Nat.beq_eq] at hchk
  obtain ⟨⟨⟨⟨honeOk, hin⟩, -⟩, -⟩, -⟩ := hchk
  have hone := val_zero (w := cd.w) (κ := cd.consts.decode (I (ir.circField c)).decode) honeOk hx
  -- every node's cuts hold
  have hcuts : ∀ m < cd.table.size, ∃ cs, ir.nodeCutsE c (cd.env ar) cd.table m = .ok cs ∧
      CutsHold (ir := ir) (c := c)
        (V := cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) (vecRead v)) cs := by
    intro m hm
    have hn0 : 0 < cd.entries.length := by
      rcases Nat.eq_zero_or_pos cd.entries.length with h0 | h0
      · have := hF.last
        simp [h0] at this
        omega
      · exact h0
    have hhead : ∀ k < cd.entries.length, okB (ir.entryHeadE c ar cd k) = true := fun k hk => by
      have := hE k hk
      simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at this
      exact this.1
    have hlast := hF.last
    rw [show Nat.beq cd.entries.length 0 = false from Bool.eq_false_iff.2 fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega, Bool.cond_false] at hlast
    obtain ⟨k, hk, hlo, hhi⟩ := exists_block (n := cd.entries.length)
      (lo := fun k => (cd.entries.getD k default).lo)
      (hi := fun k => (cd.entries.getD k default).hi)
      (fun h0 => by simpa using (entryHead_block (hhead 0 h0)).1)
      (fun k hk => by simpa using (entryHead_block (hhead (k + 1) hk)).1)
      (cd.entries.length - 1) (by omega) m (by rw [hlast]; exact hm)
    have hnodes := hE k (by omega)
    simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at hnodes
    rw [okB_entryNodesE, List.all_eq_true] at hnodes
    have hmr : m ∈ List.range' (cd.entries.getD k default).lo
        ((cd.entries.getD k default).hi - (cd.entries.getD k default).lo) := by
      rw [List.mem_range'_1]
      exact ⟨hlo, by omega⟩
    obtain ⟨cs, hcs, hrel⟩ := nodeOkE_ok (hnodes.2.1 m hmr)
    exact ⟨cs, hcs, (relOk_sound hC.hom hone hD hrel).1⟩
  -- the reader premises at the decoded valuation
  have hK : ∀ u es, (ir.value u).kind = .constant es → ∀ i,
      ir.inputValuation I c x r v u i = (I (ir.valueField u)).decode (es.getD i 0) := by
    intro u es hk i
    rw [inputValuation_eq_inputBase hL hfit hpub hP]
    exact reader_of_constant _ hk i
  have hR := defReads_inputValuation hM.wf hbd hL hfit hpub hP
  have hval : ∀ q < (ir.circuit c).inputCount,
      cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) (vecRead v) q =
        vecRead v q := by
    intro q hq
    rw [Dag.val_eq]
    have hb : Nat.blt q cd.dag.inputs = true := by
      rw [← hin, hF.inputs]
      simpa using hq
    rw [hb, Bool.cond_true]
  have hLeaf := leafReads_inputValuation hL hfit hpub hP hval hAr (E := cd.table)
  have hT := nodeTable_sound hAr hF.table hM.wf.refsOrdered hK hR hLeaf hcuts
  have hB : ir.BoundReads (ir.inputValuation I c x r v) := fun u hu e hk =>
    hR u hu e (by simp [valueDef, hk])
  have hN : ir.NormModel (ir.inputValuation I c x r v) (ir.circField c) cd.chr :=
    ⟨hM.wf.refsOrdered, hC.pos, hC.dec, hK⟩
  -- every entry
  intro en hen
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hen
  have hkc : k < cd.entries.length := by rw [hF.count]; exact hk
  have hce : (ir.circuit c).entries.getD k default = (ir.circuit c).entries[k] :=
    List.getD_eq_getElem _ _ hk
  have hh := hE k hkc
  simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at hh
  have hhead := hh.1
  unfold entryHeadE at hhead
  simp only [okB_seqE, okB_guardE, Bool.and_eq_true] at hhead
  obtain ⟨-, hroot⟩ := hhead
  rw [← hce]
  cases hr : (cd.entries.getD k default).root with
  | none =>
    -- a family entry: its record's head and cuts
    obtain ⟨f, hf, hfam⟩ := famHead_of_entryHeadE ir c ar cd hh.1 hr
    have hs : okB (ir.famSliceE c ar cd k 0 0) = true := hh.2.2
    have hIB := inputValuation_eq_inputBase hL hfit hpub hP
    rw [hIB]
    rw [hIB] at hT
    refine entryHolds_of_famHead hM hC hF.table hAr hF.chal hone hD hT
      (fun b t a T' hb ha hT' j hj => ?_) hfam hs hf
    have hq : a + j < (ir.circuit c).publicInputs := by omega
    have hqi : a + j < (ir.circuit c).inputCount := lt_of_lt_of_le hq hL.pubLe
    have h2 : a + j < 2 ^ d := lt_of_lt_of_le hqi hfit
    rw [hval _ hqi]
    simp only [vecRead, h2, ↓reduceDIte]
    rw [hpub ⟨a + j, h2⟩ hq, publicInput_weights hL hb hj]
    rfl
  | some rt =>
    simp only [hr, okB_seqE, okB_guardE, okB_mapE, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at hroot
    obtain ⟨⟨⟨⟨hrs, hfl⟩, hal⟩, -⟩, hrel, hmean⟩ := hroot
    rw [← relOk_eq_okB] at hrel
    have hz := (relOk_sound hC.hom hone hD hrel).2
    obtain ⟨hwl, hwv⟩ := hT rt hrs hfl
    refine entryHolds_of_entryMeaningB hN hAr.neg1 hmean fun ex hex => ?_
    cases hex
    intro i hi
    have hps := print_spec hM.wf.refsOrdered hF.table (ir.inputValuation I c x r v) rt
    have hi' : i < (cd.table.get rt).len := by rwa [hps.1] at hi
    have hzi := hz _ (mem_rootItems (cd := cd) (r := rt)
      (as := (cd.entries.getD k default).asserts) (by rw [hal]; exact hi') (by rw [hwl]; exact hi'))
    simp only [Assert.item, TE.eval] at hzi
    change ir.evalE _ _ _ i = 0
    rw [congrFun (hps.2 _) i]
    change ir.nodeSem (cd.env ar) cd.table (ir.inputValuation I c x r v) (ir.circuit c).domain rt
      i = 0
    rw [← hwv i hi']
    exact hzi

/-- **The program's circuits enforce their entries** (`circuitsEnforce_of_certs`): every circuit's
certificate checks, its field meets its codes, every bound value reads committed values and
constants (`hbd`), and every source is the bridge's circuit of its certificate, of input dimension
at most its circuit's width (`hd`). -/
theorem circuitsEnforce_of_certs (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w)
    (hL : ∀ c, ir.InputLayoutOk c) (cd : ℕ → CircuitData) (ar : ℕ → CodeArith)
    (hC : ∀ c < ir.circuits.length, ir.CircuitFieldOk I c (ar c) (cd c).chr)
    (h : ∀ c < ir.circuits.length, ir.circuitCertB c (ar c) (cd c) = true)
    (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
    (hd : ∀ c : Fin ir.circuits.length, (src c).d ≤ ir.circuitWidth c)
    (hS : ∀ c : Fin ir.circuits.length, (src c).S = CertificateBridge.toSource (cd c).layered
      (cd c).w ((cd c).consts.decode (I (ir.circField c)).decode) (src c).d) :
    ir.CircuitsEnforce I src := by
  refine ⟨fun c x r v hpub hP hsat => ?_, fun c => ?_⟩
  · rw [hS c] at hsat
    exact circuitHolds_of_circuitCertB hM hbd (hL c) (hC c c.2) (h c c.2) (src c).hfit hpub hP hsat
  · have hc := h c c.2
    simp only [circuitCertB, Bool.and_eq_true] at hc
    rw [hS c]
    exact toSource_shape (headerFacts_of_headerB hc.1).shape (hd c)

end GordieHowe.RealizedProgram
