-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldClaim
public import GordieHowe.Language.RealizedProgram.Locality
public import GordieHowe.ProofSystem.RingSwitching.PlanTree

@[expose] public section

/-!
# GordieHowe: the nodes the claims of a domain's masked reduction read

The packing tree of domain `d` routes each claim of the domain's masked reduction
(`GordieHowe.RealizedProgram.fieldMaskedReduction`) to the stages of the nodes it reads
(`PEdge.path`, `tree_zk.h`, `TreePlan::route` on the rows' node sets). This file gives each claim
its nodes (`GordieHowe.RealizedProgram.claimReads`) and proves that the claim reads only cells and
coordinates at those nodes (`GordieHowe.RealizedProgram.readsOnly_fieldMaskedReduction`):

* **an affine row** reads the nodes of the cells of the values its sides read of the committed
  assignment (`rowNodes`: `exprNodes`, `asgReads`, the cells' nodes `valueNodes`); its coefficient
  at a cell of another value is zero (`rowDiff_single`, `readsOnly_rowForm`), since the cells'
  valuation agrees at two cell assignments that agree on the cells of the values read
  (`cellValuation_congr`);
* **a row on views** reads the nodes of its values (`viewRowNodes`): a bit view's bits' node, the
  cells of the values another value reads (`viewValuation_congr`, `readsOnly_viewRowForm`);
* **a circuit's input claim** reads the nodes of its input blocks (`gkrNodes`);
* **a batch's claim**, on columns or bits, merged or not, reads the nodes of its operands' leaves
  (`batchNodes`, `leafNodes`: a committed value's or a pad copy's cells', a bit view's bits'),
  through the reading of the cells alone (`cellReader_congr`) or of the bit operands' variables
  (`bitsReader_congr`); the bit sumcheck after a batch on bits reads every bit of a word one of
  whose bits the batch reads, which lie at one node (`nodeOf_viewPlace_eq`).

The C++ routes by the same node sets (`CompiledDomain::extra_nodes`: a row its cells' nodes, a
batch's form rows its tables' node).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ}

/-! ## The nodes of the cells of a value -/

variable (ir) in
/-- **The nodes of the cells of value `w`**: the node of its committed coordinates and of its
pad's. -/
def valueNodes (es : List PackingEdge) (w : ℕ) : Finset ℕ :=
  (ir.cellNode es (.val w 0)).toFinset ∪ (ir.cellNode es (.pad w 0)).toFinset

/-- **The value of a cell key**: a committed coordinate's or a pad's value, none for a filler. -/
def CellKey.value : CellKey → Option ℕ
  | .val w _ => some w
  | .pad w _ => some w
  | .filler _ _ => none

/-- **A cell of a value is at one of the value's nodes.** -/
theorem mem_valueNodes {es : List PackingEdge} {k : CellKey} {w n : ℕ} (hk : k.value = some w)
    (hn : ir.cellNode es k = some n) : n ∈ ir.valueNodes es w := by
  rcases k with ⟨w', i⟩ | ⟨w', i⟩ | ⟨c, j⟩
  · cases hk
    exact Finset.mem_union_left _ (by simpa [cellNode, cellName] using hn)
  · cases hk
    exact Finset.mem_union_right _ (by simpa [cellNode, cellName] using hn)
  · cases hk

variable (ir) in
/-- **The values of the committed assignment that the expressions `xs` read** (`exprNodes`,
`asgReads`). -/
def exprsReads (xs : List Expr) : List ℕ :=
  xs.flatMap fun e => (ir.exprNodes e).flatMap (ir.asgReads ir.fuel)

/-! ## The cells' valuation reads the cells of the values read -/

variable (I) in
/-- **Two cell assignments agree on the cells of the values `W`.** -/
def CellsAgree (W : List ℕ) (z z' : ir.Cell d → (I (ir.domainField d)).K) : Prop :=
  ∀ k : ir.Cell d, ∀ w ∈ W, k.1.value = some w → z k = z' k

/-- **Cell assignments agreeing on the cells of `W` give committed assignments agreeing on
`W`.** -/
theorem asgAgree_ofCells {W : List ℕ} {z z' : ir.Cell d → (I (ir.domainField d)).K}
    (h : CellsAgree I W z z') :
    ir.AsgAgree I (· ∈ W) (ir.ofCells I d z) (ir.ofCells I d z') where
  val u hu := by
    funext i
    simp only [ofCells]
    split
    · rename_i hk
      rw [h ⟨_, hk⟩ u hu rfl]
    · rfl
  pad u hu := by
    funext i
    simp only [ofCells]
    split
    · rename_i hk
      rw [h ⟨_, hk⟩ u hu rfl]
    · rfl
  off u i hu := by
    rw [padsAgreeOff_ofCells d z u i hu, padsAgreeOff_ofCells d z' u i hu]

/-- **The cells' valuation at a value reading only `W`** agrees at cell assignments agreeing on
the cells of `W`. -/
theorem cellValuation_congr {W : List ℕ} {z z' : ir.Cell d → (I (ir.domainField d)).K}
    (h : CellsAgree I W z z') (x : ir.Valuation I) (r : (ir.layout I).Run) {u : ℕ}
    (hu : ∀ w ∈ ir.asgReads ir.fuel u, w ∈ W) :
    ir.cellValuation I d x r z u = ir.cellValuation I d x r z' u :=
  reader_bindAsg_congr (asgAgree_ofCells h) hu

/-- **An expression reads the cells' valuation at the values `exprsReads` gives it.** -/
theorem evalWith_cellValuation_congr {xs : List Expr} {z z' : ir.Cell d → (I (ir.domainField d)).K}
    (h : CellsAgree I (ir.exprsReads xs) z z') (x : ir.Valuation I) (r : (ir.layout I).Run)
    {e : Expr} (he : e ∈ xs) :
    ir.evalWith (ir.cellValuation I d x r z) d e = ir.evalWith (ir.cellValuation I d x r z') d e :=
  funext fun i => congrFun (evalE_congr fun u hu => cellValuation_congr h x r fun w hw =>
    List.mem_flatMap.2 ⟨e, he, List.mem_flatMap.2 ⟨u, hu, hw⟩⟩) i

/-! ## The affine rows -/

variable (ir) in
/-- **The values an affine row reads**: those its two sides read. -/
abbrev rowReadsVals (q : ir.Row d) : List ℕ :=
  ir.exprsReads [ir.rowLhs d q.1.1, ir.rowRhs d q.1.1]

/-- **The row's difference agrees at cell assignments agreeing on the cells of the values it
reads.** -/
theorem rowDiff_congr {q : ir.Row d} {z z' : ir.Cell d → (I (ir.domainField d)).K}
    (h : CellsAgree I (ir.rowReadsVals q) z z') (x : ir.Valuation I) (r : (ir.layout I).Run) :
    ir.rowDiff I d x r q.1.1 q.2 z = ir.rowDiff I d x r q.1.1 q.2 z' := by
  unfold rowDiff
  rw [evalWith_cellValuation_congr h x r (List.mem_cons_self ..),
    evalWith_cellValuation_congr h x r (List.mem_cons_of_mem _ (List.mem_singleton_self _))]

/-- **A row's coefficient at a cell of a value it does not read is zero.** -/
theorem rowDiff_single {q : ir.Row d} (x : ir.Valuation I) (r : (ir.layout I).Run) (k : ir.Cell d)
    (hk : ∀ w ∈ ir.rowReadsVals q, k.1.value ≠ some w) :
    ir.rowDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) =
      ir.rowDiff I d x r q.1.1 q.2 0 :=
  rowDiff_congr (fun k' w hw hk' => by
    have hne : k ≠ k' := fun h => hk w hw (h ▸ hk')
    simp [hne]) x r

end

/-! ## The claims' nodes -/

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) {Pk : (I (ir.domainField d)).Packing}
  (rs : List (REdge (I (ir.domainField d)) Pk))

/-- **The coefficient of `affineOn`** at a variable is the linear form at its unit vector. -/
theorem coeff_affineOn {F V : Type} [CommRing F] [Fintype V] [Encodable V] [DecidableEq V]
    (f : (V → F) →ₗ[F] F) (c : F) (v : V) : (affineOn f c).coeff v = f (Pi.single v 1) := by
  simp only [AffineForm.coeff, eval_affineOn, map_zero, zero_add, add_sub_cancel_right]

variable {rs} in
/-- **A cell's coordinate is at the cell's node**, or is a cell. -/
theorem nodeOf_place (Pads : Type) [Fintype Pads] (k : ir.Cell d) {n : ℕ}
    (h : nodeOf 0 (ir.fieldEdges d Pk rs Pads) (ir.place d rs Pads k) = some n) :
    ir.cellNode (rs.map REdge.plan) k.1 = some n := by
  unfold place at h
  split at h
  · rw [nodeOf_cellIn] at h
    cases h
  · rename_i a ha
    rw [ha]
    have := nodeOf_slotAt _ 0 _ _ _ n h
    rw [this, zero_add]

/-- **The nodes of an affine row**: the nodes of the cells of the values it reads. -/
def rowNodes (q : ir.Row d) : Finset ℕ :=
  (ir.rowReadsVals q).toFinset.biUnion (ir.valueNodes (rs.map REdge.plan))

/-- **An affine row reads only cells and its nodes.** -/
theorem readsOnly_rowForm (p : ir.DomainPub I) (q : ir.Row d) :
    (ir.rowForm src rs p (.inl q)).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) (rowNodes rs q)) := by
  intro z hz n hn
  have hsum : ∀ (c : ir.Cell d → (I (ir.domainField d)).K) (v : ir.Cell d → (I (ir.domainField d)).K),
      (∑ k, c k • LinearMap.proj (R := (I (ir.domainField d)).K)
        (φ := fun _ : ir.Cell d => (I (ir.domainField d)).K) k) v = ∑ k, c k * v k := by
    intro c v
    simp [LinearMap.sum_apply]
  rw [rowForm, coeff_affineOn, LinearMap.comp_apply] at hz
  change (∑ k, _ • LinearMap.proj k) _ ≠ 0 at hz
  rw [hsum] at hz
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hpk : ir.place d rs (ir.ClaimPads d src Pk) k = z := by
    by_contra hne
    apply hk
    change _ * Pi.single (M := fun _ => (I (ir.domainField d)).K) z 1
      (ir.place d rs (ir.ClaimPads d src Pk) k) = 0
    rw [Pi.single_apply, if_neg hne, mul_zero]
  have hdiff : ¬ ∀ w ∈ ir.rowReadsVals q, k.1.value ≠ some w := fun hall => by
    apply hk
    change (ir.rowDiff I d p.stmt p.run q.1.1 q.2 (fun j => if k = j then 1 else 0) -
      ir.rowDiff I d p.stmt p.run q.1.1 q.2 0) * _ = 0
    rw [rowDiff_single _ _ k hall, sub_self, zero_mul]
  push Not at hdiff
  obtain ⟨w, hw, hkw⟩ := hdiff
  rw [← hpk] at hn
  exact Finset.mem_biUnion.2 ⟨w, List.mem_toFinset.2 hw,
    mem_valueNodes hkw (nodeOf_place _ k hn)⟩

/-! ### The circuits -/

variable {rs} in
/-- **A cell's bit coordinate is at the view child of the cell's node**, or is a cell. -/
theorem nodeOf_viewPlace (Pads : Type) [Fintype Pads] (k : ir.Cell d) (j : Fin 16) {n : ℕ}
    (h : nodeOf 0 (ir.fieldEdges d Pk rs Pads) (ir.viewPlace d rs Pads k j) = some n) :
    ∃ a, ir.cellNode (rs.map REdge.plan) k.1 = some a ∧ viewChild (rs.map REdge.plan) a = some n := by
  unfold viewPlace at h
  split at h
  · rename_i a ha
    split at h
    · rename_i b hb
      have := nodeOf_slotAt _ 0 _ _ _ n h
      exact ⟨a, ha, by rw [hb, this, zero_add]⟩
    · rw [spareLog, nodeOf_cellIn] at h
      cases h
  · rw [spareLog, nodeOf_cellIn] at h
    cases h

variable (ir) in
/-- **The nodes of the bits of a bit view**: the view child of the node of its word. -/
def viewNodes (es : List PackingEdge) (u : ℕ) : Finset ℕ :=
  match (ir.value u).kind with
  | .bits w _ => ((ir.cellNode es (.val w 0)).bind (viewChild es)).toFinset
  | _ => ∅

variable (ir) in
/-- **The nodes an input block reads**: a committed value's or a pad's cells', a bit view's
bits'. -/
def blockNodes (es : List PackingEdge) : InputBlock → Finset ℕ
  | .committed u _ _ => ir.valueNodes es u
  | .pad u _ _ => ir.valueNodes es u
  | .view u _ _ => ir.viewNodes es u
  | _ => ∅

variable (ir) in
/-- **The nodes the input claim of circuit `c` reads**: its input blocks'. -/
def gkrNodes (es : List PackingEdge) (c : ℕ) : Finset ℕ :=
  (ir.circuit c).inputs.toFinset.biUnion (ir.blockNodes es)

/-- **A private input's coordinate is at a node of its circuit's input blocks**, or is a cell. -/
theorem inNodes_inputCoord (Pads : Type) [Fintype Pads] (c q : ℕ) {z : ir.TLog d rs Pads}
    (hz : ir.inputCoord rs Pads c q = some z) :
    InNodes 0 (ir.fieldEdges d Pk rs Pads) (ir.gkrNodes (rs.map REdge.plan) c) z := by
  intro n hn
  unfold inputCoord at hz
  obtain ⟨o, ho, hoz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨b, hb, hbo⟩ := List.exists_of_findSome?_eq_some ho
  simp only [id] at hoz
  subst hoz
  refine Finset.mem_biUnion.2 ⟨b, List.mem_toFinset.2 hb, ?_⟩
  have hkey : ∀ {k : CellKey} {w : ℕ}, k.value = some w →
      ir.keyCoord rs Pads k = some z → n ∈ ir.valueNodes (rs.map REdge.plan) w := by
    intro k w hkw hk
    unfold keyCoord at hk
    split at hk
    · rename_i hmem
      cases hk
      exact mem_valueNodes hkw (nodeOf_place Pads ⟨k, hmem⟩ hn)
    · cases hk
  cases b with
  | committed u a m =>
    simp only [blockCoord] at hbo
    split at hbo
    · exact hkey rfl (Option.some.inj hbo)
    · cases hbo
  | pad u a m =>
    simp only [blockCoord] at hbo
    split at hbo
    · exact hkey rfl (Option.some.inj hbo)
    · cases hbo
  | view u a m =>
    simp only [blockCoord] at hbo
    split at hbo
    · have hv := Option.some.inj hbo
      unfold viewCoord at hv
      show n ∈ ir.viewNodes _ u
      unfold viewNodes
      split at hv
      · rename_i w sel hk
        rw [hk]
        split at hv
        · rename_i hmem
          cases hv
          obtain ⟨a', ha', hb'⟩ := nodeOf_viewPlace Pads _ _ hn
          have hcn : ir.cellNode (rs.map REdge.plan) (.val w 0) = some a' := by
            simpa [cellNode, cellName] using ha'
          simp [hcn, hb']
        · cases hv
      · cases hv
    · cases hbo
  | filler a m =>
    simp only [blockCoord] at hbo
    split at hbo
    · have hv := Option.some.inj hbo
      unfold keyCoord at hv
      split at hv
      · rename_i hmem
        cases hv
        have := nodeOf_place Pads ⟨_, hmem⟩ hn
        simp [cellNode, cellName] at this
      · cases hv
    · cases hbo
  | pub _ _ _ => simp [blockCoord] at hbo
  | realizationPub _ _ _ => simp [blockCoord] at hbo
  | batchPads _ _ _ => simp [blockCoord] at hbo

/-- **The input forms of circuit `c` read only cells and its input blocks' nodes.** -/
theorem readsOnly_treeInputForms (Pads : Type) [Fintype Pads] [DecidableEq Pads] (c dd : ℕ)
    (p : ir.DomainPub I) (x : Fin (2 ^ dd)) :
    ((ir.treeInputForms rs Pads c dd).form p x).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs Pads) (ir.gkrNodes (rs.map REdge.plan) c)) := by
  simp only [treeInputForms]
  split_ifs
  · exact AffineForm.ReadsOnly.ofConst _
  · split
    · rename_i z hz
      exact AffineForm.ReadsOnly.var (inNodes_inputCoord rs Pads c x hz)
    · exact AffineForm.ReadsOnly.zero
  · exact AffineForm.ReadsOnly.zero

/-- **The input claim of the `i`-th circuit reads only cells and its input blocks' nodes.** -/
theorem readsOnly_gkrIP (i : Fin (ir.circs d).length) :
    (ir.gkrIP src rs i).ReadsOnly fun _ =>
      InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.gkrNodes (rs.map REdge.plan) (ir.circAt d i)) :=
  GKR.LayeredCircuit.readsOnly_maskedReduction _ _ _ _ _
    (readsOnly_treeInputForms rs _ _ _) fun j => by
      change InNodes 0 _ _ ((PEdge.path _ 0 _ 0 Fin.elim0).level.cell j)
      rw [level_cell]
      exact inNodes_cellIn _ _ _ _

/-! ### The leaves of batch operands and rows on views -/

/-- **The expressions of a batch operand.** -/
def BOperand.exprs : BOperand → List Expr
  | .atom e => [e]
  | .lin ts => ts.map (·.2)
  | .zero => []

/-- **An operand's value depends only on its expressions' values.** -/
theorem opValAt_congr {rd rd' : ir.Valuation I} {o : BOperand}
    (h : ∀ e ∈ o.exprs, ir.evalWith rd d e = ir.evalWith rd' d e) (i : ℕ) :
    ir.opValAt I d rd o i = ir.opValAt I d rd' o i := by
  cases o with
  | atom e =>
    simp only [opValAt, BOperand.val]
    rw [h e (List.mem_singleton_self _)]
  | lin ts =>
    simp only [opValAt, BOperand.val]
    exact sum_map_congr fun t ht => by rw [h t.2 (List.mem_map_of_mem ht)]
  | zero => rfl

/-- **A batch's operands read atoms only.** -/
theorem instOperand_exprs_atom {atom : Expr → Bool} {b : ℕ} (hb : ir.PartsOk atom d b)
    (j : Fin (ir.batch b).parts.length) (o : ℕ) :
    ∀ e ∈ (ir.instOperand atom d b j o).exprs, atom e = true := by
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part j
  have hk : (ir.partShape atom d b j).k = pf.operands.length := by rw [hsh]; rfl
  rcases instOperand_atoms hpf hops hk o with ⟨a, ha, haa⟩ | ⟨ts, hts, hall⟩ | h0
  · rw [ha]
    intro e he
    rw [BOperand.exprs, List.mem_singleton] at he
    exact he ▸ haa
  · rw [hts]
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
    exact hall t ht
  · rw [h0]
    intro e he
    cases he

variable (ir) in
/-- **A value read from its cells**: a committed value or a pad copy. -/
def isCellLeaf (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => true
  | .padCopy _ _ => true
  | _ => false

variable (ir) in
/-- **The nodes a leaf of a batch operand or a row reads**: a committed value's or a pad copy's
cells' nodes, a bit view's bits' node; none for another value. -/
def leafNodes (es : List PackingEdge) (v : ℕ) : Finset ℕ :=
  match (ir.value v).kind with
  | .priv => ir.valueNodes es v
  | .padCopy _ _ => ir.valueNodes es v
  | .bits _ _ => ir.viewNodes es v
  | _ => ∅

/-- **A value read from its cells reads its cells' nodes.** -/
theorem leafNodes_of_isCellLeaf {es : List PackingEdge} {v : ℕ} (h : ir.isCellLeaf v = true) :
    ir.leafNodes es v = ir.valueNodes es v := by
  unfold isCellLeaf at h
  unfold leafNodes
  split at h <;> simp_all

/-- **A bit view reads its bits' node.** -/
theorem leafNodes_of_bits {es : List PackingEdge} {v w : ℕ} {sel : IndexMap}
    (h : (ir.value v).kind = .bits w sel) : ir.leafNodes es v = ir.viewNodes es v := by
  simp [leafNodes, h]

variable (ir) in
/-- **The values batch `b`'s operands read** at the atom test `atom`: the values of every part's
operands' expressions. -/
def batchVals (atom : Expr → Bool) (d b : ℕ) : List ℕ :=
  (List.range (ir.batch b).parts.length).flatMap fun j =>
    (List.range (ir.relShape atom d b).k).flatMap fun o =>
      (ir.instOperand atom d b j o).exprs.flatMap ir.exprNodes

variable (ir) in
/-- **The nodes batch `b`'s claim reads**: its operands' leaves' nodes. -/
def batchNodes (es : List PackingEdge) (atom : Expr → Bool) (d b : ℕ) : Finset ℕ :=
  (ir.batchVals atom d b).toFinset.biUnion (ir.leafNodes es)

theorem mem_batchNodes {es : List PackingEdge} {atom : Expr → Bool} {b : ℕ}
    (j : Fin (ir.batch b).parts.length) {o : ℕ} (ho : o < (ir.relShape atom d b).k) {e : Expr}
    (he : e ∈ (ir.instOperand atom d b j o).exprs) {v : ℕ} (hv : v ∈ ir.exprNodes e) {n : ℕ}
    (hn : n ∈ ir.leafNodes es v) : n ∈ ir.batchNodes es atom d b :=
  Finset.mem_biUnion.2 ⟨v, List.mem_toFinset.2 (List.mem_flatMap.2 ⟨j, List.mem_range.2 j.2,
    List.mem_flatMap.2 ⟨o, List.mem_range.2 ho, List.mem_flatMap.2 ⟨e, he, hv⟩⟩⟩), hn⟩

/-- **The reading of the cells alone at a batch leaf** agrees at cell assignments agreeing on the
leaf's cells. -/
theorem cellReader_congr {z z' : ir.Cell d → (I (ir.domainField d)).K} {v : ℕ}
    (hv : ir.batchLeafOk v = true)
    (h : ir.isCellLeaf v = true → ∀ k : ir.Cell d, k.1.value = some v → z k = z' k) :
    ir.cellReader I d z v = ir.cellReader I d z' v := by
  unfold batchLeafOk at hv
  split at hv
  · rename_i hk
    have h' := h (by simp [isCellLeaf, hk])
    simp only [cellReader, reader_of_priv _ hk, ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl)]
    funext i
    simp only [ofCells]
    split
    · rename_i hm
      rw [h' ⟨_, hm⟩ rfl]
    · rfl
  · rename_i u m hk
    have h' := h (by simp [isCellLeaf, hk])
    simp only [cellReader, reader_of_padCopy _ hk,
      ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl)]
    funext i
    simp only [ofCells]
    split
    · rename_i hm
      rw [h' ⟨_, hm⟩ rfl]
    · rfl
  · rename_i es hk
    funext i
    simp only [cellReader, reader_of_constant _ hk]
  · cases hv

/-- **A gradient on the cells read through the tree reads only cells and `N`**, when changing a
cell outside the nodes `N` does not change the function. -/
theorem readsOnly_cellsGrad (Pads : Type) [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    {f : (ir.Cell d → (I (ir.domainField d)).K) → (I (ir.domainField d)).K} {N : Finset ℕ}
    (hf : ∀ k : ir.Cell d, f (fun j => if k = j then 1 else 0) ≠ f 0 →
      ∀ n, ir.cellNode (rs.map REdge.plan) k.1 = some n → n ∈ N) (c : (I (ir.domainField d)).K) :
    (affineOn ((gradLin f) ∘ₗ ir.treeCellsLin rs Pads) c).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs Pads) N) := by
  intro z hz n hn
  have hsum : ∀ (g : ir.Cell d → (I (ir.domainField d)).K) (v : ir.Cell d → (I (ir.domainField d)).K),
      (∑ k, g k • LinearMap.proj (R := (I (ir.domainField d)).K)
        (φ := fun _ : ir.Cell d => (I (ir.domainField d)).K) k) v = ∑ k, g k * v k := by
    intro g v
    simp [LinearMap.sum_apply]
  rw [coeff_affineOn, LinearMap.comp_apply] at hz
  change (∑ k, _ • LinearMap.proj k) _ ≠ 0 at hz
  rw [hsum] at hz
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hpk : ir.place d rs Pads k = z := by
    by_contra hne
    apply hk
    change _ * Pi.single (M := fun _ => (I (ir.domainField d)).K) z 1 (ir.place d rs Pads k) = 0
    rw [Pi.single_apply, if_neg hne, mul_zero]
  have hfk : f (fun j => if k = j then 1 else 0) ≠ f 0 := fun h => hk (by
    change (f (fun j => if k = j then 1 else 0) - f 0) * _ = 0
    rw [h, sub_self, zero_mul])
  rw [← hpk] at hn
  exact hf k hfk n (nodeOf_place Pads k hn)

/-- **An operand of atoms on columns at the reading of the cells alone** changes with a cell only
when the cell's value is a leaf the operand reads. -/
theorem opValAt_cellReader_single {o : BOperand} (ho : ∀ e ∈ o.exprs, ir.atomB e = true)
    (t : ℕ) (k : ir.Cell d)
    (hk : ∀ e ∈ o.exprs, ∀ v ∈ ir.exprNodes e, ir.isCellLeaf v = true → k.1.value ≠ some v) :
    ir.opValAt I d (ir.cellReader I d (fun j => if k = j then 1 else 0)) o t =
      ir.opValAt I d (ir.cellReader I d 0) o t := by
  refine opValAt_congr (fun e he => funext fun i => ?_) t
  have hae := ho e he
  simp only [atomB, Bool.and_eq_true, List.all_eq_true] at hae
  refine congrFun (evalE_congr fun v hv => cellReader_congr (hae.1.1 v hv) fun hl k' hk' => ?_) i
  have hne : k ≠ k' := fun h => hk e he v hv hl (h ▸ hk')
  simp [hne]

/-- **A covered batch on columns reads only cells and its operands' leaves' nodes.** -/
theorem readsOnly_colsForm (cb : ir.CBatch I d .columns) (p : ir.DomainPub I) (t o) :
    ((ir.colsBatchAt rs (ir.ClaimPads d src Pk) cb).form p t o).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) ir.atomB d cb.idx)) := by
  refine readsOnly_cellsGrad rs _ (fun k hk n hn => ?_) _
  by_contra hN
  apply hk
  have hb : ir.PartsOk ir.atomB d cb.idx := cb.partsOk
  refine opValAt_cellReader_single (instOperand_exprs_atom hb _ _) _ k fun e he v hv hl hkv => hN ?_
  exact mem_batchNodes _ o.2 he hv (by
    rw [leafNodes_of_isCellLeaf hl]
    exact mem_valueNodes hkv hn)

/-- **A covered merged batch on columns reads only cells and its operands' leaves' nodes.** -/
theorem readsOnly_mergedColsForm (b : Fin ir.batches.length) (p : ir.DomainPub I) {t o : ℕ}
    (ho : o < (ir.relShape ir.atomB d b).k) (hb : ir.PartsOk ir.atomB d b) :
    (ir.mergedForm rs (ir.ClaimPads d src Pk) b p t o .columns).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) ir.atomB d b)) := by
  refine readsOnly_cellsGrad rs _ (fun k hk n hn => ?_) _
  by_contra hN
  apply hk
  refine Finset.sum_congr rfl fun q _ => ?_
  refine opValAt_cellReader_single (instOperand_exprs_atom hb _ _) _ k fun e he v hv hl hkv => hN ?_
  exact mem_batchNodes q ho he hv (by
    rw [leafNodes_of_isCellLeaf hl]
    exact mem_valueNodes hkv hn)

/-- **A gradient on the logical coordinates reads only cells and `N`**, when changing a coordinate
outside the nodes `N` does not change the function. -/
theorem readsOnly_logGrad (Pads : Type) [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    {g : (ir.TLog d rs Pads → (I (ir.domainField d)).K) → (I (ir.domainField d)).K} {N : Finset ℕ}
    (hg : ∀ z, g (fun j => if z = j then 1 else 0) ≠ g 0 →
      InNodes 0 (ir.fieldEdges d Pk rs Pads) N z) (c : (I (ir.domainField d)).K) :
    (affineOn (gradLin g) c).ReadsOnly (InNodes 0 (ir.fieldEdges d Pk rs Pads) N) := by
  intro z hz
  rw [coeff_affineOn] at hz
  have hsum : (gradLin g) (Pi.single z 1) = g (fun j => if z = j then 1 else 0) - g 0 := by
    have hv : ∀ v : ir.TLog d rs Pads → (I (ir.domainField d)).K,
        (gradLin g) v = ∑ c, (g (fun j => if c = j then 1 else 0) - g 0) * v c := by
      intro v
      simp [gradLin, LinearMap.sum_apply]
    rw [hv, Finset.sum_eq_single z (fun c _ hc => by rw [Pi.single_apply, if_neg hc, mul_zero])
      (by simp), Pi.single_eq_same, mul_one]
  rw [hsum] at hz
  exact hg z (sub_ne_zero.1 hz)

/-- **The variables of the bit operands at two logical assignments agreeing at a coordinate's
cells and bits.** -/
theorem bitsReader_congr {y y' : ir.BitsVar d → (I (ir.domainField d)).K} {v : ℕ}
    (hv : ir.bitsLeafOk d v = true)
    (hc : ir.isCellLeaf v = true → ∀ k : ir.Cell d, k.1.value = some v → y (.inl k) = y' (.inl k))
    (hb : ∀ w sel, (ir.value v).kind = .bits w sel → ∀ (k : ir.Cell d) (j : Fin 16) kk,
      k.1 = .val w kk → y (.inr (.inl (k, j))) = y' (.inr (.inl (k, j))))
    (hs : ∀ i, y (.inr (.inr (v, i))) = y' (.inr (.inr (v, i)))) :
    ir.bitsReader I d y v = ir.bitsReader I d y' v := by
  funext i
  unfold bitsLeafOk at hv
  split at hv
  · rename_i hk
    have h' := hc (by simp [isCellLeaf, hk])
    simp only [bitsReader, bitValuation, hk, reader_of_priv _ hk,
      ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, Function.comp_apply]
    split
    · rename_i hm
      exact congrArg _ (h' ⟨_, hm⟩ rfl)
    · rfl
  · rename_i u m hk
    have h' := hc (by simp [isCellLeaf, hk])
    simp only [bitsReader, bitValuation, hk, reader_of_padCopy _ hk,
      ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, Function.comp_apply]
    split
    · rename_i hm
      exact congrArg _ (h' ⟨_, hm⟩ rfl)
    · rfl
  · rename_i es hk
    simp only [bitsReader, bitValuation, hk, reader_of_constant _ hk]
  · rename_i w sel hk
    simp only [bitsReader, bitValuation, hk, wordBit, Function.comp_apply]
    split
    · rename_i hm
      rw [hb w sel hk ⟨_, hm⟩ _ _ rfl]
    · rfl
  · rename_i hk
    simp only [bitsReader, bitValuation, hk, reader_of_input _ hk, hs]
  · rename_i name hk
    simp only [bitsReader, bitValuation, hk, reader_of_opaque_nil _ hk, hs]
  · cases hv

/-- **The nodes of a bit coordinate of a word** are those of its bit views. -/
theorem mem_viewNodes_of_viewPlace (Pads : Type) [Fintype Pads] {v w : ℕ} {sel : IndexMap}
    (hk : (ir.value v).kind = .bits w sel) {k : ir.Cell d} {kk : ℕ} (hkk : k.1 = .val w kk)
    {j : Fin 16} {n : ℕ}
    (hn : nodeOf 0 (ir.fieldEdges d Pk rs Pads) (ir.viewPlace d rs Pads k j) = some n) :
    n ∈ ir.leafNodes (rs.map REdge.plan) v := by
  rw [leafNodes_of_bits hk]
  obtain ⟨a, ha, hb⟩ := nodeOf_viewPlace Pads k j hn
  rw [hkk] at ha
  have hcn : ir.cellNode (rs.map REdge.plan) (.val w 0) = some a := by
    simpa [cellNode, cellName] using ha
  simp [viewNodes, hk, hcn, hb]

/-- **A bit operand read from the logical coordinates** changes with a coordinate only at the
coordinates of its leaves' cells and bits. -/
theorem opValAt_bitsReader_single (Pads : Type) [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    {o : BOperand} (ho : ∀ e ∈ o.exprs, ir.bitsAtomB d e = true) (x : ir.Valuation I) (t : ℕ)
    (z : ir.TLog d rs Pads) {N : Finset ℕ}
    (hN : ∀ e ∈ o.exprs, ∀ v ∈ ir.exprNodes e, ir.leafNodes (rs.map REdge.plan) v ⊆ N)
    (hz : ¬ InNodes 0 (ir.fieldEdges d Pk rs Pads) N z) :
    ir.opValAt I d (ir.bitsReader I d (ir.treeLift rs Pads x (fun j => if z = j then 1 else 0))) o t =
      ir.opValAt I d (ir.bitsReader I d (ir.treeLift rs Pads x 0)) o t := by
  simp only [InNodes, not_forall] at hz
  obtain ⟨n, hn, hnN⟩ := hz
  refine opValAt_congr (fun e he => funext fun i => ?_) t
  have hae := ho e he
  simp only [bitsAtomB, Bool.and_eq_true, List.all_eq_true] at hae
  refine congrFun (evalE_congr fun v hv => bitsReader_congr
    (y := ir.treeLift rs Pads x (fun j => if z = j then 1 else 0)) (y' := ir.treeLift rs Pads x 0)
    (hae.1.1 v hv) (fun hl k hkv => ?_) (fun w sel hk k j kk hkk => ?_) (fun i => rfl)) i
  · change (if z = ir.place d rs Pads k then (1 : (I (ir.domainField d)).K) else 0) = 0
    rw [if_neg]
    rintro rfl
    exact hnN (hN e he v hv (by
      rw [leafNodes_of_isCellLeaf hl]
      exact mem_valueNodes hkv (nodeOf_place Pads k hn)))
  · change (if z = ir.viewPlace d rs Pads k j then (1 : (I (ir.domainField d)).K) else 0) = 0
    rw [if_neg]
    rintro rfl
    exact hnN (hN e he v hv (mem_viewNodes_of_viewPlace rs Pads hk hkk hn))

/-- **A covered batch on bits reads only cells and its operands' leaves' nodes.** -/
theorem readsOnly_bitsForm (cb : ir.CBatch I d .bits) (p : ir.DomainPub I) (t o) :
    ((ir.bitsBatchAt rs (ir.ClaimPads d src Pk) cb).form p t o).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) (ir.bitsAtomB d) d cb.idx)) := by
  refine readsOnly_logGrad rs _ (fun z hz => ?_) _
  by_contra hN
  apply hz
  have hb : ir.PartsOk (ir.bitsAtomB d) d cb.idx := cb.partsOk
  exact opValAt_bitsReader_single rs _ (instOperand_exprs_atom hb _ _) _ _ z
    (fun e he v hv => fun n hn => mem_batchNodes _ o.2 he hv hn) hN

/-- **A covered merged batch on bits reads only cells and its operands' leaves' nodes.** -/
theorem readsOnly_mergedBitsForm (b : Fin ir.batches.length) (p : ir.DomainPub I) {t o : ℕ}
    (ho : o < (ir.relShape (ir.bitsAtomB d) d b).k) (hb : ir.PartsOk (ir.bitsAtomB d) d b) :
    (ir.mergedForm rs (ir.ClaimPads d src Pk) b p t o .bits).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) (ir.bitsAtomB d) d b)) := by
  refine readsOnly_logGrad rs _ (fun z hz => ?_) _
  by_contra hN
  apply hz
  refine Finset.sum_congr rfl fun q _ => ?_
  exact opValAt_bitsReader_single rs _ (instOperand_exprs_atom hb _ _) _ _ z
    (fun e he v hv => fun n hn => mem_batchNodes q ho he hv hn) hN

variable {rs} in
/-- **The bits of a cell lie at one node, or are all the spare cell**: the view child has relative
degree `16`, so a word's sixteen slots are in range together. -/
theorem nodeOf_viewPlace_eq (Pads : Type) [Fintype Pads] (k : ir.Cell d) (j j' : Fin 16) :
    nodeOf 0 (ir.fieldEdges d Pk rs Pads) (ir.viewPlace d rs Pads k j) =
      nodeOf 0 (ir.fieldEdges d Pk rs Pads) (ir.viewPlace d rs Pads k j') := by
  unfold viewPlace
  split
  · rename_i a ha
    split
    · rename_i b hb
      rw [nodeOf_slotAt_eq, nodeOf_slotAt_eq]
      obtain ⟨hbl, -, hview⟩ := viewChild_spec hb
      have hd : ((ir.fieldEdges d Pk rs Pads)[b]'(by rwa [length_fieldEdges, ← List.length_map
          (f := REdge.plan)])).d = 16 := by
        rw [getElem_fieldEdges]
        simp only [isView, Bool.and_eq_true, beq_iff_eq] at hview
        have := hview.1.1.2
        rw [List.getD_eq_getElem _ _ hbl] at this
        simpa [plannedEdge] using this
      split_ifs with h1 h2 h3 h3 <;> first | rfl | (rw [hd] at h2 h3; omega)
    · rfl
  · rfl

/-! ### The rows on views -/

variable (ir) in
/-- **The nodes a value read by a row on views reads**: a bit view's bits' node, the nodes of the
cells of the values another value reads of the committed assignment. -/
def viewLeafNodes (es : List PackingEdge) (u : ℕ) : Finset ℕ :=
  match (ir.value u).kind with
  | .bits _ _ => ir.viewNodes es u
  | _ => (ir.asgReads ir.fuel u).toFinset.biUnion (ir.valueNodes es)

/-- **The nodes of a row on views**: those of the values its sides read. -/
def viewRowNodes (q : ir.ViewRow d) : Finset ℕ :=
  (ir.exprNodes (ir.rowLhs d q.1.1) ++ ir.exprNodes (ir.rowRhs d q.1.1)).toFinset.biUnion
    (ir.viewLeafNodes (rs.map REdge.plan))

/-- **The views' valuation at a value** agrees at assignments agreeing on its bits' coordinates (a
bit view) or on the cells of the values it reads (another value). -/
theorem viewValuation_congr {z z' : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K}
    (x : ir.Valuation I) (r : (ir.layout I).Run) {u : ℕ}
    (hb : ∀ w sel, (ir.value u).kind = .bits w sel → ∀ (k : ir.Cell d) (j : Fin 16) kk,
      k.1 = .val w kk → z (.inr (k, j)) = z' (.inr (k, j)))
    (hc : (∀ w sel, (ir.value u).kind ≠ .bits w sel) →
      CellsAgree I (ir.asgReads ir.fuel u) (z ∘ Sum.inl) (z' ∘ Sum.inl)) :
    ir.viewValuation I d x r z u = ir.viewValuation I d x r z' u := by
  funext i
  unfold viewValuation bitValuation
  split
  · rename_i w sel hk
    simp only [wordBit, Function.comp_apply]
    split
    · rename_i hm
      rw [hb w sel hk ⟨_, hm⟩ _ _ rfl]
    · rfl
  · rename_i hk
    exact congrFun (cellValuation_congr (hc fun w sel h => hk w sel h) x r fun w hw => hw) i

/-- **A row on views reads only cells and its nodes.** -/
theorem readsOnly_viewRowForm (p : ir.DomainPub I) (q : ir.ViewRow d) :
    (ir.rowForm src rs p (.inr q)).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) (viewRowNodes rs q)) := by
  intro z hz n hn
  by_contra hN
  apply hz
  have hsum : ∀ (c : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K)
      (v : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K),
      (∑ k, c k • LinearMap.proj (R := (I (ir.domainField d)).K)
        (φ := fun _ : ir.Cell d ⊕ (ir.Cell d × Fin 16) => (I (ir.domainField d)).K) k) v =
        ∑ k, c k * v k := by
    intro c v
    simp [LinearMap.sum_apply]
  rw [rowForm, coeff_affineOn, LinearMap.comp_apply]
  change (∑ k, _ • LinearMap.proj k) _ = 0
  rw [hsum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hmem : ∀ u, u ∈ ir.exprNodes (ir.rowLhs d q.1.1) ++ ir.exprNodes (ir.rowRhs d q.1.1) →
      n ∈ ir.viewLeafNodes (rs.map REdge.plan) u → False := fun u hu hnu =>
    hN (Finset.mem_biUnion.2 ⟨u, List.mem_toFinset.2 hu, hnu⟩)
  -- the views' valuation agrees at the unit vector `s` and at zero
  have hcongr : (∀ u, u ∈ ir.exprNodes (ir.rowLhs d q.1.1) ++ ir.exprNodes (ir.rowRhs d q.1.1) →
      ir.viewValuation I d p.stmt p.run (fun j => if s = j then 1 else 0) u =
        ir.viewValuation I d p.stmt p.run 0 u) →
      ir.viewDiff I d p.stmt p.run q.1.1 q.2 (fun j => if s = j then 1 else 0) =
        ir.viewDiff I d p.stmt p.run q.1.1 q.2 0 := fun h => by
    unfold viewDiff
    have e1 := evalE_congr (f := ir.domainField d) (e := ir.rowLhs d q.1.1)
      fun u hu => h u (List.mem_append_left _ hu)
    have e2 := evalE_congr (f := ir.domainField d) (e := ir.rowRhs d q.1.1)
      fun u hu => h u (List.mem_append_right _ hu)
    simp only [evalWith]
    rw [e1, e2]
  rcases s with k | ⟨k, j⟩
  · -- a cell
    by_cases hpk : ir.place d rs (ir.ClaimPads d src Pk) k = z
    · rw [hcongr fun u hu => viewValuation_congr _ _ (fun w sel hk k' j kk hkk => by
          simp) fun hnb k' w hw hk' => by
          by_cases hkk : k = k'
          · subst hkk
            exfalso
            refine hmem u hu ?_
            unfold viewLeafNodes
            split
            · rename_i w' sel' hk''
              exact absurd hk'' (hnb w' sel')
            · rw [← hpk] at hn
              exact Finset.mem_biUnion.2 ⟨w, List.mem_toFinset.2 hw,
                mem_valueNodes hk' (nodeOf_place _ k hn)⟩
          · simp [hkk]]
      rw [sub_self, zero_mul]
    · change _ * Pi.single (M := fun _ => (I (ir.domainField d)).K) z 1
        (ir.place d rs (ir.ClaimPads d src Pk) k) = 0
      rw [Pi.single_apply, if_neg hpk, mul_zero]
  · -- a bit
    by_cases hpk : ir.viewPlace d rs (ir.ClaimPads d src Pk) k j = z
    · rw [hcongr fun u hu => viewValuation_congr _ _ (fun w sel hk k' j' kk hkk => by
          by_cases he : (Sum.inr (k, j) : ir.Cell d ⊕ (ir.Cell d × Fin 16)) = .inr (k', j')
          · exfalso
            simp only [Sum.inr.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            refine hmem u hu ?_
            rw [← hpk] at hn
            unfold viewLeafNodes
            rw [hk]
            obtain ⟨a, ha, hb⟩ := nodeOf_viewPlace _ k j hn
            rw [hkk] at ha
            have hcn : ir.cellNode (rs.map REdge.plan) (.val w 0) = some a := by
              simpa [cellNode, cellName] using ha
            simp [viewNodes, hk, hcn, hb]
          · simp [he]) fun _ k' w _ _ => by simp]
      rw [sub_self, zero_mul]
    · change _ * Pi.single (M := fun _ => (I (ir.domainField d)).K) z 1
        (ir.viewPlace d rs (ir.ClaimPads d src Pk) k j) = 0
      rw [Pi.single_apply, if_neg hpk, mul_zero]

/-- **A cell's coordinate in the tree's level reads no node.** -/
theorem inNodes_treeLevel_cell (Pads : Type) [Fintype Pads] {N : Finset ℕ}
    (c : ir.TreeCell d Pk rs Pads) :
    InNodes 0 (ir.fieldEdges d Pk rs Pads) N ((ir.treeLevel d rs Pads).cell c) := by
  change InNodes 0 _ _ ((PEdge.path _ 0 _ 0 Fin.elim0).level.cell c)
  rw [level_cell]
  exact inNodes_cellIn _ _ _ _

/-- **The bits of a word in the bit layout are at one node, or all cells.** -/
theorem inNodes_bitLayout {N : Finset ℕ} (pad : BitPad → ir.FCell src Pk rs)
    (nodes : Sumcheck.Nodes (I (ir.domainField d)).K) (q : Fin (ir.cellKeys d).length) (b b')
    (h : InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) N
      ((ir.bitLayoutAt src rs pad nodes).bit q b')) :
    InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) N
      ((ir.bitLayoutAt src rs pad nodes).bit q b) := fun n hn => h n (by
  change nodeOf 0 _ (ir.viewPlace d rs _ _ _) = some n at hn ⊢
  rwa [nodeOf_viewPlace_eq] at hn)

/-- **A covered merged batch reads only cells and its operands' leaves' nodes**, on columns. -/
theorem readsOnly_mergedForm_cols (cb : ir.MBatch I d) (hom : cb.om = .columns)
    (p : ir.DomainPub I) (t o) :
    ((ir.mergedBatchAt rs (ir.ClaimPads d src Pk) cb).form p t o).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) ir.atomB d cb.idx)) := by
  obtain ⟨idx, ok, om, hops, hm, dom⟩ := cb
  subst hom
  exact readsOnly_mergedColsForm src rs idx p o.2
    (MBatch.partsOk (cb := ⟨idx, ok, .columns, hops, hm, dom⟩))

/-- **A covered merged batch reads only cells and its operands' leaves' nodes**, on bits. -/
theorem readsOnly_mergedForm_bits (cb : ir.MBatch I d) (hom : cb.om = .bits)
    (p : ir.DomainPub I) (t o) :
    ((ir.mergedBatchAt rs (ir.ClaimPads d src Pk) cb).form p t o).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (ir.batchNodes (rs.map REdge.plan) (ir.bitsAtomB d) d cb.idx)) := by
  obtain ⟨idx, ok, om, hops, hm, dom⟩ := cb
  subst hom
  exact readsOnly_mergedBitsForm src rs idx p o.2
    (MBatch.partsOk (cb := ⟨idx, ok, .bits, hops, hm, dom⟩))

/-- **The nodes the claims of branch `j` read**: a batch's, its operands' leaves' nodes
(`batchNodes`); each circuit's input claim its input blocks' (`gkrNodes`). -/
def branchReads : (j : ir.BranchIdx d Pk) → Fin (ir.branchNc d Pk j) → Finset ℕ
  | .inl (.inl (.inl i)) => fun _ => ir.batchNodes (rs.map REdge.plan) ir.atomB d (ir.cbatches d Pk)[i].idx
  | .inl (.inl (.inr i)) => fun _ =>
      ir.batchNodes (rs.map REdge.plan) (ir.bitsAtomB d) d ((ir.sumBatches d Pk)[i]).cb.idx
  | .inl (.inr (.inl i)) => fun _ => ir.batchNodes (rs.map REdge.plan) ir.atomB d (ir.mbatches d Pk)[i].idx
  | .inl (.inr (.inr i)) => fun _ =>
      ir.batchNodes (rs.map REdge.plan) (ir.bitsAtomB d) d ((ir.sumMBatches d Pk)[i]).mb.idx
  | .inr _ => FieldProof.MaskedReduction.ofListFamily (ncOf := fun _ => 1)
      (fun i _ => ir.gkrNodes (rs.map REdge.plan) (ir.circAt d i)) (List.finRange _)

/-- **Every branch's claims read only cells and their nodes.** -/
theorem readsOnly_branchIP : (j : ir.BranchIdx d Pk) →
    (ir.branchIP src rs j).ReadsOnly
      (fun c => InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) (branchReads rs j c))
  | .inl (.inl (.inl i)) => BatchedZerocheck.AffineBatch.readsOnly_ip _ _ _ _
      (fun p t o => readsOnly_colsForm src rs _ p t o) (inNodes_treeLevel_cell rs _)
  | .inl (.inl (.inr i)) => FieldProof.MaskedReduction.ReadsOnly.bitSumcheck
      (BatchedZerocheck.AffineBatch.readsOnly_ip _ _ _ _
        (fun p t o => readsOnly_bitsForm src rs _ p t o) (inNodes_treeLevel_cell rs _))
      (fun _ _ => inNodes_treeLevel_cell rs _ _)
      (fun q b b' h => inNodes_bitLayout src rs _ _ q b b' h)
  | .inl (.inr (.inl i)) => BatchedZerocheck.MergedAffineBatch.readsOnly_ip _ _ _ _
      (fun p t o => readsOnly_mergedForm_cols src rs _
        (om_of_mem_mbatches (List.getElem_mem _)) p t o) (inNodes_treeLevel_cell rs _)
  | .inl (.inr (.inr i)) => FieldProof.MaskedReduction.ReadsOnly.bitSumcheck
      (BatchedZerocheck.MergedAffineBatch.readsOnly_ip _ _ _ _
        (fun p t o => readsOnly_mergedForm_bits src rs _ ((ir.sumMBatches d Pk)[i]).bits p t o)
        (inNodes_treeLevel_cell rs _))
      (fun _ _ => inNodes_treeLevel_cell rs _ _)
      (fun q b b' h => inNodes_bitLayout src rs _ _ q b b' h)
  | .inr _ => FieldProof.MaskedReduction.ReadsOnly.ofList
      (S := fun N => InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) N)
      (fun i => readsOnly_gkrIP src rs i) _

/-- **The nodes of a row of domain `d`**: an affine row's (`rowNodes`), a row on views'
(`viewRowNodes`). -/
def rowIdxNodes : ir.RowIdx d → Finset ℕ
  | .inl q => rowNodes rs q
  | .inr q => viewRowNodes rs q

/-- **Every row reads only cells and its nodes.** -/
theorem readsOnly_rowClaims (p : ir.DomainPub I) (q : Fin (Fintype.card (ir.RowIdx d))) :
    (ir.rowClaims src rs p q).ReadsOnly
      (InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))
        (rowIdxNodes rs ((Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm q))) := by
  unfold rowClaims
  generalize (Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm q = t
  rcases t with q | q
  · exact readsOnly_rowForm src rs p q
  · exact readsOnly_viewRowForm src rs p q

/-- **The nodes each claim of domain `d`'s masked reduction reads**: each branch's
(`branchReads`: every node for a batch's claim, its input blocks' for a circuit's), each row's
(`rowIdxNodes`). -/
def claimReads : Fin (ir.claimCount (d := d) (Pk := Pk)) → Finset ℕ :=
  Fin.append (FieldProof.MaskedReduction.ofListFamily
      (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
      (fun b => branchReads rs (ir.branchEquiv d Pk b)) (List.finRange _))
    fun q => rowIdxNodes rs ((Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm q)

/-- **Every claim of domain `d`'s masked reduction reads only cells and its nodes.** -/
theorem readsOnly_fieldMaskedReduction :
    (ir.fieldMaskedReduction src rs).ReadsOnly
      (fun c => InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) (claimReads rs c)) := by
  have hb := FieldProof.MaskedReduction.ReadsOnly.ofList
    (S := fun N => InNodes 0 (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) N)
    (fun b => readsOnly_branchIP src rs (ir.branchEquiv d Pk b)) (List.finRange _)
  have hr := FieldProof.MaskedReduction.readsOnly_staticProducts (Wit := ir.FCell src Pk rs →
      (I (ir.domainField d)).K) (cells := id) (products := ir.quadProducts src rs)
    (readsOnly_rowClaims src rs)
  refine (hb.append hr).mono fun c z hz => ?_
  refine Fin.addCases (fun c hz => ?_) (fun c hz => ?_) c hz
  · rw [Fin.append_left] at hz
    rw [claimReads, Fin.append_left]
    exact hz
  · rw [Fin.append_right] at hz
    rw [claimReads, Fin.append_right]
    exact hz

/-- **A claim's nodes are positions of the tree.** -/
theorem lt_of_mem_claimReads {c : Fin (ir.claimCount (d := d) (Pk := Pk))} {n : ℕ}
    (h : n ∈ claimReads rs c) : n < rs.length := by
  have hcell : ∀ k, ir.cellNode (rs.map REdge.plan) k = some n → n < rs.length := fun k hk => by
    unfold cellNode at hk
    cases hn : ir.cellName k with
    | none => rw [hn] at hk; cases hk
    | some s =>
      rw [hn] at hk
      obtain ⟨ha, -⟩ := nodeIdx_spec hk
      simpa using ha
  have hval : ∀ w, n ∈ ir.valueNodes (rs.map REdge.plan) w → n < rs.length := fun w hw => by
    rcases Finset.mem_union.1 hw with hw | hw
    · exact hcell _ (Option.mem_toFinset.1 hw)
    · exact hcell _ (Option.mem_toFinset.1 hw)
  have hview : ∀ u, n ∈ ir.viewNodes (rs.map REdge.plan) u → n < rs.length := fun u hu => by
    unfold viewNodes at hu
    split at hu
    · obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 (Option.mem_toFinset.1 hu)
      have hb := List.mem_range.1 (List.mem_of_find?_eq_some ha)
      simpa using hb
    · simp at hu
  have hleaf : ∀ v, n ∈ ir.leafNodes (rs.map REdge.plan) v → n < rs.length := fun v hv => by
    unfold leafNodes at hv
    split at hv
    · exact hval v hv
    · exact hval v hv
    · exact hview v hv
    · simp at hv
  have hbatch : ∀ atom b, n ∈ ir.batchNodes (rs.map REdge.plan) atom d b → n < rs.length :=
    fun atom b hb => by
      obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.1 hb
      exact hleaf v hv
  refine Fin.addCases (fun c h => ?_) (fun c h => ?_) c h
  · rw [claimReads, Fin.append_left] at h
    refine FieldProof.MaskedReduction.ofListFamily_of (P := fun N => n ∈ N → n < rs.length)
      (fun b c h => ?_) _ c h
    generalize ir.branchEquiv d Pk b = j at c h
    rcases j with ((j | j) | (j | j)) | j
    · exact hbatch _ _ h
    · exact hbatch _ _ h
    · exact hbatch _ _ h
    · exact hbatch _ _ h
    · refine FieldProof.MaskedReduction.ofListFamily_of (P := fun N => n ∈ N → n < rs.length)
        (fun i _ h => ?_) _ c h
      obtain ⟨blk, -, hblk⟩ := Finset.mem_biUnion.1 h
      cases blk with
      | committed u _ _ => exact hval u hblk
      | pad u _ _ => exact hval u hblk
      | view u _ _ => exact hview u hblk
      | _ => simp [blockNodes] at hblk
  · rw [claimReads, Fin.append_right] at h
    generalize (Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm c = t at h
    rcases t with q | q
    · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 h
      exact hval w hw
    · obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.1 h
      unfold viewLeafNodes at hu
      split at hu
      · exact hview u hu
      · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.1 hu
        exact hval w hw

/-- The edges' relative degrees are the plan's. -/
theorem map_d_fieldEdges (Pads : Type) :
    (ir.fieldEdges d Pk rs Pads).map (fun e => e.d + 1) = rs.map fun r => r.plan.degree + 1 := by
  refine List.ext_getElem (by simp [fieldEdges]) fun i h1 h2 => ?_
  simp only [List.getElem_map, fieldEdges, List.getElem_mapIdx]
  rfl

/-- **The bound on every stage's touching claims after the first**, in decidable form: the claims
that do not read the first edge's child (at most every branch's claim, and the rows whose nodes
miss it) and `d + 1` per edge (`PEdge.stagesOk_cons_of`, `card_passing_le`). -/
def laterBound : ℕ :=
  ((List.finRange (ir.nBranch d Pk)).map fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b)).sum +
    (Finset.univ.filter fun q : ir.RowIdx d => 0 ∉ rowIdxNodes rs q).card +
    (rs.map fun r => r.plan.degree + 1).sum

/-- **The claims that do not read the first edge's child** are at most those of `laterBound`. -/
theorem card_passing_le :
    (Finset.univ.filter fun c : Fin (ir.claimCount (d := d) (Pk := Pk)) => 0 ∉ claimReads rs c).card +
      (rs.map fun r => r.plan.degree + 1).sum ≤ laterBound rs := by
  unfold laterBound
  refine Nat.add_le_add_right ?_ _
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [claimReads, Fin.append_left, Fin.append_right]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · refine (Finset.sum_le_sum fun i _ => ite_le_one le_rfl zero_le_one).trans ?_
    simp
  · rw [Finset.card_filter]
    exact Fintype.sum_equiv (Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm _ _ fun _ => rfl

end

end GordieHowe.RealizedProgram
