-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldDomain
public import GordieHowe.ProofSystem.Program.FieldPackingGeneric
public import GordieHowe.Headline

@[expose] public section

/-!
# GordieHowe: the checks of a domain at the generic member of the packing class

The checks of a domain (`GordieHowe.RealizedProgram.fieldOkB`) read the field's packing facts only through their
shape: which plan edges have an edge kit, the node degrees of the cells' names, which batches have a
skip domain, the degree `n` and the point count `q` (`fieldOkB_mono`). So a program that passes the
checks at one member of the class passes them at every member that realizes at least as much:

* **the tree's divisibility** (`TreeOk.dvd`): every edge `F_{p^m} <d` of a tree that passes the
  tree check has `m d ∣ n`;
* **monotonicity** (`fieldOkB_mono`): the checks pass at `Pk'` when they pass at `Pk`, the degree
  and point count agree, and `Pk'` realizes every plan edge, node degree (of a dividing degree) and
  skip domain that `Pk` does;
* **the generic member** (`fieldOkB_generic`): a program passing the checks at a member `Pk` of a
  field of `p^n` elements passes them at the generic member at `Pk`'s numbers
  (`FieldInterp.Packing.generic`), when `s0 ∣ n`, the tops of `Pk`'s bit edges are named by their
  degree (`BitNodesNamed`), and the plan's edges meet the generic member's masking conditions
  (`genericEdgesOkB`: subfield masks over a child containing `S0`, squaring-chain masks over `F_2`);
* **the ready data** (`FieldReady.generic`): the domain's ready data at the generic member, so the
  domain's circuit proof (`fieldProof`, `fieldSound`) holds at it.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {I : Interp} {d : ℕ}

/-- **Every edge of a tree spans a divisor of `n`**: `m d ∣ n` for the edge `F_{p^m} <d`, by the
chain of parents up to a root child, which spans `n`. -/
theorem TreeOk.dvd {es : List PackingEdge} {n : ℕ} (h : TreeOk es n) {b : ℕ}
    (hb : b < es.length) : es[b].childDegree * es[b].degree ∣ n := by
  suffices H : ∀ k b (hb : b < es.length), es.length - b ≤ k →
      es[b].childDegree * es[b].degree ∣ n from H _ b hb le_rfl
  intro k
  induction k with
  | zero =>
    intro b hb hk
    omega
  | succ k ih =>
    intro b hb hk
    cases hp : parentIdx es b with
    | none => rw [h.root b hb hp]
    | some j =>
      obtain ⟨hbj, hj, hjd⟩ := h.parent b hb j hp
      have hdj := ih j hj (by omega)
      rw [← hjd]
      exact Dvd.dvd.trans (Dvd.intro _ rfl) hdj

/-- **The child of every edge of a tree has a degree dividing `n`.** -/
theorem TreeOk.childDegree_dvd {es : List PackingEdge} {n : ℕ} (h : TreeOk es n) {b : ℕ}
    (hb : b < es.length) : es[b].childDegree ∣ n :=
  Dvd.dvd.trans (Dvd.intro _ rfl) (h.dvd hb)

/-- The edge of a node lies in the list. -/
theorem nodeIdx_lt {es : List PackingEdge} {s : String} {a : ℕ} (h : nodeIdx es s = some a) :
    a < es.length := by
  unfold nodeIdx at h
  exact List.findIdx?_eq_some_iff_getElem.1 h |>.1

/-- **The plan edges of the realized edges** are the plan edges the field realizes. -/
theorem realizedEdges_map_plan {F : FieldInterp} (Pk : F.Packing) (es : List PackingEdge) :
    (realizedEdges Pk es).map REdge.plan =
      es.filter fun e => (Pk.edge e.childDegree e.degree e.mode).isSome := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [realizedEdges, List.filterMap_cons, List.filter_cons] at ih ⊢
    cases h : Pk.edge e.childDegree e.degree e.mode with
    | none => simpa [h] using ih
    | some k => simpa [h] using ih

/-- **Every plan edge is realized** when the realized edges are as many as the plan's. -/
theorem realizedEdges_map_plan_of_length {F : FieldInterp} {Pk : F.Packing}
    {es : List PackingEdge} (h : (realizedEdges Pk es).length = es.length) :
    (realizedEdges Pk es).map REdge.plan = es := by
  rw [realizedEdges_map_plan]
  apply List.filter_eq_self.2
  rw [← List.length_filter_eq_length_iff, ← realizedEdges_map_plan, List.length_map]
  exact h

/-- The realized edges are as many as the plan's when every plan edge is realized. -/
theorem realizedEdges_length_of_all {F : FieldInterp} {Pk : F.Packing} {es : List PackingEdge}
    (h : ∀ e ∈ es, (Pk.edge e.childDegree e.degree e.mode).isSome) :
    (realizedEdges Pk es).length = es.length := by
  rw [← List.length_map (f := REdge.plan), realizedEdges_map_plan, List.filter_eq_self.2 h]

/-- **The placement check is monotone in the node degrees**: it passes at `Pk'` when it passes at
`Pk` on a tree, the degrees agree, and `Pk'` has every node degree of `Pk` that divides `n`. -/
theorem placeOkB_mono {Pk Pk' : (I (ir.domainField d)).Packing} {es : List PackingEdge}
    (ht : TreeOk es Pk.n) (h : ir.placeOkB d Pk es = true) (hn : Pk.n = Pk'.n)
    (hdeg : ∀ s m, m ∣ Pk.n → Pk.nodeDeg s = some m → Pk'.nodeDeg s = some m) :
    ir.placeOkB d Pk' es = true := by
  simp only [placeOkB, List.all_eq_true] at h ⊢
  intro k hk
  have hk' := h k hk
  cases hs : ir.cellName k with
  | none => rfl
  | some s =>
    rw [hs] at hk'
    cases ha : ir.cellNode es k with
    | none =>
      simp only [ha, beq_iff_eq] at hk' ⊢
      rw [← hn]
      exact hdeg s Pk.n dvd_rfl hk'
    | some a =>
      simp only [ha, beq_iff_eq] at hk' ⊢
      have hal : a < es.length := by
        rw [cellNode, hs] at ha
        exact nodeIdx_lt ha
      have hget : es.getD a noEdge = es[a] := by
        rw [List.getD_eq_getElem _ _ hal]
      rw [hget] at hk' ⊢
      exact hdeg s _ (ht.childDegree_dvd hal) hk'

/-- **The batch check is monotone in the skip domains.** -/
theorem batchesOkB_mono {Pk Pk' : (I (ir.domainField d)).Packing}
    (h : ir.batchesOkB d Pk = true)
    (hskip : ∀ w D, (Pk.skip w D).isSome → (Pk'.skip w D).isSome)
    (hnodes : Pk.nodes.isSome → Pk'.nodes.isSome) :
    ir.batchesOkB d Pk' = true := by
  simp only [batchesOkB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true] at h ⊢
  intro b hb
  rcases h b hb with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hskip _ _ h1, h2.imp_right (And.imp_right hnodes)⟩

/-- **The checks of a domain read the packing only through its shape**: they pass at `Pk'` when
they pass at `Pk`, the degree `n` and the point count `q` agree, and `Pk'` realizes every plan edge,
every node degree dividing `n` and every skip domain that `Pk` does. -/
theorem fieldOkB_mono {P : Export.Plan} {c : LigeroCert}
    {Pk Pk' : (I (ir.domainField d)).Packing} (h : ir.fieldOkB d P Pk c = true)
    (hn : Pk.n = Pk'.n) (hq : Pk.q = Pk'.q)
    (hedge : ∀ e ∈ ir.planPacking P d, (Pk.edge e.childDegree e.degree e.mode).isSome →
      (Pk'.edge e.childDegree e.degree e.mode).isSome)
    (hdeg : ∀ s m, m ∣ Pk.n → Pk.nodeDeg s = some m → Pk'.nodeDeg s = some m)
    (hskip : ∀ w D, (Pk.skip w D).isSome → (Pk'.skip w D).isSome)
    (hnodes : Pk.nodes.isSome → Pk'.nodes.isSome) :
    ir.fieldOkB d P Pk' c = true := by
  simp only [fieldOkB, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, ht⟩, hp⟩, hv⟩, hc⟩, hb⟩, hqd⟩, hval⟩, hlg⟩ := h
  have hmap := realizedEdges_map_plan_of_length hl
  have hall : ∀ e ∈ ir.planPacking P d, (Pk.edge e.childDegree e.degree e.mode).isSome := by
    have := hmap
    rw [realizedEdges_map_plan] at this
    exact List.filter_eq_self.1 this
  have hl' : (ir.fieldEdgesOf d P Pk').length = (ir.planPacking P d).length :=
    realizedEdges_length_of_all fun e he => hedge e he (hall e he)
  have hmap' := realizedEdges_map_plan_of_length hl'
  change (realizedEdges Pk (ir.planPacking P d)).map REdge.plan = _ at hmap
  change (realizedEdges Pk' (ir.planPacking P d)).map REdge.plan = _ at hmap'
  simp only [fieldEdgesOf] at ht hp hv ⊢
  rw [hmap] at ht hp hv
  rw [hmap', ← hn, ← hq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hl', ht⟩, placeOkB_mono (TreeOk.of_treeOkB ht) hp hn hdeg⟩, hv⟩, hc⟩,
    batchesOkB_mono hb hskip hnodes⟩, hqd⟩, hval⟩, hlg⟩

variable (ir) in
/-- **The plan's edges of domain `d` meet the generic member's masking conditions**, as a test:
an edge with subfield masks has a child containing `S0 = F_{p^s0}` (`s0 ∣ m`), an edge with
squaring-chain masks is a bit edge over `F_2` (`p = 2`, `m = 1`). -/
def genericEdgesOkB (P : Export.Plan) (d p s0 : ℕ) : Bool :=
  (ir.planPacking P d).all fun e =>
    match e.mode with
    | .subfieldMasks => decide (s0 ∣ e.childDegree)
    | .squaringChain => p == 2 && e.childDegree == 1

/-- **A program passing the checks at a member passes them at the generic member at its
numbers** (`FieldInterp.Packing.generic`), for a field of `p^n` elements with `s0 ∣ n`, when the
tops of the member's bit edges are named by their degree and the plan's edges meet the generic
member's masking conditions. -/
@[headline]
theorem fieldOkB_generic {P : Export.Plan} {c : LigeroCert}
    {Pk : (I (ir.domainField d)).Packing} (h : ir.fieldOkB d P Pk c = true)
    (hK : Fintype.card (I (ir.domainField d)).K = Pk.p ^ Pk.n) (hs0 : Pk.s0 ∣ Pk.n)
    (hcov : Pk.BitNodesNamed) (hE : ir.genericEdgesOkB P d Pk.p Pk.s0 = true) :
    ir.fieldOkB d P (Pk.generic hK hs0 hcov) c = true := by
  have hR := Pk.generic_realizes hK hs0 hcov
  have ht : TreeOk (ir.planPacking P d) Pk.n := by
    have h' := h
    simp only [fieldOkB, Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, ht⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
    have hmap := realizedEdges_map_plan_of_length hl
    change treeOkB ((realizedEdges Pk (ir.planPacking P d)).map REdge.plan) Pk.n = true at ht
    rw [hmap] at ht
    exact TreeOk.of_treeOkB ht
  refine fieldOkB_mono h hR.n_eq.symm hR.q_eq.symm ?_ ?_ ?_ fun hn => hn
  · intro e he hsome
    obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.1 he
    have hdvd := ht.dvd hb
    have hEe := List.all_eq_true.1 hE _ he
    cases hm : (ir.planPacking P d)[b].mode with
    | subfieldMasks =>
      simp only [hm, decide_eq_true_eq] at hEe hsome
      exact (hR.subfield _ _).2 ⟨hdvd, hEe⟩
    | squaringChain =>
      simp only [hm, Bool.and_eq_true, beq_iff_eq] at hEe hsome
      obtain ⟨hp2, hm1⟩ := hEe
      rw [hm1] at hsome ⊢
      rw [hm1, one_mul] at hdvd
      exact (hR.squaring _ _).2 ⟨hp2, rfl, hdvd, hsome⟩
  · intro s m hm hs
    exact (hR.nodeDeg s m).2 ⟨hm, Pk.node_eq s m hs⟩
  · intro w D hs
    exact (hR.skip w D).2 (Pk.skip_le hs)

/-- **The ready data of domain `d` at the generic member** of the class at the numbers of `R`'s
member (`fieldOkB_generic`): the domain's circuit proof (`fieldProof`, `fieldSound`) holds at the
generic member. -/
noncomputable def FieldReady.generic {P : Export.Plan} (R : ir.FieldReady I d P)
    (hK : Fintype.card (I (ir.domainField d)).K = R.Pk.p ^ R.Pk.n) (hs0 : R.Pk.s0 ∣ R.Pk.n)
    (hcov : R.Pk.BitNodesNamed) (hE : ir.genericEdgesOkB P d R.Pk.p R.Pk.s0 = true) :
    ir.FieldReady I d P where
  Pk := R.Pk.generic hK hs0 hcov
  cert := R.cert
  ok := fieldOkB_generic R.ok hK hs0 hcov hE
  wf := R.wf

end

end GordieHowe.RealizedProgram
