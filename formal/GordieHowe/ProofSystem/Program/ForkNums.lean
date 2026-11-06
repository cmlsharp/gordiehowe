-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ProgramFigures
public import GordieHowe.Language.RealizedProgram.Placement
public import GordieHowe.Language.RealizedProgram.CellsReader
public import GordieHowe.ProofSystem.Program.FieldReadyGeneric
public import GordieHowe.ProofSystem.Program.FieldReader
public import GordieHoweNative.ProofSystem.Program.ForkNums
public import GordieHowe.Language.Realizations.Circuit.Width

/-!
# GordieHowe: the numbers of a domain's forked proof are the ready data's

The numbers `ForkReader.domainNums` computes from the program, the plan, the field's packing
descriptor and the tableau's numbers are the ready data's (`GordieHowe/ProofSystem/Program/
ForkNums.lean` of `GordieHoweNative`), when the batches pass the batch check (`batchesB`), the
descriptor is the field's at its queries (`Pk.desc D = D`) and answers the plan's edges' mask
cells, and the tableau's numbers are the certificate's: the size bounds on the numbers
(`DomainNums.fitsB`, `restB`) give `FitsOk` and `ForkRestNumbers`.
-/

public section

namespace GordieHowe.RealizedProgram

open Export

/-! ## Lists filtered by index -/

/-- **A `filterMap` over `finRange` keeping indices**, mapped to the indices, is the indices'
filter. -/
theorem map_filterMap_finRange {n : ℕ} {α : Type} (f : Fin n → Option α) (g : α → ℕ)
    (q : ℕ → Bool) (h : ∀ b : Fin n, (f b).map g = if q b then some (b : ℕ) else none) :
    ((List.finRange n).filterMap f).map g = (List.range n).filter q := by
  rw [List.map_filterMap, ← List.map_coe_finRange_eq_range, List.filter_map]
  rw [funext h]
  induction (List.finRange n) with
  | nil => rfl
  | cons b l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases hq : q b <;> simp [hq, ih]

/-! ## The product cells of a relation are its shape's -/

open Sumcheck.FieldSkip in
/-- **The product cells of a monomial shape are a list shape's** when the two have the same factor
multisets (on `ℕ`): `padMonomials` maps injectively onto `Shape.cellSet`. -/
theorem MonoShape.card_padMonomials_eq_cells {k : ℕ} (S : MonoShape k) (sh : Shape)
    (h1 : ∀ i, ∃ c ∈ sh.monos, (S.factors i).map Fin.val = (c.2 : Multiset ℕ))
    (h2 : ∀ c ∈ sh.monos, ∃ i, (S.factors i).map Fin.val = (c.2 : Multiset ℕ)) :
    S.padMonomials.card = sh.cells := by
  have hinj : Function.Injective (Multiset.map (Fin.val : Fin k → ℕ)) :=
    Multiset.map_injective Fin.val_injective
  rw [Shape.cells, ← Finset.card_map ⟨_, hinj⟩]
  congr 1
  ext M'
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Shape.cellSet, Finset.mem_biUnion,
    List.mem_toFinset, Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset]
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨hc, i, hi⟩ := (MonoShape.mem_padMonomials S).1 hM
    obtain ⟨c, hcm, hce⟩ := h1 i
    exact ⟨c, hcm, hce ▸ Multiset.map_le_map hi, by rwa [Multiset.card_map]⟩
  · rintro ⟨c, hcm, hle, hc⟩
    obtain ⟨i, hi⟩ := h2 c hcm
    have hmem : M' ∈ Multiset.powersetCard (Multiset.card M') ((S.factors i).map Fin.val) :=
      Multiset.mem_powersetCard.2 ⟨hi ▸ hle, rfl⟩
    rw [Multiset.powersetCard_map, Multiset.mem_map] at hmem
    obtain ⟨M, hM, rfl⟩ := hmem
    refine ⟨M, (MonoShape.mem_padMonomials S).2 ⟨by rwa [Multiset.card_map] at hc, i,
      (Multiset.mem_powersetCard.1 hM).1⟩, rfl⟩

open Sumcheck.FieldSkip in
/-- **A shape's relation has the shape's factors.** -/
theorem Shape.rel_factors {I : Interp} {f D : ℕ} (sh : Shape) (h : sh.Ok D)
    (i : Fin (sh.rel I f D h).nm) :
    ((sh.rel I f D h).factors i).map Fin.val = (sh.monos[i.1].2 : Multiset ℕ) := by
  simp only [MonoShape.factors, Multiset.map_map]
  rw [Fin.univ_val_map]
  congr 1
  exact List.ofFn_getElem

open Sumcheck.FieldSkip in
/-- **A shape's relation has the shape's product cells.** -/
theorem Shape.card_padMonomials_rel {I : Interp} {f D : ℕ} (sh : Shape) (h : sh.Ok D) :
    (sh.rel I f D h).padMonomials.card = sh.cells := by
  refine MonoShape.card_padMonomials_eq_cells _ sh (fun i => ⟨_, List.getElem_mem _,
    Shape.rel_factors sh h i⟩) fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  exact ⟨⟨i, hi⟩, Shape.rel_factors sh h ⟨i, hi⟩⟩

/-! ## The kits' mask cells -/

section Masks

/-- The key of a mask query: child degree, relative degree, masking mode. -/
abbrev maskKey (m k : ℕ) (mode : PackingMode) (x : ℕ × ℕ × PackingMode × ℕ × ℕ) : Bool :=
  x.1 == m && x.2.1 == k && x.2.2.1 == mode

/-- **The descriptor of `Pk` answers a queried edge's mask cells with its kit's.** -/
theorem desc_maskNums {F : FieldInterp} (Pk : F.Packing) (D : PackingDesc) {m k : ℕ}
    {mode : PackingMode} (h : (D.masks.find? (maskKey m k mode)).isSome) :
    (Pk.desc D).maskNums m k mode =
      ((Pk.edge m k mode).map fun kit => (kit.masks.nPre, kit.masks.nOwn)).getD (0, 0) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  have hp := List.find?_some hx
  simp only [maskKey, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  unfold PackingDesc.maskNums
  rw [FieldInterp.Packing.desc]
  simp only [List.find?_map]
  have hfind : D.masks.find? ((fun x => x.1 == m && x.2.1 == k && x.2.2.1 == mode) ∘
      fun x => (x.1, x.2.1, x.2.2.1, ((Pk.edge x.1 x.2.1 x.2.2.1).map fun kit =>
        (kit.masks.nPre, kit.masks.nOwn)).getD (0, 0))) = some x := by
    rw [← hx]
    rfl
  rw [hfind]
  subst h1 h2 h3
  rfl

/-- **A realized edge's kit is the field's** for its plan edge. -/
theorem edge_of_mem_realizedEdges {F : FieldInterp} {Pk : F.Packing} {es : List PackingEdge}
    {r : REdge F Pk} (h : r ∈ realizedEdges Pk es) :
    Pk.edge r.plan.childDegree r.plan.degree r.plan.mode = some r.kit := by
  obtain ⟨e, -, he⟩ := List.mem_filterMap.1 h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 he
  exact hk

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}

/-- **The ready data's edges are the plan's.** -/
theorem FieldReady.rs_plan (R : ir.FieldReady I d P) :
    R.rs.map REdge.plan = ir.planPacking P d := by
  have h := R.ok
  simp only [fieldOkB, Bool.and_eq_true, beq_iff_eq] at h
  exact realizedEdges_map_plan_of_length h.1.1.1.1.1.1.1.1

/-- **The descriptor answers every plan edge's mask cells.** -/
@[expose] def MasksCover (D : PackingDesc) (es : List PackingEdge) : Prop :=
  ∀ e ∈ es, (D.masks.find? (maskKey e.childDegree e.degree e.mode)).isSome

/-- **The mask-query coverage test is sound and complete.** -/
theorem masksCoverB_iff (D : PackingDesc) (es : List PackingEdge) :
    D.masksCoverB es = true ↔ MasksCover D es := by
  simp only [PackingDesc.masksCoverB, List.all_eq_true, MasksCover, maskKey]

/-- **A realized edge's mask cells are the descriptor's**, at a covered query. -/
theorem FieldReady.masks_eq (R : ir.FieldReady I d P) {D : PackingDesc} (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) {r : REdge _ R.Pk} (hr : r ∈ R.rs) :
    D.maskNums r.plan.childDegree r.plan.degree r.plan.mode =
      (r.kit.masks.nPre, r.kit.masks.nOwn) := by
  have hmem : r.plan ∈ ir.planPacking P d := R.rs_plan ▸ List.mem_map_of_mem hr
  have h := desc_maskNums R.Pk D (hc _ hmem)
  rw [hD, edge_of_mem_realizedEdges hr] at h
  exact h

/-- **The masks' own cells are the descriptor's.** -/
theorem FieldReady.ownSum_eq (R : ir.FieldReady I d P) {D : PackingDesc} (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) :
    (R.rs.map fun r => r.kit.masks.nOwn).sum = ForkReader.ownN ir d P D := by
  rw [ForkReader.ownN, ForkReader.es, ← R.rs_plan, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  simp only [Function.comp_apply, R.masks_eq hD hc hr]

/-- **The masks' prefix cells are the descriptor's.** -/
theorem FieldReady.np_eq (R : ir.FieldReady I d P) {D : PackingDesc} (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) :
    npOf R.Pk R.rs = ForkReader.npN ir d P D := by
  rw [npOf, preOff, List.take_length, ForkReader.npN, ForkReader.es, ← R.rs_plan, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  simp only [Function.comp_apply, R.masks_eq hD hc hr]

end Masks

/-! ## Sums over finite index types as list sums -/

theorem sum_fin_eq_list (g : ℕ → ℕ) (n : ℕ) : ∑ i : Fin n, g i = ((List.range n).map g).sum := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem sum_subtype_eq_list (n : ℕ) (q : ℕ → Bool) (g : ℕ → ℕ) :
    ∑ p : {p : Fin n // q p = true}, g p.1 =
      ((List.range n).map fun p => if q p then g p else 0).sum := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n => q p = true) (by simp)
    (fun p : Fin n => g p), Finset.sum_filter]
  exact sum_fin_eq_list (fun p => if q p then g p else 0) n

/-- **The elements of a sigma type with a property of the index**, counted by index. -/
theorem card_filter_sigma {ι : Type} [Fintype ι] (f : ι → ℕ) (P : ι → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : Σ p, Fin (f p) => P x.1).card = ∑ p, if P p then f p else 0 := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  split <;> simp [*]

/-- **Counting a sigma over a filtered index type** with a property of the index, as a list sum. -/
theorem count_sigma_subtype (n : ℕ) (q : ℕ → Bool) (f : ℕ → ℕ) (P : ℕ → Bool) :
    (∑ x : (Σ p : {p : Fin n // q p = true}, Fin (f p.1)), if P x.1.1 = true then 1 else 0) =
      ((List.range n).map fun p => if q p = true then (if P p = true then f p else 0)
        else 0).sum := by
  rw [Fintype.sum_sigma, ← sum_subtype_eq_list n q fun p => if P p = true then f p else 0]
  refine Finset.sum_congr rfl fun x _ => ?_
  split <;> simp

/-! ## The cells and the tree -/

section Tree

variable (ir : RealizedProgram) (d : ℕ)

local notation "CR" => CellsReader.ofProgram ir

theorem cellNode_eq (es : List PackingEdge) (k : CellKey) :
    @ForkReader.cellNode (CR) es k = ir.cellNode es k := by
  cases k <;> rfl

theorem cellNode_lt {es : List PackingEdge} {k : CellKey} {a : ℕ} (h : ir.cellNode es k = some a) :
    a < es.length := by
  obtain ⟨s, -, hs⟩ := Option.bind_eq_some_iff.1 h
  exact nodeIdx_lt hs

/-- The bucket of a cell: its node, `es.length` at no node. -/
abbrev bucket (es : List PackingEdge) (k : CellKey) : ℕ := (ir.cellNode es k).getD es.length

theorem length_filter_flatMap {α β : Type} (l : List α) (g : α → List β) (p : β → Bool) :
    ((l.flatMap g).filter p).length = (l.map fun x => ((g x).filter p).length).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem length_filter_map_const {β : Type} (n : ℕ) (f : ℕ → β) (p : β → Bool)
    (h : ∀ i j, p (f i) = p (f j)) :
    (((List.range n).map f).filter p).length = if p (f 0) then n else 0 := by
  split
  · rename_i hp
    rw [List.filter_eq_self.2 fun x hx => ?_, List.length_map, List.length_range]
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    rw [h i 0]; exact hp
  · rename_i hp
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    rw [h i 0]; exact hp

/-- **The cells in a bucket** are the reader's count. -/
theorem filter_bucket_length (es : List PackingEdge) (a : ℕ) :
    ((ir.cellKeys d).filter fun k => ir.bucket es k = a).length =
      @ForkReader.cellCount ir (CR) d es a := by
  rw [cellKeys, List.filter_append, List.length_append, length_filter_flatMap,
    length_filter_flatMap, ForkReader.cellCount, ForkReader.valueCells, ForkReader.fillerCount,
    List.map_map]
  congr 1
  · have hn : (CellsReader.ofProgram ir).nValues = ir.values.length := rfl
    rw [hn]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    have hc : @CellsReader.isCellValue (CR) d v = ir.isCellValue d v := rfl
    have hl : @CellsReader.isLateOf ir (CR) d v = ir.isLateOf d v := rfl
    have hv : (CellsReader.ofProgram ir).value v = ir.value v := rfl
    have hb : ∀ k, @ForkReader.bucketOf (CR) es k = ir.bucket es k := fun k => by
      simp [ForkReader.bucketOf, cellNode_eq]
    simp only [Function.comp_apply, hc, hl, hb, hv]
    by_cases hcv : ir.isCellValue d v = true
    · simp only [hcv, ite_true]
      rw [length_filter_map_const _ _ _ fun i j => rfl]
      by_cases h : ir.bucket es (.val v 0) = a <;> simp [h]
    · by_cases hl' : ir.isLateOf d v = true
      · simp only [hcv, hl', ite_true, Bool.false_eq_true, ite_false]
        rw [length_filter_map_const _ _ _ fun i j => rfl]
        by_cases h : ir.bucket es (.pad v 0) = a <;> simp [h]
      · simp [hcv, hl']
  · have hf : ∀ (c : ℕ) (x : InputBlock) (k : CellKey), k ∈ x.fillerKeys c →
        ir.bucket es k = es.length := by
      intro c x k hk
      cases x <;> simp only [InputBlock.fillerKeys, List.not_mem_nil, List.mem_map] at hk
      obtain ⟨j, -, rfl⟩ := hk
      rfl
    by_cases ha : a = es.length
    · rw [ite_eq_left_iff.2 (fun h => absurd ha h)]
      congr 1
      refine List.map_congr_left fun c _ => ?_
      split
      · rw [List.filter_eq_self.2 fun k hk => ?_, List.length_flatMap]
        · congr 1
        · obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 hk
          simpa [ha] using hf c x k hx
      · rfl
    · rw [ite_eq_right_iff.2 (fun h => absurd h ha)]
      refine List.sum_eq_zero fun n hn => ?_
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hn
      split
      · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro k hk
        obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 hk
        simp [hf c x k hx, Ne.symm ha]
      · rfl

theorem nodeCounts_length (es : List PackingEdge) :
    (@ForkReader.nodeCounts ir (CR) d es).length = es.length + 1 := by
  simp [ForkReader.nodeCounts]

theorem nodeCounts_getD (es : List PackingEdge) {a : ℕ} (ha : a < es.length + 1) :
    (@ForkReader.nodeCounts ir (CR) d es).getD a 0 = @ForkReader.cellCount ir (CR) d es a := by
  simp [ForkReader.nodeCounts, List.getD_eq_getElem?_getD, ha]

theorem own_eq (es : List PackingEdge) (a : ℕ) :
    ir.own d es a = ForkReader.ownC (@ForkReader.nodeCounts ir (CR) d es) a := by
  rw [ForkReader.ownC, nodeCounts_length, own, ownKeys]
  split
  · rw [nodeCounts_getD _ _ _ (by omega), ← filter_bucket_length]
    congr 1
    refine List.filter_congr fun k _ => ?_
    cases h : ir.cellNode es k with
    | none => simp [bucket, h]; omega
    | some b =>
      simp only [bucket, h, Option.getD_some]
      by_cases hb : b = a <;> simp [hb]
  · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro k _ hk
    simp only [beq_iff_eq] at hk
    have := ir.cellNode_lt hk
    omega

theorem root_eq (es : List PackingEdge) :
    ((ir.cellKeys d).filter fun k => (ir.cellNode es k).isNone).length =
      (@ForkReader.nodeCounts ir (CR) d es).getD es.length 0 := by
  rw [nodeCounts_getD _ _ _ (by omega), ← filter_bucket_length]
  congr 1
  refine List.filter_congr fun k _ => ?_
  cases h : ir.cellNode es k with
  | none => simp [bucket, h]
  | some b => have := ir.cellNode_lt h; simp [bucket, h]; omega

theorem ngFuel_eq (es : List PackingEdge) (f a : ℕ) :
    ir.ngFuel d es f a = ForkReader.ngFuel es (@ForkReader.nodeCounts ir (CR) d es) f a := by
  induction f generalizing a with
  | zero => rfl
  | succ f ih =>
    have hv : ∀ j, viewChild es j = ForkReader.viewChild es j := fun _ => rfl
    have ho : ∀ j b, otherChild es j b = ForkReader.otherChild es j b := fun _ _ => rfl
    have hg : ir.given d es a = ForkReader.given es (@ForkReader.nodeCounts ir (CR) d es) a := by
      cases hp : parentIdx es a <;> simp [given, ForkReader.given, hp, hv, own_eq]
    have ih' : ir.ngFuel d es f = ForkReader.ngFuel es (@ForkReader.nodeCounts ir (CR) d es) f :=
      funext ih
    have ho' : otherChild es a = ForkReader.otherChild es a := rfl
    simp only [ngFuel, ForkReader.ngFuel, hg, ih', own_eq, hv, ho']
    rfl

theorem nwOf_eq (es : List PackingEdge) :
    ir.nwOf d es = ForkReader.nwOf es (@ForkReader.nodeCounts ir (CR) d es) := by
  have h : ir.ngOf d es = fun a =>
      ForkReader.ngFuel es (@ForkReader.nodeCounts ir (CR) d es) (a + 1) a :=
    funext fun a => ngFuel_eq ir d es (a + 1) a
  simp only [nwOf, rootOff, ForkReader.nwOf, h]

/-! ### The rows -/

theorem zero_mem_valueNodes (es : List PackingEdge) (w : ℕ) :
    0 ∈ ir.valueNodes es w ↔ @ForkReader.atZero (CR) es w = true := by
  simp only [valueNodes, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    ForkReader.atZero, cellNode_eq, Bool.or_eq_true, beq_iff_eq]

theorem mem_asgReadsOf (hwf : ir.WellFormed) (u x : ℕ) :
    x ∈ @ForkReader.asgReadsOf ir (CR) u ↔ x ∈ ir.asgReads ir.fuel u := by
  unfold ForkReader.asgReadsOf
  split
  · exact (mem_asgReadsT hwf (by assumption) x).symm
  · exact Iff.rfl

theorem zero_mem_rowNodes (hwf : ir.WellFormed) {I : Interp} {Pk : (I (ir.domainField d)).Packing}
    (rs : List (REdge _ Pk)) (q : ir.Row d) :
    0 ∈ rowNodes rs q ↔ @ForkReader.rowAtZero ir (CR) d (rs.map REdge.plan) q.1.1 = true := by
  simp only [rowNodes, rowReadsVals, exprsReads, Finset.mem_biUnion, List.mem_toFinset,
    List.mem_flatMap, ForkReader.rowAtZero, List.any_eq_true, zero_mem_valueNodes,
    ← mem_asgReadsOf ir hwf]
  aesop

theorem zero_mem_viewRowNodes (hwf : ir.WellFormed) {I : Interp}
    {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge _ Pk)) (q : ir.ViewRow d) :
    0 ∈ viewRowNodes rs q ↔
      @ForkReader.viewRowAtZero ir (CR) d (rs.map REdge.plan) q.1.1 = true := by
  simp only [viewRowNodes, Finset.mem_biUnion, List.mem_toFinset, ForkReader.viewRowAtZero,
    List.any_eq_true]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  unfold viewLeafNodes viewNodes
  change _ ↔ (match (ir.value u).kind with
    | .bits w _ => ((@ForkReader.cellNode (CR) (rs.map REdge.plan) (.val w 0)).bind
        (ForkReader.viewChild (rs.map REdge.plan)) == some 0)
    | _ => (@ForkReader.asgReadsOf ir (CR) u).any (@ForkReader.atZero (CR) (rs.map REdge.plan)))
      = true
  split
  · rename_i w sel hk
    simp only [hk, Option.mem_toFinset, Option.mem_def, cellNode_eq, beq_iff_eq]
    rfl
  · simp only [Finset.mem_biUnion, List.mem_toFinset, List.any_eq_true, zero_mem_valueNodes,
      mem_asgReadsOf ir hwf]

variable {ir d} in
theorem isViewRow_isRow {p : ℕ} (h : ir.isViewRow d p = true) : ir.isRow d p = false := by
  unfold isViewRow at h
  split at h
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  · cases h

theorem isRow_eq (p : ℕ) : @ForkReader.isRow ir (CR) d p = ir.isRow d p := rfl

theorem isViewRow_eq (p : ℕ) : @ForkReader.isViewRow ir (CR) d p = ir.isViewRow d p := rfl

/-- **The rows' coordinates** (`RowIdx`) are the reader's. -/
theorem card_rowIdx : Fintype.card (ir.RowIdx d) =
    ((List.range ir.predicates.length).map (@ForkReader.rowLen ir (CR) d)).sum := by
  rw [Fintype.card_sum]
  change Fintype.card (Σ p : ir.RowPred d, Fin _) + Fintype.card (Σ p : ir.ViewRowPred d, Fin _) = _
  simp only [Fintype.card_sigma, Fintype.card_fin]
  have h1 : (∑ x : ir.RowPred d, ir.exprLen (ir.rowLhs d x.1)) = ((List.range
      ir.predicates.length).map fun p => if ir.isRow d p then ir.exprLen (ir.rowLhs d p) else 0).sum :=
    sum_subtype_eq_list _ (ir.isRow d) (fun p => ir.exprLen (ir.rowLhs d p))
  have h2 : (∑ x : ir.ViewRowPred d, ir.exprLen (ir.rowLhs d x.1)) = ((List.range
      ir.predicates.length).map fun p =>
        if ir.isViewRow d p then ir.exprLen (ir.rowLhs d p) else 0).sum :=
    sum_subtype_eq_list _ (ir.isViewRow d) (fun p => ir.exprLen (ir.rowLhs d p))
  rw [h1, h2, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  have hrl : @ForkReader.rowLhs (CR) d p = ir.rowLhs d p := rfl
  simp only [ForkReader.rowLen, isRow_eq, isViewRow_eq, hrl]
  cases hr : ir.isRow d p <;> cases hv : ir.isViewRow d p <;> simp
  all_goals first | rfl | exact absurd (isViewRow_isRow hv) (by simp [hr])

/-- **The rows' coordinates reading no node `0`** are the reader's. -/
theorem card_rowIdx_off (hwf : ir.WellFormed) {I : Interp} {Pk : (I (ir.domainField d)).Packing}
    (rs : List (REdge _ Pk)) :
    (Finset.univ.filter fun q : ir.RowIdx d => 0 ∉ rowIdxNodes rs q).card =
      ((List.range ir.predicates.length).map
        (@ForkReader.rowLenOff ir (CR) d (rs.map REdge.plan))).sum := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp only [rowIdxNodes, zero_mem_rowNodes ir d hwf, zero_mem_viewRowNodes ir d hwf]
  have h1 : (∑ x : ir.Row d, if ¬@ForkReader.rowAtZero ir (CR) d (rs.map REdge.plan) x.1.1 = true
      then 1 else 0) = ((List.range ir.predicates.length).map fun p =>
        if ir.isRow d p = true then
          (if (!@ForkReader.rowAtZero ir (CR) d (rs.map REdge.plan) p) = true
            then ir.exprLen (ir.rowLhs d p) else 0) else 0).sum := by
    rw [← count_sigma_subtype]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  have h2 : (∑ x : ir.ViewRow d, if ¬@ForkReader.viewRowAtZero ir (CR) d (rs.map REdge.plan)
      x.1.1 = true then 1 else 0) = ((List.range ir.predicates.length).map fun p =>
        if ir.isViewRow d p = true then
          (if (!@ForkReader.viewRowAtZero ir (CR) d (rs.map REdge.plan) p) = true
            then ir.exprLen (ir.rowLhs d p) else 0) else 0).sum := by
    rw [← count_sigma_subtype]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  rw [h1, h2, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  have hrl : @ForkReader.rowLhs (CR) d p = ir.rowLhs d p := rfl
  simp only [ForkReader.rowLenOff, isRow_eq, isViewRow_eq, hrl]
  cases hr : ir.isRow d p <;> cases hv : ir.isViewRow d p <;>
    cases ha : @ForkReader.rowAtZero ir (CR) d (rs.map REdge.plan) p <;>
    cases hb : @ForkReader.viewRowAtZero ir (CR) d (rs.map REdge.plan) p <;> simp
  all_goals first | rfl | exact absurd (isViewRow_isRow hv) (by simp [hr])

/-- **The quadratic triples' coordinates** (`QuadIdx`) are the reader's. -/
theorem card_quadIdx : Fintype.card (ir.QuadIdx d) = @ForkReader.quadCount (CR) d := by
  change Fintype.card (Σ q : ir.QuadPred d, Fin _) = _
  simp only [Fintype.card_sigma, Fintype.card_fin]
  exact sum_subtype_eq_list _ (ir.isQuad d) (fun p => ir.exprLen (ir.quadLhs p))

/-! ### The circuits -/



end Tree

theorem sortN_eq (l : List ℕ) : sortN l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [sortN]
  | cons a l ih =>
    rw [sortN, ih, List.insertionSort_cons]
    generalize l.insertionSort (· ≤ ·) = m
    induction m with
    | nil => simp [insN]
    | cons b m ihm =>
      simp only [insN, List.orderedInsert_cons]
      split <;> simp_all

/-- **The product cells by insertion sort are `cellsL`'s.** -/
theorem Shape.cellsK_eq (sh : Shape) : sh.cellsK = sh.cellsL := by
  simp only [Shape.cellsK, Shape.cellsL, sortN_eq, List.mergeSort_eq_insertionSort]

/-- **The kernel's structural product-cell counter gives the same batch check.** -/
theorem CellsReader.batchesK_eq (ir : RealizedProgram) [r : CellsReader] :
    @CellsReader.batchesWith ir r Shape.cellsK = @CellsReader.batchesE ir r := by
  rw [show Shape.cellsK = Shape.cellsL from funext Shape.cellsK_eq]
  rfl


section Batches

variable {ir : RealizedProgram} {I : Interp} {d : ℕ}

/-- **The covered batches on columns are the batches of `d` on columns, unmerged**, when every
batch passes the batch check at its domain and the field has their skip domains. -/
theorem cbatches_idx {Pk : (I (ir.domainField d)).Packing} (hbat : ir.batchesB = true)
    (hB : ir.batchesOkB d Pk = true) :
    (ir.cbatches d Pk).map (fun cb => (cb.idx : ℕ)) = ForkReader.cbs ir d := by
  apply map_filterMap_finRange
  intro b
  have hB' := BatchesOk.of_batchesOkB hB b
  by_cases hd : (ir.batch b).domain = d
  · have hok : ir.batchOkB d b = true := hd ▸ batchOk_of_batchesB hbat b.2
    obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB' hok).1
    by_cases hc : (ir.batch b).operands = .columns ∧ ir.merged b = false
    · simp [hok, hc, hdom, hd]
    · simp only [hok, true_and, hc, ↓reduceDIte, Option.map_none, hd, beq_self_eq_true]
      split <;> simp_all
  · have hok : ir.batchOkB d b = false := by
      cases h : ir.batchOkB d b
      · rfl
      · exact absurd (ir.batchOkB_domain h) hd
    simp [hok, hd]

/-- **The covered batches on bits are the batches of `d` on bits, unmerged.** -/
theorem sumBatches_idx {Pk : (I (ir.domainField d)).Packing} (hbat : ir.batchesB = true)
    (hB : ir.batchesOkB d Pk = true) :
    (ir.sumBatches d Pk).map (fun sb => (sb.cb.idx : ℕ)) = ForkReader.sbs ir d := by
  apply map_filterMap_finRange
  intro b
  have hB' := BatchesOk.of_batchesOkB hB b
  by_cases hd : (ir.batch b).domain = d
  · have hok : ir.batchOkB d b = true := hd ▸ batchOk_of_batchesB hbat b.2
    obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB' hok).1
    by_cases hc : (ir.batch b).operands = .bits ∧ ir.merged b = false
    · obtain ⟨nodes, hn⟩ := Option.isSome_iff_exists.1 ((hB' hok).2 hc.1).2
      simp [hok, hc, hdom, hd, hn]
    · simp only [hok, true_and, hc, ↓reduceDIte, Option.map_none, hd, beq_self_eq_true]
      split <;> simp_all
  · have hok : ir.batchOkB d b = false := by
      cases h : ir.batchOkB d b
      · rfl
      · exact absurd (ir.batchOkB_domain h) hd
    simp [hok, hd]

/-- **The covered merged batches on columns are the batches of `d` on columns, merged.** -/
theorem mbatches_idx {Pk : (I (ir.domainField d)).Packing} (hbat : ir.batchesB = true)
    (hB : ir.batchesOkB d Pk = true) :
    (ir.mbatches d Pk).map (fun cb => (cb.idx : ℕ)) = ForkReader.mbs ir d := by
  apply map_filterMap_finRange
  intro b
  have hB' := BatchesOk.of_batchesOkB hB b
  by_cases hd : (ir.batch b).domain = d
  · have hok : ir.batchOkB d b = true := hd ▸ batchOk_of_batchesB hbat b.2
    obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB' hok).1
    by_cases hc : ir.merged b = true ∧ (ir.batch b).operands = .columns
    · simp [hok, hc, hdom, hd]
    · simp only [hok, true_and, hc, ↓reduceDIte, Option.map_none, hd, beq_self_eq_true]
      split <;> simp_all
  · have hok : ir.batchOkB d b = false := by
      cases h : ir.batchOkB d b
      · rfl
      · exact absurd (ir.batchOkB_domain h) hd
    simp [hok, hd]

/-- **The covered merged batches on bits are the batches of `d` on bits, merged.** -/
theorem sumMBatches_idx {Pk : (I (ir.domainField d)).Packing} (hbat : ir.batchesB = true)
    (hB : ir.batchesOkB d Pk = true) :
    (ir.sumMBatches d Pk).map (fun sb => (sb.mb.idx : ℕ)) = ForkReader.smbs ir d := by
  apply map_filterMap_finRange
  intro b
  have hB' := BatchesOk.of_batchesOkB hB b
  by_cases hd : (ir.batch b).domain = d
  · have hok : ir.batchOkB d b = true := hd ▸ batchOk_of_batchesB hbat b.2
    obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB' hok).1
    by_cases hc : ir.merged b = true ∧ (ir.batch b).operands = .bits
    · obtain ⟨nodes, hn⟩ := Option.isSome_iff_exists.1 ((hB' hok).2 hc.2).2
      simp [hok, hc, hdom, hd, hn]
    · simp only [hok, true_and, hc, ↓reduceDIte, Option.map_none, hd, beq_self_eq_true]
      split <;> simp_all
  · have hok : ir.batchOkB d b = false := by
      cases h : ir.batchOkB d b
      · rfl
      · exact absurd (ir.batchOkB_domain h) hd
    simp [hok, hd]

open Sumcheck.FieldSkip in
/-- **The merged shape's factors are its parts'.** -/
theorem mergeShape_factors {K : Type} [Field K] {k D np : ℕ} (Rs : Fin np → MonoRelation K k D)
    (m : Fin (MonoRelation.mergeShape Rs).nm) :
    (MonoRelation.mergeShape Rs).factors m =
      (Rs (finSigmaFinEquiv.symm m).1).factors (finSigmaFinEquiv.symm m).2 := rfl

open Sumcheck.FieldSkip in
/-- **The merged shape's factors at a part's monomial are the part's.** -/
theorem mergeShape_factors_mk {K : Type} [Field K] {k D np : ℕ} (Rs : Fin np → MonoRelation K k D)
    (x : Σ q, Fin (Rs q).nm) :
    (MonoRelation.mergeShape Rs).factors (finSigmaFinEquiv x : Fin (∑ q, (Rs q).nm)) =
      (Rs x.1).factors x.2 := by
  have key : ∀ y, y = finSigmaFinEquiv.symm (finSigmaFinEquiv x) →
      (Rs y.1).factors y.2 = (Rs x.1).factors x.2 := by
    intro y hy
    rw [Equiv.symm_apply_apply] at hy
    subst hy
    rfl
  exact key _ rfl

open Sumcheck.FieldSkip in
/-- **A covered merged batch's relations have its shape's product cells**: the merged shape's
monomials are the parts' on their slices, the batch's shape's. -/
theorem MBatch.card_padMonomials (cb : ir.MBatch I d) :
    (MonoRelation.mergeShape cb.rels).padMonomials.card =
      (ir.relShape (atomAt ir d cb.om) d cb.idx).cells := by
  have hm := cb.merged
  have hmonos : (ir.relShape (atomAt ir d cb.om) d cb.idx).monos =
      (List.range (ir.batch cb.idx).parts.length).flatMap fun j =>
        (ir.partShape (atomAt ir d cb.om) d cb.idx j).shift
          (ir.partOffset (atomAt ir d cb.om) d cb.idx j) := by
    simp [relShape, Shape.batched, partOffset, hm]
  refine MonoShape.card_padMonomials_eq_cells _ _ (fun m => ?_) fun c hc => ?_
  · rw [mergeShape_factors]
    refine ⟨_, ?_, Shape.rel_factors _ _ (finSigmaFinEquiv.symm m).2⟩
    rw [hmonos, List.mem_flatMap]
    exact ⟨_, List.mem_range.2 (finSigmaFinEquiv.symm m).1.2, List.getElem_mem _⟩
  · rw [hmonos, List.mem_flatMap] at hc
    obtain ⟨q, hq, hc⟩ := hc
    have hq' := List.mem_range.1 hq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (show c ∈ (ir.sliceShape (atomAt ir d cb.om) d
      cb.idx q).monos from hc)
    let j' : Fin (cb.rels ⟨q, hq'⟩).nm := ⟨j, by exact hj⟩
    refine ⟨finSigmaFinEquiv ⟨⟨q, hq'⟩, j'⟩, ?_⟩
    rw [mergeShape_factors_mk cb.rels ⟨⟨q, hq'⟩, j'⟩]
    exact Shape.rel_factors _ _ j'

/-- **The pads of a batch**: skip pads, round pads, terminal claims and product cells. -/
theorem card_padIdx {e D n k : ℕ} {C : Type} [Fintype C] :
    Fintype.card (BatchedZerocheck.PadIdx e D n k C) = e + n * D + k + Fintype.card C := by
  change @Fintype.card _ (Fintype.ofEquiv _ _) = _
  rw [Fintype.ofEquiv_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

local notation "CR" => CellsReader.ofProgram ir

/-- **A batch's shape is the reader's** at its operand map. -/
theorem relShape_eq_shapeOf {om : OperandMap} {b : ℕ} (h : (ir.batch b).operands = om) :
    ir.relShape (atomAt ir d om) d b = @ForkReader.shapeOf ir (CR) d b := by
  rw [relShape_eq_batchShape, ForkReader.shapeOf, ← formsOf_eq_reader, formsOf_eq]
  congr 2
  cases om <;> simp [atomOf, h]

/-- A covered batch's operands are the reader's. -/
theorem CBatch.k_eq {om : OperandMap} (cb : ir.CBatch I d om) :
    (ir.relShape (atomAt ir d om) d cb.idx).k = @ForkReader.bK ir (CR) d cb.idx := by
  rw [relShape_eq_shapeOf cb.operands]
  rfl

/-- A covered batch's product cells are the reader's. -/
theorem CBatch.m_eq {om : OperandMap} (cb : ir.CBatch I d om) :
    cb.rel.padMonomials.card = @ForkReader.bM ir (CR) d cb.idx := by
  rw [Shape.card_padMonomials_rel, relShape_eq_shapeOf cb.operands, ForkReader.bM,
    Shape.cells_eq_cellsL, Shape.cellsK_eq]

/-- A covered batch's pads are the reader's. -/
theorem CBatch.card_pad {om : OperandMap} (cb : ir.CBatch I d om) :
    Fintype.card cb.Pad = @ForkReader.bPads ir (CR) d cb.idx := by
  erw [card_padIdx, Fintype.card_coe, CBatch.m_eq]
  rw [ForkReader.bPads, ForkReader.bE, ← CBatch.k_eq]

/-- A covered merged batch's operands are the reader's. -/
theorem MBatch.k_eq (cb : ir.MBatch I d) :
    (ir.relShape (atomAt ir d cb.om) d cb.idx).k = @ForkReader.bK ir (CR) d cb.idx := by
  rw [relShape_eq_shapeOf cb.operands]
  rfl

open Sumcheck.FieldSkip in
/-- A covered merged batch's product cells are the reader's. -/
theorem MBatch.m_eq (cb : ir.MBatch I d) :
    (MonoRelation.mergeShape cb.rels).padMonomials.card = @ForkReader.bM ir (CR) d cb.idx := by
  rw [MBatch.card_padMonomials, relShape_eq_shapeOf cb.operands, ForkReader.bM,
    Shape.cells_eq_cellsL, Shape.cellsK_eq]

/-- A covered merged batch's pads are the reader's. -/
theorem MBatch.card_pad (cb : ir.MBatch I d) :
    Fintype.card cb.Pad = @ForkReader.bPads ir (CR) d cb.idx := by
  erw [card_padIdx, Fintype.card_coe, MBatch.m_eq]
  rw [ForkReader.bPads, ForkReader.bE, ← MBatch.k_eq]

end Batches

/-! ## The size bounds from the numbers -/

section Bounds

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}

local notation "CR" => CellsReader.ofProgram ir

/-- An entry of a mapped list is in the image. -/
theorem idx_mem {α : Type} {L : List α} {g : α → ℕ} {M : List ℕ} (h : L.map g = M)
    (i : Fin L.length) : g L[i] ∈ M :=
  h ▸ List.mem_map_of_mem (List.getElem_mem _)

/-- The domain's numbers' batch entries. -/
abbrev entryOf (merged bits : Bool) (b : ℕ) : ForkReader.BatchNums :=
  ⟨merged, bits, (ir.batch b).rounds, (ir.batch b).degree, (ir.batch b).width,
    (ir.batch b).parts.length, @ForkReader.bK ir (CR) d b, @ForkReader.bPads ir (CR) d b,
    @ForkReader.bM ir (CR) d b, ForkReader.bE ir b⟩

theorem batches_eq (D : PackingDesc) :
    (@ForkReader.domainNums ir (CR) d P D).batches =
      (ForkReader.cbs ir d).map (entryOf (ir := ir) (d := d) false false) ++
        (ForkReader.sbs ir d).map (entryOf (ir := ir) (d := d) false true) ++
        (ForkReader.mbs ir d).map (entryOf (ir := ir) (d := d) true false) ++
        (ForkReader.smbs ir d).map (entryOf (ir := ir) (d := d) true true) := rfl

/-- **`ForkSizesLe` from the numbers.** -/
theorem forkSizesLe_of (R : ir.FieldReady I d P) (hbat : ir.batchesB = true) (D : PackingDesc)
    {Mx : ℕ} (h : (@ForkReader.domainNums ir (CR) d P D).sizesB Mx = true) :
    ForkSizesLe R Mx := by
  have hB : ir.batchesOkB d R.Pk = true := by
    have h := R.ok
    simp only [fieldOkB, Bool.and_eq_true] at h
    exact h.1.1.1.2
  simp only [ForkReader.DomainNums.sizesB, Bool.and_eq_true, List.all_eq_true, batches_eq,
    List.mem_append, List.mem_map, decide_eq_true_eq] at h
  obtain ⟨hb, hdeg⟩ := h
  refine ⟨fun i => ?_, fun i => ?_, ⟨fun i => ?_, fun i => ?_⟩, fun r hr => ?_⟩
  · have := hb _ (Or.inl (Or.inl (Or.inl ⟨_, idx_mem (cbatches_idx hbat hB) i, rfl⟩)))
    simp only [Bool.not_false, Bool.true_or, and_true] at this
    exact ⟨this.1.1, this.1.2, (CBatch.k_eq _).trans_le this.2⟩
  · have := hb _ (Or.inl (Or.inl (Or.inr ⟨_, idx_mem (sumBatches_idx hbat hB) i, rfl⟩)))
    simp only [Bool.not_true, Bool.false_or] at this
    exact ⟨this.1.1.1, this.1.1.2, (CBatch.k_eq _).trans_le this.1.2, of_decide_eq_true this.2⟩
  · have := hb _ (Or.inl (Or.inr ⟨_, idx_mem (mbatches_idx hbat hB) i, rfl⟩))
    simp only [Bool.not_false, Bool.true_or, and_true] at this
    exact ⟨this.1.1, this.1.2, (MBatch.k_eq _).trans_le this.2⟩
  · have := hb _ (Or.inr ⟨_, idx_mem (sumMBatches_idx hbat hB) i, rfl⟩)
    simp only [Bool.not_true, Bool.false_or] at this
    exact ⟨this.1.1.1, this.1.1.2, (MBatch.k_eq _).trans_le this.1.2, of_decide_eq_true this.2⟩
  · have hm : r.plan ∈ ir.planPacking P d := R.rs_plan ▸ List.mem_map_of_mem hr
    exact hdeg _ (List.mem_map_of_mem (f := PackingEdge.degree) hm)

/-- **A sum over a list's entries through an index map** is the indices' sum. -/
theorem sum_fin_idx {α : Type} {L : List α} {g : α → ℕ} {M : List ℕ} (h : L.map g = M)
    (f : ℕ → ℕ) : ∑ i : Fin L.length, f (g L[i]) = (M.map f).sum := by
  simp only [Fin.getElem_fin]
  rw [Fin.sum_univ_fun_getElem L (fun x => f (g x)), ← h, List.map_map]
  rfl

theorem circs_idx (d : ℕ) : List.map Fin.val (ir.circs d) = ForkReader.circs ir d := by
  rw [circs, ForkReader.circs, ← List.map_coe_finRange_eq_range, List.filter_map]
  induction (List.finRange ir.circuits.length) with
  | nil => rfl
  | cons b l ih => rw [List.filter_cons, List.filter_cons]; split <;> simp_all

theorem circs_length (d : ℕ) : (ir.circs d).length = (ForkReader.circs ir d).length := by
  have := congrArg List.length (circs_idx (ir := ir) d)
  rw [List.length_map] at this
  exact this

/-- **The branches' claims**: one per covered batch, one per circuit. -/
theorem branchNc_sum (Pk : (I (ir.domainField d)).Packing) :
    ((List.finRange (ir.nBranch d Pk)).map fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b)).sum =
      (ir.cbatches d Pk).length + (ir.sumBatches d Pk).length +
        ((ir.mbatches d Pk).length + (ir.sumMBatches d Pk).length) + (ir.circs d).length := by
  rw [← Fin.sum_univ_def, Equiv.sum_comp (ir.branchEquiv d Pk) (ir.branchNc d Pk)]
  simp [Fintype.sum_sum_type, branchNc]

variable (R : ir.FieldReady I d P) {D : PackingDesc}

/-- The domain's numbers. -/
local notation "N" => @ForkReader.domainNums ir (CR) d P D

theorem batches_length (hbat : ir.batchesB = true) (hB : ir.batchesOkB d R.Pk = true) :
    (N).batches.length = (ir.cbatches d R.Pk).length + (ir.sumBatches d R.Pk).length +
      ((ir.mbatches d R.Pk).length + (ir.sumMBatches d R.Pk).length) := by
  rw [batches_eq]
  simp only [List.length_append, List.length_map, ← cbatches_idx hbat hB,
    ← sumBatches_idx hbat hB, ← mbatches_idx hbat hB, ← sumMBatches_idx hbat hB]
  omega

theorem FieldReady.batchesOk : ir.batchesOkB d R.Pk = true := by
  have h := R.ok
  simp only [fieldOkB, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- **`laterBound` is the numbers'.** -/
theorem laterBound_eq (hbat : ir.batchesB = true) : laterBound R.rs = (N).later := by
  have hB := R.batchesOk
  rw [laterBound, branchNc_sum, card_rowIdx_off ir d R.wf R.rs, R.rs_plan,
    ForkReader.DomainNums.later, batches_length R hbat hB, circs_length]
  have hdeg : (R.rs.map fun r => r.plan.degree + 1).sum =
      (((N).degrees).map (· + 1)).sum := by
    change _ = (((ForkReader.es ir d P).map (·.degree)).map (· + 1)).sum
    rw [ForkReader.es, ← R.rs_plan, List.map_map, List.map_map]
    rfl
  have hc : (N).circuits.length = (ForkReader.circs ir d).length := List.length_map ..
  have hr : (N).rowsOff = ((List.range ir.predicates.length).map
      (@ForkReader.rowLenOff ir (CR) d (ir.planPacking P d))).sum := rfl
  rw [hdeg, hc, hr]

theorem circL_sum : ∑ i : Fin (ir.circs d).length, ir.circL d i =
    ((ForkReader.circs ir d).map (ForkReader.circL ir)).sum :=
  sum_fin_idx (circs_idx d) (ForkReader.circL ir)

theorem gtSum_eq : (N).gtSum = ((ForkReader.circs ir d).map (ForkReader.circL ir)).sum := by
  change ((ForkReader.circs ir d).map (fun c => (ForkReader.circW ir c, ForkReader.circL ir c))
    |>.map (·.2)).sum = _
  rw [List.map_map]
  rfl

theorem cellsSum_eq : (N).cellsSum =
    ((ForkReader.cbs ir d).map (@ForkReader.bM ir (CR) d)).sum +
      ((ForkReader.sbs ir d).map (@ForkReader.bM ir (CR) d)).sum +
      ((ForkReader.mbs ir d).map (@ForkReader.bM ir (CR) d)).sum +
      ((ForkReader.smbs ir d).map (@ForkReader.bM ir (CR) d)).sum := by
  simp only [ForkReader.DomainNums.cellsSum, batches_eq, List.map_append, List.sum_append,
    List.map_map]
  rfl

/-- **`forkQBound` is the numbers'.** -/
theorem forkQBound_eq (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) :
    forkQBound R (ir.circL d) = (N).qBound := by
  have hB := R.batchesOk
  rw [forkQBound, ForkReader.DomainNums.qBound, cellsSum_eq, gtSum_eq, ← circL_sum,
    card_quadIdx, R.ownSum_eq hD hc]
  have h1 : ∑ i : Fin (ir.cbatches d R.Pk).length,
      (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).m =
        ((ForkReader.cbs ir d).map (@ForkReader.bM ir (CR) d)).sum :=
    (Finset.sum_congr rfl fun i _ => CBatch.m_eq _).trans
      (sum_fin_idx (cbatches_idx hbat hB) _)
  have h2 : ∑ i : Fin (ir.sumBatches d R.Pk).length,
      (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).m =
        ((ForkReader.sbs ir d).map (@ForkReader.bM ir (CR) d)).sum :=
    (Finset.sum_congr rfl fun i _ => CBatch.m_eq _).trans
      (sum_fin_idx (sumBatches_idx hbat hB) _)
  have h3 : ∑ i : Fin (ir.mbatches d R.Pk).length,
      (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).m =
        ((ForkReader.mbs ir d).map (@ForkReader.bM ir (CR) d)).sum :=
    (Finset.sum_congr rfl fun i _ => MBatch.m_eq _).trans
      (sum_fin_idx (mbatches_idx hbat hB) _)
  have h4 : ∑ i : Fin (ir.sumMBatches d R.Pk).length,
      (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).m =
        ((ForkReader.smbs ir d).map (@ForkReader.bM ir (CR) d)).sum :=
    (Finset.sum_congr rfl fun i _ => MBatch.m_eq _).trans
      (sum_fin_idx (sumMBatches_idx hbat hB) _)
  rw [h1, h2, h3, h4]
  rfl

/-- **`forkLinBound` is the numbers'.** -/
theorem forkLinBound_eq (hbat : ir.batchesB = true) :
    forkLinBound R (ir.circL d) = (N).linBound := by
  rw [forkLinBound, ForkReader.DomainNums.linBound, batches_length R hbat R.batchesOk, gtSum_eq,
    ← circL_sum, laterBound_eq (D := D) R hbat]
  omega

theorem gpSum_eq : (N).gpSum = ∑ i : Fin (ir.circs d).length, ir.padBound d i := by
  rw [show ∑ i : Fin (ir.circs d).length, ir.padBound d i = ((ForkReader.circs ir d).map fun c =>
      ForkReader.circL ir c * (4 * ForkReader.circW ir c + 3)).sum from ?_]
  · change ((ForkReader.circs ir d).map (fun c => (ForkReader.circW ir c, ForkReader.circL ir c))
      |>.map fun c => c.2 * (4 * c.1 + 3)).sum = _
    rw [List.map_map]
    rfl
  · rw [← sum_fin_idx (circs_idx d)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [padBound, circL, circW, circuitWidth_eq]
    rfl

theorem padsSum_eq (hbat : ir.batchesB = true) :
    ∑ i : Fin (ir.cbatches d R.Pk).length, Fintype.card ((ir.cbatches d R.Pk)[i]).Pad +
        ∑ i : Fin (ir.sumBatches d R.Pk).length,
          (Fintype.card ((ir.sumBatches d R.Pk)[i]).cb.Pad + 8) +
        ∑ i : Fin (ir.mbatches d R.Pk).length, Fintype.card ((ir.mbatches d R.Pk)[i]).Pad +
        ∑ i : Fin (ir.sumMBatches d R.Pk).length,
          (Fintype.card ((ir.sumMBatches d R.Pk)[i]).mb.Pad + 8) = (N).padsSum := by
  have hB := R.batchesOk
  have h1 := (Finset.sum_congr rfl fun i _ => CBatch.card_pad _).trans
    (sum_fin_idx (cbatches_idx hbat hB) (@ForkReader.bPads ir (CR) d))
  have h2 := (Finset.sum_congr rfl fun i _ => congrArg (· + 8) (CBatch.card_pad _)).trans
    (sum_fin_idx (sumBatches_idx hbat hB) (fun b => @ForkReader.bPads ir (CR) d b + 8))
  have h3 := (Finset.sum_congr rfl fun i _ => MBatch.card_pad _).trans
    (sum_fin_idx (mbatches_idx hbat hB) (@ForkReader.bPads ir (CR) d))
  have h4 := (Finset.sum_congr rfl fun i _ => congrArg (· + 8) (MBatch.card_pad _)).trans
    (sum_fin_idx (sumMBatches_idx hbat hB) (fun b => @ForkReader.bPads ir (CR) d b + 8))
  rw [h1, h2, h3, h4]
  simp only [ForkReader.DomainNums.padsSum, batches_eq, List.map_append, List.sum_append,
    List.map_map]
  rfl

variable {t : TableauNums}

theorem sh_w (ht : R.cert.nums = t) : R.numbers.Sh.w = ForkReader.DomainNums.w t := by
  subst ht; rfl

theorem sh_N (ht : R.cert.nums = t) : R.cert.Sh.N = t.N := by subst ht; rfl

theorem sh_block (ht : R.cert.nums = t) : R.cert.Sh.block = t.block := by subst ht; rfl

theorem sh_nrep (ht : R.cert.nums = t) : R.cert.Sh.nrep = t.nrep := by subst ht; rfl

/-- **`forkRBound` is the numbers'.** -/
theorem forkRBound_eq (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) :
    forkRBound R (ir.padBound d) (ir.circL d) = (N).rBound t := by
  rw [forkRBound, ForkReader.DomainNums.rBound, Ligero.MaskRow.TreeLayout.prefixRows, sh_w R ht,
    R.np_eq hD hc, padsSum_eq R hbat, ← gpSum_eq, forkQBound_eq R hbat hD hc, R.ownSum_eq hD hc,
    R.rs_plan, nwOf_eq, root_eq]
  rfl

/-- **`claimCount` is the numbers'.** -/
theorem claimCount_eq (hbat : ir.batchesB = true) :
    ir.claimCount (d := d) (Pk := R.Pk) = (N).claims := by
  rw [claimCount, branchNc_sum, card_rowIdx, ForkReader.DomainNums.claims,
    batches_length R hbat R.batchesOk, circs_length]
  have hc : (N).circuits.length = (ForkReader.circs ir d).length := List.length_map ..
  rw [hc]
  rfl

/-- **`ForkRestNumbers` from the numbers.** -/
theorem forkRestNumbers_of (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) {Lmax : ℕ}
    (h : (N).restB t Lmax = true) :
    ForkRestNumbers R (ir.padBound d) (ir.circL d) Lmax := by
  have hB := R.batchesOk
  simp only [ForkReader.DomainNums.restB, Bool.and_eq_true, List.all_eq_true, batches_eq,
    List.mem_append, List.mem_map, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hb, hcirc⟩, hl⟩, hr⟩ := h
  refine ⟨fun i => ?_, fun i => ?_, ⟨fun i => ?_, fun i => ?_⟩, fun i => ?_, ?_, ?_⟩
  · have := hb _ (Or.inl (Or.inl (Or.inl ⟨_, idx_mem (cbatches_idx hbat hB) i, rfl⟩)))
    rw [show (ir.colsBatchAt R.rs Unit (ir.cbatches d R.Pk)[i]).k = _ from CBatch.k_eq _]
    exact this
  · have := hb _ (Or.inl (Or.inl (Or.inr ⟨_, idx_mem (sumBatches_idx hbat hB) i, rfl⟩)))
    rw [show (ir.bitsBatchAt R.rs Unit ((ir.sumBatches d R.Pk)[i]).cb).k = _ from CBatch.k_eq _]
    exact this
  · have := hb _ (Or.inl (Or.inr ⟨_, idx_mem (mbatches_idx hbat hB) i, rfl⟩))
    rw [show (ir.mergedBatchAt R.rs Unit (ir.mbatches d R.Pk)[i]).k = _ from MBatch.k_eq _]
    exact this
  · have := hb _ (Or.inr ⟨_, idx_mem (sumMBatches_idx hbat hB) i, rfl⟩)
    rw [show (ir.mergedBatchAt R.rs Unit ((ir.sumMBatches d R.Pk)[i]).mb).k = _ from
      MBatch.k_eq _]
    exact this
  · have hm := idx_mem (circs_idx (ir := ir) d) i
    have := hcirc _ (List.mem_map_of_mem (f := fun c => (ForkReader.circW ir c,
      ForkReader.circL ir c)) hm)
    rw [circuitWidth_eq]
    exact this
  · rw [laterBound_eq R hbat]
    exact hl
  · rw [forkRBound_eq R hbat hD hc ht, forkLinBound_eq R hbat, forkQBound_eq R hbat hD hc,
      sh_w R ht, show R.numbers.Sh.nrep = t.nrep from sh_nrep R ht]
    exact hr

/-- **`ForkLoadNumbers` from the numbers.** -/
theorem forkLoadNumbers_of (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) {Lmax : ℕ}
    (h : (N).loadB t Lmax = true) :
    ForkLoadNumbers R (ir.padBound d) (ir.circL d) Lmax := by
  simp only [ForkReader.DomainNums.loadB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := forkRestNumbers_of R hbat hD hc ht h.2
  exact ⟨b1, b2, b3, b4, (claimCount_eq R hbat).trans_le h.1, b5, b6⟩

/-- **`FitsOk` from the numbers.** -/
theorem fitsOk_of (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) {fb Mx Lmax : ℕ}
    (h : (N).fitsB t fb Mx Lmax = true) : FitsOk R fb Mx Lmax := by
  simp only [ForkReader.DomainNums.fitsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, forkSizesLe_of R hbat D h2, h3, by rwa [sh_N R ht], by rwa [sh_block R ht],
    by rwa [sh_nrep R ht, sh_block R ht], by rwa [sh_nrep R ht],
    forkLoadNumbers_of R hbat hD hc ht h8⟩

end Bounds

end GordieHowe.RealizedProgram
