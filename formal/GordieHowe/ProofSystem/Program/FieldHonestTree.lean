-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldInput
public import GordieHowe.ProofSystem.RingSwitching.PlanTreeHonest

@[expose] public section

/-!
# GordieHowe: the honest committed cells of a domain's packing tree

The honest committed cells of domain `d`'s packing tree (`GordieHowe.RealizedProgram.fieldTree`) at cells `a` of the
domain, every cell in its base:

* **the groups at a slot** (`GordieHowe.RealizedProgram.groupAt`, `GordieHowe.RealizedProgram.rootGroupAt`): the child group a node's slot
  or a root word holds, found by a search over the edges; the children's slot intervals are
  disjoint (`GordieHowe.RealizedProgram.slot_disjoint`, `GordieHowe.RealizedProgram.root_disjoint`), so the search finds every group at
  its slot (`GordieHowe.RealizedProgram.groupAt_slotOf`, `GordieHowe.RealizedProgram.rootGroupAt_rootOff`);
* **the honest own values** (`GordieHowe.RealizedProgram.treeOwn`, `GordieHowe.RealizedProgram.treeGiven`): a node's own region holds its
  own cells; the given region of a view child holds the coordinates of its parent's own cells;
* **the honest committed cells** (`GordieHowe.RealizedProgram.treeHonestCells`, `PEdge.cellVal`): the root words packed
  from their groups, the root own cells and the masks' and the masked reduction's pads from given values;
* **the layout facts** (`GordieHowe.RealizedProgram.fillSpec`, `PEdge.FillSpec`), so the honest slots decode from
  their words (`PEdge.wordsAt_slotVal`);
* **the decoded cells** (`GordieHowe.RealizedProgram.treeDecode_treeHonestCells`): the honest committed cells decode to
  the cells `a`.
-/

namespace GordieHowe.RealizedProgram

open Export PackingStage RelativePacking Ligero.MaskRow PEdge

section

/-! ## The slots' intervals -/

section Slots

variable (ir : RealizedProgram) (d : ℕ)

theorem slotOf_eq_add (es : List PackingEdge) (b g : ℕ) :
    ir.slotOf d es b g = ir.slotOf d es b 0 + g := by
  unfold slotOf
  split
  · split_ifs <;> omega
  · omega

variable {ir d}

theorem ownStart_le_slotOf {es : List PackingEdge} {a b : ℕ} (hp : parentIdx es b = some a) :
    ir.ownStart d es a ≤ ir.slotOf d es b 0 := by
  simp only [slotOf, hp]
  split_ifs <;> omega

theorem slotOf_view {es : List PackingEdge} {a b : ℕ} (hp : parentIdx es b = some a)
    (hv : viewChild es a = some b) (g : ℕ) : ir.slotOf d es b g = ir.ownStart d es a + g := by
  simp only [slotOf, hp, hv, ↓reduceIte]

theorem slotOf_other {es : List PackingEdge} {a b : ℕ} (hp : parentIdx es b = some a)
    (hv : viewChild es a ≠ some b) (g : ℕ) :
    ir.slotOf d es b g =
      ir.ownStart d es a + ir.baseOf d es a + ir.otherOff d es a b + g := by
  simp only [slotOf, hp, if_neg hv]

theorem baseOf_view {es : List PackingEdge} {a b : ℕ} (hv : viewChild es a = some b) :
    ir.baseOf d es a = ir.ngOf d es b := by
  simp only [baseOf, hv]

theorem baseOf_none {es : List PackingEdge} {a : ℕ} (hv : viewChild es a = none) :
    ir.baseOf d es a = ir.own d es a := by
  simp only [baseOf, hv]

/-- **The slot intervals of two children of a node are disjoint**: the view child's lies in the own
region, the other children's follow in order. -/
theorem slot_disjoint {es : List PackingEdge} {a b b' s : ℕ} (hp : parentIdx es b = some a)
    (hp' : parentIdx es b' = some a) (hne : b' ≠ b)
    (hs : ir.slotOf d es b 0 ≤ s ∧ s < ir.slotOf d es b 0 + ir.ngOf d es b) :
    ¬ (ir.slotOf d es b' 0 ≤ s ∧ s < ir.slotOf d es b' 0 + ir.ngOf d es b') := by
  rintro ⟨h1, h2⟩
  by_cases hv : viewChild es a = some b
  · have hv' : viewChild es a ≠ some b' := fun h => hne (Option.some.inj (h.symm.trans hv))
    rw [slotOf_view hp hv] at hs
    rw [slotOf_other hp' hv', baseOf_view hv] at h1
    omega
  · by_cases hv' : viewChild es a = some b'
    · rw [slotOf_view hp' hv'] at h1 h2
      rw [slotOf_other hp hv, baseOf_view hv'] at hs
      omega
    · rw [slotOf_other hp hv] at hs
      rw [slotOf_other hp' hv'] at h1 h2
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := sum_filter_range_add_le (otherChild es a) (ir.ngOf d es) hlt
          (by simp [otherChild, hp', hv'])
        simp only [otherOff] at hs h1 h2
        omega
      · have := sum_filter_range_add_le (otherChild es a) (ir.ngOf d es) hlt
          (by simp [otherChild, hp, hv])
        simp only [otherOff] at hs h1 h2
        omega

/-- **The word intervals of two root children are disjoint.** -/
theorem root_disjoint {es : List PackingEdge} {b b' w : ℕ} (hp : parentIdx es b = none)
    (hp' : parentIdx es b' = none) (hne : b' ≠ b)
    (hw : ir.rootOff d es b ≤ w ∧ w < ir.rootOff d es b + ir.ngOf d es b) :
    ¬ (ir.rootOff d es b' ≤ w ∧ w < ir.rootOff d es b' + ir.ngOf d es b') := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := sum_filter_range_add_le (fun b => (parentIdx es b).isNone) (ir.ngOf d es) hlt
      (by simp [hp'])
    simp only [rootOff] at hw h1 h2
    omega
  · have := sum_filter_range_add_le (fun b => (parentIdx es b).isNone) (ir.ngOf d es) hlt
      (by simp [hp])
    simp only [rootOff] at hw h1 h2
    omega

variable (ir d)

/-- **The child group at slot `s` of node `a`**: the child edge whose slot interval holds `s`, and
the group's index. -/
def groupAt (es : List PackingEdge) (a s : ℕ) : Option (ℕ × ℕ) :=
  (List.range es.length).findSome? fun b =>
    if parentIdx es b = some a ∧ ir.slotOf d es b 0 ≤ s ∧ s < ir.slotOf d es b 0 + ir.ngOf d es b
    then some (b, s - ir.slotOf d es b 0) else none

/-- **The root child group at committed word `w`.** -/
def rootGroupAt (es : List PackingEdge) (w : ℕ) : Option (ℕ × ℕ) :=
  (List.range es.length).findSome? fun b =>
    if parentIdx es b = none ∧ ir.rootOff d es b ≤ w ∧ w < ir.rootOff d es b + ir.ngOf d es b
    then some (b, w - ir.rootOff d es b) else none

variable {ir d}

/-- **Every group lies at its slot.** -/
theorem groupAt_slotOf {es : List PackingEdge} {a b g : ℕ} (hb : b < es.length)
    (hp : parentIdx es b = some a) (hg : g < ir.ngOf d es b) :
    ir.groupAt d es a (ir.slotOf d es b g) = some (b, g) := by
  have hs := ir.slotOf_eq_add d es b g
  unfold groupAt
  rw [findSome?_eq_of_unique (b := b) (List.mem_range.2 hb)]
  · rw [if_pos ⟨hp, by omega, by omega⟩]
    congr 2
    omega
  · intro b' _ hne
    by_contra hb'
    split_ifs at hne with hc
    · exact slot_disjoint hp hc.1 hb' ⟨by omega, by omega⟩ hc.2
    · exact hne rfl

/-- **A group found at a slot** is a group of a child edge, at that slot. -/
theorem groupAt_spec {es : List PackingEdge} {a s b g : ℕ} (h : ir.groupAt d es a s = some (b, g)) :
    b < es.length ∧ parentIdx es b = some a ∧ g < ir.ngOf d es b ∧ s = ir.slotOf d es b g := by
  unfold groupAt at h
  obtain ⟨b', hb', hf⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hf with hc
  cases hf
  refine ⟨List.mem_range.1 hb', hc.1, by omega, ?_⟩
  rw [slotOf_eq_add]
  omega

/-- **No group lies below every child's slots.** -/
theorem groupAt_eq_none {es : List PackingEdge} {a s : ℕ}
    (h : ∀ b, parentIdx es b = some a → s < ir.slotOf d es b 0) : ir.groupAt d es a s = none := by
  unfold groupAt
  rw [List.findSome?_eq_none_iff]
  intro b _
  rw [if_neg]
  rintro ⟨hp, h1, -⟩
  have := h b hp
  omega

/-- **Every root group lies at its committed word.** -/
theorem rootGroupAt_rootOff {es : List PackingEdge} {b g : ℕ} (hb : b < es.length)
    (hp : parentIdx es b = none) (hg : g < ir.ngOf d es b) :
    ir.rootGroupAt d es (ir.rootOff d es b + g) = some (b, g) := by
  unfold rootGroupAt
  rw [findSome?_eq_of_unique (b := b) (List.mem_range.2 hb)]
  · rw [if_pos ⟨hp, by omega, by omega⟩]
    congr 2
    omega
  · intro b' _ hne
    by_contra hb'
    split_ifs at hne with hc
    · exact root_disjoint hp hc.1 hb' ⟨by omega, by omega⟩ hc.2
    · exact hne rfl

end Slots

/-! ## The masks' cells -/

section Masks

variable {F : FieldInterp} {Pk : F.Packing}

theorem preOff_succ {rs : List (REdge F Pk)} {a : ℕ} (ha : a < rs.length) :
    preOff Pk rs (a + 1) = preOff Pk rs a + rs[a].kit.masks.nPre := by
  simp only [preOff, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero]

theorem preOff_mono {rs : List (REdge F Pk)} {a b : ℕ} (h : a ≤ b) :
    preOff Pk rs a ≤ preOff Pk rs b := by
  unfold preOff
  have hab : (rs.take b).take a = rs.take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [← hab, ← List.sum_take_add_sum_drop ((rs.take b).map fun r => r.kit.masks.nPre) a,
    List.map_take]
  exact Nat.le_add_right _ _

variable (ir : RealizedProgram) (d : ℕ)

/-- **The prefix cells of a planned edge** lie at its prefix offset. -/
theorem plannedEdge_maskPre {rs : List (REdge F Pk)} (Pads : Type) {a : ℕ} (ha : a < rs.length)
    (j : Fin rs[a].kit.masks.nPre) :
    (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j = .inl ⟨preOff Pk rs a + j, preOff_add_lt ha j.2⟩ := by
  simp only [plannedEdge, dif_pos (preOff_add_lt ha j.2)]

/-- **The masks' own cells of a planned edge.** -/
theorem plannedEdge_maskOwn {rs : List (REdge F Pk)} (Pads : Type) {a : ℕ} (ha : a < rs.length)
    (o : Fin rs[a].kit.masks.nOwn) :
    (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o = .inr (.inr (.mask ⟨⟨a, ha⟩, o⟩)) := by
  simp only [plannedEdge, dif_pos ha]
  rfl

variable {ir d} {Pads : Type} [Fintype Pads] [DecidableEq Pads] [Encodable Pads]

/-- **The prefix cells of the tree's edges are prefix cells.** -/
theorem fieldEdges_maskPre {rs : List (REdge F Pk)} {e : PEdge F.K (ir.TreeCell d Pk rs Pads) Pk.p Pk.S0}
    (he : e ∈ ir.fieldEdges d Pk rs Pads) (j : Fin e.kit.masks.nPre) : ∃ j', e.maskPre j = .inl j' := by
  obtain ⟨a, ha, rfl⟩ := List.mem_mapIdx.1 he
  exact ⟨_, plannedEdge_maskPre ir d Pads ha j⟩

/-- **The masks' own cells of the tree's edges are masks' own cells.** -/
theorem fieldEdges_maskOwn {rs : List (REdge F Pk)} {e : PEdge F.K (ir.TreeCell d Pk rs Pads) Pk.p Pk.S0}
    (he : e ∈ ir.fieldEdges d Pk rs Pads) (o : Fin e.kit.masks.nOwn) :
    ∃ o', e.maskOwn o = .inr (.inr (.mask o')) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_mapIdx.1 he
  exact ⟨_, plannedEdge_maskOwn ir d Pads ha o⟩

/-- **The mask cells of the tree's edges are distinct** (`preOff_mono`). -/
theorem maskCellsDistinct_fieldEdges (rs : List (REdge F Pk)) :
    MaskCellsDistinct (ir.fieldEdges d Pk rs Pads) := by
  refine maskCellsDistinct_of_getElem _ (fun a ha => ?_) fun a b ha hb hab => ?_
  · have ha' : a < rs.length := by rwa [length_fieldEdges] at ha
    rw [getElem_fieldEdges]
    intro c c' h
    rcases c with j | o <;> rcases c' with j' | o'
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j =
        (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j' at h
      rw [plannedEdge_maskPre ir d Pads ha' j, plannedEdge_maskPre ir d Pads ha' j'] at h
      simp only [Sum.inl.injEq, Fin.mk.injEq, Nat.add_left_cancel_iff] at h
      exact congrArg Sum.inl (Fin.ext h)
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j =
        (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o' at h
      rw [plannedEdge_maskPre ir d Pads ha' j, plannedEdge_maskOwn ir d Pads ha' o'] at h
      cases h
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o =
        (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j' at h
      rw [plannedEdge_maskOwn ir d Pads ha' o, plannedEdge_maskPre ir d Pads ha' j'] at h
      cases h
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o =
        (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o' at h
      rw [plannedEdge_maskOwn ir d Pads ha' o, plannedEdge_maskOwn ir d Pads ha' o'] at h
      injection h with h
      injection h with h
      injection h with h
      cases h
      rfl
  · have ha' : a < rs.length := by rwa [length_fieldEdges] at ha
    have hb' : b < rs.length := by rwa [length_fieldEdges] at hb
    rw [getElem_fieldEdges ir d rs Pads a ha, getElem_fieldEdges ir d rs Pads b hb]
    intro c c' h
    have h1 := preOff_succ (Pk := Pk) ha'
    have h2 := preOff_mono (Pk := Pk) (rs := rs) (show a + 1 ≤ b by omega)
    rcases c with j | o <;> rcases c' with j' | o'
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j =
        (ir.plannedEdge d Pk rs Pads b rs[b]).maskPre j' at h
      rw [plannedEdge_maskPre ir d Pads ha' j, plannedEdge_maskPre ir d Pads hb' j'] at h
      have hv := congrArg Fin.val (Sum.inl.inj h)
      have hj : (j : ℕ) < rs[a].kit.masks.nPre := j.2
      simp only at hv
      omega
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskPre j =
        (ir.plannedEdge d Pk rs Pads b rs[b]).maskOwn o' at h
      rw [plannedEdge_maskPre ir d Pads ha' j, plannedEdge_maskOwn ir d Pads hb' o'] at h
      cases h
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o =
        (ir.plannedEdge d Pk rs Pads b rs[b]).maskPre j' at h
      rw [plannedEdge_maskOwn ir d Pads ha' o, plannedEdge_maskPre ir d Pads hb' j'] at h
      cases h
    · change (ir.plannedEdge d Pk rs Pads a rs[a]).maskOwn o =
        (ir.plannedEdge d Pk rs Pads b rs[b]).maskOwn o' at h
      rw [plannedEdge_maskOwn ir d Pads ha' o, plannedEdge_maskOwn ir d Pads hb' o'] at h
      injection h with h
      injection h with h
      injection h with h
      have hv := congrArg (fun s => (s.1 : ℕ)) h
      simp only at hv
      omega

end Masks

/-! ## The honest committed cells -/

section Honest

variable (ir : RealizedProgram) {I : Interp} (d : ℕ) {Pk : (I (ir.domainField d)).Packing}
  (rs : List (REdge (I (ir.domainField d)) Pk))

/-- **Own cell `i` of node `a`** at the cells `a0`. -/
def ownCellAt (a0 : ir.Cell d → (I (ir.domainField d)).K) (a i : ℕ) : (I (ir.domainField d)).K :=
  match (ir.ownKeys d (rs.map REdge.plan) a)[i]? with
  | some k => if hk : k ∈ ir.cellKeys d then a0 ⟨k, hk⟩ else 0
  | none => 0

/-- **The honest own value of slot `s` of node `a`** at the cells `a0`: in the given region, the
coordinate `s mod d` of the parent's own cell `s / d`; in the own region, the node's own cell; `0`
after. -/
def treeOwn (a0 : ir.Cell d → (I (ir.domainField d)).K) (a s : ℕ) : (I (ir.domainField d)).K :=
  if s < ir.ownStart d (rs.map REdge.plan) a then
    match parentIdx (rs.map REdge.plan) a with
    | some j =>
      if ha : a < rs.length then
        if hd : 0 < rs[a].plan.degree then
          rs[a].kit.basis.coord (ir.ownCellAt d rs a0 j (s / rs[a].plan.degree))
            ⟨s % rs[a].plan.degree, Nat.mod_lt _ hd⟩
        else 0
      else 0
    | none => 0
  else if s < ir.ownStart d (rs.map REdge.plan) a + ir.own d (rs.map REdge.plan) a then
    ir.ownCellAt d rs a0 a (s - ir.ownStart d (rs.map REdge.plan) a)
  else 0

/-- **Group `g` of edge `a` is given**: `a` is its parent's view child and `g` one of the parent's
own cells. -/
def treeGiven (a g : ℕ) : Bool :=
  match parentIdx (rs.map REdge.plan) a with
  | some j => viewChild (rs.map REdge.plan) j == some a && decide (g < ir.own d (rs.map REdge.plan) j)
  | none => false

variable (Pads : Type)

/-- **The root group of a committed cell**: a root word's group, none for any other cell. -/
def treeRootAt : ir.TreeCell d Pk rs Pads → Option (ℕ × ℕ)
  | .inr (.inl w) => ir.rootGroupAt d (rs.map REdge.plan) w.1
  | _ => none

/-- **The honest value of a committed cell that is not a root word**: a prefix cell `pre`, a root
cell its cell of `a0`, a mask's own cell `mask`, a pad `pad`, the spare cell `0`. -/
def treeBase (a0 : ir.Cell d → (I (ir.domainField d)).K) (pre : Fin (npOf Pk rs) → (I (ir.domainField d)).K)
    (mask : MaskOwn Pk rs → (I (ir.domainField d)).K) (pad : Pads → (I (ir.domainField d)).K) :
    ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K
  | .inl j => pre j
  | .inr (.inl _) => 0
  | .inr (.inr .spare) => 0
  | .inr (.inr (.cell k)) => a0 k.1
  | .inr (.inr (.mask o)) => mask o
  | .inr (.inr (.pad q)) => pad q

/-- **The honest slot values** at the cells `a0` (`PEdge.slotVal`). -/
def honestSlots (a0 : ir.Cell d → (I (ir.domainField d)).K) : ℕ → ℕ → (I (ir.domainField d)).K :=
  slotVal (ir.fieldEdges d Pk rs Pads) (ir.treeOwn d rs a0) (ir.treeGiven d rs)
    (ir.groupAt d (rs.map REdge.plan))

/-- **The honest committed cells** at the cells `a0` and the given values of the prefix cells, the
masks' own cells and the pads (`PEdge.cellVal`). -/
def treeHonestCells (a0 : ir.Cell d → (I (ir.domainField d)).K) (pre : Fin (npOf Pk rs) → (I (ir.domainField d)).K)
    (mask : MaskOwn Pk rs → (I (ir.domainField d)).K) (pad : Pads → (I (ir.domainField d)).K) :
    ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K :=
  cellVal (ir.fieldEdges d Pk rs Pads) (ir.treeOwn d rs a0) (ir.treeGiven d rs)
    (ir.groupAt d (rs.map REdge.plan)) (ir.treeRootAt d rs Pads) (ir.treeBase d rs Pads a0 pre mask pad)

variable {ir d rs Pads}

/-- **A cell at node `a` lies in the node's subfield**, when it lies in its base. -/
theorem cell_mem_node (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    {a0 : ir.Cell d → (I (ir.domainField d)).K} (hbase : ∀ k, a0 k ∈ ir.cellBase I d k)
    {k : ir.Cell d} {a : ℕ} (hn : ir.cellNode (rs.map REdge.plan) k.1 = some a) (ha : a < rs.length) :
    a0 k ∈ fixedField (I (ir.domainField d)).K Pk.p rs[a].plan.childDegree := by
  obtain ⟨s, hs⟩ : ∃ s, ir.cellName k.1 = some s := by
    unfold cellNode at hn
    cases h : ir.cellName k.1 with
    | none => rw [h] at hn; cases hn
    | some s => exact ⟨s, rfl⟩
  have hdeg := hp.nodes k.1 k.2 a s hn hs
  rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map] at hdeg
  have h := hbase k
  rw [cellBase_of_name ir hs, Pk.node_eq s _ hdeg] at h
  exact h

/-- **The own cells of node `a` lie in its subfield.** -/
theorem ownCellAt_mem (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    {a0 : ir.Cell d → (I (ir.domainField d)).K} (hbase : ∀ k, a0 k ∈ ir.cellBase I d k)
    {a : ℕ} (ha : a < rs.length) (i : ℕ) :
    ir.ownCellAt d rs a0 a i ∈ fixedField (I (ir.domainField d)).K Pk.p rs[a].plan.childDegree := by
  unfold ownCellAt
  split
  · rename_i k hk
    split
    · rename_i hkc
      have hmem := List.mem_of_getElem? hk
      simp only [ownKeys, List.mem_filter, beq_iff_eq] at hmem
      exact cell_mem_node hp hbase (k := ⟨k, hkc⟩) hmem.2 ha
    · exact Subfield.zero_mem _
  · exact Subfield.zero_mem _

/-- **A cell is the own cell of its node at its index.** -/
theorem ownCellAt_idxOf (a0 : ir.Cell d → (I (ir.domainField d)).K) {k : ir.Cell d} {a : ℕ}
    (hn : ir.cellNode (rs.map REdge.plan) k.1 = some a) :
    ir.ownCellAt d rs a0 a ((ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1) = a0 k := by
  have hmem : k.1 ∈ ir.ownKeys d (rs.map REdge.plan) a := by
    simp only [ownKeys, List.mem_filter, hn, beq_self_eq_true, and_true]
    exact k.2
  unfold ownCellAt
  rw [List.getElem?_idxOf hmem]
  simp only [dif_pos k.2]
  rfl

variable [Fintype Pads]

/-- **The honest layout facts of the field tree** (`PEdge.FillSpec`): every group is found at its
slot or its root word (`groupAt_slotOf`, `rootGroupAt_rootOff`); a found group is a child's; the
own values lie in their nodes' subfields (`ownCellAt_mem`, `StageBasis.coord_mem_fixedField`);
a given group's child slots hold the coordinates of the parent's own cell. -/
theorem fillSpec (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    {a0 : ir.Cell d → (I (ir.domainField d)).K} (hbase : ∀ k, a0 k ∈ ir.cellBase I d k) :
    FillSpec (ir.fieldEdges d Pk rs Pads) (ir.treeOwn d rs a0) (ir.treeGiven d rs)
      (ir.groupAt d (rs.map REdge.plan)) (ir.treeRootAt d rs Pads) where
  find b hb j hpar := by
    have hb' : b < (rs.map REdge.plan).length := by
      rw [List.length_map]
      rwa [length_fieldEdges] at hb
    rw [getElem_fieldEdges] at hpar ⊢
    intro g
    exact groupAt_slotOf hb' hpar g.2
  findRoot b hb hpar := by
    have hb' : b < (rs.map REdge.plan).length := by
      rw [List.length_map]
      rwa [length_fieldEdges] at hb
    rw [getElem_fieldEdges] at hpar ⊢
    intro g
    have hlt := rootOff_add_lt (ir := ir) (d := d) hb' hpar g.2
    refine ⟨?_, ?_⟩
    · simp only [plannedEdge, dif_pos hlt, treeRootAt]
      exact rootGroupAt_rootOff hb' hpar g.2
    · change ir.treeGiven d rs b g = false
      simp only [treeGiven]
      rw [show parentIdx (rs.map REdge.plan) b = none from hpar]
  child a s b g h := by
    obtain ⟨hb, hpar, hg, -⟩ := groupAt_spec h
    have hb0 : b < (ir.fieldEdges d Pk rs Pads).length := by
      rw [length_fieldEdges]
      simpa using hb
    refine ⟨hb0, ?_⟩
    rw [getElem_fieldEdges]
    exact ⟨hpar, hg⟩
  own_mem a ha s := by
    have ha' : a < rs.length := by rwa [length_fieldEdges] at ha
    rw [getElem_fieldEdges]
    change ir.treeOwn d rs a0 a s ∈ fixedField _ Pk.p rs[a].plan.childDegree
    unfold treeOwn
    by_cases h1 : s < ir.ownStart d (rs.map REdge.plan) a
    · rw [if_pos h1]
      split
      · rename_i j hj
        rw [dif_pos ha']
        by_cases hd : 0 < rs[a].plan.degree
        · rw [dif_pos hd]
          apply StageBasis.coord_mem_fixedField
          rw [rs[a].kit.top_eq]
          obtain ⟨-, hjl, hjd⟩ := ht.parent a (by simpa using ha') j hj
          have hm := ownCellAt_mem hp hbase (a := j) (by simpa using hjl)
            (s / rs[a].plan.degree)
          simp only [List.getElem_map] at hjd
          rwa [← hjd]
        · rw [dif_neg hd]
          exact Subfield.zero_mem _
      · exact Subfield.zero_mem _
    · rw [if_neg h1]
      split_ifs
      · exact ownCellAt_mem hp hbase ha' _
      · exact Subfield.zero_mem _
  given_coord b hb j hpar := by
    have hb' : b < rs.length := by rwa [length_fieldEdges] at hb
    have hbm : b < (rs.map REdge.plan).length := by simpa using hb'
    rw [getElem_fieldEdges] at hpar ⊢
    intro g hg i
    change parentIdx (rs.map REdge.plan) b = some j at hpar
    have hgv : viewChild (rs.map REdge.plan) j = some b ∧ (g : ℕ) < ir.own d (rs.map REdge.plan) j := by
      change ir.treeGiven d rs b g = true at hg
      simp only [treeGiven, hpar, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      exact hg
    have hdeg : 0 < rs[b].plan.degree := by
      have := ht.deg_pos b hbm
      simpa using this
    have hgb : ir.given d (rs.map REdge.plan) b = ir.own d (rs.map REdge.plan) j := by
      simp only [given, hpar, hgv.1, ↓reduceIte]
    have hi : (i : ℕ) < rs[b].plan.degree := i.2
    have hlt : (g : ℕ) * rs[b].plan.degree + i < ir.ownStart d (rs.map REdge.plan) b := by
      unfold ownStart
      rw [hgb, List.getD_eq_getElem _ _ hbm, List.getElem_map]
      have : (g : ℕ) + 1 ≤ ir.own d (rs.map REdge.plan) j := hgv.2
      nlinarith
    change slotVal (ir.fieldEdges d Pk rs Pads) (ir.treeOwn d rs a0) (ir.treeGiven d rs)
        (ir.groupAt d (rs.map REdge.plan)) b (g * rs[b].plan.degree + i) =
      rs[b].kit.basis.coord (ir.treeOwn d rs a0 j (ir.slotOf d (rs.map REdge.plan) b g)) i
    rw [slotVal_eq, groupAt_eq_none fun c hc => lt_of_lt_of_le hlt (ownStart_le_slotOf hc)]
    simp only
    rw [slotOf_view hpar hgv.1]
    unfold treeOwn
    rw [if_pos hlt, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    simp only [hpar, dif_pos hb', dif_pos hdeg]
    congr 2
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hdeg, Nat.div_eq_of_lt hi, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- **The logical assignment of the honest committed cells** is the honest slots' fill
(`PEdge.level_view_fill`, `PEdge.wordsAt_slotVal`). -/
theorem treeLevel_view_treeHonestCells (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) {a0 : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a0 k ∈ ir.cellBase I d k) (pre : Fin (npOf Pk rs) → (I (ir.domainField d)).K)
    (mask : MaskOwn Pk rs → (I (ir.domainField d)).K) (pad : Pads → (I (ir.domainField d)).K) :
    (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad) =
      fill (ir.honestSlots d rs Pads a0) (ir.treeHonestCells d rs Pads a0 pre mask pad) 0
        (ir.fieldEdges d Pk rs Pads) := by
  have h := level_view_fill (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) 0 Fin.elim0
    (ir.honestSlots d rs Pads a0) (ir.treeHonestCells d rs Pads a0 pre mask pad)
    (ir.shapedAt_fieldEdges d Pads ht)
    (wordsAt_slotVal (ir.treeBase d rs Pads a0 pre mask pad) (ir.shapedAt_fieldEdges d Pads ht)
      (fillSpec ht hp hbase))
  have hc : fill (ir.honestSlots d rs Pads a0) (ir.treeHonestCells d rs Pads a0 pre mask pad) 0
      (ir.fieldEdges d Pk rs Pads) ∘ cellIn (ir.fieldEdges d Pk rs Pads) =
        ir.treeHonestCells d rs Pads a0 pre mask pad :=
    funext fun i => fill_cellIn _ _ 0 _ i
  rw [hc] at h
  exact h

/-- **The honest committed cells decode to the cells**: a root cell is its committed cell; a cell
at a node is its slot's own value (`ownCellAt_idxOf`), a given group of the node's view child when
it has one. -/
theorem treeDecode_treeHonestCells (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) {a0 : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a0 k ∈ ir.cellBase I d k) (pre : Fin (npOf Pk rs) → (I (ir.domainField d)).K)
    (mask : MaskOwn Pk rs → (I (ir.domainField d)).K) (pad : Pads → (I (ir.domainField d)).K) :
    ir.treeDecode d rs Pads (ir.treeHonestCells d rs Pads a0 pre mask pad) = a0 := by
  funext k
  unfold treeDecode
  rw [treeLevel_view_treeHonestCells ht hp hbase]
  unfold place
  split
  · rw [fill_cellIn]
    rfl
  · rename_i a hn
    obtain ⟨s, hs, ha⟩ : ∃ s, ir.cellName k.1 = some s ∧ nodeIdx (rs.map REdge.plan) s = some a := by
      unfold cellNode at hn
      cases h : ir.cellName k.1 with
      | none => rw [h] at hn; cases hn
      | some s => rw [h] at hn; exact ⟨s, rfl, hn⟩
    obtain ⟨hal, -⟩ := nodeIdx_spec ha
    have hal' : a < rs.length := by simpa using hal
    have hal0 : a < (ir.fieldEdges d Pk rs Pads).length := by rwa [length_fieldEdges]
    have hidx := idxOf_lt_own ir hn
    have hrange := ownStart_add_lt ir ht hal hidx
    rw [List.getD_eq_getElem _ _ hal, List.getElem_map] at hrange
    rw [fill_slotAt _ _ _ 0 _ a _ hal0 (by rw [getElem_fieldEdges]; exact hrange), Nat.zero_add]
    unfold honestSlots
    rw [slotVal_eq]
    have hown : ir.treeOwn d rs a0 a (ir.ownStart d (rs.map REdge.plan) a +
        (ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1) = a0 k := by
      unfold treeOwn
      rw [if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), if_pos (Nat.add_lt_add_left hidx _),
        Nat.add_sub_cancel_left]
      exact ownCellAt_idxOf a0 hn
    cases hv : viewChild (rs.map REdge.plan) a with
    | some b =>
      obtain ⟨hbl, hbp, -⟩ := viewChild_spec hv
      have hng : (ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1 < ir.ngOf d (rs.map REdge.plan) b :=
        lt_of_lt_of_le hidx ((own_le_baseOf (d := d) ir ht a).trans_eq (baseOf_view hv))
      have hg := groupAt_slotOf hbl hbp hng
      rw [slotOf_view hbp hv] at hg
      rw [hg]
      have hba : b < a := (ht.parent b hbl a hbp).1
      have hb0 : b < (ir.fieldEdges d Pk rs Pads).length := by
        rw [length_fieldEdges]
        simpa using hbl
      have hgv : ir.treeGiven d rs b ((ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1) = true := by
        simp only [treeGiven, hbp, hv, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
        exact hidx
      simp only [hba, ↓reduceDIte, List.getElem?_eq_getElem hb0, hgv, ↓reduceIte]
      exact hown
    | none =>
      have hg : ir.groupAt d (rs.map REdge.plan) a (ir.ownStart d (rs.map REdge.plan) a +
          (ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1) = none :=
        groupAt_eq_none fun c hc => by
          have hvc : viewChild (rs.map REdge.plan) a ≠ some c := by
            rw [hv]
            exact (Option.some_ne_none c).symm
          rw [slotOf_other hc hvc, baseOf_none hv]
          unfold own at hidx
          unfold own
          omega
      rw [hg]
      exact hown

/-- **The honest cells agree off the prefix, the masks and the pads**: at the spare cell, the root
cells and the root words they are those of any other choice of the given values. -/
theorem treeHonestCells_congr {a0 : ir.Cell d → (I (ir.domainField d)).K}
    {pre pre' : Fin (npOf Pk rs) → (I (ir.domainField d)).K} {mask mask' : MaskOwn Pk rs → (I (ir.domainField d)).K}
    {pad pad' : Pads → (I (ir.domainField d)).K} {i : ir.TreeCell d Pk rs Pads}
    (hi : ∀ j, i ≠ .inl j) (hm : ∀ o, i ≠ .inr (.inr (.mask o))) (hq : ∀ q, i ≠ .inr (.inr (.pad q))) :
    ir.treeHonestCells d rs Pads a0 pre mask pad i = ir.treeHonestCells d rs Pads a0 pre' mask' pad' i := by
  refine cellVal_congr (h := ?_) ..
  rcases i with j | w | (_ | k | o | q)
  · exact absurd rfl (hi j)
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (hm o)
  · exact absurd rfl (hq q)

/-- **The logical assignment of the honest cells at a slot or a cell other than the prefix, the
masks and the pads** does not depend on the given values (`fill_slotAt_congr`). -/
theorem honestView_congr (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) {a0 : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a0 k ∈ ir.cellBase I d k)
    (pre pre' : Fin (npOf Pk rs) → (I (ir.domainField d)).K) (mask mask' : MaskOwn Pk rs → (I (ir.domainField d)).K)
    (pad pad' : Pads → (I (ir.domainField d)).K) :
    (∀ j s, (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad)
        (slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) j s) =
      (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre' mask' pad')
        (slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) j s)) ∧
    (∀ i : ir.TreeCell d Pk rs Pads, (∀ j, i ≠ .inl j) → (∀ o, i ≠ .inr (.inr (.mask o))) →
      (∀ q, i ≠ .inr (.inr (.pad q))) →
      (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad)
          (cellIn (ir.fieldEdges d Pk rs Pads) i) =
        (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre' mask' pad')
          (cellIn (ir.fieldEdges d Pk rs Pads) i)) := by
  rw [treeLevel_view_treeHonestCells ht hp hbase, treeLevel_view_treeHonestCells ht hp hbase]
  refine ⟨fun j s => fill_slotAt_congr _ _ (treeHonestCells_congr (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => by cases h)) 0 _ j s, fun i hi hm hq => ?_⟩
  rw [fill_cellIn, fill_cellIn]
  exact treeHonestCells_congr hi hm hq

/-- **The honest cells' cells and bits do not depend on the given values**: their coordinates are
slots, root cells and the spare cell (`place`, `viewPlace`). -/
theorem honestView_place (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) {a0 : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a0 k ∈ ir.cellBase I d k)
    (pre pre' : Fin (npOf Pk rs) → (I (ir.domainField d)).K) (mask mask' : MaskOwn Pk rs → (I (ir.domainField d)).K)
    (pad pad' : Pads → (I (ir.domainField d)).K) :
    (∀ k, (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad) (ir.place d rs Pads k) =
      (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre' mask' pad') (ir.place d rs Pads k)) ∧
    (∀ k j, (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad)
        (ir.viewPlace d rs Pads k j) =
      (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre' mask' pad')
        (ir.viewPlace d rs Pads k j)) := by
  obtain ⟨hs, hc⟩ := honestView_congr ht hp hbase pre pre' mask mask' pad pad'
  refine ⟨fun k => ?_, fun k j => ?_⟩
  · unfold place
    split
    · exact hc _ (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    · exact hs _ _
  · unfold viewPlace
    split
    · split
      · exact hs _ _
      · exact hc _ (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    · exact hc _ (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)

/-- **The honest cells' words do not depend on the given values** (`fill_isWord_congr`): the
words are slots, root words and the spare cell. -/
theorem honestView_word (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) {a0 : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a0 k ∈ ir.cellBase I d k)
    (pre pre' : Fin (npOf Pk rs) → (I (ir.domainField d)).K) (mask mask' : MaskOwn Pk rs → (I (ir.domainField d)).K)
    (pad pad' : Pads → (I (ir.domainField d)).K) (nc : ℕ) (r : Fin nc → Finset ℕ)
    (z : ir.TLog d rs Pads)
    (hz : (PEdge.path (ir.spareCell d Pk rs Pads) 0 (ir.fieldEdges d Pk rs Pads) nc r).IsWord z) :
    (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre mask pad) z =
      (ir.treeLevel d rs Pads).view (ir.treeHonestCells d rs Pads a0 pre' mask' pad') z := by
  rw [treeLevel_view_treeHonestCells ht hp hbase, treeLevel_view_treeHonestCells ht hp hbase]
  refine fill_isWord_congr _ _ (treeHonestCells_congr (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h))
    0 _ (fun e he g => ?_) nc r z hz
  obtain ⟨a, r, -, rfl⟩ := List.mem_mapIdx.1 he
  simp only [plannedEdge]
  split
  · exact treeHonestCells_congr (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  · exact treeHonestCells_congr (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)

end Honest

end

end GordieHowe.RealizedProgram
