-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldPacking
public import GordieHowe.Language.RealizedProgram.Views

@[expose] public section

/-!
# GordieHowe: a domain's packing tree read from its plan

The packing tree of domain `d` (`PEdge.treeSpec`) from the plan's edges (`GordieHowe.RealizedProgram.Export.Domain.packing`,
in processing order) and the field's packing facts (`FieldInterp.Packing`), for any tree:

* **the realized edges** (`GordieHowe.RealizedProgram.realizedEdges`): each plan edge with the field's edge kit for
  its child degree, relative degree and mode;
* **the nodes** (`GordieHowe.RealizedProgram.parentIdx`, `GordieHowe.RealizedProgram.cellNode`): an edge's parent is the edge whose child
  it names (`none`: the root); a cell lies at the node of its value (`Value.node`), of its pad's
  space, or at the root (no node, the whole field, a filler input);
* **the slots of a node** (child of edge `a`, from slot `0`): the given region (`given a · d_a`
  slots, when `a` is the view child of its parent: the coordinates of the parent's own cells), the
  node's own cells (`ownKeys`; with a view child `b`, they are `b`'s first groups and the region
  holds all of `b`'s groups), then the groups of the other children in increasing order. The view
  child of a node (`viewChild`) is its bit edge (`F_2 <16`, squaring-chain masks), whose groups
  decode the node's own cells into the bits that bit views read;
* **the groups** (`GordieHowe.RealizedProgram.ngOf`): `⌈slots / d⌉` per edge, computed children first (fuel
  recursion, `ngFuel`);
* **the committed cells** (`GordieHowe.RealizedProgram.TreeCell`): the tree layout `[prefix | words | root own]`
  (`TreeLayout.Coord`) with the masks' prefix cells, the root children's words, and the root own
  cells: a spare cell, the cells at the root, the masks' own cells and the masked reduction's pads `Pads`;
* **the tree** (`GordieHowe.RealizedProgram.fieldEdges`, `GordieHowe.RealizedProgram.fieldTree`): the planned edges, a member of the
  class `𝒯(K, S0)` over the field's masking subfield on the tree layout.
-/

namespace GordieHowe.RealizedProgram

open Export PackingStage RelativePacking Ligero.MaskRow PEdge

section

variable (ir : RealizedProgram) (I : Interp) (d : ℕ)

/-! ## The realized edges -/

/-- **A plan edge realized in a field**: the edge and the field's kit for it. -/
structure REdge (F : FieldInterp) (Pk : F.Packing) where
  /-- The plan edge. -/
  plan : PackingEdge
  /-- The field's kit. -/
  kit : EdgeKit F.K Pk.p Pk.S0 plan.childDegree plan.degree

/-- **The realized edges of a plan domain**: each edge the field realizes, with its kit. -/
def realizedEdges {F : FieldInterp} (Pk : F.Packing) (es : List PackingEdge) : List (REdge F Pk) :=
  es.filterMap fun e => (Pk.edge e.childDegree e.degree e.mode).map fun k => ⟨e, k⟩

/-! ## Nodes -/

/-- The edge read outside a list of edges: no child, no parent, degree `0`. -/
def noEdge : PackingEdge := ⟨"", "", .subfieldMasks, 0, 0, 0, 0, 0, 0, true, 0⟩

/-- **The parent edge of edge `a`**: the edge whose child is `a`'s parent (`none`: the root). -/
def parentIdx (es : List PackingEdge) (a : ℕ) : Option ℕ :=
  es.findIdx? fun e => e.child == (es.getD a noEdge).parent

/-- **The edge whose child is node `name`**. -/
def nodeIdx (es : List PackingEdge) (name : String) : Option ℕ :=
  es.findIdx? fun e => e.child == name

/-- **The node name of a cell**: its value's node, its pad's space, none for a filler input or a
value at no node. -/
def cellName : CellKey → Option String
  | .val v _ => (ir.value v).node.map (·.name)
  | .pad v _ =>
    match (ir.value v).padSpace with
    | .full => none
    | .node s => some s
  | .filler _ _ => none

/-- **The node of a cell**: the edge whose child is the cell's node, `none` for the root. -/
def cellNode (es : List PackingEdge) (k : CellKey) : Option ℕ :=
  (ir.cellName k).bind (nodeIdx es)

/-- **The own cells of node `a`** (the child of edge `a`), in the order of the cell keys. -/
def ownKeys (es : List PackingEdge) (a : ℕ) : List CellKey :=
  (ir.cellKeys d).filter fun k => ir.cellNode es k == some a

/-- The number of own cells of node `a`. -/
def own (es : List PackingEdge) (a : ℕ) : ℕ := (ir.ownKeys d es a).length

/-- **A view edge**: a bit edge `F_2 <16` with squaring-chain masks under a non-root parent; its
groups decode the parent's own cells into their bits. -/
def isView (es : List PackingEdge) (b : ℕ) : Bool :=
  (es.getD b noEdge).childDegree == 1 && (es.getD b noEdge).degree == 16 &&
    (es.getD b noEdge).mode == .squaringChain && (parentIdx es b).isSome

/-- **The view child of node `a`**: its first view edge. -/
def viewChild (es : List PackingEdge) (a : ℕ) : Option ℕ :=
  (List.range es.length).find? fun b => parentIdx es b == some a && isView es b

/-- **Edge `b` is a non-view child of node `a`.** -/
def otherChild (es : List PackingEdge) (a b : ℕ) : Bool :=
  parentIdx es b == some a && viewChild es a != some b

/-- **The given groups of edge `a`**: the parent's own cells, when `a` is the view child of its
parent; none otherwise. -/
def given (es : List PackingEdge) (a : ℕ) : ℕ :=
  match parentIdx es a with
  | some j => if viewChild es j = some a then ir.own d es j else 0
  | none => 0

/-! ## Groups -/

/-- **The groups of every edge with fuel `f`**: `⌈slots / d⌉`, the slots the given region, the
own region (the view child's groups, else the own cells) and the other children's groups. -/
def ngFuel (es : List PackingEdge) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, a =>
    let dg := (es.getD a noEdge).degree
    let base := match viewChild es a with
      | some b => ngFuel es f b
      | none => ir.own d es a
    let others := ((List.range a).filter (otherChild es a)).map (ngFuel es f)
    (ir.given d es a * dg + base + others.sum + dg - 1) / dg

/-- **The groups of edge `a`.** -/
def ngOf (es : List PackingEdge) (a : ℕ) : ℕ := ir.ngFuel d es (a + 1) a

/-- **The start of the own region of node `a`**: after the given region. -/
def ownStart (es : List PackingEdge) (a : ℕ) : ℕ := ir.given d es a * (es.getD a noEdge).degree

/-- **The size of the own region of node `a`**: the view child's groups, else the own cells. -/
def baseOf (es : List PackingEdge) (a : ℕ) : ℕ :=
  match viewChild es a with
  | some b => ir.ngOf d es b
  | none => ir.own d es a

/-- **The offset of child `b` among the other children of node `a`**. -/
def otherOff (es : List PackingEdge) (a b : ℕ) : ℕ :=
  (((List.range b).filter (otherChild es a)).map (ir.ngOf d es)).sum

/-- **The parent's slot holding group `g` of edge `b`**: in the own region for the view child, after
it for another child. -/
def slotOf (es : List PackingEdge) (b g : ℕ) : ℕ :=
  match parentIdx es b with
  | some a =>
    if viewChild es a = some b then ir.ownStart d es a + g
    else ir.ownStart d es a + ir.baseOf d es a + ir.otherOff d es a b + g
  | none => g

/-- **The offset of root child `b` among the root's children**. -/
def rootOff (es : List PackingEdge) (b : ℕ) : ℕ :=
  (((List.range b).filter fun b' => (parentIdx es b').isNone).map (ir.ngOf d es)).sum

/-- **The root's committed words**: the groups of every root child. -/
def nwOf (es : List PackingEdge) : ℕ := ir.rootOff d es es.length

/-! ## The committed cells -/

/-- **The cells at the root.** -/
def RootCell (es : List PackingEdge) : Type := {k : ir.Cell d // ir.cellNode es k.1 = none}

instance (es : List PackingEdge) : Fintype (ir.RootCell d es) :=
  inferInstanceAs (Fintype {k : ir.Cell d // ir.cellNode es k.1 = none})

instance (es : List PackingEdge) : DecidableEq (ir.RootCell d es) :=
  inferInstanceAs (DecidableEq {k : ir.Cell d // ir.cellNode es k.1 = none})

/-- The cells at the root are encoded as cells. -/
instance (es : List PackingEdge) : Encodable (ir.RootCell d es) :=
  inferInstanceAs (Encodable {k : ir.Cell d // ir.cellNode es k.1 = none})

variable {I d}

variable {F : FieldInterp} (Pk : F.Packing)

/-- **The masks' prefix cells of every realized edge before `a`.** -/
def preOff (rs : List (REdge F Pk)) (a : ℕ) : ℕ :=
  ((rs.take a).map fun r => r.kit.masks.nPre).sum

/-- **The masks' prefix cells**: those of every realized edge. -/
def npOf (rs : List (REdge F Pk)) : ℕ := preOff Pk rs rs.length

/-- **The masks' own cells of every realized edge.** -/
def MaskOwn (rs : List (REdge F Pk)) : Type := Σ a : Fin rs.length, Fin rs[a].kit.masks.nOwn

instance (rs : List (REdge F Pk)) : Fintype (MaskOwn Pk rs) :=
  inferInstanceAs (Fintype (Σ a : Fin rs.length, Fin rs[a].kit.masks.nOwn))

instance (rs : List (REdge F Pk)) : DecidableEq (MaskOwn Pk rs) :=
  inferInstanceAs (DecidableEq (Σ a : Fin rs.length, Fin rs[a].kit.masks.nOwn))

/-- The masks' own cells are encoded as the sigma type. -/
instance (rs : List (REdge F Pk)) : Encodable (MaskOwn Pk rs) :=
  inferInstanceAs (Encodable (Σ a : Fin rs.length, Fin rs[a].kit.masks.nOwn))

variable (d)

/-- **A root own cell**: a spare cell (the totality fallback of the tree's word maps), a cell at
the root, a mask's own cell, or a pad of the masked reduction. -/
inductive RootOwn (rs : List (REdge F Pk)) (Pads : Type) where
  /-- The spare cell. -/
  | spare
  /-- A cell at the root. -/
  | cell (k : ir.RootCell d (rs.map REdge.plan))
  /-- A mask's own cell. -/
  | mask (o : MaskOwn Pk rs)
  /-- A pad of the masked reduction. -/
  | pad (π : Pads)
  deriving DecidableEq

/-- The root own cells as a sum: the spare cell, the cells at the root, the masks' own cells and
the pads. -/
def RootOwn.equivSum (rs : List (REdge F Pk)) (Pads : Type) :
    ir.RootOwn d Pk rs Pads ≃ Unit ⊕ ir.RootCell d (rs.map REdge.plan) ⊕ MaskOwn Pk rs ⊕ Pads where
  toFun
    | .spare => .inl ()
    | .cell k => .inr (.inl k)
    | .mask o => .inr (.inr (.inl o))
    | .pad π => .inr (.inr (.inr π))
  invFun
    | .inl _ => .spare
    | .inr (.inl k) => .cell k
    | .inr (.inr (.inl o)) => .mask o
    | .inr (.inr (.inr π)) => .pad π
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ <;> rfl

instance (rs : List (REdge F Pk)) (Pads : Type) [Fintype Pads] :
    Fintype (ir.RootOwn d Pk rs Pads) :=
  Fintype.ofEquiv _ (RootOwn.equivSum ir d Pk rs Pads).symm

/-- The root own cells are encoded as a sum (`RootOwn.equivSum`). -/
instance (rs : List (REdge F Pk)) (Pads : Type) [Encodable Pads] :
    Encodable (ir.RootOwn d Pk rs Pads) :=
  Encodable.ofEquiv _ (RootOwn.equivSum ir d Pk rs Pads)

/-- **The committed cells of domain `d`**: the tree layout `[prefix | words | root own]`. -/
abbrev TreeCell (rs : List (REdge F Pk)) (Pads : Type) : Type :=
  TreeLayout.Coord (npOf Pk rs) (ir.nwOf d (rs.map REdge.plan)) (ir.RootOwn d Pk rs Pads)

/-- The spare cell. -/
def spareCell (rs : List (REdge F Pk)) (Pads : Type) : ir.TreeCell d Pk rs Pads :=
  .inr (.inr .spare)

/-- **The planned edge at position `a`** (see the module docstring). -/
def plannedEdge (rs : List (REdge F Pk)) (Pads : Type) (a : ℕ) (r : REdge F Pk) :
    PEdge F.K (ir.TreeCell d Pk rs Pads) Pk.p Pk.S0 where
  m := r.plan.childDegree
  d := r.plan.degree
  kit := r.kit
  ng := ir.ngOf d (rs.map REdge.plan) a
  parent := parentIdx (rs.map REdge.plan) a
  slot g := ir.slotOf d (rs.map REdge.plan) a g
  rootWord g :=
    if h : ir.rootOff d (rs.map REdge.plan) a + g < ir.nwOf d (rs.map REdge.plan) then
      .inr (.inl ⟨_, h⟩)
    else ir.spareCell d Pk rs Pads
  maskPre j := if h : preOff Pk rs a + j < npOf Pk rs then .inl ⟨_, h⟩ else ir.spareCell d Pk rs Pads
  maskOwn j :=
    if h : a < rs.length then
      if h' : r.kit.masks.nOwn = rs[a].kit.masks.nOwn then .inr (.inr (.mask ⟨⟨a, h⟩, j.cast h'⟩))
      else ir.spareCell d Pk rs Pads
    else ir.spareCell d Pk rs Pads

/-- **The planned edges of domain `d`**. -/
def fieldEdges (rs : List (REdge F Pk)) (Pads : Type) :
    List (PEdge F.K (ir.TreeCell d Pk rs Pads) Pk.p Pk.S0) :=
  rs.mapIdx (ir.plannedEdge d Pk rs Pads)

/-! ## The tree check -/

variable {d}

/-- **The tree condition on the plan's edges** (`Export.Domain.IsTree` with degrees): every
parent comes later and spans its child's edge, every root child spans the field (degree `n`),
every relative degree is positive. -/
structure TreeOk (es : List PackingEdge) (n : ℕ) : Prop where
  /-- A parent comes later and its child has degree `m d`. -/
  parent : ∀ (b : ℕ) (hb : b < es.length) (j : ℕ), parentIdx es b = some j → b < j ∧
    ∃ hj : j < es.length, es[j].childDegree = es[b].childDegree * es[b].degree
  /-- A root child spans the field. -/
  root : ∀ (b : ℕ) (hb : b < es.length), parentIdx es b = none →
    es[b].childDegree * es[b].degree = n
  /-- Every relative degree is positive. -/
  deg_pos : ∀ (b : ℕ) (hb : b < es.length), 0 < es[b].degree

/-- **The tree condition as a test.** -/
def treeOkB (es : List PackingEdge) (n : ℕ) : Bool :=
  (List.finRange es.length).all fun b =>
    decide (0 < es[b].degree) &&
      match parentIdx es b with
      | none => es[b].childDegree * es[b].degree == n
      | some j => decide (b < j) &&
          if hj : j < es.length then es[j].childDegree == es[b].childDegree * es[b].degree
          else false

theorem parentIdx_lt {es : List PackingEdge} {b j : ℕ} (h : parentIdx es b = some j) :
    j < es.length := by
  unfold parentIdx at h
  exact List.findIdx?_eq_some_iff_getElem.1 h |>.1

theorem TreeOk.of_treeOkB {es : List PackingEdge} {n : ℕ} (h : treeOkB es n = true) :
    TreeOk es n := by
  simp only [treeOkB, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at h
  refine ⟨fun b hb j hp => ?_, fun b hb hp => ?_, fun b hb => (h ⟨b, hb⟩).1⟩
  · have h2 := (h ⟨b, hb⟩).2
    have hj := parentIdx_lt hp
    simp only [Fin.getElem_fin, hp, hj, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h2
    exact ⟨h2.1, hj, h2.2⟩
  · have h2 := (h ⟨b, hb⟩).2
    simp only [Fin.getElem_fin, hp, beq_iff_eq] at h2
    exact h2

theorem viewChild_spec {es : List PackingEdge} {a b : ℕ} (h : viewChild es a = some b) :
    b < es.length ∧ parentIdx es b = some a ∧ isView es b = true := by
  unfold viewChild at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_range.1 hm, hp.1, hp.2⟩

/-- **A filtered sum over `range (n + 1)`** adds the last term when it passes the filter. -/
theorem sum_filter_range_succ (P : ℕ → Bool) (f : ℕ → ℕ) (n : ℕ) :
    (((List.range (n + 1)).filter P).map f).sum =
      (((List.range n).filter P).map f).sum + if P n then f n else 0 := by
  rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
  by_cases h : P n <;> simp [List.filter_cons, h]

/-- A filtered sum over `range n` is monotone in `n`. -/
theorem sum_filter_range_mono (P : ℕ → Bool) (f : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') :
    (((List.range n).filter P).map f).sum ≤ (((List.range n').filter P).map f).sum := by
  induction n', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n' _ ih => rw [sum_filter_range_succ]; omega

/-- **A term passing the filter lies within the filtered sum after it.** -/
theorem sum_filter_range_add_le (P : ℕ → Bool) (f : ℕ → ℕ) {b n : ℕ} (hb : b < n) (hP : P b = true) :
    (((List.range b).filter P).map f).sum + f b ≤ (((List.range n).filter P).map f).sum := by
  have h1 := sum_filter_range_succ P f b
  rw [if_pos hP] at h1
  rw [← h1]
  exact sum_filter_range_mono P f hb

variable (d) in
/-- **The groups are independent of the fuel** above the edge's position, when parents come
later. -/
theorem ngFuel_stable {es : List PackingEdge} {n : ℕ} (ht : TreeOk es n) :
    ∀ b f f', b < f → b < f' → ir.ngFuel d es f b = ir.ngFuel d es f' b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ f₀, f = f₀ + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f₀, f' = f₀ + 1 := ⟨f' - 1, by omega⟩
    simp only [ngFuel]
    have hbase : (match viewChild es b with
        | some c => ir.ngFuel d es f c
        | none => ir.own d es b) =
        (match viewChild es b with
        | some c => ir.ngFuel d es f' c
        | none => ir.own d es b) := by
      split
      · rename_i c hc
        obtain ⟨hcl, hcp, -⟩ := viewChild_spec hc
        have hcb := (ht.parent c hcl b hcp).1
        exact ih c hcb f f' (by omega) (by omega)
      · rfl
    have hoth : ((List.range b).filter (otherChild es b)).map (ir.ngFuel d es f) =
        ((List.range b).filter (otherChild es b)).map (ir.ngFuel d es f') :=
      List.map_congr_left fun c hc => by
        have hcb := List.mem_range.1 (List.mem_filter.1 hc).1
        exact ih c hcb f f' (by omega) (by omega)
    rw [hbase, hoth]

variable (d) in
/-- The sum of the other children's groups of node `a`. -/
def othersSum (es : List PackingEdge) (a : ℕ) : ℕ :=
  (((List.range a).filter (otherChild es a)).map (ir.ngOf d es)).sum

variable (d) in
/-- **The groups of an edge**: `⌈slots / d⌉`, the slots the given region, the own region and the
other children's groups. -/
theorem ngOf_eq {es : List PackingEdge} {n : ℕ} (ht : TreeOk es n) (a : ℕ) :
    ir.ngOf d es a = (ir.ownStart d es a + ir.baseOf d es a + ir.othersSum d es a +
      (es.getD a noEdge).degree - 1) / (es.getD a noEdge).degree := by
  simp only [ngOf, ngFuel, ownStart, baseOf, othersSum]
  have hbase : (match viewChild es a with
      | some c => ir.ngFuel d es a c
      | none => ir.own d es a) =
      (match viewChild es a with
      | some c => ir.ngFuel d es (c + 1) c
      | none => ir.own d es a) := by
    split
    · rename_i c hc
      obtain ⟨hcl, hcp, -⟩ := viewChild_spec hc
      have hca := (ht.parent c hcl a hcp).1
      exact ngFuel_stable ir d ht c a (c + 1) hca (by omega)
    · rfl
  have hoth : ((List.range a).filter (otherChild es a)).map (ir.ngFuel d es a) =
      ((List.range a).filter (otherChild es a)).map fun c => ir.ngFuel d es (c + 1) c :=
    List.map_congr_left fun c hc => by
      have hca := List.mem_range.1 (List.mem_filter.1 hc).1
      exact ngFuel_stable ir d ht c a (c + 1) hca (by omega)
  rw [hbase, hoth]
  rfl

theorem le_ceil_mul {s q : ℕ} (hq : 0 < q) : s ≤ (s + q - 1) / q * q := by
  have := Nat.div_add_mod (s + q - 1) q
  have := Nat.mod_lt (s + q - 1) hq
  have h2 : (s + q - 1) / q * q = q * ((s + q - 1) / q) := Nat.mul_comm _ _
  omega

variable (d) in
/-- **The slots of a node hold its children's groups**: group `g` of child `b` of node `a` lies
below `ngOf a · d_a`. -/
theorem slotOf_lt {es : List PackingEdge} {n : ℕ} (ht : TreeOk es n) {b a : ℕ}
    (hb : b < es.length) (hp : parentIdx es b = some a) {g : ℕ} (hg : g < ir.ngOf d es b) :
    ir.slotOf d es b g < ir.ngOf d es a * (es.getD a noEdge).degree := by
  obtain ⟨hba, hal, -⟩ := ht.parent b hb a hp
  have hdeg : 0 < (es.getD a noEdge).degree := by
    rw [List.getD_eq_getElem _ _ hal]
    exact ht.deg_pos a hal
  rw [ngOf_eq ir d ht a]
  refine lt_of_lt_of_le ?_ (le_ceil_mul hdeg)
  simp only [slotOf, hp]
  split
  · rename_i hv
    have : ir.baseOf d es a = ir.ngOf d es b := by simp only [baseOf, hv]
    omega
  · rename_i hv
    have hoc : otherChild es a b = true := by
      simp only [otherChild, hp, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq, hv,
        not_false_eq_true]
    have := sum_filter_range_add_le (otherChild es a) (ir.ngOf d es) hba hoc
    simp only [otherOff, othersSum] at *
    omega

variable (d) in
/-- **The root's words hold its children's groups.** -/
theorem rootOff_add_lt {es : List PackingEdge} {b : ℕ} (hb : b < es.length)
    (hp : parentIdx es b = none) {g : ℕ} (hg : g < ir.ngOf d es b) :
    ir.rootOff d es b + g < ir.nwOf d es := by
  have := sum_filter_range_add_le (fun b' => (parentIdx es b').isNone) (ir.ngOf d es) hb
    (by simp [hp])
  simp only [rootOff, nwOf] at *
  omega

/-! ## The tree -/

variable {F : FieldInterp} {Pk : F.Packing}

/-- **The masks' prefix cells of an edge lie in the prefix.** -/
theorem preOff_add_lt {rs : List (REdge F Pk)} {a : ℕ} (ha : a < rs.length)
    {j : ℕ} (hj : j < rs[a].kit.masks.nPre) : preOff Pk rs a + j < npOf Pk rs := by
  have h1 : preOff Pk rs (a + 1) = preOff Pk rs a + rs[a].kit.masks.nPre := by
    simp only [preOff, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
      List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
  have h2 : preOff Pk rs (a + 1) ≤ npOf Pk rs := by
    simp only [npOf, preOff]
    have := List.take_append_drop (a + 1) rs
    calc ((rs.take (a + 1)).map fun r => r.kit.masks.nPre).sum
        ≤ ((rs.take (a + 1)).map fun r => r.kit.masks.nPre).sum +
            ((rs.drop (a + 1)).map fun r => r.kit.masks.nPre).sum := Nat.le_add_right _ _
      _ = (rs.map fun r => r.kit.masks.nPre).sum := by
          rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      _ = ((rs.take rs.length).map fun r => r.kit.masks.nPre).sum := by rw [List.take_length]
  omega

variable (d) in
theorem length_fieldEdges (rs : List (REdge F Pk)) (Pads : Type) :
    (ir.fieldEdges d Pk rs Pads).length = rs.length :=
  List.length_mapIdx

variable (d) in
theorem getElem_fieldEdges (rs : List (REdge F Pk)) (Pads : Type) (a : ℕ)
    (ha : a < (ir.fieldEdges d Pk rs Pads).length) :
    (ir.fieldEdges d Pk rs Pads)[a] =
      ir.plannedEdge d Pk rs Pads a (rs[a]'(by rwa [length_fieldEdges] at ha)) :=
  List.getElem_mapIdx ..

variable (d) in
/-- **The planned edges are shaped** (`PEdge.ShapedAt`), under the tree condition. -/
theorem shapedAt_fieldEdges {rs : List (REdge F Pk)} (Pads : Type)
    (ht : TreeOk (rs.map REdge.plan) Pk.n) : ShapedAt Pk.n (ir.fieldEdges d Pk rs Pads) := by
  intro b hb
  have hb' : b < rs.length := by rwa [length_fieldEdges] at hb
  have hbm : b < (rs.map REdge.plan).length := by rwa [List.length_map]
  rw [getElem_fieldEdges]
  change match parentIdx (rs.map REdge.plan) b with
    | none => _
    | some j => _
  split
  · rename_i hp
    have := ht.root b hbm hp
    simp only [List.getElem_map] at this
    exact this
  · rename_i j hp
    obtain ⟨hbj, hj, hm⟩ := ht.parent b hbm j hp
    have hj' : j < (ir.fieldEdges d Pk rs Pads).length := by
      rwa [length_fieldEdges, ← List.length_map (f := REdge.plan)]
    refine ⟨hbj, hj', ?_, fun g => ?_⟩
    · rw [getElem_fieldEdges]
      simp only [List.getElem_map] at hm
      exact hm
    · rw [getElem_fieldEdges]
      have hl := ir.slotOf_lt d ht hbm hp g.2
      rw [List.getD_eq_getElem _ _ hj] at hl
      simp only [List.getElem_map] at hl
      exact hl

variable (d) in
/-- **The masks' prefix cells are prefix cells** of the tree layout. -/
theorem masksIn_fieldEdges (rs : List (REdge F Pk)) (Pads : Type) :
    MasksIn (TreeLayout.IsPrefix _ _ _) (ir.fieldEdges d Pk rs Pads) := by
  intro e he j
  obtain ⟨a, ha', rfl⟩ := List.mem_mapIdx.1 he
  change TreeLayout.IsPrefix _ _ _
    (if h : preOff Pk rs a + j < npOf Pk rs then .inl ⟨_, h⟩ else ir.spareCell d Pk rs Pads)
  rw [dif_pos (preOff_add_lt ha' j.2)]
  exact ⟨_, rfl⟩

variable (d) in
/-- **The packing tree of domain `d`** read from the realized edges, for `nc` claims reading the
nodes `reads`: a member of the class `𝒯(K, S0)` over the field's masking subfield on the tree
layout, every edge's stage combining the claims that read its child (`PEdge.path`). -/
def fieldTree (rs : List (REdge F Pk)) (Pads : Type) [Fintype Pads] (nc : ℕ)
    (reads : Fin nc → Finset ℕ) (ht : TreeOk (rs.map REdge.plan) Pk.n) :
    TreeSpec F.K Pk.p (ir.TreeCell d Pk rs Pads) Pk.S0 (TreeLayout.IsPrefix _ _ _)
      (Logical (ir.TreeCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads)) nc :=
  treeSpec (ir.spareCell d Pk rs Pads) Pk.top_eq _ _ nc reads (ir.shapedAt_fieldEdges d Pads ht)
    (ir.masksIn_fieldEdges d rs Pads)

/-! ## The cells in the tree -/

section Place

variable (d)
variable {I : Interp} {Pk : (I (ir.domainField d)).Packing}
  (rs : List (REdge (I (ir.domainField d)) Pk)) (Pads : Type)

/-- **The logical coordinates of domain `d`'s tree.** -/
abbrev TLog : Type := Logical (ir.TreeCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads)

/-- The spare cell as a logical coordinate. -/
def spareLog : ir.TLog d rs Pads := cellIn _ (ir.spareCell d Pk rs Pads)

/-- **The coordinate of a cell**: a root own cell at the root, slot `ownStart + i` of its node
for the `i`-th own cell of the node. -/
def place (k : ir.Cell d) : ir.TLog d rs Pads :=
  match h : ir.cellNode (rs.map REdge.plan) k.1 with
  | none => cellIn _ (.inr (.inr (.cell ⟨k, h⟩)))
  | some a => slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) a
      (ir.ownStart d (rs.map REdge.plan) a + (ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1)

/-- **The coordinate of bit `j` of a cell**: coordinate `j` of the cell's group of its node's view
child (the spare cell for a cell with no view child). -/
def viewPlace (k : ir.Cell d) (j : Fin 16) : ir.TLog d rs Pads :=
  match ir.cellNode (rs.map REdge.plan) k.1 with
  | some a =>
    match viewChild (rs.map REdge.plan) a with
    | some b => slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) b
        ((ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1 * 16 + j)
    | none => ir.spareLog d rs Pads
  | none => ir.spareLog d rs Pads

/-- **The logical assignment of domain `d`'s tree** read from the committed cells. -/
def treeLevel : Level (I (ir.domainField d)).K (ir.TreeCell d Pk rs Pads) (ir.TLog d rs Pads) :=
  (PEdge.path (ir.spareCell d Pk rs Pads) 0 (ir.fieldEdges d Pk rs Pads) 0 Fin.elim0).level

/-- **The cells decoded from the committed cells**: each cell's coordinate. -/
def treeDecode (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) :
    ir.Cell d → (I (ir.domainField d)).K :=
  fun k => (ir.treeLevel d rs Pads).view x (ir.place d rs Pads k)

/-- **The bits of the cells decoded from the committed cells**: each bit's coordinate. -/
def treeBits (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) :
    ir.Cell d × Fin 16 → (I (ir.domainField d)).K :=
  fun kj => (ir.treeLevel d rs Pads).view x (ir.viewPlace d rs Pads kj.1 kj.2)

end Place

/-! ## The placement checks -/

variable {I : Interp}

variable (d) in
/-- **The cells' nodes are the field's** (field facts on the plan's names): a cell's node has its
edge's child degree in the field, and a named node at the root is the whole field. -/
structure PlaceOk (Pk : (I (ir.domainField d)).Packing) (es : List PackingEdge) : Prop where
  /-- A cell's node has its edge's child degree. -/
  nodes : ∀ k ∈ ir.cellKeys d, ∀ a s, ir.cellNode es k = some a → ir.cellName k = some s →
    Pk.nodeDeg s = some (es.getD a noEdge).childDegree
  /-- A named node at the root is the whole field. -/
  root : ∀ k ∈ ir.cellKeys d, ir.cellNode es k = none → ∀ s, ir.cellName k = some s →
    Pk.nodeDeg s = some Pk.n

variable (d) in
/-- **The placement checks as a test.** -/
def placeOkB (Pk : (I (ir.domainField d)).Packing) (es : List PackingEdge) : Bool :=
  (ir.cellKeys d).all fun k =>
    match ir.cellName k with
    | none => true
    | some s =>
      match ir.cellNode es k with
      | some a => Pk.nodeDeg s == some (es.getD a noEdge).childDegree
      | none => Pk.nodeDeg s == some Pk.n

theorem PlaceOk.of_placeOkB {Pk : (I (ir.domainField d)).Packing} {es : List PackingEdge}
    (h : ir.placeOkB d Pk es = true) : ir.PlaceOk d Pk es := by
  simp only [placeOkB, List.all_eq_true] at h
  refine ⟨fun k hk a s hn hs => ?_, fun k hk hn s hs => ?_⟩
  · have := h k hk
    simp only [hs, hn, beq_iff_eq] at this
    exact this
  · have := h k hk
    simp only [hs, hn, beq_iff_eq] at this
    exact this

theorem nodeIdx_spec {es : List PackingEdge} {s : String} {a : ℕ} (h : nodeIdx es s = some a) :
    ∃ ha : a < es.length, es[a].child = s := by
  unfold nodeIdx at h
  obtain ⟨ha, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨ha, by simpa using hp⟩

/-- **The base of a named cell is its node's subgroup.** -/
theorem cellBase_of_name {k : ir.Cell d} {s : String} (h : ir.cellName k.1 = some s) :
    ir.cellBase I d k = ((I (ir.domainField d)).node s : Set _) := by
  obtain ⟨⟨v, i⟩ | ⟨v, i⟩ | ⟨c, j⟩, hk⟩ := k
  · simp only [cellName, Option.map_eq_some_iff] at h
    obtain ⟨nr, hnr, rfl⟩ := h
    simp only [cellBase, hnr]
  · simp only [cellName] at h
    simp only [cellBase, FieldInterp.space]
    revert h
    cases (ir.value v).padSpace with
    | full => intro h; cases h
    | node s' => intro h; cases h; rfl
  · cases h

/-- **The base of an unnamed cell is the whole field.** -/
theorem cellBase_of_none {k : ir.Cell d} (h : ir.cellName k.1 = none) :
    ir.cellBase I d k = Set.univ := by
  obtain ⟨⟨v, i⟩ | ⟨v, i⟩ | ⟨c, j⟩, hk⟩ := k
  · simp only [cellName, Option.map_eq_none_iff] at h
    simp only [cellBase, h]
  · simp only [cellName] at h
    simp only [cellBase, FieldInterp.space]
    revert h
    cases (ir.value v).padSpace with
    | full => intro _; simp
    | node s' => intro h; cases h
  · rfl

/-- **A cell of node `a` is an own cell of `a`**, below the own count. -/
theorem idxOf_lt_own {es : List PackingEdge} {k : ir.Cell d} {a : ℕ}
    (h : ir.cellNode es k.1 = some a) :
    (ir.ownKeys d es a).idxOf k.1 < ir.own d es a := by
  apply List.idxOf_lt_length_of_mem
  simp only [ownKeys, List.mem_filter, h, beq_self_eq_true, and_true]
  exact k.2

/-- **The own cells fit the own region**: the view child's groups include the given ones. -/
theorem own_le_baseOf {es : List PackingEdge} {n : ℕ} (ht : TreeOk es n) (a : ℕ) :
    ir.own d es a ≤ ir.baseOf d es a := by
  unfold baseOf
  split
  · rename_i b hb
    obtain ⟨hbl, hbp, -⟩ := viewChild_spec hb
    have hg : ir.given d es b = ir.own d es a := by simp only [given, hbp, hb, ↓reduceIte]
    have hdeg : 0 < (es.getD b noEdge).degree := by
      rw [List.getD_eq_getElem _ _ hbl]
      exact ht.deg_pos b hbl
    rw [ngOf_eq ir d ht b, ← hg]
    apply (Nat.le_div_iff_mul_le hdeg).2
    simp only [ownStart]
    omega
  · exact le_rfl

/-- **The own region lies in the node's slots.** -/
theorem ownStart_add_lt {es : List PackingEdge} {n : ℕ} (ht : TreeOk es n) {a : ℕ}
    (ha : a < es.length) {o : ℕ} (ho : o < ir.own d es a) :
    ir.ownStart d es a + o < ir.ngOf d es a * (es.getD a noEdge).degree := by
  have hdeg : 0 < (es.getD a noEdge).degree := by
    rw [List.getD_eq_getElem _ _ ha]
    exact ht.deg_pos a ha
  rw [ngOf_eq ir d ht a]
  refine lt_of_lt_of_le ?_ (le_ceil_mul hdeg)
  have := own_le_baseOf (d := d) ir ht a
  omega

variable (d) in
/-- **The realized edges carry the field's kits.** -/
def RealizedOk {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk)) :
    Prop :=
  ∀ r ∈ rs, Pk.edge r.plan.childDegree r.plan.degree r.plan.mode = some r.kit

theorem realizedOk_realizedEdges {Pk : (I (ir.domainField d)).Packing} (es : List PackingEdge) :
    ir.RealizedOk d (realizedEdges Pk es) := by
  intro r hr
  obtain ⟨e, -, he⟩ := List.mem_filterMap.1 hr
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 he
  exact hk

/-- **A decoded cell lies in its base** (`RingSwitching.Tree.level_mem`): in its node's subfield, whose
subgroup is the cell's base (`PlaceOk.nodes`); at the root, a cell of the whole field
(`PlaceOk.root`). -/
theorem treeDecode_mem {Pk : (I (ir.domainField d)).Packing}
    {rs : List (REdge (I (ir.domainField d)) Pk)} {Pads : Type} [Fintype Pads]
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) (k : ir.Cell d) :
    ir.treeDecode d rs Pads x k ∈ ir.cellBase I d k := by
  unfold treeDecode place
  split
  · rename_i hn
    cases hs : ir.cellName k.1 with
    | none => rw [cellBase_of_none ir hs]; trivial
    | some s =>
      rw [cellBase_of_name ir hs, Pk.node_eq s Pk.n (hp.root k.1 k.2 hn s hs), Pk.top_eq]
      exact Subfield.mem_top _
  · rename_i a hn
    obtain ⟨s, hs, ha⟩ : ∃ s, ir.cellName k.1 = some s ∧ nodeIdx (rs.map REdge.plan) s = some a := by
      unfold cellNode at hn
      cases h : ir.cellName k.1 with
      | none => rw [h] at hn; cases hn
      | some s => rw [h] at hn; exact ⟨s, rfl, hn⟩
    obtain ⟨hal, hch⟩ := nodeIdx_spec ha
    have hal' : a < (ir.fieldEdges d Pk rs Pads).length := by
      rwa [length_fieldEdges, ← List.length_map (f := REdge.plan)]
    have hrange := ownStart_add_lt ir ht hal (idxOf_lt_own ir hn)
    rw [List.getD_eq_getElem _ _ hal] at hrange
    have hmem := RingSwitching.Tree.level_mem _ (ir.fieldTree d rs Pads 0 Fin.elim0 ht).nested x
      (slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) a
        (ir.ownStart d (rs.map REdge.plan) a + (ir.ownKeys d (rs.map REdge.plan) a).idxOf k.1))
    change _ ∈ (PEdge.path (ir.spareCell d Pk rs Pads) 0 (ir.fieldEdges d Pk rs Pads) 0
      Fin.elim0).field _ at hmem
    rw [field_slotAt _ 0 _ 0 _ a _ hal' (by
      rw [getElem_fieldEdges]
      simp only [List.getElem_map] at hrange
      exact hrange)] at hmem
    have hdeg := hp.nodes k.1 k.2 a s hn hs
    rw [List.getD_eq_getElem _ _ hal] at hdeg
    rw [cellBase_of_name ir hs, Pk.node_eq s _ hdeg]
    rw [getElem_fieldEdges] at hmem
    simp only [List.getElem_map] at hmem ⊢
    exact hmem

/-- **The bits of a viewed cell decoded from the committed cells are the cell's bits**: bit `j` of
own cell `o` of node `a` is coordinate `j` of group `o` of `a`'s view child `b`, whose word is the
cell (`PEdge.consistent_slotAt_eq`), and the field's bit coordinates are the bit stage's
(`FieldInterp.Packing.coord_eq`). -/
theorem treeBits_eq {Pk : (I (ir.domainField d)).Packing}
    {rs : List (REdge (I (ir.domainField d)) Pk)} {Pads : Type} [Fintype Pads]
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk d rs) (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    {k : ir.Cell d} {a b : ℕ} (ha : ir.cellNode (rs.map REdge.plan) k.1 = some a)
    (hb : viewChild (rs.map REdge.plan) a = some b)
    (hkey : ir.keyNode k.1 = ((rs.map REdge.plan).getD a noEdge).child) (j : Fin 16) :
    ir.treeBits d rs Pads x (k, j) = (I (ir.domainField d)).ofBool
      ((I (ir.domainField d)).coord (ir.keyNode k.1) (ir.treeDecode d rs Pads x k) j) := by
  set es := rs.map REdge.plan with hes
  obtain ⟨hbl, hbp, hview⟩ := viewChild_spec hb
  simp only [isView, Bool.and_eq_true, beq_iff_eq] at hview
  obtain ⟨⟨⟨hc1, hd16⟩, hsc⟩, -⟩ := hview
  rw [List.getD_eq_getElem _ _ hbl] at hc1 hd16 hsc
  obtain ⟨hba, hal, hm⟩ := ht.parent b hbl a hbp
  rw [List.getD_eq_getElem _ _ hal] at hkey
  have hbl' : b < rs.length := by rwa [List.length_map] at hbl
  have hbf : b < (ir.fieldEdges d Pk rs Pads).length := by rwa [length_fieldEdges]
  set o := (ir.ownKeys d es a).idxOf k.1 with ho
  have hown : o < ir.own d es a := idxOf_lt_own ir ha
  have hng : o < ir.ngOf d es b := by
    have := own_le_baseOf (d := d) ir ht a
    simp only [baseOf, hb] at this
    omega
  have hd : (rs[b]'hbl').plan.degree = 16 := by simpa only [hes, List.getElem_map] using hd16
  have hz := consistent_level_view (ir.spareCell d Pk rs Pads) 0 (ir.fieldEdges d Pk rs Pads) 0
    Fin.elim0 x
  have hsh : Shaped Pk.n 0 (ir.fieldEdges d Pk rs Pads) :=
    shaped_of_shapedAt (ir.shapedAt_fieldEdges d Pads ht) 0 _ List.drop_zero.symm
  have key := consistent_slotAt_eq (ir.spareCell d Pk rs Pads) hsh hz hbf
    (getElem_fieldEdges ir d rs Pads b hbf) (a := a) hbp ⟨o, hng⟩ ⟨j, by
      change (j : ℕ) < (rs[b]'hbl').plan.degree
      rw [hd]
      exact j.2⟩
  have hslot : ir.slotOf d es b o = ir.ownStart d es a + o := by
    simp only [slotOf, hbp, hb, ↓reduceIte]
  change (ir.treeLevel d rs Pads).view x (ir.viewPlace d rs Pads k j) = _
  have hvp : ir.viewPlace d rs Pads k j = slotAt (ir.spareCell d Pk rs Pads)
      (ir.fieldEdges d Pk rs Pads) b (o * (rs[b]'hbl').plan.degree + j) := by
    unfold viewPlace
    split
    · rename_i a' h
      rw [ha] at h
      cases h
      split
      · rename_i b' h'
        rw [hb] at h'
        cases h'
        rw [hd]
      · rename_i h'
        rw [hb] at h'
        cases h'
    · rename_i h
      rw [ha] at h
      cases h
  have hpl : ir.place d rs Pads k = slotAt (ir.spareCell d Pk rs Pads)
      (ir.fieldEdges d Pk rs Pads) (a - 0) (ir.slotOf d es b o) := by
    rw [hslot, Nat.sub_zero]
    unfold place
    split
    · rename_i h; rw [ha] at h; cases h
    · rename_i a' h
      rw [ha] at h
      cases h
      rfl
  rw [hvp]
  refine key.trans ?_
  change (rs[b]'hbl').kit.basis.coord ((ir.treeLevel d rs Pads).view x
    (slotAt (ir.spareCell d Pk rs Pads) (ir.fieldEdges d Pk rs Pads) (a - 0)
      (ir.slotOf d es b o))) _ = _
  rw [← hpl]
  have hmemd : ir.treeDecode d rs Pads x k ∈ fixedField (I (ir.domainField d)).K Pk.p 16 := by
    have h1 := treeDecode_mem ir ht hp x k
    obtain ⟨s, hs, hidx⟩ : ∃ s, ir.cellName k.1 = some s ∧ nodeIdx es s = some a := by
      unfold cellNode at ha
      cases h : ir.cellName k.1 with
      | none => rw [h] at ha; cases ha
      | some s => rw [h] at ha; exact ⟨s, rfl, ha⟩
    have hdeg := hp.nodes k.1 k.2 a s ha hs
    rw [List.getD_eq_getElem _ _ hal] at hdeg
    rw [cellBase_of_name ir hs, Pk.node_eq s _ hdeg] at h1
    have : es[a].childDegree = 16 := by rw [hm, hc1, hd16, one_mul]
    rw [this] at h1
    exact h1
  have hkeyDeg : Pk.nodeDeg (ir.keyNode k.1) = some (rs[b]'hbl').plan.degree := by
    obtain ⟨s, hs, hidx⟩ : ∃ s, ir.cellName k.1 = some s ∧ nodeIdx es s = some a := by
      unfold cellNode at ha
      cases h : ir.cellName k.1 with
      | none => rw [h] at ha; cases ha
      | some s => rw [h] at ha; exact ⟨s, rfl, ha⟩
    obtain ⟨_, hch⟩ := nodeIdx_spec hidx
    have hdeg := hp.nodes k.1 k.2 a s ha hs
    rw [List.getD_eq_getElem _ _ hal] at hdeg
    rw [hkey, hch, hdeg, hm, hc1, one_mul]
    simp only [hes, List.getElem_map]
  have hc1' : (rs[b]'hbl').plan.childDegree = 1 := by simpa only [hes, List.getElem_map] using hc1
  have := Pk.coord_eq (ir.keyNode k.1) (rs[b]'hbl').plan.mode (rs[b]'hbl').kit
    (hr _ (List.getElem_mem hbl')) hc1' (by simpa only [hes, List.getElem_map] using hsc) hkeyDeg
    (ir.treeDecode d rs Pads x k) (hd ▸ hmemd)
    ⟨j, by rw [hd]; exact j.2⟩
  exact this.symm

/-- **A cell at the root decodes to its committed cell.** -/
theorem treeDecode_root {Pk : (I (ir.domainField d)).Packing}
    {rs : List (REdge (I (ir.domainField d)) Pk)} {Pads : Type} [Fintype Pads]
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) {k : ir.Cell d}
    (h : ir.cellNode (rs.map REdge.plan) k.1 = none) :
    ir.treeDecode d rs Pads x k = x (.inr (.inr (.cell ⟨k, h⟩))) := by
  unfold treeDecode place
  split
  · rename_i h'
    exact level_view_cellIn _ 0 _ 0 _ x _
  · rename_i a h'
    rw [h] at h'
    cases h'

end

end GordieHowe.RealizedProgram
