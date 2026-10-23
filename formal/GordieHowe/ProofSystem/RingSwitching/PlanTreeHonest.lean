-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PlanTree

@[expose] public section

/-!
# The honest run of a planned packing tree

The honest prover of the tree of planned edges (`PEdge.path`), generic in the edges:

* **the honest masks** (`PEdge.maskHonest`): each edge's kit's honest masks on its mask cells
  (`MaskKit.honest`);
* **the masks' pads** (`PEdge.MaskPads`, `PEdge.MaskPads.get`) and the masks' commitment
  (`PEdge.MaskCommits`; `PEdge.maskCommits_of_maskVal` when the mask cells hold the masks' values
  and are distinct): every edge's mask cells hold its kit's values;
* **the honest run's pads** (`PEdge.splitPads`): the masked reduction's pads and every edge's mask pads;
  the honest run commits the masked reduction's pads and every edge's masks
  (`PEdge.commits_honestRun_iff`).
-/

namespace GordieHowe

open IOP PackingStage RelativePacking

namespace PEdge

variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p]
  {S0 : Subfield K} [Fintype ι]

/-- **The honest masks of every edge** from absolute position `pos` on: each edge's kit's honest
masks on its mask cells (`MaskKit.honest`). -/
def maskHonest (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) → (path fb pos es nc r).MaskHonest
  | _, [], _, _ => PUnit.unit
  | pos, e :: es, _, r =>
    (e.kit.masks.honest e.maskPre e.maskOwn, maskHonest fb (pos + 1) es _ (nextReads pos e r))

/-- **The masks' pads of the edges.** -/
def MaskPads : List (PEdge K ι p S0) → Type
  | [] => PUnit
  | e :: es => e.kit.masks.Pads × MaskPads es

/-- **The cells `x` commit the edges' masks** at the pads `π`: every edge's mask cells hold its
kit's values. -/
def MaskCommits : (es : List (PEdge K ι p S0)) → MaskPads es → (ι → K) → Prop
  | [], _, _ => True
  | e :: es, π, x => (e.kit.masks.honest e.maskPre e.maskOwn).Commits π.1 x ∧ MaskCommits es π.2 x

/-- **A slot reads the cells only at the spare cell `fb`** (out of range). -/
theorem fill_slotAt_congr (fb : ι) (vals : ℕ → ℕ → K) {x x' : ι → K} (h : x fb = x' fb) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) → (j s : ℕ) →
      fill vals x pos es (slotAt fb es j s) = fill vals x' pos es (slotAt fb es j s)
  | _, [], _, _ => h
  | pos, e :: es, 0, s => by
    simp only [slotAt]
    by_cases hs : s < e.ng * e.d
    · simp only [hs, ↓reduceDIte]
      rfl
    · simp only [hs, ↓reduceDIte, fill, Sum.elim_inl]
      rw [fill_cellIn, fill_cellIn]
      exact h
  | pos, _ :: es, j + 1, s => fill_slotAt_congr fb vals h (pos + 1) es j s

/-- **The words read the cells only at the spare cell and the root words.** -/
theorem fill_isWord_congr (fb : ι) (vals : ℕ → ℕ → K) {x x' : ι → K} (hfb : x fb = x' fb) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) →
    (∀ e ∈ es, ∀ g, x (e.rootWord g) = x' (e.rootWord g)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
      (z : Logical ι es) →
      (path fb pos es nc r).IsWord z → fill vals x pos es z = fill vals x' pos es z
  | _, [], _, _, _, _, h => h.elim
  | _, _ :: _, _, _, _, .inr _, h => h.elim
  | pos, e :: es, hroot, _, r, .inl y, h => by
    let _ := e.kit.order
    change (∃ g, (stage fb pos e es).word g = y) ∨
      (path fb (pos + 1) es _ (nextReads pos e r)).IsWord y at h
    change fill vals x (pos + 1) es y = fill vals x' (pos + 1) es y
    rcases h with ⟨g, rfl⟩ | h
    · change fill vals x (pos + 1) es (word fb pos e es g) = fill vals x' (pos + 1) es (word fb pos e es g)
      unfold word
      split
      · rw [fill_cellIn, fill_cellIn]
        exact hroot e List.mem_cons_self g
      · exact fill_slotAt_congr fb vals hfb (pos + 1) es _ _
    · exact fill_isWord_congr fb vals hfb (pos + 1) es
        (fun e' he' => hroot e' (List.mem_cons_of_mem _ he')) _ (nextReads pos e r) y h

/-- **An honest cell reads its base value only at itself.** -/
theorem cellVal_congr (es0 : List (PEdge K ι p S0)) (own : ℕ → ℕ → K) (given : ℕ → ℕ → Bool)
    (groupAt : ℕ → ℕ → Option (ℕ × ℕ)) (rootAt : ι → Option (ℕ × ℕ)) {base base' : ι → K} {i : ι}
    (h : base i = base' i) :
    cellVal es0 own given groupAt rootAt base i = cellVal es0 own given groupAt rootAt base' i := by
  unfold cellVal
  split
  · split
    · rfl
    · exact h
  · exact h

/-- **The mask cells of an edge**: its prefix cells, then its own cells. -/
def maskCell (e : PEdge K ι p S0) : Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn → ι :=
  Sum.elim e.maskPre e.maskOwn

/-- **The kit's value at a mask cell** at the pads `π`. -/
def maskCellVal (e : PEdge K ι p S0) (π : e.kit.masks.Pads) :
    Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn → K :=
  Sum.elim (e.kit.masks.preVal π) (e.kit.masks.ownVal π)

/-- **The mask cells are distinct**: within each edge and across the edges. -/
def MaskCellsDistinct : List (PEdge K ι p S0) → Prop
  | [] => True
  | e :: es => Function.Injective e.maskCell ∧
      (∀ c, ∀ e' ∈ es, ∀ c', e.maskCell c ≠ e'.maskCell c') ∧ MaskCellsDistinct es

/-- **The mask cells of an edge, listed.** -/
def maskCells (e : PEdge K ι p S0) : List (Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn) :=
  (List.finRange _).map Sum.inl ++ (List.finRange _).map Sum.inr

theorem mem_maskCells (e : PEdge K ι p S0) (c : Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn) :
    c ∈ e.maskCells := by
  rcases c with j | o <;> simp [maskCells]

section MaskVal

variable [DecidableEq ι]

/-- **The masks' value at a cell**: the kit's value at the first mask cell equal to it, none off
the mask cells. -/
def maskVal : (es : List (PEdge K ι p S0)) → MaskPads es → ι → Option K
  | [], _, _ => none
  | e :: es, π, i =>
    match e.maskCells.find? fun c => decide (e.maskCell c = i) with
    | some c => some (e.maskCellVal π.1 c)
    | none => maskVal es π.2 i

/-- **The masks' value is at a mask cell.** -/
theorem mem_of_maskVal : (es : List (PEdge K ι p S0)) → (π : MaskPads es) → (i : ι) → (v : K) →
    maskVal es π i = some v → ∃ e ∈ es, ∃ c, e.maskCell c = i
  | [], _, _, _, h => by cases h
  | e :: es, π, i, v, h => by
    simp only [maskVal] at h
    split at h
    · rename_i c hc
      have := List.find?_some hc
      simp only [decide_eq_true_eq] at this
      exact ⟨e, List.mem_cons_self, c, this⟩
    · obtain ⟨e', he', c, hc⟩ := mem_of_maskVal es π.2 i v h
      exact ⟨e', List.mem_cons_of_mem _ he', c, hc⟩

/-- **The masks' value is a kit's value at one of its mask cells.** -/
theorem exists_of_maskVal : (es : List (PEdge K ι p S0)) → (π : MaskPads es) → (i : ι) → (v : K) →
    (h : maskVal es π i = some v) →
      ∃ e ∈ es, ∃ (πe : e.kit.masks.Pads) (c : Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn),
        e.maskCell c = i ∧ v = e.maskCellVal πe c
  | [], _, _, _, h => by cases h
  | e :: es, π, i, v, h => by
    simp only [maskVal] at h
    split at h
    · rename_i c hc
      have := List.find?_some hc
      simp only [decide_eq_true_eq] at this
      cases h
      exact ⟨e, List.mem_cons_self, π.1, c, this, rfl⟩
    · obtain ⟨e', he', πe, c, hc, hv⟩ := exists_of_maskVal es π.2 i v h
      exact ⟨e', List.mem_cons_of_mem _ he', πe, c, hc, hv⟩

/-- **The first edge's mask cell holds its kit's value**, its mask cells being distinct. -/
theorem maskVal_cons_maskCell (e : PEdge K ι p S0) (es : List (PEdge K ι p S0)) (π : MaskPads (e :: es))
    (hinj : Function.Injective e.maskCell) (c : Fin e.kit.masks.nPre ⊕ Fin e.kit.masks.nOwn) :
    maskVal (e :: es) π (e.maskCell c) = some (e.maskCellVal π.1 c) := by
  simp only [maskVal]
  split
  · rename_i c' hc'
    have := List.find?_some hc'
    simp only [decide_eq_true_eq] at this
    rw [hinj this]
  · rename_i hn
    exact absurd (List.find?_eq_none.1 hn c (mem_maskCells e c)) (by simp)

/-- **Cells holding the masks' values commit the masks**, when the mask cells are distinct. -/
theorem maskCommits_of_maskVal : (es : List (PEdge K ι p S0)) → (π : MaskPads es) →
    MaskCellsDistinct es → (x : ι → K) →
    (∀ i v, maskVal es π i = some v → x i = v) → MaskCommits es π x
  | [], _, _, _, _ => trivial
  | e :: es, π, ⟨hinj, hdis, hd⟩, x, hx => by
    refine ⟨⟨fun j => hx _ _ (maskVal_cons_maskCell e es π hinj (.inl j)),
      fun o => hx _ _ (maskVal_cons_maskCell e es π hinj (.inr o))⟩,
      maskCommits_of_maskVal es π.2 hd x fun i v hv => ?_⟩
    obtain ⟨e', he', c', rfl⟩ := mem_of_maskVal es π.2 i v hv
    refine hx _ v ?_
    simp only [maskVal]
    rw [List.find?_eq_none.2 fun c _ => by simpa using hdis c e' he' c']
    exact hv

/-- **Distinct mask cells, by position**: each edge's mask cells are injective and no two edges
share a mask cell. -/
theorem maskCellsDistinct_of_getElem : (es : List (PEdge K ι p S0)) →
    (∀ (a : ℕ) (ha : a < es.length), Function.Injective es[a].maskCell) →
    (∀ (a b : ℕ) (ha : a < es.length) (hb : b < es.length), a < b →
      ∀ (c : Fin es[a].kit.masks.nPre ⊕ Fin es[a].kit.masks.nOwn)
        (c' : Fin es[b].kit.masks.nPre ⊕ Fin es[b].kit.masks.nOwn),
        es[a].maskCell c ≠ es[b].maskCell c') → MaskCellsDistinct es
  | [], _, _ => trivial
  | e :: es, hinj, hdis => by
    refine ⟨hinj 0 (Nat.succ_pos _), fun c e' he' c' => ?_, maskCellsDistinct_of_getElem es
      (fun a ha => hinj (a + 1) (Nat.succ_lt_succ ha))
      (fun a b ha hb hab => hdis (a + 1) (b + 1) (Nat.succ_lt_succ ha) (Nat.succ_lt_succ hb)
        (Nat.succ_lt_succ hab))⟩
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem he'
    exact hdis 0 (b + 1) (Nat.succ_pos _) (Nat.succ_lt_succ hb) (Nat.succ_pos _) c c'

end MaskVal

variable {Pub Wit In : Type} {cells : Wit → ι → K} {dom : Pub → In → Prop}

/-- **The honest run's pads** split into the masked reduction's and every edge's mask pads. -/
def splitPads (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    {M : FieldProof.MaskedReduction K ι Pub Wit cells (Logical ι es) nc} →
    (hR : (path fb pos es nc r).Routes M) →
    {SM : M.Sim} → (H : M.Honest (path fb pos es nc r).level.view In dom SM) →
    (val : Pub → In → H.Pads → Logical ι es → K) →
    (hval : ∀ p x π w, H.Commits p x π w → ∀ z, (path fb pos es nc r).IsWord z →
      (path fb pos es nc r).level.view (cells w) z = val p x π z) →
    ((path fb pos es nc r).honestRun hR H (maskHonest fb pos es nc r) val hval).Pads →
      H.Pads × MaskPads es
  | _, [], _, _, _, _, _, _, _, _, π => (π, PUnit.unit)
  | pos, e :: es, _, r, _, hR, _, H, val, hval, π =>
    letI := e.kit.order
    let q := splitPads fb (pos + 1) es _ (nextReads pos e r) hR.2
      (H.routedStage (S := stage fb pos e es) (e.kit.masks.honest e.maskPre e.maskOwn)
        (fun p x π g => val p x π (.inl ((stage fb pos e es).word g)))
        (fun p x π w hw g => hval p x π w hw (.inl ((stage fb pos e es).word g)) (Or.inl ⟨g, rfl⟩))
        hR.1)
      (fun p x π y => val p x π.1 (.inl y))
      (fun p x π w hw y hy => hval p x π.1 w hw.1 (.inl y) (Or.inr hy)) π
    (q.1.1, (q.1.2, q.2))

/-- **The honest run commits the masked reduction's pads and every edge's masks.** -/
theorem commits_honestRun_iff (fb : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    {M : FieldProof.MaskedReduction K ι Pub Wit cells (Logical ι es) nc} →
    (hR : (path fb pos es nc r).Routes M) →
    {SM : M.Sim} → (H : M.Honest (path fb pos es nc r).level.view In dom SM) →
    (val : Pub → In → H.Pads → Logical ι es → K) →
    (hval : ∀ p x π w, H.Commits p x π w → ∀ z, (path fb pos es nc r).IsWord z →
      (path fb pos es nc r).level.view (cells w) z = val p x π z) →
    ∀ p x π w,
      (((path fb pos es nc r).honestRun hR H (maskHonest fb pos es nc r) val hval).Commits p x π w ↔
        H.Commits p x (splitPads fb pos es nc r hR H val hval π).1 w ∧
          MaskCommits es (splitPads fb pos es nc r hR H val hval π).2 (cells w))
  | _, [], _, _, _, _, _, _, _, _, _, _, _, _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | pos, e :: es, _, r, _, hR, _, H, val, hval, p, x, π, w => by
    let _ := e.kit.order
    exact (commits_honestRun_iff fb (pos + 1) es _ (nextReads pos e r) hR.2
      (H.routedStage (S := stage fb pos e es) (e.kit.masks.honest e.maskPre e.maskOwn)
        (fun p x π g => val p x π (.inl ((stage fb pos e es).word g)))
        (fun p x π w hw g => hval p x π w hw (.inl ((stage fb pos e es).word g)) (Or.inl ⟨g, rfl⟩))
        hR.1)
      (fun p x π y => val p x π.1 (.inl y))
      (fun p x π w hw y hy => hval p x π.1 w hw.1 (.inl y) (Or.inr hy)) p x π w).trans and_assoc

end PEdge

end GordieHowe
