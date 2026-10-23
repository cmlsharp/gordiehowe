-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merges

@[expose] public section

/-!
# Series–parallel terms with merges

`MTerm ι`: a series–parallel term whose nodes may be merges `merge r br d`, the part
`(br 0 ∥ … ∥ br (r-1)) ; d` of the paper's `prot:generalized-bcs`. Each branch `br b` and the part
`d` are again terms with merges, so a branch may be a parallel composition, contain merges, or be
the part of an outer merge. `toSP` forgets the merges: the series–parallel term of the causal
order (`merge r br d` is `seq (parN r br) d`).

* `MTerm.Site t`: the branches of the merges of `t`, one per branch (`top b` at a merge, and the
  sites inside a branch, inside the part, or inside the two subterms of a node).
* `Site.mem s q`: the leaf `q` of `t.toSP` lies in the branch of `s`; `Site.part s p`: `p` lies in
  the part of the merge of `s`.
* `MTerm.merges t`: the merges on `t.toSP` (`Merges`), with the laws proved by induction on the
  term: every branch has a leaf (`exists_mem`), a branch is before its part (`before_of_part`), two
  branches containing one leaf and hiding one leaf are one (`eq_of_part_of_mem`), and the merges
  nest (`part_iff_of_before`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.IOP IOP.SPTerm

variable {ι : Type}

/-- **A series–parallel term with merges** (module docstring). -/
inductive MTerm (ι : Type) where
  /-- One component. -/
  | leaf (j : ι)
  /-- Two subterms composed by `k`. -/
  | node (k : Comp) (a b : MTerm ι)
  /-- The merge of the branches `br` side by side, followed by the part `d`. -/
  | merge (r : ℕ) (br : Fin r → MTerm ι) (d : MTerm ι)

namespace MTerm

/-- **The series–parallel term of the causal order**: a merge is its branches side by side, then
its part. -/
def toSP : MTerm ι → SPTerm ι
  | leaf j => .leaf j
  | node k a b => .node k a.toSP b.toSP
  | merge r br d => .seq (SPTerm.parN r fun b => (br b).toSP) d.toSP

/-- **Every term has a leaf.** -/
theorem nonempty_leaf : (t : MTerm ι) → Nonempty t.toSP.Leaf
  | leaf j => ⟨.here j⟩
  | node _ a _ => (nonempty_leaf a).map .left
  | merge _ _ d => (nonempty_leaf d).map .right

/-- **The branches of the merges of a term.** -/
inductive Site : MTerm ι → Type where
  /-- A site of the first subterm of a node. -/
  | left {k : Comp} {a b : MTerm ι} : Site a → Site (node k a b)
  /-- A site of the second subterm of a node. -/
  | right {k : Comp} {a b : MTerm ι} : Site b → Site (node k a b)
  /-- Branch `i` of a merge. -/
  | top {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} (i : Fin r) : Site (merge r br d)
  /-- A site inside branch `i` of a merge. -/
  | inBr {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} (i : Fin r) : Site (br i) → Site (merge r br d)
  /-- A site inside the part of a merge. -/
  | inD {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} : Site d → Site (merge r br d)

namespace Site

/-- The sites of a node are those of its two subterms. -/
def equivNode {k : Comp} {a b : MTerm ι} : Site (node k a b) ≃ Site a ⊕ Site b where
  toFun
    | left s => .inl s
    | right s => .inr s
  invFun
    | .inl s => left s
    | .inr s => right s
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- The sites of a merge: its branches, those inside each branch, and those inside its part. -/
def equivMerge {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} :
    Site (merge r br d) ≃ Fin r ⊕ (Σ i, Site (br i)) ⊕ Site d where
  toFun
    | top i => .inl i
    | inBr i s => .inr (.inl ⟨i, s⟩)
    | inD s => .inr (.inr s)
  invFun
    | .inl i => top i
    | .inr (.inl ⟨i, s⟩) => inBr i s
    | .inr (.inr s) => inD s
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | ⟨_, _⟩ | _ <;> rfl

/-- A term has finitely many sites. -/
instance fintype : (t : MTerm ι) → Fintype (Site t)
  | leaf _ => ⟨∅, fun s => nomatch s⟩
  | node _ a b =>
    letI := fintype a
    letI := fintype b
    Fintype.ofEquiv _ equivNode.symm
  | merge _ br d =>
    letI : ∀ i, Fintype (Site (br i)) := fun i => fintype (br i)
    letI := fintype d
    Fintype.ofEquiv _ equivMerge.symm

/-- The sites of a term have decidable equality. -/
instance decEq : (t : MTerm ι) → DecidableEq (Site t)
  | leaf _ => fun s => nomatch s
  | node _ a b =>
    letI := decEq a
    letI := decEq b
    equivNode.decidableEq
  | merge _ br d =>
    letI : ∀ i, DecidableEq (Site (br i)) := fun i => decEq (br i)
    letI := decEq d
    equivMerge.decidableEq

/-- The sites of a term are encoded through their branches (`equivNode`, `equivMerge`). -/
instance encodable : (t : MTerm ι) → Encodable (Site t)
  | leaf _ => ⟨fun s => (nomatch s), fun _ => none, fun s => (nomatch s)⟩
  | node _ a b =>
    letI := encodable a
    letI := encodable b
    Encodable.ofEquiv _ equivNode
  | merge _ br d =>
    letI : ∀ i, Encodable (Site (br i)) := fun i => encodable (br i)
    letI := encodable d
    Encodable.ofEquiv _ equivMerge

/-- **The leaves of the branch of a site.** -/
def mem : {t : MTerm ι} → Site t → t.toSP.Leaf → Prop
  | node _ _ _, left s, .left q => s.mem q
  | node _ _ _, left _, .right _ => False
  | node _ _ _, right _, .left _ => False
  | node _ _ _, right s, .right q => s.mem q
  | merge r _ _, top i, .left q => ∃ q', q = Leaf.inN .par r i q'
  | merge _ _ _, top _, .right _ => False
  | merge r _ _, inBr i s, .left q => ∃ q', q = Leaf.inN .par r i q' ∧ s.mem q'
  | merge _ _ _, inBr _ _, .right _ => False
  | merge _ _ _, inD _, .left _ => False
  | merge _ _ _, inD s, .right q => s.mem q

/-- **The leaves of the part of the merge of a site.** -/
def part : {t : MTerm ι} → Site t → t.toSP.Leaf → Prop
  | node _ _ _, left s, .left q => s.part q
  | node _ _ _, left _, .right _ => False
  | node _ _ _, right _, .left _ => False
  | node _ _ _, right s, .right q => s.part q
  | merge _ _ _, top _, .left _ => False
  | merge _ _ _, top _, .right _ => True
  | merge r _ _, inBr i s, .left q => ∃ q', q = Leaf.inN .par r i q' ∧ s.part q'
  | merge _ _ _, inBr _ _, .right _ => False
  | merge _ _ _, inD _, .left _ => False
  | merge _ _ _, inD s, .right q => s.part q

/-- Membership in a branch is decidable. -/
instance decMem : {t : MTerm ι} → (s : Site t) → DecidablePred s.mem
  | node _ _ _, left s, .left q => decMem s q
  | node _ _ _, left _, .right _ => instDecidableFalse
  | node _ _ _, right _, .left _ => instDecidableFalse
  | node _ _ _, right s, .right q => decMem s q
  | merge _ _ _, top _, .left _ => Fintype.decidableExistsFintype
  | merge _ _ _, top _, .right _ => instDecidableFalse
  | merge _ _ _, inBr _ s, .left _ =>
    letI := decMem s
    Fintype.decidableExistsFintype
  | merge _ _ _, inBr _ _, .right _ => instDecidableFalse
  | merge _ _ _, inD _, .left _ => instDecidableFalse
  | merge _ _ _, inD s, .right q => decMem s q

/-- Membership in a part is decidable. -/
instance decPart : {t : MTerm ι} → (s : Site t) → DecidablePred s.part
  | node _ _ _, left s, .left q => decPart s q
  | node _ _ _, left _, .right _ => instDecidableFalse
  | node _ _ _, right _, .left _ => instDecidableFalse
  | node _ _ _, right s, .right q => decPart s q
  | merge _ _ _, top _, .left _ => instDecidableFalse
  | merge _ _ _, top _, .right _ => instDecidableTrue
  | merge _ _ _, inBr _ s, .left _ =>
    letI := decPart s
    Fintype.decidableExistsFintype
  | merge _ _ _, inBr _ _, .right _ => instDecidableFalse
  | merge _ _ _, inD _, .left _ => instDecidableFalse
  | merge _ _ _, inD s, .right q => decPart s q

/-! ### Membership at the leaves of a merge -/

section MergeLeaves

variable {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι}

/-- The leaf `x` of branch `i'` as a leaf of the merge. -/
abbrev brLeaf (i : Fin r) (x : (br i).toSP.Leaf) : (merge r br d).toSP.Leaf :=
  .left (Leaf.inN .par r (c := fun b => (br b).toSP) i x)

/-- The leaf `x` of the part as a leaf of the merge. -/
abbrev dLeaf (x : d.toSP.Leaf) : (merge r br d).toSP.Leaf := .right x

/-- **Every leaf of a merge is a leaf of a branch or of the part.** -/
theorem leaf_cases (p : (merge r br d).toSP.Leaf) :
    (∃ i x, p = brLeaf (br := br) (d := d) i x) ∨ ∃ x, p = dLeaf (br := br) x := by
  rcases p with _ | q | x
  · obtain ⟨i, x, rfl⟩ := Leaf.exists_inN .par r q
    exact Or.inl ⟨i, x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

theorem brLeaf_injective {i i' : Fin r} {x : (br i).toSP.Leaf} {x' : (br i').toSP.Leaf}
    (h : brLeaf (d := d) i x = brLeaf i' x') : i = i' ∧ HEq x x' := by
  by_cases hi : i = i'
  · subst hi
    exact ⟨rfl, heq_of_eq (Leaf.inN_injective .par r i (Leaf.left_injective h))⟩
  · exact absurd (Leaf.left_injective h) (Leaf.inN_ne_inN .par r (c := fun b => (br b).toSP) hi x x')

@[simp] theorem mem_top_brLeaf {i i' : Fin r} {x : (br i').toSP.Leaf} :
    (top (br := br) (d := d) i).mem (brLeaf i' x) ↔ i' = i := by
  constructor
  · rintro ⟨q', hq'⟩
    exact (brLeaf_injective (d := d) (congrArg Leaf.left hq')).1
  · rintro rfl
    exact ⟨x, rfl⟩

@[simp] theorem not_mem_top_dLeaf {i : Fin r} {x : d.toSP.Leaf} :
    ¬ (top (br := br) (d := d) i).mem (dLeaf x) := id

@[simp] theorem mem_inBr_brLeaf_self {i : Fin r} {s : Site (br i)} {x : (br i).toSP.Leaf} :
    (inBr (d := d) i s).mem (brLeaf i x) ↔ s.mem x := by
  constructor
  · rintro ⟨q', hq', hm⟩
    rwa [← Leaf.inN_injective .par r i hq'] at hm
  · exact fun h => ⟨x, rfl, h⟩

theorem not_mem_inBr_brLeaf {i i' : Fin r} (hi : i' ≠ i) {s : Site (br i)}
    {x : (br i').toSP.Leaf} : ¬ (inBr (d := d) i s).mem (brLeaf i' x) := by
  rintro ⟨q', hq', -⟩
  exact Leaf.inN_ne_inN .par r (c := fun b => (br b).toSP) hi x q' hq'

@[simp] theorem not_mem_inBr_dLeaf {i : Fin r} {s : Site (br i)} {x : d.toSP.Leaf} :
    ¬ (inBr i s).mem (dLeaf (br := br) x) := id

@[simp] theorem not_mem_inD_brLeaf {s : Site d} {i : Fin r} {x : (br i).toSP.Leaf} :
    ¬ (inD (br := br) s).mem (brLeaf i x) := id

@[simp] theorem mem_inD_dLeaf {s : Site d} {x : d.toSP.Leaf} :
    (inD (br := br) s).mem (dLeaf x) ↔ s.mem x := Iff.rfl

@[simp] theorem not_part_top_brLeaf {i i' : Fin r} {x : (br i').toSP.Leaf} :
    ¬ (top (br := br) (d := d) i).part (brLeaf i' x) := id

@[simp] theorem part_top_dLeaf {i : Fin r} {x : d.toSP.Leaf} :
    (top (br := br) (d := d) i).part (dLeaf x) := trivial

@[simp] theorem part_inBr_brLeaf_self {i : Fin r} {s : Site (br i)} {x : (br i).toSP.Leaf} :
    (inBr (d := d) i s).part (brLeaf i x) ↔ s.part x := by
  constructor
  · rintro ⟨q', hq', hm⟩
    rwa [← Leaf.inN_injective .par r i hq'] at hm
  · exact fun h => ⟨x, rfl, h⟩

theorem not_part_inBr_brLeaf {i i' : Fin r} (hi : i' ≠ i) {s : Site (br i)}
    {x : (br i').toSP.Leaf} : ¬ (inBr (d := d) i s).part (brLeaf i' x) := by
  rintro ⟨q', hq', -⟩
  exact Leaf.inN_ne_inN .par r (c := fun b => (br b).toSP) hi x q' hq'

@[simp] theorem not_part_inBr_dLeaf {i : Fin r} {s : Site (br i)} {x : d.toSP.Leaf} :
    ¬ (inBr i s).part (dLeaf (br := br) x) := id

@[simp] theorem not_part_inD_brLeaf {s : Site d} {i : Fin r} {x : (br i).toSP.Leaf} :
    ¬ (inD (br := br) s).part (brLeaf i x) := id

@[simp] theorem part_inD_dLeaf {s : Site d} {x : d.toSP.Leaf} :
    (inD (br := br) s).part (dLeaf x) ↔ s.part x := Iff.rfl

/-- A branch leaf is before a part leaf. -/
@[simp] theorem brLeaf_before_dLeaf {i : Fin r} {x : (br i).toSP.Leaf} {y : d.toSP.Leaf} :
    (brLeaf (d := d) i x).Before (dLeaf y) := rfl

/-- A part leaf is not before a branch leaf. -/
@[simp] theorem not_dLeaf_before_brLeaf {i : Fin r} {x : (br i).toSP.Leaf} {y : d.toSP.Leaf} :
    ¬ (dLeaf (br := br) y).Before (brLeaf i x) := id

/-- Two leaves of one branch are ordered as in the branch. -/
@[simp] theorem brLeaf_before_brLeaf {i : Fin r} {x y : (br i).toSP.Leaf} :
    (brLeaf (d := d) i x).Before (brLeaf i y) ↔ x.Before y :=
  Leaf.inN_before_inN_iff .par r (c := fun b => (br b).toSP) i x y

/-- Leaves of distinct branches are not ordered. -/
theorem not_brLeaf_before_brLeaf {i i' : Fin r} (hi : i ≠ i') {x : (br i).toSP.Leaf}
    {y : (br i').toSP.Leaf} : ¬ (brLeaf (d := d) i x).Before (brLeaf i' y) :=
  Leaf.not_inN_before_inN_par r (c := fun b => (br b).toSP) hi x y

/-- Two leaves of the part are ordered as in the part. -/
@[simp] theorem dLeaf_before_dLeaf {x y : d.toSP.Leaf} :
    (dLeaf (br := br) x).Before (dLeaf y) ↔ x.Before y := Iff.rfl

end MergeLeaves

/-! ### The laws -/

/-- **Every branch has a leaf.** -/
theorem exists_mem : {t : MTerm ι} → (s : Site t) → ∃ q, s.mem q
  | node _ _ _, left s => let ⟨q, h⟩ := exists_mem s; ⟨.left q, h⟩
  | node _ _ _, right s => let ⟨q, h⟩ := exists_mem s; ⟨.right q, h⟩
  | merge _ br _, top i => let ⟨x⟩ := nonempty_leaf (br i); ⟨brLeaf i x, mem_top_brLeaf.2 rfl⟩
  | merge _ _ _, inBr i s => let ⟨q, h⟩ := exists_mem s; ⟨brLeaf i q, mem_inBr_brLeaf_self.2 h⟩
  | merge _ _ _, inD s => let ⟨q, h⟩ := exists_mem s; ⟨dLeaf q, h⟩

/-- **A leaf of a merge in the branch of a site inside branch `i`** is a leaf of branch `i`. -/
theorem eq_brLeaf_of_mem_inBr {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} {i : Fin r}
    {s : Site (br i)} {q : (merge r br d).toSP.Leaf} (h : (inBr i s).mem q) :
    ∃ x, q = brLeaf i x ∧ s.mem x := by
  rcases q with _ | q | x
  · obtain ⟨q', rfl, hm⟩ := h
    exact ⟨q', rfl, hm⟩
  · exact h.elim

/-- **A branch is a module**: a leaf outside it that is before one of its leaves is before all of
them. -/
theorem before_of_before_mem : {t : MTerm ι} → {s : Site t} → {q q' r : t.toSP.Leaf} → s.mem q →
    s.mem q' → ¬ s.mem r → r.Before q → r.Before q'
  | node _ _ _, left _, .left _, .left _, .left _, hq, hq', hr, hb =>
    before_of_before_mem (t := _) hq hq' hr hb
  | node _ _ _, left _, .left _, .left _, .right _, _, _, _, hb => hb.elim
  | node _ _ _, right _, .right _, .right _, .left _, _, _, _, hb => hb
  | node _ _ _, right _, .right _, .right _, .right _, hq, hq', hr, hb =>
    before_of_before_mem (t := _) hq hq' hr hb
  | node _ _ _, left _, .right _, _, _, hq, _, _, _ => hq.elim
  | node _ _ _, left _, .left _, .right _, _, _, hq', _, _ => hq'.elim
  | node _ _ _, right _, .left _, _, _, hq, _, _, _ => hq.elim
  | node _ _ _, right _, .right _, .left _, _, _, hq', _, _ => hq'.elim
  | merge _ _ _, s, q, q', r, hq, hq', hr, hb => by
    cases s with
    | top i =>
      rcases leaf_cases q with ⟨i₁, x, rfl⟩ | ⟨_, rfl⟩
      · obtain rfl := mem_top_brLeaf.1 hq
        rcases leaf_cases r with ⟨i₂, y, rfl⟩ | ⟨_, rfl⟩
        · by_cases hi : i₂ = i₁
          · exact (hr (mem_top_brLeaf.2 hi)).elim
          · exact (not_brLeaf_before_brLeaf hi hb).elim
        · exact (not_dLeaf_before_brLeaf hb).elim
      · exact (not_mem_top_dLeaf hq).elim
    | inBr i s₀ =>
      obtain ⟨x, rfl, hx⟩ := eq_brLeaf_of_mem_inBr hq
      obtain ⟨x', rfl, hx'⟩ := eq_brLeaf_of_mem_inBr hq'
      rcases leaf_cases r with ⟨i₂, y, rfl⟩ | ⟨_, rfl⟩
      · by_cases hi : i₂ = i
        · subst hi
          exact brLeaf_before_brLeaf.2 (before_of_before_mem hx hx'
            (fun hy => hr (mem_inBr_brLeaf_self.2 hy)) (brLeaf_before_brLeaf.1 hb))
        · exact (not_brLeaf_before_brLeaf hi hb).elim
      · exact (not_dLeaf_before_brLeaf hb).elim
    | inD s₀ =>
      rcases leaf_cases q with ⟨_, _, rfl⟩ | ⟨x, rfl⟩
      · exact (not_mem_inD_brLeaf hq).elim
      rcases leaf_cases q' with ⟨_, _, rfl⟩ | ⟨x', rfl⟩
      · exact (not_mem_inD_brLeaf hq').elim
      rcases leaf_cases r with ⟨_, _, rfl⟩ | ⟨y, rfl⟩
      · exact brLeaf_before_dLeaf
      · exact before_of_before_mem (t := _) (s := s₀) hq hq' hr hb

/-- **A branch is before its merge's part.** -/
theorem before_of_part : {t : MTerm ι} → {s : Site t} → {q p : t.toSP.Leaf} → s.mem q →
    s.part p → q.Before p
  | node _ _ _, left _, .left _, .left _, hq, hp => before_of_part (t := _) hq hp
  | node _ _ _, right _, .right _, .right _, hq, hp => before_of_part (t := _) hq hp
  | merge _ _ _, top _, .left _, .right _, _, _ => rfl
  | merge _ _ _, inBr i s, q, p, hq, hp => by
    obtain ⟨x, rfl, hx⟩ := eq_brLeaf_of_mem_inBr hq
    rcases p with _ | p | y
    · obtain ⟨y, rfl, hy⟩ := hp
      exact brLeaf_before_brLeaf.2 (before_of_part hx hy)
    · exact hp.elim
  | merge _ _ _, inD _, .right _, .right _, hq, hp => before_of_part (t := _) hq hp
  | node _ _ _, left _, .left _, .right _, _, hp => hp.elim
  | node _ _ _, left _, .right _, _, hq, _ => hq.elim
  | node _ _ _, right _, .left _, _, hq, _ => hq.elim
  | node _ _ _, right _, .right _, .left _, _, hp => hp.elim
  | merge _ _ _, top _, .left _, .left _, _, hp => hp.elim
  | merge _ _ _, top _, .right _, _, hq, _ => hq.elim
  | merge _ _ _, inD _, .left _, _, hq, _ => hq.elim
  | merge _ _ _, inD _, .right _, .left _, _, hp => hp.elim

/-- **Two branches containing one leaf and both hidden from one leaf are one branch.** -/
theorem eq_of_part_of_mem : {t : MTerm ι} → {s s' : Site t} → {p r : t.toSP.Leaf} → s.part p →
    s'.part p → s.mem r → s'.mem r → s = s'
  | node _ _ _, left _, left _, .left _, .left _, hp, hp', hr, hr' =>
    congrArg left (eq_of_part_of_mem (t := _) hp hp' hr hr')
  | node _ _ _, right _, right _, .right _, .right _, hp, hp', hr, hr' =>
    congrArg right (eq_of_part_of_mem (t := _) hp hp' hr hr')
  | node _ _ _, left _, right _, _, .left _, _, _, _, hr' => hr'.elim
  | node _ _ _, left _, right _, _, .right _, _, _, hr, _ => hr.elim
  | node _ _ _, right _, left _, _, .left _, _, _, hr, _ => hr.elim
  | node _ _ _, right _, left _, _, .right _, _, _, _, hr' => hr'.elim
  | node _ _ _, left _, left _, .right _, _, hp, _, _, _ => hp.elim
  | node _ _ _, left _, left _, .left _, .right _, _, _, hr, _ => hr.elim
  | node _ _ _, right _, right _, .left _, _, hp, _, _, _ => hp.elim
  | node _ _ _, right _, right _, .right _, .left _, _, _, hr, _ => hr.elim
  | merge _ _ _, s, s', p, r, hp, hp', hr, hr' => by
    rcases leaf_cases r with ⟨i, x, rfl⟩ | ⟨x, rfl⟩
    · cases s with
      | top j =>
        obtain rfl := mem_top_brLeaf.1 hr
        cases s' with
        | top j' => rw [mem_top_brLeaf.1 hr']
        | inBr j' s'' =>
          rcases leaf_cases p with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
          · exact (not_part_top_brLeaf hp).elim
          · exact (not_part_inBr_dLeaf hp').elim
        | inD _ => exact (not_mem_inD_brLeaf hr').elim
      | inBr j s₁ =>
        by_cases hj : i = j
        · subst hj
          cases s' with
          | top _ =>
            rcases leaf_cases p with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
            · exact (not_part_top_brLeaf hp').elim
            · exact (not_part_inBr_dLeaf hp).elim
          | inBr j' s₂ =>
            by_cases hj' : i = j'
            · subst hj'
              rcases leaf_cases p with ⟨i', y, rfl⟩ | ⟨_, rfl⟩
              · by_cases hi' : i' = i
                · subst hi'
                  rw [eq_of_part_of_mem (part_inBr_brLeaf_self.1 hp) (part_inBr_brLeaf_self.1 hp')
                    (mem_inBr_brLeaf_self.1 hr) (mem_inBr_brLeaf_self.1 hr')]
                · exact (not_part_inBr_brLeaf hi' hp).elim
              · exact (not_part_inBr_dLeaf hp).elim
            · exact (not_mem_inBr_brLeaf hj' hr').elim
          | inD _ => exact (not_mem_inD_brLeaf hr').elim
        · exact (not_mem_inBr_brLeaf hj hr).elim
      | inD _ => exact (not_mem_inD_brLeaf hr).elim
    · cases s with
      | top _ => exact (not_mem_top_dLeaf hr).elim
      | inBr _ _ => exact (not_mem_inBr_dLeaf hr).elim
      | inD s₁ =>
        cases s' with
        | top _ => exact (not_mem_top_dLeaf hr').elim
        | inBr _ _ => exact (not_mem_inBr_dLeaf hr').elim
        | inD s₂ =>
          rcases leaf_cases p with ⟨_, _, rfl⟩ | ⟨y, rfl⟩
          · exact (not_part_inD_brLeaf hp).elim
          · exact congrArg inD (eq_of_part_of_mem (t := _) hp hp' hr hr')

/-! ### Nesting -/

theorem forall_mem_left {k : Comp} {a b : MTerm ι} {s : Site a} {P : (node k a b).toSP.Leaf → Prop} :
    (∀ q, (left (b := b) (k := k) s).mem q → P q) ↔ ∀ x, s.mem x → P (.left x) := by
  refine ⟨fun h x hx => h _ hx, fun h q hq => ?_⟩
  rcases q with _ | x | x
  · exact h x hq
  · exact hq.elim

theorem forall_mem_right {k : Comp} {a b : MTerm ι} {s : Site b}
    {P : (node k a b).toSP.Leaf → Prop} :
    (∀ q, (right (a := a) (k := k) s).mem q → P q) ↔ ∀ x, s.mem x → P (.right x) := by
  refine ⟨fun h x hx => h _ hx, fun h q hq => ?_⟩
  rcases q with _ | x | x
  · exact hq.elim
  · exact h x hq

section MergeForall

variable {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} {P : (merge r br d).toSP.Leaf → Prop}

theorem forall_mem_inBr {i : Fin r} {s : Site (br i)} :
    (∀ q, (inBr (d := d) i s).mem q → P q) ↔ ∀ x, s.mem x → P (brLeaf i x) := by
  refine ⟨fun h x hx => h _ (mem_inBr_brLeaf_self.2 hx), fun h q hq => ?_⟩
  obtain ⟨x, rfl, hx⟩ := eq_brLeaf_of_mem_inBr hq
  exact h x hx

theorem forall_mem_inD {s : Site d} :
    (∀ q, (inD (br := br) s).mem q → P q) ↔ ∀ x, s.mem x → P (dLeaf x) := by
  refine ⟨fun h x hx => h _ hx, fun h q hq => ?_⟩
  rcases leaf_cases q with ⟨_, _, rfl⟩ | ⟨x, rfl⟩
  · exact (not_mem_inD_brLeaf hq).elim
  · exact h x hq

end MergeForall

/-- **The merges nest**: if `p` is in the part of `s` and the leaf `r` of the branch of `s'` is
before the branch of `s`, the part of `s'` contains the branch of `s` exactly when it contains
`p`. -/
theorem part_iff_of_before : {t : MTerm ι} → {s s' : Site t} → {p r : t.toSP.Leaf} → s.part p →
    s'.mem r → (∀ q, s.mem q → r.Before q) → ((∀ q, s.mem q → s'.part q) ↔ s'.part p)
  | node _ _ _, left s, left s', .left _, .left _, hp, hr, hbef => by
    rw [forall_mem_left]
    exact part_iff_of_before (t := _) (s := s) (s' := s') hp hr fun x hx => hbef (.left x) hx
  | node _ _ _, right s, right s', .right _, .right _, hp, hr, hbef => by
    rw [forall_mem_right]
    exact part_iff_of_before (t := _) (s := s) (s' := s') hp hr fun x hx => hbef (.right x) hx
  | node _ _ _, left s, right _, _, .right _, _, _, hbef => by
    obtain ⟨x, hx⟩ := exists_mem s
    exact (hbef (.left x) hx).elim
  | node _ _ _, right s, left _, .right _, .left _, _, _, _ => by
    obtain ⟨x, hx⟩ := exists_mem s
    exact iff_of_false (fun h => h (.right x) hx) id
  | node _ _ _, left _, left _, .right _, _, hp, _, _ => hp.elim
  | node _ _ _, left _, left _, .left _, .right _, _, hr, _ => hr.elim
  | node _ _ _, left _, right _, _, .left _, _, hr, _ => hr.elim
  | node _ _ _, right _, left _, .left _, _, hp, _, _ => hp.elim
  | node _ _ _, right _, left _, .right _, .right _, _, hr, _ => hr.elim
  | node _ _ _, right _, right _, .left _, _, hp, _, _ => hp.elim
  | node _ _ _, right _, right _, .right _, .left _, _, hr, _ => hr.elim
  | merge _ br _, s, s', p, r, hp, hr, hbef => by
    cases s with
    | top i =>
      obtain ⟨x⟩ := nonempty_leaf (br i)
      have hq := hbef (brLeaf i x) (mem_top_brLeaf.2 rfl)
      rcases leaf_cases r with ⟨i', y, rfl⟩ | ⟨y, rfl⟩
      · by_cases hi : i' = i
        · subst hi
          exact (Leaf.not_before_self _ (hbef _ (mem_top_brLeaf.2 rfl))).elim
        · exact (not_brLeaf_before_brLeaf hi hq).elim
      · exact (not_dLeaf_before_brLeaf hq).elim
    | inBr i s₀ =>
      obtain ⟨x, hx⟩ := exists_mem s₀
      have hq := hbef (brLeaf i x) (mem_inBr_brLeaf_self.2 hx)
      rcases leaf_cases p with ⟨i'', z, rfl⟩ | ⟨z, rfl⟩
      · by_cases hi'' : i'' = i
        · subst hi''
          have hz := part_inBr_brLeaf_self.1 hp
          cases s' with
          | top _ =>
            exact iff_of_false (fun h => not_part_top_brLeaf (h _ (mem_inBr_brLeaf_self.2 hx)))
              not_part_top_brLeaf
          | inBr i' s₁ =>
            rcases leaf_cases r with ⟨i₁, y, rfl⟩ | ⟨y, rfl⟩
            · by_cases hi₁ : i₁ = i'
              · subst hi₁
                have hy := mem_inBr_brLeaf_self.1 hr
                by_cases hi : i₁ = i''
                · subst hi
                  rw [forall_mem_inBr, part_inBr_brLeaf_self]
                  simp only [part_inBr_brLeaf_self]
                  exact part_iff_of_before hz hy fun x' hx' =>
                    brLeaf_before_brLeaf.1 (hbef _ (mem_inBr_brLeaf_self.2 hx'))
                · exact (not_brLeaf_before_brLeaf hi hq).elim
              · exact (not_mem_inBr_brLeaf hi₁ hr).elim
            · exact (not_mem_inBr_dLeaf hr).elim
          | inD _ =>
            exact iff_of_false (fun h => not_part_inD_brLeaf (h _ (mem_inBr_brLeaf_self.2 hx)))
              not_part_inD_brLeaf
        · exact (not_part_inBr_brLeaf hi'' hp).elim
      · exact (not_part_inBr_dLeaf hp).elim
    | inD s₀ =>
      obtain ⟨x, hx⟩ := exists_mem s₀
      rcases leaf_cases p with ⟨_, _, rfl⟩ | ⟨z, rfl⟩
      · exact (not_part_inD_brLeaf hp).elim
      · cases s' with
        | top _ => exact iff_of_true (fun q _ => by
            rcases leaf_cases q with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
            · contradiction
            · exact part_top_dLeaf) part_top_dLeaf
        | inBr _ _ =>
          exact iff_of_false (fun h => not_part_inBr_dLeaf (h (dLeaf x) hx)) not_part_inBr_dLeaf
        | inD s₁ =>
          rcases leaf_cases r with ⟨_, _, rfl⟩ | ⟨y, rfl⟩
          · exact (not_mem_inD_brLeaf hr).elim
          · rw [forall_mem_inD]
            exact part_iff_of_before (t := _) (s := s₀) (s' := s₁) hp hr fun x' hx' =>
              hbef (dLeaf x') hx'

end Site

/-! ### The number of branches hidden from a leaf -/

/-- **The largest number of branches hidden from one leaf**, computed on the term: `0` at a
leaf, the larger of the two subterms' at a node, and at a merge of `r` branches the larger of the
branches' and `r` plus the part's. For a message `i` this is the sum of the numbers of branches of
the merges whose part contains `i`, maximized over `i` (`nJ_merges`). -/
def nJ : MTerm ι → ℕ
  | leaf _ => 0
  | node _ a b => max a.nJ b.nJ
  | merge r br d => max (Finset.univ.sup fun i => (br i).nJ) (r + d.nJ)

namespace Site

/-- The number of branches hidden from the leaf `p`. -/
def hideCount (t : MTerm ι) (p : t.toSP.Leaf) : ℕ := (Finset.univ.filter fun s : Site t => s.part p).card

@[simp] theorem part_left_left {k : Comp} {a b : MTerm ι} (s : Site a) (x : a.toSP.Leaf) :
    (left (k := k) (b := b) s).part (.left x) ↔ s.part x := Iff.rfl

@[simp] theorem not_part_left_right {k : Comp} {a b : MTerm ι} (s : Site a) (x : b.toSP.Leaf) :
    ¬ (left (k := k) (b := b) s).part (.right x) := id

@[simp] theorem not_part_right_left {k : Comp} {a b : MTerm ι} (s : Site b) (x : a.toSP.Leaf) :
    ¬ (right (k := k) (a := a) s).part (.left x) := id

@[simp] theorem part_right_right {k : Comp} {a b : MTerm ι} (s : Site b) (x : b.toSP.Leaf) :
    (right (k := k) (a := a) s).part (.right x) ↔ s.part x := Iff.rfl

theorem hideCount_left {k : Comp} {a b : MTerm ι} (x : a.toSP.Leaf) :
    hideCount (node k a b) (.left x) = hideCount a x := by
  unfold hideCount
  rw [Finset.card_filter, ← Equiv.sum_comp equivNode.symm, Fintype.sum_sum_type]
  simp [equivNode]

theorem hideCount_right {k : Comp} {a b : MTerm ι} (x : b.toSP.Leaf) :
    hideCount (node k a b) (.right x) = hideCount b x := by
  unfold hideCount
  rw [Finset.card_filter, ← Equiv.sum_comp equivNode.symm, Fintype.sum_sum_type]
  simp [equivNode]

theorem hideCount_brLeaf {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} (i : Fin r)
    (x : (br i).toSP.Leaf) : hideCount (merge r br d) (brLeaf i x) = hideCount (br i) x := by
  unfold hideCount
  rw [Finset.card_filter, ← Equiv.sum_comp equivMerge.symm,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [equivMerge, Equiv.coe_fn_symm_mk, not_part_top_brLeaf, not_part_inD_brLeaf,
    ite_false, Finset.sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact Finset.sum_eq_zero fun s _ => ite_eq_right_iff.2 fun h =>
      (not_part_inBr_brLeaf (Ne.symm hj) h).elim
  · simp

theorem hideCount_dLeaf {r : ℕ} {br : Fin r → MTerm ι} {d : MTerm ι} (x : d.toSP.Leaf) :
    hideCount (merge r br d) (dLeaf x) = r + hideCount d x := by
  unfold hideCount
  rw [Finset.card_filter, ← Equiv.sum_comp equivMerge.symm,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [equivMerge, not_part_inBr_dLeaf]

/-- Every leaf is hidden from at most `nJ` branches. -/
theorem hideCount_le : (t : MTerm ι) → (p : t.toSP.Leaf) → hideCount t p ≤ t.nJ
  | node _ a _, .left x => by
    rw [hideCount_left]
    exact (hideCount_le a x).trans (le_max_left _ _)
  | node _ _ b, .right x => by
    rw [hideCount_right]
    exact (hideCount_le b x).trans (le_max_right _ _)
  | merge _ br d, p => by
    rcases leaf_cases p with ⟨i, x, rfl⟩ | ⟨x, rfl⟩
    · rw [hideCount_brLeaf]
      exact ((hideCount_le (br i) x).trans
        (Finset.le_sup (f := fun i => (br i).nJ) (Finset.mem_univ i))).trans (le_max_left _ _)
    · rw [hideCount_dLeaf]
      exact (Nat.add_le_add_left (hideCount_le d x) _).trans (le_max_right _ _)
  | leaf _, .here _ => (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun s => nomatch s)).le

/-- Some leaf is hidden from exactly `nJ` branches. -/
theorem exists_hideCount_eq : (t : MTerm ι) → ∃ p : t.toSP.Leaf, hideCount t p = t.nJ
  | leaf j => ⟨.here j, Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun s => nomatch s)⟩
  | node _ a b => by
    rcases le_total a.nJ b.nJ with h | h
    · obtain ⟨x, hx⟩ := exists_hideCount_eq b
      exact ⟨.right x, by rw [hideCount_right, hx, nJ, max_eq_right h]⟩
    · obtain ⟨x, hx⟩ := exists_hideCount_eq a
      exact ⟨.left x, by rw [hideCount_left, hx, nJ, max_eq_left h]⟩
  | merge r br d => by
    by_cases h : (Finset.univ.sup fun i => (br i).nJ) ≤ r + d.nJ
    · obtain ⟨x, hx⟩ := exists_hideCount_eq d
      exact ⟨dLeaf x, by rw [hideCount_dLeaf, hx, nJ, max_eq_right h]⟩
    · have hr : (Finset.univ : Finset (Fin r)).Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sup_empty, Nat.bot_eq_zero] at h
        omega
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hr fun i => (br i).nJ
      obtain ⟨x, hx⟩ := exists_hideCount_eq (br i)
      exact ⟨brLeaf i x, by rw [hideCount_brLeaf, hx, nJ, max_eq_left (by omega), hi]⟩

end Site

/-- **The merges of a term with merges**, on its series–parallel term. -/
def merges (t : MTerm ι) : Merges t.toSP where
  Site := Site t
  mem := Site.mem
  part := Site.part
  exists_mem := Site.exists_mem
  before_of_before_mem := Site.before_of_before_mem
  before_of_part := Site.before_of_part
  eq_of_part_of_mem := Site.eq_of_part_of_mem
  part_iff_of_before := Site.part_iff_of_before

/-- **The paper's `n_J` of a term with merges** (`def:bcs-quantities`): the largest number of
branches hidden from one leaf is `nJ`, computed on the term. -/
theorem nJ_merges (t : MTerm ι) : t.merges.nJ = t.nJ :=
  le_antisymm (Finset.sup_le fun p _ => Site.hideCount_le t p)
    (let ⟨p, hp⟩ := Site.exists_hideCount_eq t
     hp ▸ Finset.le_sup (f := fun p => Site.hideCount t p) (Finset.mem_univ p))

end MTerm

end GordieHowe.SPBCS
