-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.TermLayout

@[expose] public section

/-!
# Merges along an isomorphism of causal orders

The merges on a series–parallel term (`Merges`) read the term only through its leaves and their
causal order (`Leaf.Before`), so they carry over along an isomorphism of causal orders. This lets
a term with merges (`MTerm`) give the merges of a series–parallel term that is not literally its
`toSP`: an `MTerm` has no empty composition, so a term built with `SPTerm.nodeN` (which ends in
`nil`) is reached through `nodeNPos` and its isomorphism `nodeNPosIso`.

* `SPTerm.LeafIso t t'`: an isomorphism of the causal orders of the leaves of `t` and `t'`
  (Mathlib's `RelIso` for `Leaf.Before`); `LeafIso.node` composes two, `LeafIso.nodeNil` drops an
  empty second subterm.
* `Merges.comap e Mg`, `SiteLayout.comap e Λ`: the merges and the site layout of `t` from those of
  `t'` along `e : LeafIso t t'`, with the same sites and the same `nJ` (`nJ_comap`).
* `MTerm.nodeNSucc k m c`, `MTerm.nodeNPos k m c`: `m + 1` (or `m ≥ 1`) terms with merges composed
  by `k`, whose `toSP` is isomorphic to `SPTerm.nodeN k m` of their `toSP`s
  (`nodeNSuccIso`, `nodeNPosIso`).
* `MTerm.codeLen`: a bound on the length of the code of every site (`Site.length_code_le`); the
  number of sites of a node, a merge and composed terms (`card_site_node`, `card_site_merge`,
  `card_site_nodeNPos`).
-/

namespace GordieHowe.IOP.SPTerm

variable {ι : Type}

/-- **An isomorphism of the causal orders of the leaves of two terms**: a bijection of the leaves
that preserves and reflects `Before`. -/
abbrev LeafIso (t t' : SPTerm ι) : Type :=
  (Leaf.Before : t.Leaf → t.Leaf → Prop) ≃r (Leaf.Before : t'.Leaf → t'.Leaf → Prop)

namespace LeafIso

variable {k : Comp} {a a' b b' : SPTerm ι}

/-- The leaf map of two subterm maps on a node. -/
def nodeMap (f : a.Leaf → a'.Leaf) (g : b.Leaf → b'.Leaf) :
    (node k a b).Leaf → (node k a' b').Leaf
  | .left p => .left (f p)
  | .right p => .right (g p)

/-- **Two isomorphisms of the subterms give one of the node.** -/
def node (ea : LeafIso a a') (eb : LeafIso b b') : LeafIso (node k a b) (node k a' b') where
  toFun := nodeMap ea eb
  invFun := nodeMap ea.symm eb.symm
  left_inv p := by
    cases p <;> simp [nodeMap]
  right_inv p := by
    cases p <;> simp [nodeMap]
  map_rel_iff' {q p} := by
    cases q <;> cases p <;> simp only [nodeMap, Equiv.coe_fn_mk, Leaf.before_left_left,
      Leaf.before_right_right, Leaf.before_left_right, Leaf.not_before_right_left]
    · exact ea.map_rel_iff
    · exact eb.map_rel_iff

/-- The leaf of the first subterm of a node whose second subterm is empty. -/
def ofNodeNil : (SPTerm.node k a nil).Leaf → a.Leaf
  | .left p => p

/-- **A node with an empty second subterm has the leaves of its first subterm.** -/
def nodeNil (a : SPTerm ι) : LeafIso (SPTerm.node k a nil) a where
  toFun := ofNodeNil
  invFun := .left
  left_inv p := by
    cases p with
    | left p => rfl
    | right p => cases p
  right_inv _ := rfl
  map_rel_iff' {q p} := by
    cases q with
    | left q =>
      cases p with
      | left p => exact Iff.rfl
      | right p => cases p
    | right q => cases q

end LeafIso

end GordieHowe.IOP.SPTerm

namespace GordieHowe.SPBCS

open GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t t' : SPTerm ι}

namespace Merges

/-- **The merges of `t` from those of `t'`** along an isomorphism of their causal orders: the same
sites, a leaf of `t` in a branch or a part when its image is. -/
def comap (e : LeafIso t t') (Mg : Merges t') : Merges t where
  Site := Mg.Site
  mem s q := Mg.mem s (e q)
  instDecMem s q := inferInstanceAs (Decidable (Mg.mem s (e q)))
  part s p := Mg.part s (e p)
  instDecPart s p := inferInstanceAs (Decidable (Mg.part s (e p)))
  exists_mem s := by
    obtain ⟨q, hq⟩ := Mg.exists_mem s
    exact ⟨e.symm q, by simpa using hq⟩
  before_of_before_mem hq hq' hr hb :=
    e.map_rel_iff.1 (Mg.before_of_before_mem hq hq' hr (e.map_rel_iff.2 hb))
  before_of_part hq hp := e.map_rel_iff.1 (Mg.before_of_part hq hp)
  eq_of_part_of_mem := Mg.eq_of_part_of_mem
  part_iff_of_before {s s' p r} hp hr hall := by
    have hall' : ∀ q, Mg.mem s q → (e r).Before q := fun q hq => by
      have h := e.map_rel_iff.2 (hall (e.symm q) (by simpa using hq))
      simpa using h
    rw [← Mg.part_iff_of_before hp hr hall']
    constructor
    · intro h q hq
      simpa using h (e.symm q) (by simpa using hq)
    · intro h q hq
      exact h (e q) hq

variable (e : LeafIso t t') (Mg : Merges t')

theorem mem_comap {s : (Mg.comap e).Site} {q : t.Leaf} : (Mg.comap e).mem s q ↔ Mg.mem s (e q) :=
  Iff.rfl

theorem part_comap {s : (Mg.comap e).Site} {p : t.Leaf} :
    (Mg.comap e).part s p ↔ Mg.part s (e p) :=
  Iff.rfl

/-- **The merges along an isomorphism hide as many branches from one leaf.** -/
theorem nJ_comap : (Mg.comap e).nJ = Mg.nJ := by
  refine le_antisymm (Finset.sup_le fun p _ => ?_) (Finset.sup_le fun p _ => ?_)
  · exact Finset.le_sup (f := fun p : t'.Leaf => (Finset.univ.filter fun s => Mg.part s p).card)
      (Finset.mem_univ (e p))
  · calc (Finset.univ.filter fun s => Mg.part s p).card
        = (Finset.univ.filter fun s => Mg.part s (e (e.symm p))).card := by
          rw [RelIso.apply_symm_apply]
      _ ≤ (Mg.comap e).nJ := Finset.le_sup
          (f := fun p : t.Leaf => (Finset.univ.filter fun s => (Mg.comap e).part s p).card)
          (Finset.mem_univ (e.symm p))

end Merges

/-- **The site layout of the merges along an isomorphism**: the same sites and codes. -/
def SiteLayout.comap {Mg : Merges t'} (e : LeafIso t t') (Λ : SiteLayout Mg) :
    SiteLayout (Mg.comap e) where
  sites := Λ.sites
  nodup := Λ.nodup
  mem_sites := Λ.mem_sites
  code := Λ.code
  code_append_inj := Λ.code_append_inj

namespace MTerm

/-- **`m + 1` terms with merges composed by `k`**: `c 0` composed with the rest, ending with the
last term. -/
def nodeNSucc (k : Comp) : (m : ℕ) → (Fin (m + 1) → MTerm ι) → MTerm ι
  | 0, c => c 0
  | m + 1, c => node k (c 0) (nodeNSucc k m fun i => c i.succ)

/-- **`m + 1` terms composed by `k` have the causal order of `SPTerm.nodeN`** of their
series–parallel terms. -/
def nodeNSuccIso (k : Comp) : (m : ℕ) → (c : Fin (m + 1) → MTerm ι) →
    LeafIso (SPTerm.nodeN k (m + 1) fun i => (c i).toSP) (nodeNSucc k m c).toSP
  | 0, c => LeafIso.nodeNil (c 0).toSP
  | m + 1, c => LeafIso.node (RelIso.refl _) (nodeNSuccIso k m fun i => c i.succ)

/-- **`m ≥ 1` terms with merges composed by `k`** (`nodeNSucc`). -/
def nodeNPos (k : Comp) : (m : ℕ) → [NeZero m] → (Fin m → MTerm ι) → MTerm ι
  | 0, h, _ => absurd rfl h.ne
  | m + 1, _, c => nodeNSucc k m c

/-- **`m ≥ 1` terms composed by `k` have the causal order of `SPTerm.nodeN`** of their
series–parallel terms. -/
def nodeNPosIso (k : Comp) : (m : ℕ) → [NeZero m] → (c : Fin m → MTerm ι) →
    LeafIso (SPTerm.nodeN k m fun i => (c i).toSP) (nodeNPos k m c).toSP
  | 0, h, _ => absurd rfl h.ne
  | m + 1, _, c => nodeNSuccIso k m c

/-- **The largest number of branches hidden from one leaf of `m + 1` composed terms** is the
largest of the terms'. -/
theorem nJ_nodeNSucc (k : Comp) : (m : ℕ) → (c : Fin (m + 1) → MTerm ι) →
    (nodeNSucc k m c).nJ = Finset.univ.sup fun i => (c i).nJ
  | 0, c => by
    simp [nodeNSucc]
  | m + 1, c => by
    rw [nodeNSucc, nJ, nJ_nodeNSucc k m]
    conv_rhs => rw [Fin.univ_succ, Finset.sup_cons, Finset.sup_map]
    rfl

theorem nJ_nodeNPos (k : Comp) : (m : ℕ) → [NeZero m] → (c : Fin m → MTerm ι) →
    (nodeNPos k m c).nJ = Finset.univ.sup fun i => (c i).nJ
  | 0, h, _ => absurd rfl h.ne
  | m + 1, _, c => nJ_nodeNSucc k m c

/-- **A bound on the code length of the sites of a term**: `0` at a leaf, one more than the
subterms' at a node, and at a merge of `r` branches two more than `r` and the branches' and the
part's. -/
def codeLen : MTerm ι → ℕ
  | leaf _ => 0
  | node _ a b => 1 + max a.codeLen b.codeLen
  | merge r br d => r + 2 + max (Finset.univ.sup fun i => (br i).codeLen) d.codeLen

/-- **Every site's code has at most `codeLen` bytes.** -/
theorem Site.length_code_le : {t : MTerm ι} → (s : Site t) → s.code.length ≤ t.codeLen
  | _, .left s => by
    have := Site.length_code_le s
    simp only [Site.code, List.length_cons, codeLen]
    omega
  | _, .right s => by
    have := Site.length_code_le s
    simp only [Site.code, List.length_cons, codeLen]
    omega
  | _, .top i => by
    have := i.2
    simp only [Site.code, unary, List.length_cons, List.length_append, List.length_replicate,
      List.length_nil, codeLen]
    omega
  | _, .inBr (br := br) i s => by
    have := Site.length_code_le s
    have hi := i.2
    have hs : (br i).codeLen ≤ Finset.univ.sup fun i => (br i).codeLen :=
      Finset.le_sup (f := fun i => (br i).codeLen) (Finset.mem_univ i)
    simp only [Site.code, unary, List.length_cons, List.length_append, List.length_replicate,
      List.length_nil, codeLen]
    omega
  | _, .inD s => by
    have := Site.length_code_le s
    simp only [Site.code, List.length_cons, codeLen]
    omega

/-- **The code bound of `m + 1` composed terms**: `m` steps and the largest of the terms'. -/
theorem codeLen_nodeNSucc_le (k : Comp) : (m : ℕ) → (c : Fin (m + 1) → MTerm ι) →
    (nodeNSucc k m c).codeLen ≤ m + Finset.univ.sup fun i => (c i).codeLen
  | 0, c => by
    have : (c 0).codeLen ≤ Finset.univ.sup fun i => (c i).codeLen :=
      Finset.le_sup (f := fun i => (c i).codeLen) (Finset.mem_univ 0)
    change (c 0).codeLen ≤ 0 + _
    omega
  | m + 1, c => by
    have ih := codeLen_nodeNSucc_le k m fun i => c i.succ
    have h0 : (c 0).codeLen ≤ Finset.univ.sup fun i => (c i).codeLen :=
      Finset.le_sup (f := fun i => (c i).codeLen) (Finset.mem_univ 0)
    have hs : (Finset.univ.sup fun i : Fin (m + 1) => (c i.succ).codeLen) ≤
        Finset.univ.sup fun i => (c i).codeLen :=
      Finset.sup_le fun i _ => Finset.le_sup (f := fun i => (c i).codeLen) (Finset.mem_univ i.succ)
    change 1 + max (c 0).codeLen (nodeNSucc k m fun i => c i.succ).codeLen ≤ m + 1 + _
    omega

theorem codeLen_nodeNPos_le (k : Comp) : (m : ℕ) → [NeZero m] → (c : Fin m → MTerm ι) →
    (nodeNPos k m c).codeLen ≤ m - 1 + Finset.univ.sup fun i => (c i).codeLen
  | 0, h, _ => absurd rfl h.ne
  | m + 1, _, c => codeLen_nodeNSucc_le k m c

/-! ### The number of sites -/

theorem card_site_leaf (j : ι) : Fintype.card (Site (leaf j)) = 0 :=
  Fintype.card_eq_zero_iff.2 ⟨fun s => nomatch s⟩

theorem card_site_node (k : Comp) (a b : MTerm ι) :
    Fintype.card (Site (node k a b)) = Fintype.card (Site a) + Fintype.card (Site b) := by
  rw [Fintype.card_congr Site.equivNode, Fintype.card_sum]

theorem card_site_merge (r : ℕ) (br : Fin r → MTerm ι) (d : MTerm ι) :
    Fintype.card (Site (merge r br d)) = r + (∑ i, Fintype.card (Site (br i))) + Fintype.card (Site d) := by
  rw [Fintype.card_congr Site.equivMerge, Fintype.card_sum, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, Nat.add_assoc]

/-- **The sites of `m + 1` composed terms** are those of the terms. -/
theorem card_site_nodeNSucc (k : Comp) : (m : ℕ) → (c : Fin (m + 1) → MTerm ι) →
    Fintype.card (Site (nodeNSucc k m c)) = ∑ i, Fintype.card (Site (c i))
  | 0, c => by
    rw [Fin.sum_univ_one]
    rfl
  | m + 1, c => by
    rw [Fin.sum_univ_succ, ← card_site_nodeNSucc k m fun i => c i.succ]
    exact card_site_node k _ _

theorem card_site_nodeNPos (k : Comp) : (m : ℕ) → [NeZero m] → (c : Fin m → MTerm ι) →
    Fintype.card (Site (nodeNPos k m c)) = ∑ i, Fintype.card (Site (c i))
  | 0, h, _ => absurd rfl h.ne
  | m + 1, _, c => card_site_nodeNSucc k m c

end MTerm

end GordieHowe.SPBCS
