-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoin
public import GordieHowe.SPBCS.TermIso

@[expose] public section

/-!
# A multi-circuit IOP with forked domains as a term with merges

The series–parallel term of a multi-circuit IOP with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP.term`) with the
merges of the proof system: each domain merges its branches into its join part, so the chain input of
a join round reads every branch of its domain through the branch's final digest.

    seq prefix (par over d of (merge over b of branch d b) into (join d))

* `mterm`: the term with merges (`MTerm`): the prefix, then the domains side by side
  (`MTerm.nodeNPos`), domain `d` the merge of its branches into its join part (`domainMTerm`).
* `leafIso`: an `MTerm` has no empty composition while `term` ends its domains with `nil`
  (`SPTerm.nodeN`), so `mterm.toSP` is not `term`; the two have isomorphic causal orders
  (`SPTerm.LeafIso`).
* `merges`, `siteLayout`: the merges and the site layout of `term`, those of `mterm`
  (`MTerm.merges`, `MTerm.siteLayout`) along `leafIso` (`Merges.comap`).
* Sizes: one site per branch (`card_site`), at most the largest branch count hidden from one leaf
  (`nJ_merges`), site codes, leaf paths and observer labels of at most `m + N + 3` bytes for
  branch counts at most `N` (`length_code_le`, `length_pathBytes_le`, `length_label_le`).
-/

namespace GordieHowe

open IOP IOP.SPTerm GordieHowe.SPBCS

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-- **Domain `d` as a term with merges**: the merge of its branches into its join part. -/
abbrev domainMTerm (d : Fin C.m) : MTerm C.shape.Idx :=
  .merge (C.shape.nb d) (fun b => .leaf (.br d b)) (.leaf (.jn d))

/-- **The series–parallel term with merges** (module docstring). -/
def mterm : MTerm C.shape.Idx :=
  .node .seq (.leaf .pre) (MTerm.nodeNPos .par C.m C.domainMTerm)

/-- **The series–parallel term and the term with merges have isomorphic causal orders.** -/
def leafIso : LeafIso C.term C.mterm.toSP :=
  LeafIso.node (RelIso.refl _) (MTerm.nodeNPosIso .par C.m C.domainMTerm)

/-- **The merges of the series–parallel term**: those of `mterm` along `leafIso`. -/
def merges : Merges C.term := C.mterm.merges.comap C.leafIso

/-- **The site layout of the merges** (`MTerm.siteLayout` along `leafIso`). -/
def siteLayout : SiteLayout C.merges := C.mterm.siteLayout.comap C.leafIso

/-- **One site per branch.** -/
theorem card_site : Fintype.card C.merges.Site = ∑ d, C.shape.nb d := by
  change Fintype.card (MTerm.Site C.mterm) = _
  rw [mterm, MTerm.card_site_node, MTerm.card_site_leaf, MTerm.card_site_nodeNPos, Nat.zero_add]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MTerm.card_site_merge, MTerm.card_site_leaf]
  simp [MTerm.card_site_leaf]

/-- **The largest number of branches hidden from one leaf** is the largest branch count of a
domain (the join part of a domain reads its branches through their final digests). -/
theorem nJ_merges : C.merges.nJ = Finset.univ.sup C.shape.nb := by
  rw [merges, Merges.nJ_comap, MTerm.nJ_merges, mterm, MTerm.nJ, MTerm.nJ_nodeNPos]
  simp [MTerm.nJ]

/-- **The site codes have at most `m + N + 2` bytes** for branch counts at most `N`. -/
theorem length_code_le {N : ℕ} (hN : ∀ d, C.shape.nb d ≤ N) (s : C.merges.Site) :
    (C.siteLayout.code s).length ≤ C.m + N + 2 := by
  have h1 : (C.siteLayout.code s).length ≤ C.mterm.codeLen := MTerm.Site.length_code_le (t := C.mterm) s
  have h2 := MTerm.codeLen_nodeNPos_le .par C.m C.domainMTerm
  have h3 : (Finset.univ.sup fun d => (C.domainMTerm d).codeLen) ≤ N + 2 :=
    Finset.sup_le fun d _ => by
      have h0 : (Finset.univ.sup fun _ : Fin (C.shape.nb d) => (0 : ℕ)) = 0 :=
        Nat.eq_zero_of_le_zero (Finset.sup_le fun _ _ => le_rfl)
      change C.shape.nb d + 2 + max (Finset.univ.sup fun _ : Fin (C.shape.nb d) => (0 : ℕ)) 0 ≤ N + 2
      rw [h0, Nat.max_self]
      have := hN d
      omega
  have h4 := NeZero.pos C.m
  have h5 : C.mterm.codeLen = 1 + (MTerm.nodeNPos .par C.m C.domainMTerm).codeLen := by
    simp [mterm, MTerm.codeLen]
  omega

/-- **The path bytes of a leaf of the series–parallel term** have at most `m + N + 2` bytes for branch
counts at most `N`: one step into the prefix or the domains, `d + 1` to domain `d`, one into its
branches or its join, and `b + 1` to branch `b`. -/
theorem length_pathBytes_le {N : ℕ} (hN : ∀ d, C.shape.nb d ≤ N) (p : C.term.Leaf) :
    p.pathBytes.length ≤ C.m + N + 2 := by
  have hm : C.shape.nd = C.m := rfl
  rw [← IOP.Shape.leafOf_label p]
  rcases p.label with _ | ⟨d, b⟩ | d
  · simp [IOP.Shape.leafOf, Leaf.pathBytes]
  · have := hN d
    have := b.2
    have := d.2
    simp only [IOP.Shape.leafOf, Leaf.pathBytes, List.length_cons,
      Leaf.length_pathBytes_inN, List.length_nil]
    omega
  · have := d.2
    simp only [IOP.Shape.leafOf, Leaf.pathBytes, List.length_cons,
      Leaf.length_pathBytes_inN, List.length_nil]
    omega

/-- **The label of a leaf of the series–parallel term** has at most `m + N + 2` bytes. -/
theorem length_pathLabel_le {N : ℕ} (hN : ∀ d, C.shape.nb d ≤ N) (p : C.term.Leaf) :
    p.pathLabel.length ≤ C.m + N + 2 := by
  unfold Leaf.pathLabel
  split_ifs
  · simp
  · exact C.length_pathBytes_le hN p

/-- **The label of an observer** (`MergeBytes.label`: a tag byte, then a leaf's path bytes or a
site's code) has at most `m + N + 3` bytes for branch counts at most `N`. -/
theorem length_label_le {N : ℕ} (hN : ∀ d, C.shape.nb d ≤ N) (o : C.merges.Obs) :
    (MergeBytes.label C.siteLayout o).length ≤ C.m + N + 3 := by
  cases o with
  | leaf p =>
    have := C.length_pathBytes_le hN p
    simp only [MergeBytes.label, List.length_cons]
    omega
  | sink s =>
    have := C.length_code_le hN s
    simp only [MergeBytes.label, List.length_cons]
    omega

end RealizedProgram.ProofSystem.IOP

end GordieHowe
