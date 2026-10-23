-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalLeaves

@[expose] public section

/-!
# The series–parallel shape of a multi-circuit IOP with forked domains

The series–parallel term the proof system's transcripts realize (`lib/gordiehowe/transcript_fork.h`):
a prefix, then the domains side by side; in each domain its branches (the batches in compiled
order, then GKR) side by side, then the domain's join part.

    seq prefix (par over d of (seq (par over b of branch d b) (join d)))

* `Shape`: the number of domains `nd` and the number of branches `nb d ≥ 1` of each domain.
* `Shape.Idx`: the components, one per leaf: the prefix `pre`, the branches `br d b` and the join
  parts `jn d`; `Shape.term` is the term over them.
* `Shape.leafOf`: the leaf of a component; every leaf is the leaf of its label (`leafOf_label`),
  so the leaves and the components correspond (`leafEquiv`).
* `before_iff`: the causal order (`IdxBefore`). The prefix is before every other leaf, and each
  branch of a domain is before the domain's join part; nothing else is ordered.
-/

namespace GordieHowe.RealizedProgram.ProofSystem.IOP

open GordieHowe.IOP IOP.SPTerm

/-- **The series–parallel shape**: `nd` domains, domain `d` with `nb d ≥ 1` branches (every domain of
the proof system has its GKR branch). -/
structure Shape where
  /-- The number of domains. -/
  nd : ℕ
  /-- The number of branches of each domain. -/
  nb : Fin nd → ℕ
  /-- Every domain has a branch. -/
  nb_pos : ∀ d, 0 < nb d

namespace Shape

variable (S : Shape)

/-- **The components of the series–parallel term**: the prefix, the branches and the join parts. -/
inductive Idx where
  /-- The prefix. -/
  | pre
  /-- Branch `b` of domain `d`. -/
  | br (d : Fin S.nd) (b : Fin (S.nb d))
  /-- The join part of domain `d`. -/
  | jn (d : Fin S.nd)
  deriving DecidableEq

/-- **The series–parallel term**: the prefix, then the domains side by side, each its branches side by
side and then its join part. -/
abbrev term : SPTerm S.Idx :=
  seq (leaf .pre) (parN S.nd fun d => seq (parN (S.nb d) fun b => leaf (.br d b)) (leaf (.jn d)))

/-- **The leaf of a component.** -/
def leafOf : S.Idx → S.term.Leaf
  | .pre => .left (.here _)
  | .br d b => .right (Leaf.inN .par S.nd d (.left (Leaf.inN .par (S.nb d) b (.here _))))
  | .jn d => .right (Leaf.inN .par S.nd d (.right (.here _)))

variable {S}

@[simp] theorem label_leafOf (j : S.Idx) : (S.leafOf j).label = j := by
  cases j <;> simp [leafOf]

/-- **Every leaf is the leaf of its label.** -/
theorem leafOf_label (p : S.term.Leaf) : S.leafOf p.label = p := by
  rcases p with _ | ⟨⟨⟩⟩ | q
  · rfl
  · obtain ⟨d, q', rfl⟩ := Leaf.exists_inN .par S.nd q
    rcases q' with _ | q'' | ⟨⟨⟩⟩
    · obtain ⟨b, ⟨⟩, rfl⟩ := Leaf.exists_inN .par (S.nb d) q''
      simp [leafOf]
    · simp [leafOf]

/-- The relation `before_iff` states on components. -/
def IdxBefore : S.Idx → S.Idx → Prop
  | .pre, .pre => False
  | .pre, _ => True
  | .br d _, .jn d' => d = d'
  | _, _ => False

theorem leafOf_before_leafOf (j j' : S.Idx) :
    (S.leafOf j).Before (S.leafOf j') ↔ IdxBefore j j' := by
  cases j with
  | pre => cases j' <;> simp [leafOf, IdxBefore, Leaf.Before]
  | br d b =>
    cases j' with
    | pre => simp [leafOf, IdxBefore]
    | br d' b' =>
      simp only [leafOf, Leaf.before_right_right, IdxBefore, iff_false]
      by_cases hd : d = d'
      · subst hd
        rw [Leaf.inN_before_inN_iff, Leaf.before_left_left]
        by_cases hb : b = b'
        · subst hb
          rw [Leaf.inN_before_inN_iff]
          exact id
        · exact Leaf.not_inN_before_inN_par _ hb _ _
      · exact Leaf.not_inN_before_inN_par _ hd _ _
    | jn d' =>
      simp only [leafOf, Leaf.before_right_right, IdxBefore]
      by_cases hd : d = d'
      · subst hd
        rw [Leaf.inN_before_inN_iff, Leaf.before_left_right]
        simp
      · simp only [hd, iff_false]
        exact Leaf.not_inN_before_inN_par _ hd _ _
  | jn d =>
    cases j' with
    | pre => simp [leafOf, IdxBefore]
    | br d' b' =>
      simp only [leafOf, Leaf.before_right_right, IdxBefore, iff_false]
      by_cases hd : d = d'
      · subst hd
        rw [Leaf.inN_before_inN_iff]
        exact Leaf.not_before_right_left _ _
      · exact Leaf.not_inN_before_inN_par _ hd _ _
    | jn d' =>
      simp only [leafOf, Leaf.before_right_right, IdxBefore, iff_false]
      by_cases hd : d = d'
      · subst hd
        rw [Leaf.inN_before_inN_iff, Leaf.before_right_right]
        exact id
      · exact Leaf.not_inN_before_inN_par _ hd _ _

/-- **The causal order of the series–parallel term**: the prefix is before every other leaf, and each
branch of a domain is before the domain's join part (`IdxBefore`). -/
theorem before_iff (q p : S.term.Leaf) : q.Before p ↔ IdxBefore q.label p.label := by
  rw [← leafOf_label q, ← leafOf_label p, leafOf_before_leafOf, label_leafOf, label_leafOf]

theorem eq_leafOf_of_label {p : S.term.Leaf} {j : S.Idx} (h : p.label = j) : p = S.leafOf j := by
  rw [← h, leafOf_label]

/-- **The rounds of the series–parallel term**: the prefix's, then every domain's branches' and join
part's. -/
theorem size_term (n : S.Idx → ℕ) :
    S.term.size n = n .pre + ∑ d, (∑ b, n (.br d b) + n (.jn d)) := by
  simp [size_nodeN]

/-- **A sum over the leaves of the series–parallel term** is the prefix's, then every domain's branches'
and join part's. -/
theorem sum_leaves_label (n : S.Idx → ℕ) :
    ∑ q : S.term.Leaf, n q.label = n .pre + ∑ d, (∑ b, n (.br d b) + n (.jn d)) := by
  rw [← size_eq_sum, size_term]

end Shape

end GordieHowe.RealizedProgram.ProofSystem.IOP
