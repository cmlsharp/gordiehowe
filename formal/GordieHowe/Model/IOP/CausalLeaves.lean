-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Causal

@[expose] public section

/-!
# Leaves in term order, par-free terms and causal fixpoints

Facts about series–parallel terms (`GordieHowe/Model/IOP/Causal.lean`) that a Fiat–Shamir compiler over a
term uses.

* `SPTerm.leaves`: the leaves of a term in term order (first subterm, then second); every leaf
  occurs once (`mem_leaves`, `nodup_leaves`).
* `Leaf.ctxList p`: the leaves sequenced before `p`, in term order. A compiler writes the messages
  of these leaves, in this order, into the chain input of a challenge at `p`.
* `SPTerm.ParFree`: the term has no `par` node, so its leaves are totally ordered by `Before`
  (`ParFree.before_or_before`), and the leaves before `p` are a prefix of the term order ending
  just before `p` (`ParFree.leaves_eq`).
* `SPTerm.solve`: the causal fixpoint. Given, for each leaf, a value computed from the values of
  the leaves sequenced before it, `solve` computes all of them (`solve_eq`). A compiler computes
  the chains of all leaves this way, each from the chains in its causal past.
-/

namespace GordieHowe.IOP

namespace SPTerm

variable {ι : Type}

namespace Leaf

theorem left_injective {k : Comp} {a b : SPTerm ι} :
    Function.Injective (Leaf.left (k := k) (a := a) (b := b)) := fun _ _ h => by
  cases h
  rfl

theorem right_injective {k : Comp} {a b : SPTerm ι} :
    Function.Injective (Leaf.right (k := k) (a := a) (b := b)) := fun _ _ h => by
  cases h
  rfl

/-- `Before` is decidable. -/
instance decBefore : {t : SPTerm ι} → (q p : t.Leaf) → Decidable (q.Before p)
  | _, here _, here _ => isFalse id
  | _, left q, left p => decBefore q p
  | _, right q, right p => decBefore q p
  | node k _ _, left _, right _ => inferInstanceAs (Decidable (k = .seq))
  | _, right _, left _ => isFalse id

end Leaf

/-- **The leaves of a term in term order**: those of the first subterm, then those of the
second. -/
def leaves : (t : SPTerm ι) → List t.Leaf
  | nil => []
  | leaf j => [.here j]
  | node _ a b => a.leaves.map .left ++ b.leaves.map .right

@[simp] theorem leaves_node (k : Comp) (a b : SPTerm ι) :
    (node k a b).leaves = a.leaves.map .left ++ b.leaves.map .right := rfl

/-- Every leaf occurs in the term order. -/
theorem mem_leaves : {t : SPTerm ι} → (p : t.Leaf) → p ∈ t.leaves
  | _, .here _ => List.mem_singleton_self _
  | _, .left p => List.mem_append_left _ (List.mem_map_of_mem (mem_leaves p))
  | _, .right p => List.mem_append_right _ (List.mem_map_of_mem (mem_leaves p))

/-- Every leaf occurs once in the term order. -/
theorem nodup_leaves : (t : SPTerm ι) → t.leaves.Nodup
  | nil => List.nodup_nil
  | leaf _ => List.nodup_singleton _
  | node _ a b => by
    refine List.Nodup.append ((nodup_leaves a).map Leaf.left_injective)
      ((nodup_leaves b).map Leaf.right_injective) ?_
    intro x hx hy
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, -, hq⟩ := List.mem_map.1 hy
    cases hq

namespace Leaf

/-- **The leaves sequenced before `p`, in term order.** -/
def ctxList {t : SPTerm ι} (p : t.Leaf) : List t.Leaf := t.leaves.filter fun q => q.Before p

theorem mem_ctxList {t : SPTerm ι} {p q : t.Leaf} : q ∈ p.ctxList ↔ q.Before p := by
  simp [ctxList, mem_leaves]

theorem nodup_ctxList {t : SPTerm ι} (p : t.Leaf) : p.ctxList.Nodup :=
  (nodup_leaves t).filter _

theorem not_mem_ctxList_self {t : SPTerm ι} (p : t.Leaf) : p ∉ p.ctxList :=
  fun h => not_before_self p (mem_ctxList.1 h)

/-- The leaves before a first-subterm leaf are first-subterm leaves. -/
theorem ctxList_left {k : Comp} {a b : SPTerm ι} (p : a.Leaf) :
    (left (k := k) (b := b) p).ctxList = p.ctxList.map left := by
  simp only [ctxList, leaves_node, List.filter_append, List.filter_map]
  have : b.leaves.filter ((fun q => decide (q.Before (left (k := k) (b := b) p))) ∘ right) = [] :=
    List.filter_eq_nil_iff.2 fun q _ => by simp
  rw [this, List.map_nil, List.append_nil]
  rfl

/-- The leaves before a second-subterm leaf: all first-subterm leaves under `seq`, none under
`par`, then the second-subterm leaves before it. -/
theorem ctxList_right {k : Comp} {a b : SPTerm ι} (p : b.Leaf) :
    (right (k := k) (a := a) p).ctxList =
      (if k = .seq then a.leaves.map left else []) ++ p.ctxList.map right := by
  simp only [ctxList, leaves_node, List.filter_append, List.filter_map]
  congr 1
  split_ifs with hk
  · rw [List.filter_eq_self.2 fun q _ => by simp [hk]]
  · rw [List.filter_eq_nil_iff.2 fun q _ => by simp [hk], List.map_nil]

end Leaf

/-! ### Par-free terms -/

/-- **A par-free term**: no node runs its subterms side by side, so the leaves are totally ordered
(a chain of components). -/
def ParFree : SPTerm ι → Prop
  | nil => True
  | leaf _ => True
  | node k a b => k = .seq ∧ a.ParFree ∧ b.ParFree

/-- Being par-free is decidable. -/
instance decParFree : (t : SPTerm ι) → Decidable t.ParFree
  | nil => isTrue trivial
  | leaf _ => isTrue trivial
  | node k a b =>
    haveI := decParFree a
    haveI := decParFree b
    inferInstanceAs (Decidable (k = .seq ∧ a.ParFree ∧ b.ParFree))

/-- A `seq` node of par-free terms is par-free. -/
@[simp] theorem parFree_seq {a b : SPTerm ι} : (seq a b).ParFree ↔ a.ParFree ∧ b.ParFree := by
  simp [ParFree]

/-- A `par` node is not par-free. -/
@[simp] theorem not_parFree_par {a b : SPTerm ι} : ¬ (par a b).ParFree := by
  simp [ParFree]

/-- A chain of subterms is par-free when each subterm is. -/
theorem parFree_chainN : ∀ {m : ℕ} {c : Fin m → SPTerm ι}, (∀ i, (c i).ParFree) →
    (chainN m c).ParFree
  | 0, _, _ => trivial
  | m + 1, _, h => ⟨rfl, h 0, parFree_chainN (m := m) fun i => h i.succ⟩

namespace ParFree

/-- **In a par-free term the leaves are totally ordered by `Before`.** -/
theorem before_or_before : {t : SPTerm ι} → t.ParFree → ∀ (q p : t.Leaf), q ≠ p →
    q.Before p ∨ p.Before q
  | _, _, .here _, .here _, hne => absurd rfl hne
  | node _ _ _, h, .left q, .left p, hne =>
    before_or_before h.2.1 q p fun e => hne (e ▸ rfl)
  | node _ _ _, h, .right q, .right p, hne =>
    before_or_before h.2.2 q p fun e => hne (e ▸ rfl)
  | node _ _ _, h, .left _, .right _, _ => .inl h.1
  | node _ _ _, h, .right _, .left _, _ => .inr h.1

/-- **In a par-free term the leaves before `p` are the leaves preceding `p` in term order**: the
term order is `p.ctxList ++ p :: R` for the leaves `R` after `p`. -/
theorem leaves_eq : {t : SPTerm ι} → t.ParFree → ∀ p : t.Leaf,
    ∃ R, t.leaves = p.ctxList ++ p :: R
  | _, _, .here j => ⟨[], by simp [leaves, Leaf.ctxList, Leaf.Before]⟩
  | node k a b, h, .left p => by
    obtain ⟨R, hR⟩ := leaves_eq h.2.1 p
    refine ⟨R.map .left ++ b.leaves.map .right, ?_⟩
    rw [Leaf.ctxList_left, leaves_node, hR]
    simp
  | node k a b, h, .right p => by
    obtain ⟨R, hR⟩ := leaves_eq h.2.2 p
    refine ⟨R.map .right, ?_⟩
    rw [Leaf.ctxList_right, leaves_node, hR]
    simp [h.1]

/-- **In a par-free term, the leaves before a later leaf extend those before an earlier one**:
for `q` before `p`, the leaves before `p` are those before `q`, then `q`, then the leaves
between. -/
theorem ctxList_of_before {t : SPTerm ι} (ht : t.ParFree) {q p : t.Leaf} (hqp : q.Before p) :
    ∃ M, p.ctxList = q.ctxList ++ q :: M := by
  obtain ⟨R, hR⟩ := leaves_eq ht q
  refine ⟨R.filter fun r => r.Before p, ?_⟩
  have hctx : p.ctxList = (q.ctxList ++ q :: R).filter fun r => r.Before p := by
    rw [← hR]
    rfl
  rw [hctx, List.filter_append, List.filter_cons_of_pos (by simpa using hqp)]
  congr 1
  refine List.filter_eq_self.2 fun r hr => ?_
  simpa using (Leaf.mem_ctxList.1 hr).trans hqp

end ParFree

/-! ### Round offsets in term order -/

section Offsets

variable (n : ι → ℕ)

/-- **The number of rounds of a term**: the rounds of its leaves, `n` of each component. -/
def size (t : SPTerm ι) : ℕ := (t.leaves.map fun q => n q.label).sum

@[simp] theorem size_node (k : Comp) (a b : SPTerm ι) :
    (node k a b).size n = a.size n + b.size n := by
  simp [size, List.map_append, Function.comp_def]

@[simp] theorem size_nil : (nil : SPTerm ι).size n = 0 := rfl

@[simp] theorem size_leaf (j : ι) : (leaf j).size n = n j := by
  simp [size, leaves]

/-- **The rounds of `m` subterms** are the sum of their rounds. -/
theorem size_nodeN (k : Comp) : (m : ℕ) → (c : Fin m → SPTerm ι) →
    (SPTerm.nodeN k m c).size n = ∑ i, (c i).size n
  | 0, _ => rfl
  | m + 1, c => by
    rw [SPTerm.nodeN, size_node, size_nodeN k m, Fin.sum_univ_succ]

/-- The number of rounds is the sum over the leaves. -/
theorem size_eq_sum (t : SPTerm ι) : t.size n = ∑ q : t.Leaf, n q.label := by
  classical
  rw [size, ← List.sum_toFinset _ (nodup_leaves t)]
  congr 1
  ext q
  simp [mem_leaves]

namespace Leaf

/-- **The offset of a leaf**: the rounds of the leaves before it in term order. -/
def off : {t : SPTerm ι} → t.Leaf → ℕ
  | _, here _ => 0
  | _, left p => off p
  | node _ a _, right p => a.size n + off p

/-- A leaf's rounds end within the term's. -/
theorem off_add_le : {t : SPTerm ι} → (p : t.Leaf) → p.off n + n p.label ≤ t.size n
  | _, here _ => by simp [off, size, leaves]
  | node _ _ _, left p => by
    have := off_add_le p
    simp only [off, label_left, size_node]
    omega
  | node _ _ _, right p => by
    have := off_add_le p
    simp only [off, label_right, size_node]
    omega

/-- **A leaf before another ends before the other's offset.** -/
theorem Before.off_add_le {t : SPTerm ι} : ∀ {q p : t.Leaf}, q.Before p →
    q.off n + n q.label ≤ p.off n := by
  induction t with
  | nil => intro q; cases q
  | leaf j => intro q p h; cases q; cases p; exact False.elim h
  | node k a b iha ihb =>
    intro q p h
    cases q with
    | left q =>
      cases p with
      | left p => exact iha h
      | right p =>
        have := Leaf.off_add_le n q
        show q.off n + n q.label ≤ a.size n + p.off n
        omega
    | right q =>
      cases p with
      | left p => exact False.elim h
      | right p =>
        have := ihb h
        show a.size n + q.off n + n q.label ≤ a.size n + p.off n
        omega

end Leaf

/-- **A round of a term**: a leaf and a round of its component. -/
structure Slot (t : SPTerm ι) where
  /-- The leaf. -/
  leaf : t.Leaf
  /-- The round of the leaf's component. -/
  round : Fin (n leaf.label)

/-- **The rounds of a term in term order**: each leaf's rounds in order, leaves in term order. -/
def slots (t : SPTerm ι) : List (Slot n t) :=
  t.leaves.flatMap fun p => (List.finRange (n p.label)).map fun r => ⟨p, r⟩

theorem slots_node (k : Comp) (a b : SPTerm ι) :
    (node k a b).slots n = (a.slots n).map (fun s => ⟨.left s.leaf, s.round⟩) ++
      (b.slots n).map (fun s => ⟨.right s.leaf, s.round⟩) := by
  simp [slots, List.flatMap_append, List.flatMap_map, List.map_flatMap, Function.comp_def]

theorem length_slots : (t : SPTerm ι) → (t.slots n).length = t.size n
  | nil => rfl
  | leaf j => by simp [slots, size, leaves]
  | node k a b => by
    rw [slots_node, List.length_append, List.length_map, List.length_map, length_slots a,
      length_slots b, size_node]

/-- **Round `r` of leaf `p` is slot `p.off + r`.** -/
theorem slots_getElem : {t : SPTerm ι} → (p : t.Leaf) → (r : Fin (n p.label)) →
    (t.slots n)[p.off n + r]? = some ⟨p, r⟩
  | _, .here j, r => by
    simp only [slots, leaves, List.flatMap_singleton, Leaf.off, Nat.zero_add, List.getElem?_map]
    have hr : (r : ℕ) < n j := r.2
    rw [List.getElem?_eq_getElem (by simpa using hr)]
    simp only [List.getElem_finRange]
    rfl
  | node k a b, .left p, r => by
    show ((node k a b).slots n)[p.off n + r]? = _
    have hr : (r : ℕ) < n p.label := r.2
    rw [slots_node, List.getElem?_append_left (by
      rw [List.length_map, length_slots]; have := Leaf.off_add_le n p; omega)]
    simp only [List.getElem?_map]
    rw [slots_getElem p r]
    rfl
  | node k a b, .right p, r => by
    show ((node k a b).slots n)[a.size n + p.off n + r]? = _
    rw [slots_node, List.getElem?_append_right (by rw [List.length_map, length_slots]; omega)]
    simp only [List.length_map, length_slots, List.getElem?_map]
    rw [show a.size n + p.off n + r - a.size n = p.off n + r by omega, slots_getElem p r]
    rfl

/-- Every round of a term occurs once in the term order. -/
theorem nodup_slots (t : SPTerm ι) : (t.slots n).Nodup := by
  unfold slots
  refine List.nodup_flatMap.2 ⟨fun p _ => (List.nodup_finRange _).map fun r r' h =>
    eq_of_heq (Slot.mk.inj h).2, ?_⟩
  refine (nodup_leaves t).pairwise_of_forall_ne fun p _ q _ hpq => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
  rintro _ ⟨r, rfl⟩ ⟨r', h⟩
  exact hpq (congrArg Slot.leaf h).symm

/-- **Slot `g` is round `g - p.off` of its leaf `p`.** -/
theorem eq_off_of_slots_getElem {t : SPTerm ι} {g : ℕ} {s : Slot n t}
    (h : (t.slots n)[g]? = some s) : g = s.leaf.off n + s.round :=
  ((nodup_slots n t).getElem?_inj (List.getElem?_eq_some_iff.1 h).1).1
    (h.trans (slots_getElem n s.leaf s.round).symm)

/-- Every index below the number of rounds is a slot. -/
theorem exists_slots_getElem {t : SPTerm ι} {g : ℕ} (hg : g < t.size n) :
    ∃ s, (t.slots n)[g]? = some s :=
  ⟨_, List.getElem?_eq_getElem (by rw [length_slots]; exact hg)⟩

end Offsets

/-! ### Causal fixpoints -/

namespace Leaf

/-- A function on the leaves of a node from its values on the two subterms' leaves. -/
def nodeRec {k : Comp} {a b : SPTerm ι} {V : (node k a b).Leaf → Sort*}
    (fa : ∀ q, V (.left q)) (fb : ∀ q, V (.right q)) : ∀ p, V p
  | .left q => fa q
  | .right q => fb q

/-- The (empty) context of the leaf of a one-component term. -/
def ctxHere {j : ι} {V : (leaf j).Leaf → Type} : (r : {r : (leaf j).Leaf // r.Before (.here j)}) → V r.1
  | ⟨.here _, h⟩ => False.elim h

/-- The context of a first-subterm leaf of a node from its context in the subterm. -/
def ctxLeft {k : Comp} {a b : SPTerm ι} {V : (node k a b).Leaf → Type} {q : a.Leaf}
    (ctx : (r : {r : a.Leaf // r.Before q}) → V (.left r.1)) :
    (r : {r : (node k a b).Leaf // r.Before (.left q)}) → V r.1
  | ⟨.left r, h⟩ => ctx ⟨r, h⟩
  | ⟨.right _, h⟩ => False.elim h

/-- The context of a second-subterm leaf of a node from the values `sa` at the first subterm's
leaves and its context in the second subterm. -/
def ctxRight {k : Comp} {a b : SPTerm ι} {V : (node k a b).Leaf → Type}
    (sa : ∀ r : a.Leaf, V (.left r)) {q : b.Leaf}
    (ctx : (r : {r : b.Leaf // r.Before q}) → V (.right r.1)) :
    (r : {r : (node k a b).Leaf // r.Before (.right q)}) → V r.1
  | ⟨.left r, _⟩ => sa r
  | ⟨.right r, h⟩ => ctx ⟨r, h⟩

end Leaf

/-- **The causal fixpoint**: from a rule `F p ctx` computing the value at the leaf `p` from the
values `ctx` at the leaves sequenced before it, the values at all leaves (`solve_eq`). Defined by
recursion on the term: under `node k a b`, the first subterm's values, then the second subterm's,
each first-subterm value available to a second-subterm leaf when `k = .seq`.

Running time: evaluated with memoization (each leaf's value stored once computed, leaves in term
order), one evaluation of `F` per leaf. The definition itself is the specification. This running
time is argued here, not proved in Lean. -/
def solve : {t : SPTerm ι} → {V : t.Leaf → Type} →
    ((p : t.Leaf) → ((q : {q : t.Leaf // q.Before p}) → V q.1) → V p) → (p : t.Leaf) → V p
  | leaf j, _, F, .here _ => F (.here j) Leaf.ctxHere
  | node _ _ _, _, F, p =>
    Leaf.nodeRec (solve fun q ctx => F (.left q) (Leaf.ctxLeft ctx))
      (solve fun q ctx => F (.right q)
        (Leaf.ctxRight (solve fun q ctx => F (.left q) (Leaf.ctxLeft ctx)) ctx)) p

/-- **The defining equation of the causal fixpoint**: the value at `p` is the rule at `p` applied
to the values at the leaves before `p`. -/
theorem solve_eq : {t : SPTerm ι} → {V : t.Leaf → Type} →
    (F : (p : t.Leaf) → ((q : {q : t.Leaf // q.Before p}) → V q.1) → V p) → (p : t.Leaf) →
    solve F p = F p fun q => solve F q.1
  | leaf j, _, F, .here _ => by
    show F _ Leaf.ctxHere = _
    congr 1
    funext q
    obtain ⟨⟨⟩, h⟩ := q
    exact False.elim h
  | node _ a b, V, F, .left p => by
    show solve _ p = _
    rw [solve_eq]
    congr 1
    funext r
    obtain ⟨r, h⟩ := r
    cases r with
    | left r => rfl
    | right r => exact False.elim h
  | node _ a b, V, F, .right p => by
    show solve _ p = _
    rw [solve_eq]
    congr 1
    funext r
    obtain ⟨r, h⟩ := r
    cases r with
    | left r => rfl
    | right r => rfl

/-- **`Before` is well founded**: a finite strict order. -/
theorem wellFounded_before (t : SPTerm ι) : WellFounded fun q p : t.Leaf => q.Before p := by
  have : IsTrans t.Leaf fun q p => q.Before p := ⟨fun _ _ _ => Leaf.Before.trans⟩
  have : Std.Irrefl fun q p : t.Leaf => q.Before p := ⟨Leaf.not_before_self⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- **The causal fixpoint is the only solution of its defining equation.** -/
theorem solve_unique {t : SPTerm ι} {V : t.Leaf → Type}
    (F : (p : t.Leaf) → ((q : {q : t.Leaf // q.Before p}) → V q.1) → V p) (f : (p : t.Leaf) → V p)
    (hf : ∀ p, f p = F p fun q => f q.1) : f = solve F := by
  funext p
  induction p using (wellFounded_before t).induction with
  | _ p ih =>
    rw [hf p, solve_eq F p]
    congr 1
    funext q
    exact ih q.1 q.2

/-! ### Leaves of many subterms -/

namespace Leaf

/-- **A leaf of subterm `i` as a leaf of `nodeN k m c`.** -/
def inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) → (c i).Leaf →
    (SPTerm.nodeN k m c).Leaf
  | 0, _, i, _ => i.elim0
  | m + 1, c, i, p =>
    Fin.cases (motive := fun i => (c i).Leaf → (SPTerm.nodeN k (m + 1) c).Leaf)
      (fun p => .left p) (fun i p => .right (inN k m (c := fun i => c i.succ) i p)) i p

theorem inN_zero (k : Comp) (m : ℕ) {c : Fin (m + 1) → SPTerm ι} (p : (c 0).Leaf) :
    inN k (m + 1) 0 p = .left p := rfl

theorem inN_succ (k : Comp) (m : ℕ) {c : Fin (m + 1) → SPTerm ι} (i : Fin m)
    (p : (c i.succ).Leaf) : inN k (m + 1) i.succ p = .right (inN k m (c := fun i => c i.succ) i p) :=
  rfl

@[simp] theorem label_inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) →
    (p : (c i).Leaf) → (inN k m i p).label = p.label
  | 0, _, i, _ => i.elim0
  | m + 1, c, i, p => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact label_inN k m (c := fun i => c i.succ) i p

/-- **Every leaf of `nodeN k m c` is a leaf of one subterm.** -/
theorem exists_inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (p : (SPTerm.nodeN k m c).Leaf) → ∃ i q, p = inN k m i q
  | 0, _, p => nomatch p
  | m + 1, c, .left q => ⟨0, q, rfl⟩
  | m + 1, c, .right q => by
    obtain ⟨i, q', rfl⟩ := exists_inN k m (c := fun i => c i.succ) q
    exact ⟨i.succ, q', rfl⟩

/-- Leaves of one subterm side by side are before each other as in the subterm. -/
@[simp] theorem inN_before_inN_iff (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) →
    (q p : (c i).Leaf) → (inN k m i q).Before (inN k m i p) ↔ q.Before p
  | 0, _, i, _, _ => i.elim0
  | m + 1, c, i, q, p => by
    induction i using Fin.cases with
    | zero => exact Iff.rfl
    | succ i => exact inN_before_inN_iff k m (c := fun i => c i.succ) i q p

/-- **Leaves of distinct subterms side by side are not before each other.** -/
theorem not_inN_before_inN_par : (m : ℕ) → {c : Fin m → SPTerm ι} → {i i' : Fin m} → i ≠ i' →
    (q : (c i).Leaf) → (p : (c i').Leaf) → ¬ (inN .par m i q).Before (inN .par m i' p)
  | 0, _, i, _, _, _, _ => i.elim0
  | m + 1, c, i, i', hne, q, p => by
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => exact absurd rfl hne
      | succ i' => exact fun h => Comp.noConfusion h
    | succ i =>
      induction i' using Fin.cases with
      | zero => exact id
      | succ i' =>
        exact not_inN_before_inN_par m (c := fun i => c i.succ)
          (fun h => hne (congrArg Fin.succ h)) q p

/-- `inN` is injective on each subterm. -/
theorem inN_injective (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) →
    Function.Injective (inN k m (c := c) i)
  | 0, _, i => i.elim0
  | m + 1, c, i => by
    induction i using Fin.cases with
    | zero => exact left_injective
    | succ i => exact right_injective.comp (inN_injective k m (c := fun i => c i.succ) i)

/-- Leaves of distinct subterms are distinct. -/
theorem inN_ne_inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → {i i' : Fin m} → i ≠ i' →
    (q : (c i).Leaf) → (p : (c i').Leaf) → inN k m i q ≠ inN k m i' p
  | 0, _, i, _, _, _, _ => i.elim0
  | m + 1, c, i, i', hne, q, p => by
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => exact absurd rfl hne
      | succ i' => exact fun h => by cases h
    | succ i =>
      induction i' using Fin.cases with
      | zero => exact fun h => by cases h
      | succ i' =>
        exact fun h => inN_ne_inN k m (c := fun i => c i.succ)
          (fun h' => hne (congrArg Fin.succ h')) q p (right_injective h)

end Leaf

end SPTerm

end GordieHowe.IOP
