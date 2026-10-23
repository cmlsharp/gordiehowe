-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalLeaves

@[expose] public section

/-!
# Merges on a series–parallel term

The merges of the spBCS compiler (paper `prot:generalized-bcs`) on a series–parallel term
`t` of components. A merge is a part `(A_0 ∥ … ∥ A_{r-1}) ; D` of the term; its *branches* `A_b`
are arbitrary subterms (they may be parallel compositions and contain merges themselves). Every
branch has a *site*: `mem s q` says that the leaf `q` lies in the branch of site `s`, and
`part s p` that `p` lies in the part `D` of the merge of `s`. A chain input of a leaf of `D` reads
each branch through one final digest.

* `Merges t`: the sites, their branches (`mem`) and parts (`part`), and the laws of the
  series–parallel structure: every branch has a leaf (`exists_mem`), a branch is a module of the
  causal order (`before_of_before_mem`), a branch is before its part
  (`before_of_part`), a leaf lies in the part of at most one branch containing a given leaf
  (`eq_of_part_of_mem`), and the merges nest (`part_iff_of_before`: for a branch `s` hidden from
  `p` and a branch `s'` whose leaf `r` is before `s`, the part of `s'` contains all of `s` exactly
  when it contains `p`). `GordieHowe/SPBCS/Term.lean` proves the laws for every term with merges.
* `Obs M`: the *observers* that have a chain input: a leaf (`leaf p`, one input per challenge
  round) and the *sink* of a site (`sink s`, the input of the branch's final digest). The sink of
  `s` is the leaf of a message composed in series after the branch of `s`: it sees the branch's
  leaves and the leaves before the branch (`Sees`), and is hidden from exactly the branches whose
  part contains the whole branch of `s` (`Hides`). For a branch that is a chain this is the input
  of the branch's last message with that message's item, as in the paper.
* `Hides s o`: the branch of `s` is read by `o` through its final digest; `Visible o r`: `o` reads
  the full chain of `r`.
* `nJ`: the largest number of branches hidden from one leaf, the paper's `n_J`
  (`def:bcs-quantities`): for a message `i`, the sum of the numbers of branches of the merges whose
  part contains `i`. A sink is hidden from at most that many branches (`card_hiders_le`).

The derived laws used by the compiler: a hidden branch is in the past of its observer
(`sees_of_hides_of_mem`), at most one hidden branch contains a leaf (`eq_of_hides`), a sink reads
its own branch in full (`visible_sink_of_mem`), and a sink reads the leaves before its branch as
every observer the branch is hidden from does (`hides_sink_iff`, `visible_sink_iff`). So the
final input of a hidden branch holds the observer's view of the branch's past, which is what lets
a database extractor recover the observer's causal past by following each final digest once.
-/

namespace GordieHowe.SPBCS

open GordieHowe.IOP IOP.SPTerm

variable {ι : Type}

/-- **The merges on a term** (module docstring): the sites of the branches, the leaves of each
branch (`mem`) and of its merge's part (`part`), and the laws of their nesting. -/
structure Merges (t : SPTerm ι) where
  /-- The sites, one per branch of a merge. -/
  Site : Type
  /-- Finitely many sites. -/
  [instFintype : Fintype Site]
  /-- Decidable equality of sites. -/
  [instDecEq : DecidableEq Site]
  /-- An encoding of the sites, which orders them (`Encodable.sortedUniv`). -/
  [instEncodable : Encodable Site]
  /-- The leaves of the branch of a site. -/
  mem : Site → t.Leaf → Prop
  /-- Membership is decidable. -/
  [instDecMem : ∀ s, DecidablePred (mem s)]
  /-- The leaves of the part of a site's merge. -/
  part : Site → t.Leaf → Prop
  /-- Membership in the part is decidable. -/
  [instDecPart : ∀ s, DecidablePred (part s)]
  /-- Every branch has a leaf. -/
  exists_mem : ∀ s, ∃ q, mem s q
  /-- A branch is a module: a leaf outside it that is before one of its leaves is before all of
  them. -/
  before_of_before_mem : ∀ {s q q' r}, mem s q → mem s q' → ¬ mem s r → r.Before q → r.Before q'
  /-- A branch is before its merge's part. -/
  before_of_part : ∀ {s q p}, mem s q → part s p → q.Before p
  /-- A leaf of a part lies in the part of at most one branch containing a given leaf. -/
  eq_of_part_of_mem : ∀ {s s' p r}, part s p → part s' p → mem s r → mem s' r → s = s'
  /-- The merges nest: if `p` is in the part of `s` and the leaf `r` of the branch `s'` is before
  the branch of `s`, the part of `s'` contains the branch of `s` exactly when it contains `p`. -/
  part_iff_of_before : ∀ {s s' p r}, part s p → mem s' r → (∀ q, mem s q → r.Before q) →
    ((∀ q, mem s q → part s' q) ↔ part s' p)

attribute [instance] Merges.instFintype Merges.instDecEq Merges.instEncodable Merges.instDecMem
  Merges.instDecPart

namespace Merges

variable {t : SPTerm ι}

/-- **No merges**: no sites. -/
def none (t : SPTerm ι) : Merges t where
  Site := Empty
  mem s _ := s.elim
  instDecMem s := s.elim
  part s _ := s.elim
  instDecPart s := s.elim
  exists_mem s := s.elim
  before_of_before_mem {s} := s.elim
  before_of_part {s} := s.elim
  eq_of_part_of_mem {s} := s.elim
  part_iff_of_before {s} := s.elim

variable (M : Merges t)

/-- **An observer**: a leaf, whose chain inputs are those of its challenge rounds, or the sink of
a site, whose chain input is the branch's final input. -/
inductive Obs where
  /-- A leaf. -/
  | leaf (p : t.Leaf)
  /-- The sink of a site. -/
  | sink (s : M.Site)

instance : DecidableEq M.Obs := fun o o' =>
  match o, o' with
  | .leaf p, .leaf p' => if h : p = p' then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .sink s, .sink s' => if h : s = s' then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .leaf _, .sink _ => isFalse fun e => by cases e
  | .sink _, .leaf _ => isFalse fun e => by cases e

variable {M}

/-- **The leaves an observer stands for**: a leaf itself; the leaves of a site's branch. -/
def Obs.Covers : M.Obs → t.Leaf → Prop
  | .leaf p, q => q = p
  | .sink s, q => M.mem s q

/-- **The past of an observer**: the leaves before a leaf; the leaves of a site's branch and those
before it. -/
def Obs.Sees : M.Obs → t.Leaf → Prop
  | .leaf p, r => r.Before p
  | .sink s, r => M.mem s r ∨ ∀ q, M.mem s q → r.Before q

variable (M) in
/-- **The branch of `s` is read by `o` through its final digest**: every leaf `o` stands for is in
the part of the merge of `s`. -/
def Hides (s : M.Site) : M.Obs → Prop
  | .leaf p => M.part s p
  | .sink s' => ∀ q, M.mem s' q → M.part s q

/-- **`o` reads the full chain of `r`**: `r` is in the past of `o` and in no branch hidden from
`o`. -/
def Obs.Visible (o : M.Obs) (r : t.Leaf) : Prop := o.Sees r ∧ ∀ s, M.Hides s o → ¬ M.mem s r

instance (o : M.Obs) : DecidablePred o.Sees := fun r => by
  cases o <;> unfold Obs.Sees <;> infer_instance

instance (s : M.Site) : DecidablePred (M.Hides s) := fun o => by
  cases o <;> unfold Hides <;> infer_instance

instance (o : M.Obs) : DecidablePred o.Visible := fun _ => inferInstanceAs (Decidable (_ ∧ _))

variable (M) in
/-- **The largest number of branches hidden from one leaf** (the paper's `n_J`), `0` without a
leaf. -/
def nJ : ℕ := Finset.univ.sup fun p : t.Leaf => (Finset.univ.filter fun s => M.part s p).card

/-! ### Derived laws -/

@[simp] theorem hides_leaf {s : M.Site} {p : t.Leaf} : M.Hides s (.leaf p) ↔ M.part s p := Iff.rfl

@[simp] theorem hides_sink {s s' : M.Site} :
    M.Hides s (.sink s') ↔ ∀ q, M.mem s' q → M.part s q := Iff.rfl

@[simp] theorem sees_leaf {p r : t.Leaf} : (Obs.leaf (M := M) p).Sees r ↔ r.Before p := Iff.rfl

@[simp] theorem sees_sink {s : M.Site} {r : t.Leaf} :
    (Obs.sink s).Sees r ↔ M.mem s r ∨ ∀ q, M.mem s q → r.Before q := Iff.rfl

/-- **Every observer stands for a leaf.** -/
theorem Obs.exists_covers (o : M.Obs) : ∃ q, o.Covers q := by
  cases o with
  | leaf p => exact ⟨p, rfl⟩
  | sink s => exact M.exists_mem s

/-- `Hides` through the leaves an observer stands for. -/
theorem hides_iff_forall_covers {s : M.Site} {o : M.Obs} :
    M.Hides s o ↔ ∀ q, o.Covers q → M.part s q := by
  cases o with
  | leaf p => exact ⟨fun h q hq => hq ▸ h, fun h => h p rfl⟩
  | sink s' => exact Iff.rfl

/-- **The leaves a hidden branch is before**: every leaf its observer stands for. -/
theorem before_of_hides {s : M.Site} {o : M.Obs} (hs : M.Hides s o) {r q : t.Leaf}
    (hr : M.mem s r) (hq : o.Covers q) : r.Before q :=
  M.before_of_part hr (hides_iff_forall_covers.1 hs q hq)

/-- **A hidden branch is in the past of its observer.** -/
theorem sees_of_hides_of_mem {s : M.Site} {o : M.Obs} (hs : M.Hides s o) {r : t.Leaf}
    (hr : M.mem s r) : o.Sees r := by
  cases o with
  | leaf p => exact before_of_hides hs hr rfl
  | sink s' => exact Or.inr fun q hq => before_of_hides hs hr hq

/-- **At most one branch hidden from an observer contains a leaf.** -/
theorem eq_of_hides {s s' : M.Site} {o : M.Obs} (hs : M.Hides s o) (hs' : M.Hides s' o)
    {r : t.Leaf} (hr : M.mem s r) (hr' : M.mem s' r) : s = s' := by
  obtain ⟨q, hq⟩ := o.exists_covers
  exact M.eq_of_part_of_mem (hides_iff_forall_covers.1 hs q hq) (hides_iff_forall_covers.1 hs' q hq)
    hr hr'

/-- **A branch is not hidden from its own sink.** -/
theorem not_hides_sink_self (s : M.Site) : ¬ M.Hides s (.sink s) := fun h => by
  obtain ⟨q, hq⟩ := M.exists_mem s
  exact Leaf.not_before_self q (before_of_hides h hq hq)

/-- **The branches hidden from a sink are outside its branch.** -/
theorem not_mem_of_hides_sink {s s' : M.Site} (hs' : M.Hides s' (.sink s)) {r : t.Leaf}
    (hr : M.mem s' r) : ¬ M.mem s r := fun hrs =>
  Leaf.not_before_self r (before_of_hides hs' hr hrs)

/-- **A sink reads its own branch in full.** -/
theorem visible_sink_of_mem {s : M.Site} {r : t.Leaf} (hr : M.mem s r) : (Obs.sink s).Visible r :=
  ⟨Or.inl hr, fun _ hs' hr' => not_mem_of_hides_sink hs' hr' hr⟩

/-- **A sink is hidden from a branch whose leaves are before its branch exactly when an observer
hidden from its branch is.** -/
theorem hides_sink_iff {s s' : M.Site} {o : M.Obs} (hs : M.Hides s o) {r : t.Leaf}
    (hr : M.mem s' r) (hbef : ∀ q, M.mem s q → r.Before q) :
    M.Hides s' (.sink s) ↔ M.Hides s' o := by
  obtain ⟨q₀, hq₀⟩ := o.exists_covers
  rw [hides_sink, hides_iff_forall_covers]
  constructor
  · intro h q hq
    exact (M.part_iff_of_before (hides_iff_forall_covers.1 hs q hq) hr hbef).1 h
  · intro h
    exact (M.part_iff_of_before (hides_iff_forall_covers.1 hs q₀ hq₀) hr hbef).2 (h q₀ hq₀)

/-- **The branches hidden from the sink of a hidden branch are hidden from the observer.** -/
theorem hides_of_hides_sink {s s' : M.Site} {o : M.Obs} (hs : M.Hides s o)
    (hs' : M.Hides s' (.sink s)) : M.Hides s' o := by
  obtain ⟨r, hr⟩ := M.exists_mem s'
  exact (hides_sink_iff hs hr fun q hq => before_of_hides hs' hr hq).1 hs'

/-- **The past of the sink of a hidden branch is in the past of the observer.** -/
theorem sees_of_sees_sink {s : M.Site} {o : M.Obs} (hs : M.Hides s o) {r : t.Leaf}
    (hr : (Obs.sink s).Sees r) : o.Sees r := by
  rcases hr with hr | hr
  · exact sees_of_hides_of_mem hs hr
  · obtain ⟨q, hq⟩ := M.exists_mem s
    have hrq := hr q hq
    cases o with
    | leaf p => exact hrq.trans (before_of_hides hs hq rfl)
    | sink _ => exact Or.inr fun q' hq' => hrq.trans (before_of_hides hs hq hq')

/-- **The sink of a hidden branch reads a leaf before the branch in full exactly when the observer
does.** -/
theorem visible_sink_iff {s : M.Site} {o : M.Obs} (hs : M.Hides s o) {r : t.Leaf}
    (hbef : ∀ q, M.mem s q → r.Before q) : (Obs.sink s).Visible r ↔ o.Visible r := by
  have hsees : (Obs.sink s).Sees r := Or.inr hbef
  refine ⟨fun h => ⟨sees_of_sees_sink hs hsees, fun s' hs' hr => ?_⟩,
    fun h => ⟨hsees, fun s' hs' hr => h.2 s' ((hides_sink_iff hs hr hbef).1 hs') hr⟩⟩
  exact h.2 s' ((hides_sink_iff hs hr hbef).2 hs') hr

/-- **The past of a sink is closed under `Before`.** -/
theorem sees_sink_of_before {s : M.Site} {q r : t.Leaf} (hq : (Obs.sink s).Sees q)
    (hr : r.Before q) : (Obs.sink s).Sees r := by
  by_cases hrs : M.mem s r
  · exact Or.inl hrs
  · rcases hq with hq | hq
    · exact Or.inr fun q' hq' => M.before_of_before_mem hq hq' hrs hr
    · exact Or.inr fun q' hq' => hr.trans (hq q' hq')

/-! ### Counting the hidden branches -/

/-- The branches hidden from an observer. -/
def hiders (o : M.Obs) : Finset M.Site := Finset.univ.filter fun s => M.Hides s o

@[simp] theorem mem_hiders {o : M.Obs} {s : M.Site} : s ∈ hiders o ↔ M.Hides s o := by
  simp [hiders]

/-- **An observer is hidden from at most `nJ` branches.** -/
theorem card_hiders_le (o : M.Obs) : (hiders o).card ≤ M.nJ := by
  obtain ⟨q, hq⟩ := o.exists_covers
  calc (hiders o).card ≤ (Finset.univ.filter fun s => M.part s q).card :=
        Finset.card_le_card fun s hs => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hides_iff_forall_covers.1 (mem_hiders.1 hs) q hq
    _ ≤ M.nJ := Finset.le_sup (f := fun p : t.Leaf => (Finset.univ.filter fun s => M.part s p).card)
        (Finset.mem_univ q)

/-- **The branches hidden from the sink of a hidden branch are fewer**: they are hidden from the
observer, and the branch itself is not hidden from its sink. -/
theorem hiders_sink_ssubset {s : M.Site} {o : M.Obs} (hs : M.Hides s o) :
    hiders (.sink s) ⊂ hiders o :=
  Finset.ssubset_iff_of_subset (fun _ h => mem_hiders.2 (hides_of_hides_sink hs (mem_hiders.1 h)))
    |>.2 ⟨s, mem_hiders.2 hs, fun h => not_hides_sink_self s (mem_hiders.1 h)⟩

/-- Without merges no branch is hidden. -/
theorem nJ_none : (Merges.none t).nJ = 0 :=
  Nat.eq_zero_of_le_zero <| Finset.sup_le fun _ _ =>
    (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun s => s.elim)).le

/-! ### The step order -/

/-- **The position of a leaf in term order** (`SPTerm.leaves`): the offset of the leaf when every
component has one round. -/
def leafPos (p : t.Leaf) : ℕ := p.off fun _ => 1

/-- **A leaf before another comes earlier in term order.** -/
theorem leafPos_lt_of_before {q p : t.Leaf} (h : q.Before p) : leafPos q < leafPos p :=
  Nat.lt_of_succ_le (Leaf.Before.off_add_le (fun _ => 1) h)

variable (M) in
/-- **The position of the last leaf of a branch** in term order. -/
def lastPos (s : M.Site) : ℕ := (Finset.univ.filter (M.mem s)).sup leafPos

theorem leafPos_le_lastPos {s : M.Site} {q : t.Leaf} (hq : M.mem s q) : leafPos q ≤ M.lastPos s :=
  Finset.le_sup (f := leafPos) (Finset.mem_filter.2 ⟨Finset.mem_univ q, hq⟩)

theorem lastPos_lt_of_forall {s : M.Site} {m : ℕ} (h : ∀ q, M.mem s q → leafPos q < m) :
    M.lastPos s < m := by
  obtain ⟨q, hq⟩ := M.exists_mem s
  exact (Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) (h q hq))).2 fun q' hq' =>
    h q' (Finset.mem_filter.1 hq').2

/-- **The step of an observer in the prover's order**: leaves in term order, the sink of each
branch right after the branch's last leaf (`2 · leafPos p` for a leaf, `2 · lastPos s + 1` for
a sink). -/
def Obs.rank : M.Obs → ℕ
  | .leaf p => 2 * leafPos p
  | .sink s => 2 * M.lastPos s + 1

/-- **What the step of an observer reads**: the chain of every leaf in its past, and the final
digest of every branch hidden from it. -/
def Obs.Reads : M.Obs → M.Obs → Prop
  | o, .leaf r => o.Sees r
  | o, .sink s' => M.Hides s' o

@[simp] theorem Obs.reads_leaf {o : M.Obs} {r : t.Leaf} : o.Reads (.leaf r) ↔ o.Sees r := Iff.rfl

@[simp] theorem Obs.reads_sink {o : M.Obs} {s' : M.Site} : o.Reads (.sink s') ↔ M.Hides s' o :=
  Iff.rfl

/-- **The prover's order is a topological order**: every step comes after the steps it reads. -/
theorem Obs.rank_lt_of_reads {o o' : M.Obs} (h : o.Reads o') : o'.rank < o.rank := by
  cases o' with
  | leaf r =>
    cases o with
    | leaf p =>
      have := leafPos_lt_of_before (Obs.reads_leaf.1 h)
      simp only [rank]
      omega
    | sink s =>
      rcases Obs.reads_leaf.1 h with hr | hr
      · have := leafPos_le_lastPos hr
        simp only [rank]
        omega
      · obtain ⟨q, hq⟩ := M.exists_mem s
        have := leafPos_lt_of_before (hr q hq)
        have := leafPos_le_lastPos hq
        simp only [rank]
        omega
  | sink s' =>
    cases o with
    | leaf p =>
      have := lastPos_lt_of_forall fun q hq => leafPos_lt_of_before (before_of_hides (Obs.reads_sink.1 h) hq rfl)
      simp only [rank]
      omega
    | sink s =>
      obtain ⟨q, hq⟩ := M.exists_mem s
      have := lastPos_lt_of_forall fun q' hq' => leafPos_lt_of_before (before_of_hides (Obs.reads_sink.1 h) hq' hq)
      have := leafPos_le_lastPos hq
      simp only [rank]
      omega

end Merges

end GordieHowe.SPBCS
