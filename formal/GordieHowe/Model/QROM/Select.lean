-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Database
public import GordieHowe.Foundations.ToMathlib.MultisetSingle

@[expose] public section

/-!
# Reading a database by a property of its entries

Computable reads of a database `D : X ⇀ Y` (`GordieHowe/Model/QROM/Database.lean`) that look for the entry with
a property rather than at a key:

* `DB.select f D`: the value `f q y` at the one entry `(q, y)` of `D` where `f` is defined, or
  `none` when there is none or more than one (`select_eq_some_iff`, when at most one entry
  qualifies).
* `DB.pullback g D q'`: the answer recorded at the one key `q` with `g q = some q'`.
* `DB.image g D`: the database of the answers of `D` at the keys `g q` (`lookup_image`): when `g`
  is injective on the keys of `D` where it is defined, `(D.image g).lookup (g q) = D.lookup q`
  (`lookup_image_eq_some_iff`).

Running time: one pass over the entries of `D` for `select` and `pullback`; for `image`, one pass to
collect the keys and one `pullback` per key, `|D|²` evaluations of `g` in all. This running time is
argued here, not proved in Lean. -/

namespace GordieHowe.QROM

namespace DB

variable {X X' Y α : Type*}

/-- **The value of `f` at the one entry of `D` where it is defined**, or `none` when no entry or
more than one qualifies. -/
def select (f : X → Y → Option α) (D : DB X Y) : Option α :=
  (D.entries.filterMap fun s => f s.1 s.2).single?

variable [DecidableEq X]

/-- At most one entry of `D` qualifies for `f`. -/
def SelectUnique (f : X → Y → Option α) (D : DB X Y) : Prop :=
  ∀ ⦃q₁ q₂ : X⦄ ⦃y₁ y₂ : Y⦄ ⦃a₁ a₂ : α⦄, D.lookup q₁ = some y₁ → D.lookup q₂ = some y₂ →
    f q₁ y₁ = some a₁ → f q₂ y₂ = some a₂ → q₁ = q₂

variable {f : X → Y → Option α} {D : DB X Y}

theorem exists_of_select_eq_some {a : α} (h : D.select f = some a) :
    ∃ q y, D.lookup q = some y ∧ f q y = some a := by
  rw [select, Multiset.single?_eq_some_iff] at h
  have ha : a ∈ D.entries.filterMap fun s => f s.1 s.2 := by rw [h]; exact Multiset.mem_singleton_self a
  obtain ⟨s, hs, hfs⟩ := (Multiset.mem_filterMap _ _).1 ha
  exact ⟨s.1, s.2, Finmap.lookup_eq_some_iff.2 hs, hfs⟩

theorem select_eq_some_of_mem (hu : SelectUnique f D) {q : X} {y : Y} {a : α}
    (hq : D.lookup q = some y) (hf : f q y = some a) : D.select f = some a := by
  rw [select, Multiset.single?_eq_some_iff]
  have hmem : (⟨q, y⟩ : Σ _ : X, Y) ∈ D.entries := Finmap.lookup_eq_some_iff.1 hq
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hmem
  have hnd := D.nodup_entries
  rw [hrest, Multiset.nodup_cons] at hnd
  have hnone : ∀ s ∈ rest, f s.1 s.2 = none := by
    intro s hs
    rcases hfs : f s.1 s.2 with _ | b
    · rfl
    · exfalso
      have hs' : s ∈ D.entries := by rw [hrest]; exact Multiset.mem_cons_of_mem hs
      have hsq : s.1 = q := hu (Finmap.lookup_eq_some_iff.2 hs') hq hfs hf
      have hsy : s.2 = y := by
        have := Finmap.lookup_eq_some_iff.2 hs'
        rw [hsq, hq] at this
        exact (Option.some_inj.1 this).symm
      obtain ⟨s1, s2⟩ := s
      dsimp only at hsq hsy
      subst hsq hsy
      exact hnd.1 hs
  have hzero : rest.filterMap (fun s : Σ _ : X, Y => f s.1 s.2) = 0 :=
    Multiset.eq_zero_of_forall_notMem fun b hb => by
      obtain ⟨s, hs, hfs⟩ := (Multiset.mem_filterMap _ _).1 hb
      rw [hnone s hs] at hfs
      cases hfs
  rw [hrest, Multiset.filterMap_cons_some (fun s : Σ _ : X, Y => f s.1 s.2) ⟨q, y⟩ rest hf, hzero]
  rfl

/-- **Reading the one qualifying entry.** -/
theorem select_eq_some_iff (hu : SelectUnique f D) {a : α} :
    D.select f = some a ↔ ∃ q y, D.lookup q = some y ∧ f q y = some a :=
  ⟨exists_of_select_eq_some, fun ⟨_, _, hq, hf⟩ => select_eq_some_of_mem hu hq hf⟩

/-- `select` is `none` when no entry qualifies. -/
theorem select_eq_none_of_forall (h : ∀ q y, D.lookup q = some y → f q y = none) :
    D.select f = none := by
  rcases hs : D.select f with _ | a
  · rfl
  · obtain ⟨q, y, hq, hf⟩ := exists_of_select_eq_some hs
    rw [h q y hq] at hf
    cases hf

/-! ### Pullbacks and images -/

variable [DecidableEq X'] (g : X → Option X')

/-- **The answer at the one key `q` of `D` with `g q = some q'`.** -/
def pullback (D : DB X Y) (q' : X') : Option Y :=
  D.select (fun q y => if g q = some q' then some y else none)

/-- `g` is injective on the keys of `D` where it is defined. -/
def InjOnKeys (D : DB X Y) : Prop :=
  ∀ ⦃q₁ q₂ : X⦄ ⦃q' : X'⦄, q₁ ∈ D → q₂ ∈ D → g q₁ = some q' → g q₂ = some q' → q₁ = q₂

variable {g}

theorem pullback_eq_some_iff (hg : InjOnKeys g D) {q' : X'} {y : Y} :
    D.pullback g q' = some y ↔ ∃ q, D.lookup q = some y ∧ g q = some q' := by
  rw [pullback, select_eq_some_iff]
  · constructor
    · rintro ⟨q, y', hq, hf⟩
      split_ifs at hf with hgq
      exact ⟨q, (Option.some_inj.1 hf) ▸ hq, hgq⟩
    · rintro ⟨q, hq, hgq⟩
      exact ⟨q, y, hq, by simp [hgq]⟩
  · intro q₁ q₂ y₁ y₂ a₁ a₂ h₁ h₂ hf₁ hf₂
    dsimp only at hf₁ hf₂
    split_ifs at hf₁ hf₂ with hg₁ hg₂
    exact hg (Finmap.mem_of_lookup_eq_some h₁) (Finmap.mem_of_lookup_eq_some h₂) hg₁ hg₂

variable (g) in
/-- **The image database**: the answers of `D` at the keys `g q`, at the keys where exactly one key
of `D` maps. -/
def image (D : DB X Y) : DB X' Y :=
  Finmap.keysLookupEquiv.symm ⟨(((D.keys.val.filterMap g).toFinset.filter
      fun q' => (D.pullback g q').isSome), D.pullback g), fun q' => by
    simp only [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_filterMap, Finset.mem_val,
      Finmap.mem_keys]
    constructor
    · intro hs
      refine ⟨?_, hs⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨q, y', hq, hf⟩ := exists_of_select_eq_some hy
      split_ifs at hf with hgq
      exact ⟨q, Finmap.mem_of_lookup_eq_some hq, hgq⟩
    · exact fun h => h.2⟩

@[simp] theorem lookup_image (q' : X') : (D.image g).lookup q' = D.pullback g q' := by
  rw [image, Finmap.keysLookupEquiv_symm_apply_lookup]

/-- **The image database at an image key** is the answer at its one preimage. -/
theorem lookup_image_eq_some_iff (hg : InjOnKeys g D) {q' : X'} {y : Y} :
    (D.image g).lookup q' = some y ↔ ∃ q, D.lookup q = some y ∧ g q = some q' := by
  rw [lookup_image, pullback_eq_some_iff hg]

theorem lookup_image_of_lookup (hg : InjOnKeys g D) {q : X} {q' : X'} {y : Y}
    (hq : D.lookup q = some y) (hgq : g q = some q') : (D.image g).lookup q' = some y :=
  (lookup_image_eq_some_iff hg).2 ⟨q, hq, hgq⟩

theorem mem_image_iff (hg : InjOnKeys g D) {q' : X'} : q' ∈ D.image g ↔ ∃ q ∈ D, g q = some q' := by
  rw [Finmap.mem_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq, hgq⟩ := (lookup_image_eq_some_iff hg).1 hy
    exact ⟨q, Finmap.mem_of_lookup_eq_some hq, hgq⟩
  · rintro ⟨q, hq, hgq⟩
    obtain ⟨y, hy⟩ := Finmap.mem_iff.1 hq
    exact ⟨y, lookup_image_of_lookup hg hy hgq⟩

/-- The image has at most as many entries as `D`. -/
theorem size_image_le : (D.image g).size ≤ D.size := by
  unfold size
  rw [image, Finmap.keysLookupEquiv_symm_apply_keys]
  refine (Finset.card_filter_le _ _).trans ((Multiset.toFinset_card_le _).trans ?_)
  have key : ∀ m : Multiset X, Multiset.card (m.filterMap g) ≤ Multiset.card m := fun m =>
    Quot.inductionOn m fun l => by simpa using List.length_filterMap_le g l
  exact key D.keys.val

end DB

end GordieHowe.QROM
