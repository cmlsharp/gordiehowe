-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Finmap
public import Mathlib.Data.Finset.Preimage

@[expose] public section

/-!
# Databases of oracle query-answer pairs

A database `D : X ⇀ Y` is a finite partial function recording the query-answer
pairs of a simulated random oracle (Chiesa–Manohar–Spooner, "Succinct Arguments in
the Quantum Random Oracle Model", ePrint 2019/834, section 3.5, and footnote 5 on
p. 18, where the classical simulator answers an unseen query `x` with a fresh
uniform `y` and updates `D := D + [x ↦ y]`). We use Mathlib's `Finmap`.

- `x ∈ D` is `x ∈ supp(D)`; `D.keys` is `supp(D)` as a `Finset`.
- `D.size` is `|D|`, the number of entries.
- `D.extend x y` is `D + [x ↦ y]`; the paper uses it only for `x ∉ supp(D)`,
  and every lemma below that needs this says so.
- `D.lookup x` is `D(x)`, with `none` for `⊥`.
- `D.restrict ι`, for an injection `ι : X ↪ X'` and `D : X' ⇀ Y`, is `x ↦ D(ι x)`. It carries
  a database property on `X` to one on `X'` (`restrict ι ⁻¹' R`); not in the paper.

A database property (Def 5.1, p. 21) is a `Set (DB X Y)`; its negation `P̄` is the
complement `Pᶜ`.

## Paper text

Section 3.5, p. 16:

    A database mapping X to Y is a partial function D : X ⇀ Y. The support of a
    database D is supp(D) := {x ∈ X : D(x) ≠ ⊥} and its image is
    im(D) := {D(x) : x ∈ supp(D)}. The size of a database is the size of its
    support: |D| := |supp(D)|. [...]
    Given a database D, input values x, x' ∈ X, and output value y ∈ Y, we define
    the two databases
      (D − x)(x') := ⊥ if x = x', D(x') if x ≠ x'
      (D + [x ↦ y])(x') := y if x = x', D(x') if x ≠ x'.

Definition 5.1, p. 21:

    A database property P is a set of databases D : X ⇀ Y. The negation of P,
    denoted P̄, is the set (X ⇀ Y) \ P.

Correspondence: `DB X Y` is `X ⇀ Y` restricted to finite support (the paper only
uses databases with `|D| ≤ t`); `Finmap.insert` agrees with `D + [x ↦ y]` for every
`x`, not only `x ∉ supp(D)`. `D − x` is not used.
-/

namespace GordieHowe.QROM

/-- A database `D : X ⇀ Y` (CMS19 section 3.5): a finite partial function. -/
abbrev DB (X Y : Type*) := Finmap (fun _ : X => Y)

namespace DB

variable {X Y : Type*}

/-- `|D|`, the number of entries of `D` (CMS19 section 3.5). -/
def size (D : DB X Y) : ℕ := D.keys.card

/-- `D + [x ↦ y]` (CMS19 footnote 5, p. 18), meant for `x ∉ supp(D)`. -/
def extend [DecidableEq X] (D : DB X Y) (x : X) (y : Y) : DB X Y := D.insert x y

@[simp] theorem size_empty : (∅ : DB X Y).size = 0 := rfl

variable [DecidableEq X] {D : DB X Y} {x x' : X} {y : Y}

@[simp] theorem mem_extend : x' ∈ D.extend x y ↔ x' = x ∨ x' ∈ D := Finmap.mem_insert

@[simp] theorem lookup_extend_self : (D.extend x y).lookup x = some y := Finmap.lookup_insert _

theorem lookup_extend_of_ne (h : x' ≠ x) : (D.extend x y).lookup x' = D.lookup x' :=
  Finmap.lookup_insert_of_ne _ h

theorem mem_iff_lookup : x ∈ D ↔ ∃ y, D.lookup x = some y := Finmap.mem_iff

theorem keys_extend : (D.extend x y).keys = insert x D.keys := by
  ext x'
  simp only [Finmap.mem_keys, mem_extend, Finset.mem_insert]

/-- Recording a new entry adds one to the size. -/
theorem size_extend_of_notMem (h : x ∉ D) : (D.extend x y).size = D.size + 1 := by
  rw [size, keys_extend, Finset.card_insert_of_notMem (by rwa [Finmap.mem_keys]), size]

/-- Recording an entry adds at most one to the size. -/
theorem size_extend_le : (D.extend x y).size ≤ D.size + 1 := by
  rw [size, keys_extend]
  exact Finset.card_insert_le _ _

/-- `D − x` for `x ∉ supp(D)` is `D`. -/
theorem erase_of_notMem (h : x ∉ D) : D.erase x = D :=
  Finmap.ext_lookup fun x' => by
    by_cases hx : x' = x
    · subst hx
      rw [Finmap.lookup_erase, Finmap.lookup_eq_none.2 h]
    · rw [Finmap.lookup_erase_ne hx]

/-- `(D + [x ↦ y]) − x = D` for `x ∉ supp(D)`. -/
theorem erase_extend_of_notMem (h : x ∉ D) : (D.extend x y).erase x = D :=
  Finmap.ext_lookup fun x' => by
    by_cases hx : x' = x
    · subst hx
      rw [Finmap.lookup_erase, Finmap.lookup_eq_none.2 h]
    · rw [Finmap.lookup_erase_ne hx, lookup_extend_of_ne hx]

/-- `(D − x) + [x ↦ D(x)] = D`. -/
theorem extend_erase_of_lookup (h : D.lookup x = some y) : extend (D.erase x) x y = D :=
  Finmap.ext_lookup fun x' => by
    by_cases hx : x' = x
    · subst hx
      rw [lookup_extend_self, h]
    · rw [lookup_extend_of_ne hx, Finmap.lookup_erase_ne hx]

/-- For `x ∉ supp(D₀)`: `D = D₀ + [x ↦ y]` exactly when `D(x) = y` and `D − x = D₀`. -/
theorem eq_extend_iff {D₀ : DB X Y} (h : x ∉ D₀) :
    D = D₀.extend x y ↔ D.lookup x = some y ∧ D.erase x = D₀ := by
  constructor
  · rintro rfl
    exact ⟨lookup_extend_self, erase_extend_of_notMem h⟩
  · rintro ⟨h1, rfl⟩
    exact (extend_erase_of_lookup h1).symm

/-- `D − x` for `x ∈ supp(D)` has one entry fewer. -/
theorem size_erase_of_mem (h : x ∈ D) : size (D.erase x) + 1 = D.size := by
  rw [size, Finmap.keys_erase, Finset.card_erase_add_one (Finmap.mem_keys.2 h), size]

end DB

namespace DB

/-! ### Restriction along an injection -/

variable {X X' Y : Type*} [DecidableEq X] [DecidableEq X'] (ι : X ↪ X')

/-- The restriction of a database `D : X' ⇀ Y` along an injection `ι : X ↪ X'`: the database
`x ↦ D(ι x)` on `X`, whose support is the preimage of `supp(D)`. A database property `R` on `X`
is a property on `X'` as `restrict ι ⁻¹' R`. -/
noncomputable def restrict (D : DB X' Y) : DB X Y :=
  Finmap.keysLookupEquiv.symm
    ⟨(D.keys.preimage ι ι.injective.injOn, fun x => D.lookup (ι x)), fun x => by
      rw [Finset.mem_preimage, Finmap.mem_keys, Finmap.lookup_isSome]⟩

variable {ι} {D : DB X' Y}

@[simp] theorem lookup_restrict (x : X) : (D.restrict ι).lookup x = D.lookup (ι x) :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ x

@[simp] theorem mem_restrict {x : X} : x ∈ D.restrict ι ↔ ι x ∈ D := by
  rw [← Finmap.lookup_isSome, lookup_restrict, Finmap.lookup_isSome]

variable (ι) in
/-- **The restriction computed with a decoder**: `restrict ι` when `dec` inverts `ι`
(`dec x' = some x` exactly when `ι x = x'`), with support `supp(D)` decoded by `dec`
(`restrictBy_eq`). One pass over `supp(D)`, one call of `dec` per entry. -/
def restrictBy (dec : X' → Option X) (hdec : ∀ x' x, dec x' = some x ↔ ι x = x') (D : DB X' Y) :
    DB X Y :=
  Finmap.keysLookupEquiv.symm
    ⟨(D.keys.filterMap dec (fun a a' x ha ha' => ((hdec a x).1 ha).symm.trans ((hdec a' x).1 ha')),
      fun x => D.lookup (ι x)), fun x => by
      rw [Finset.mem_filterMap, Finmap.lookup_isSome]
      constructor
      · exact fun h => ⟨ι x, Finmap.mem_keys.2 h, (hdec _ x).2 rfl⟩
      · rintro ⟨a, ha, hx⟩
        rw [← (hdec a x).1 hx] at ha
        exact Finmap.mem_keys.1 ha⟩

/-- **The decoder's restriction is the restriction.** -/
theorem restrictBy_eq {dec : X' → Option X} (hdec : ∀ x' x, dec x' = some x ↔ ι x = x')
    (D : DB X' Y) : restrictBy ι dec hdec D = D.restrict ι :=
  Finmap.ext_lookup fun x => by
    rw [lookup_restrict, restrictBy]
    exact Finmap.keysLookupEquiv_symm_apply_lookup _ x

@[simp] theorem restrict_empty : (∅ : DB X' Y).restrict ι = ∅ :=
  Finmap.ext_lookup fun _ => by rw [lookup_restrict, Finmap.lookup_empty, Finmap.lookup_empty]

/-- Restriction does not add entries: `|restrict ι D| ≤ |D|`. -/
theorem size_restrict_le : (D.restrict ι).size ≤ D.size :=
  Finset.card_le_card_of_injOn ι (fun _ hx => Finmap.mem_keys.2 (mem_restrict.1
    (Finmap.mem_keys.1 hx))) ι.injective.injOn

/-- Recording an answer at an image `ι x` records it at `x` in the restriction. -/
theorem restrict_extend_image (x : X) (y : Y) :
    (D.extend (ι x) y).restrict ι = (D.restrict ι).extend x y := by
  refine Finmap.ext_lookup fun x' => ?_
  rw [lookup_restrict]
  by_cases h : x' = x
  · subst h
    rw [lookup_extend_self, lookup_extend_self]
  · rw [lookup_extend_of_ne (ι.injective.ne h), lookup_extend_of_ne h, lookup_restrict]

/-- Recording an answer outside the image of `ι` does not change the restriction. -/
theorem restrict_extend_of_notMem_range {x' : X'} (hx : x' ∉ Set.range ι) (y : Y) :
    (D.extend x' y).restrict ι = D.restrict ι := by
  refine Finmap.ext_lookup fun x => ?_
  rw [lookup_restrict, lookup_restrict, lookup_extend_of_ne fun h => hx ⟨x, h⟩]

end DB

/-! ### Tuples of base games -/

/-- **A tuple of a base game** (CMS19 Def 4.1, p. 18): `k` oracle queries `a`, `k` claimed
answers `b` and an output `c`. A base game (`BaseGame`, `GordieHowe/Model/QROM/Lifting.lean`) is a set of
them. -/
structure BaseGame.Tuple (A B C : Type*) (k : ℕ) where
  /-- The oracle queries `a`. -/
  queries : Fin k → A
  /-- The claimed answers `b`. -/
  answers : Fin k → B
  /-- The output `c`. -/
  out : C

namespace BaseGame.Tuple

variable {A B C : Type*} {k : ℕ}

/-- The claimed answers are those of the oracle `h`: `h(a_i) = b_i` for every `i`. -/
def AnsweredBy (o : Tuple A B C k) (h : A → B) : Prop :=
  ∀ i, h (o.queries i) = o.answers i

/-- The claimed answers are recorded in the database `D`: `D(a_i) = b_i` for every `i` (in
particular `D(a_i) ≠ ⊥`). -/
def InDB [DecidableEq A] (o : Tuple A B C k) (D : DB A B) : Prop :=
  ∀ i, D.lookup (o.queries i) = some (o.answers i)

theorem answeredBy_iff {o : Tuple A B C k} {h : A → B} :
    o.AnsweredBy h ↔ ∀ i, h (o.queries i) = o.answers i :=
  Iff.rfl

theorem inDB_iff [DecidableEq A] {o : Tuple A B C k} {D : DB A B} :
    o.InDB D ↔ ∀ i, D.lookup (o.queries i) = some (o.answers i) :=
  Iff.rfl

end BaseGame.Tuple

end GordieHowe.QROM
