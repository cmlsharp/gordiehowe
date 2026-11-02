-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.QROM.Select

@[expose] public section

/-!
# Reading a database by answer digest

A compiled argument whose chain inputs hold other chains' digests in place of the chains reads
those chains back through the recorded answers: the recorded `transcript` input whose answer has a
given digest, unique in a database without digest collisions.

* `findTr D v`: the recorded `transcript` input whose answer has digest `v` (`DB.select`).
* `findTr_eq_some_iff`, `findTr_of_lookup`, `findTr_eq_none`: reading it back.
* `findTr_extend`, `findTr_extend_self`: recording one fresh answer changes `findTr` only at the
  digest of a new `transcript` input.

Running time: `findTr` is one pass over the entries.
This running time is argued here, not proved in Lean.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM

variable {k kN kS L e : ℕ}

/-- The bytes of a `transcript` query. -/
def trBytes : Query k kN kS L → Option (Bytes L)
  | .transcript b => some b
  | _ => none

/-- **The recorded `transcript` input whose answer has digest `v`.** -/
def findTr (D : ODB k kN kS L e) (v : Digest k) : Option (Bytes L) :=
  D.select fun q y => if y.digest = v then trBytes q else none

/-! ### Reading by answer digest -/

section Find

variable {D : ODB k kN kS L e}

/-- **In a database without digest collisions, an answer digest determines the query.** -/
theorem eq_of_lookup_digest_eq (hD : D ∉ digestCollision) {q₁ q₂ : Query k kN kS L}
    {y₁ y₂ : Out k e} (h₁ : D.lookup q₁ = some y₁) (h₂ : D.lookup q₂ = some y₂)
    (hd : y₁.digest = y₂.digest) : q₁ = q₂ := by
  by_contra hne
  exact hD ⟨q₁, Finmap.mem_of_lookup_eq_some h₁, q₂, Finmap.mem_of_lookup_eq_some h₂, hne,
    by rw [h₁, h₂]; simp [hd]⟩

theorem selectUnique_digest (hD : D ∉ digestCollision) {α : Type*}
    (sel : Query k kN kS L → Option α) (v : Digest k) :
    DB.SelectUnique (fun q y => if y.digest = v then sel q else none) D := by
  intro q₁ q₂ y₁ y₂ a₁ a₂ h₁ h₂ hf₁ hf₂
  dsimp only at hf₁ hf₂
  split_ifs at hf₁ hf₂ with hv₁ hv₂
  exact eq_of_lookup_digest_eq hD h₁ h₂ (hv₁.trans hv₂.symm)

/-- **The `transcript` input whose answer has digest `v`.** -/
theorem findTr_eq_some_iff (hD : D ∉ digestCollision) {v : Digest k} {b : Bytes L} :
    findTr D v = some b ↔ ∃ y, D.lookup (.transcript b) = some y ∧ y.digest = v := by
  rw [findTr, DB.select_eq_some_iff (selectUnique_digest hD trBytes v)]
  constructor
  · rintro ⟨q, y, hq, hf⟩
    split_ifs at hf with hv
    cases q <;> simp only [trBytes, reduceCtorEq, Option.some.injEq] at hf
    subst hf
    exact ⟨y, hq, hv⟩
  · rintro ⟨y, hy, hv⟩
    exact ⟨_, y, hy, by simp [hv, trBytes]⟩

theorem findTr_of_lookup (hD : D ∉ digestCollision) {b : Bytes L} {y : Out k e}
    (hy : D.lookup (.transcript b) = some y) : findTr D y.digest = some b :=
  (findTr_eq_some_iff hD).2 ⟨y, hy, rfl⟩

/-- `findTr` is `none` when no recorded `transcript` input has an answer of digest `v`. -/
theorem findTr_eq_none {v : Digest k} (h : ∀ b y, D.lookup (.transcript b) = some y → y.digest ≠ v) :
    findTr D v = none :=
  DB.select_eq_none_of_forall fun q y hq => by
    cases q <;> simp only [trBytes, ite_self]
    split_ifs with hv
    · exact absurd hv (h _ y hq)
    · rfl

end Find

/-! ### Reading by digest after recording one answer -/

section FindExtend

variable {D : ODB k kN kS L e} {q : Query k kN kS L} {y : Out k e}

theorem notMem_digestCollision_of_extend (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision) :
    D ∉ digestCollision :=
  notMem_collisionOn_of_extend hq hcol

theorem lookup_extend_eq_some_iff (hq : q ∉ D) {q₀ : Query k kN kS L} {y₀ : Out k e} :
    (D.extend q y).lookup q₀ = some y₀ ↔ D.lookup q₀ = some y₀ ∨ (q₀ = q ∧ y₀ = y) := by
  by_cases h : q₀ = q
  · subst h
    rw [DB.lookup_extend_self, Finmap.lookup_eq_none.2 hq]
    simp [eq_comm]
  · rw [DB.lookup_extend_of_ne h]
    simp [h]

/-- **Recording a new answer leaves `findTr` at `v`** unless the new query is a `transcript`
input whose answer has digest `v`. -/
theorem findTr_extend (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision) {v : Digest k}
    (hv : ∀ b, q = .transcript b → y.digest ≠ v) : findTr (D.extend q y) v = findTr D v := by
  have hD := notMem_digestCollision_of_extend hq hcol
  refine Option.ext fun b => ?_
  rw [findTr_eq_some_iff hcol, findTr_eq_some_iff hD]
  constructor
  · rintro ⟨y₀, hy₀, hd⟩
    rcases (lookup_extend_eq_some_iff hq).1 hy₀ with h | ⟨hq₀, rfl⟩
    · exact ⟨y₀, h, hd⟩
    · exact absurd hd (hv b hq₀.symm)
  · rintro ⟨y₀, hy₀, hd⟩
    exact ⟨y₀, (lookup_extend_eq_some_iff hq).2 (Or.inl hy₀), hd⟩

/-- A new `transcript` input is the one input found at its answer's digest, which no input of `D`
had. -/
theorem findTr_extend_self (hq : q ∉ D) (hcol : D.extend q y ∉ digestCollision) {b : Bytes L}
    (hb : q = .transcript b) :
    findTr (D.extend q y) y.digest = some b ∧ findTr D y.digest = none := by
  have hD := notMem_digestCollision_of_extend hq hcol
  refine ⟨findTr_of_lookup hcol (hb ▸ DB.lookup_extend_self), findTr_eq_none fun b' y' hy' hd => ?_⟩
  have h1 : (D.extend q y).lookup (.transcript b') = some y' :=
    (lookup_extend_eq_some_iff hq).2 (Or.inl hy')
  have h2 : (D.extend q y).lookup q = some y := DB.lookup_extend_self
  have := eq_of_lookup_digest_eq hcol h1 h2 hd
  exact hq (this ▸ Finmap.mem_of_lookup_eq_some hy')

end FindExtend

end GordieHowe.SPBCS
