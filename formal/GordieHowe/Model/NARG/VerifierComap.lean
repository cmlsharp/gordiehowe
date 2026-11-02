-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.QROM

@[expose] public section

/-!
# A verifier read at the statements of another type

A verifier `V` on claims `Cl` with statements in `Stmt₀`, read at statements `x : Stmt` through a
statement map `stmt : Stmt → Stmt₀` and a statement check `check : Stmt → Bool`: its claims are
pairs `(x, c)`, accepted when `x` passes the check, the statement of `c` is `stmt x` and `V`
accepts `c`; the statement of `(x, c)` is `x`. Its queries are `V`'s on `c`. A knowledge bound of
`V` for a relation `rel₀` gives one of the read verifier for every relation `rel` that a witness
map `wit` reaches from `rel₀` at checked statements, at the same database bound.

- `QROM.Expansion.comap`: an expansion on the inputs read through a map; `run_comap`,
  `queries_comap`.
- `NARG.Verifier.comap V stmt check`: the read verifier; `accepted_comap_iff`.
  `mem_game_of_mem_game_comap`: a tuple of its base game gives one of `V`'s at the claim's second
  component, with the check passed and the statement `stmt` of the first.
- `NARG.QROM.Verifier.KnowledgeBound.comap`: the knowledge bound of the read verifier, the
  extractor's witnesses at `stmt x` mapped by `wit x`; `knowledgeError_comap`: the knowledge error
  is `V`'s.
-/

namespace GordieHowe

namespace QROM.Expansion

variable {A B C C' : Type*} (X : Expansion A B C) (f : C' → C)

/-- **The expansion on inputs read through `f`**: the next query on `c` is `X`'s on `f c`. -/
def comap : Expansion A B C' := ⟨fun c ans => X.next (f c) ans⟩

/-- The run of the read expansion on `c` is `X`'s on `f c`. -/
theorem run_comap (h : A → B) (c : C') : ∀ i, (X.comap f).run h c i = X.run h (f c) i
  | 0 => rfl
  | i + 1 => by
    simp only [run, run_comap h c i]
    rfl

/-- The queries of the read expansion on `c` are `X`'s on `f c`. -/
theorem queries_comap (h : A → B) (c : C') {k : ℕ} (i : Fin k) :
    (X.comap f).queries h c i = X.queries h (f c) i := by
  simp only [queries, run_comap]

end QROM.Expansion

namespace NARG.Verifier

variable {A B Cl Stmt₀ Stmt : Type} (V : Verifier A B Cl Stmt₀) (stmt : Stmt → Stmt₀)
  (check : Stmt → Bool)

/-- **The verifier read at the statements `Stmt`**: claims `(x, c)`, the queries of `V` on `c`,
accepted on answers when `x` passes `check`, the statement of `c` is `stmt x` and `V` accepts `c`
on them; the statement of `(x, c)` is `x`. -/
def comap : Verifier A B (Stmt × Cl) Stmt where
  kq := V.kq
  expansion := V.expansion.comap Prod.snd
  AcceptsOn c a := check c.1 = true ∧ V.stmt c.2 = stmt c.1 ∧ V.AcceptsOn c.2 a
  stmt := Prod.fst

/-- **The read verifier accepts `(x, c)` exactly when `x` passes the check, `c` is a claim of
`stmt x` and `V` accepts `c`.** -/
theorem accepted_comap_iff (h : A → B) (x : Stmt) (c : Cl) :
    (V.comap stmt check).Accepted h (x, c) ↔
      check x = true ∧ V.stmt c = stmt x ∧ V.Accepted h c := by
  have hans : (V.comap stmt check).answers h (x, c) = V.answers h c :=
    funext fun i => congrArg h (V.expansion.queries_comap Prod.snd h (x, c) i)
  change check x = true ∧ V.stmt c = stmt x ∧ V.AcceptsOn c ((V.comap stmt check).answers h (x, c))
    ↔ _
  rw [hans]
  rfl

/-- **A tuple of the base game of the read verifier** gives one of `V`'s at its claim's second
component, whose statement is `stmt` of the first, which passes the check. -/
theorem mem_game_of_mem_game_comap {o : QROM.BaseGame.Tuple A B (Stmt × Cl) V.kq}
    (ho : o ∈ (V.comap stmt check).game) :
    (⟨o.queries, o.answers, o.out.2⟩ : QROM.BaseGame.Tuple A B Cl V.kq) ∈ V.game ∧
      check o.out.1 = true ∧ V.stmt o.out.2 = stmt o.out.1 := by
  obtain ⟨hq, hc, hs, ha⟩ := ho
  exact ⟨⟨hq, ha⟩, hc, hs⟩

end NARG.Verifier

namespace NARG.QROM.Verifier

open GordieHowe.QROM
open scoped ENNReal

variable {m k e : ℕ} {Cl Stmt₀ Stmt Wit₀ Wit : Type} {V : Verifier m k e Cl Stmt₀}
  {rel₀ : Set (Stmt₀ × Wit₀)} {ext₀ : Stmt₀ → DB (Bits m) (Out k e) → Multiset Wit₀}
  {β : ℕ → ℝ≥0∞}

/-- **The knowledge bound of the read verifier**: for a knowledge bound `K` of `V` for `rel₀` at
the extractor `ext₀`, and a witness map `wit` sending a witness of `rel₀` at `stmt x` of a checked
statement `x` to a witness of `rel` at `x` (`hrel`), the read verifier has a knowledge bound for
`rel` at the extractor returning `wit x` of `ext₀`'s witnesses at `stmt x`, with `K`'s bad
databases and database bound. -/
def KnowledgeBound.comap (K : V.KnowledgeBound rel₀ ext₀ β) (stmt : Stmt → Stmt₀)
    (check : Stmt → Bool) (rel : Set (Stmt × Wit)) (wit : Stmt → Wit₀ → Wit)
    (hrel : ∀ x w, check x = true → (stmt x, w) ∈ rel₀ → (x, wit x w) ∈ rel) :
    KnowledgeBound (NARG.Verifier.comap V stmt check) rel
      (fun x D => (ext₀ (stmt x) D).map (wit x)) β where
  bad := K.bad
  mem_of_game o ho D hD := by
    obtain ⟨hg, hc, hs⟩ := NARG.Verifier.mem_game_of_mem_game_comap V stmt check ho
    rcases K.mem_of_game _ hg D hD with ⟨w, hw, hr⟩ | hb
    · change (V.stmt o.out.2, w) ∈ rel₀ at hr
      change w ∈ ext₀ (V.stmt o.out.2) D at hw
      rw [hs] at hr hw
      exact Or.inl ⟨wit o.out.1 w, Multiset.mem_map_of_mem _ hw, hrel _ _ hc hr⟩
    · exact Or.inr hb
  dbProb_le 𝒜 hb := K.dbProb_le 𝒜 hb
  mono := K.mono

/-- **The knowledge error of the read verifier is `V`'s**: it has `V`'s queries. -/
theorem knowledgeError_comap (stmt : Stmt → Stmt₀) (check : Stmt → Bool) (b : ℕ) :
    knowledgeError (NARG.Verifier.comap V stmt check) β b = V.knowledgeError β b :=
  rfl

end NARG.QROM.Verifier

end GordieHowe
