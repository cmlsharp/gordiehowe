-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The verifier of a non-interactive argument

The verifier of a non-interactive argument with an oracle `A → B` (the paper's `def:narg`, DFMS22
section 3.1), as a classical query algorithm on claims `Cl` with statements in `Stmt`: its number
`kq` of queries, its query expansion (`BCSExpand`, CMS19 p. 39), its acceptance at an oracle and
the statement of a claim. The honest prover is `GordieHowe.NARG.ProverFn`
(`GordieHowe/Model/NARG/Prover.lean`). The notions of the argument are stated over this verifier in
the quantum random-oracle model (`GordieHowe/Model/NARG/QROM.lean`) and in the classical
random-oracle model (`GordieHowe/Model/NARG/ROM.lean`).
-/

namespace GordieHowe.NARG

/-- **The verifier of a non-interactive argument** with oracle `A → B`, on claims `Cl` with
statements in `Stmt`, as a classical query algorithm (the paper's `def:narg`; the verifier of
`def:narg-ks` outputs a bit from the claim and the oracle's answers): its query expansion with `kq`
queries, its decision on the claim and the answers to its queries, and the statement of a claim. -/
structure Verifier (A B Cl Stmt : Type) where
  /-- The number of the verifier's queries. -/
  kq : ℕ
  /-- The verifier's query expansion (`BCSExpand`, CMS19 p. 39). -/
  expansion : QROM.Expansion A B Cl
  /-- The verifier's decision: it accepts the claim with these answers to its `kq` queries. -/
  AcceptsOn : Cl → (Fin kq → B) → Prop
  /-- The statement of a claim. -/
  stmt : Cl → Stmt

namespace Verifier

variable {A B Cl Stmt : Type} (V : Verifier A B Cl Stmt)

/-- **The answers of the oracle `h` to the verifier's queries on `c`.** -/
def answers (h : A → B) (c : Cl) : Fin V.kq → B :=
  fun i => h (V.expansion.queries h c i)

/-- **The verifier accepts the claim with the oracle**: its decision on the oracle's answers to its
queries. -/
def Accepted (h : A → B) (c : Cl) : Prop :=
  V.AcceptsOn c (V.answers h c)

/-- **The base game of the verifier** (CMS19 Definition 8.1, p. 39): the tuples of `kq` queries,
their answers and a claim whose queries are the verifier's queries on the answers
(`QROM.Expansion.queriesOn`) and on whose answers the verifier accepts. -/
def game : Set (QROM.BaseGame.Tuple A B Cl V.kq) :=
  {o | o.queries = V.expansion.queriesOn o.out o.answers ∧ V.AcceptsOn o.out o.answers}

/-- **CMS19 Proposition 8.11** (p. 42, classical half): the expanded claim wins the base game
exactly when the verifier accepts it. -/
theorem expand_mem_game_iff (h : A → B) (c : Cl) :
    V.expansion.expand (k := V.kq) h c ∈ V.game ↔ V.Accepted h c :=
  ⟨fun hg => hg.2, fun ha => ⟨funext fun i => V.expansion.queries_eq_queriesOn h c i, ha⟩⟩

/-- **The verifier of an acceptance predicate on oracles**: with `kq` queries by `X`, it accepts
the answers when some oracle with these answers at the queries computed from them satisfies
`Acc`. -/
def ofOracle (kq : ℕ) (X : QROM.Expansion A B Cl) (Acc : (A → B) → Cl → Prop) (stmt : Cl → Stmt) :
    Verifier A B Cl Stmt where
  kq := kq
  expansion := X
  AcceptsOn c a := ∃ h : A → B, (∀ i, h (X.queriesOn c a i) = a i) ∧ Acc h c
  stmt := stmt

variable {kq : ℕ} {X : QROM.Expansion A B Cl} {Acc : (A → B) → Cl → Prop} {stmt : Cl → Stmt}

/-- An oracle satisfying the predicate is accepted. -/
theorem ofOracle_accepted_of {h : A → B} {c : Cl} (hA : Acc h c) :
    (ofOracle kq X Acc stmt).Accepted h c :=
  ⟨h, fun i => congrArg h (X.queries_eq_queriesOn h c i).symm, hA⟩

/-- **The decision of `ofOracle` is the predicate** when the predicate reads the oracle only at
the verifier's queries (`hloc`). -/
theorem ofOracle_accepted_iff
    (hloc : ∀ h h' c, (∀ i : Fin kq, h' (X.queries h' c i) = h (X.queries h' c i)) → Acc h' c →
      Acc h c)
    {h : A → B} {c : Cl} : (ofOracle kq X Acc stmt).Accepted h c ↔ Acc h c := by
  refine ⟨fun ⟨h', hh', hA⟩ => hloc h h' c (fun i => ?_) hA, ofOracle_accepted_of⟩
  have hag : ∀ i : Fin kq, h' (X.queries h c i) = h (X.queries h c i) := fun i =>
    (congrArg h' (X.queries_eq_queriesOn h c i)).trans (hh' i)
  have he : X.expand h' c = X.expand (k := kq) h c :=
    X.expand_eq_of_queries_eq h' (o := X.expand h c)
      (funext fun i => X.queries_eq_queriesOn h c i) hag
  have hq : X.queries h' c i = X.queries h c i := congrArg (fun o => o.queries i) he
  rw [hq]
  exact hag i

/-- **The base game of `ofOracle`**: the expansions of the claims against oracles satisfying the
predicate. -/
theorem mem_game_ofOracle {o : QROM.BaseGame.Tuple A B Cl kq} :
    o ∈ (ofOracle kq X Acc stmt).game ↔ ∃ h, X.expand h o.out = o ∧ Acc h o.out := by
  constructor
  · rintro ⟨hq, h, hh, hA⟩
    exact ⟨h, X.expand_eq_of_queries_eq h hq fun i => by rw [hq]; exact hh i, hA⟩
  · rintro ⟨h, he, hA⟩
    rw [← he]
    exact ((ofOracle kq X Acc stmt).expand_mem_game_iff h o.out).2 (ofOracle_accepted_of hA)

end Verifier

/-- **An output with the verifier's verdict on it** (the tuple `(inst, π, Z, v)` of DFMS22
Definition 3.1, p. 10): the adversary's output, `none` when it does not terminate, and whether the
verifier accepts the claim read from it. -/
structure VerifiedOutput (O : Type) where
  /-- The output; `none` when the adversary does not terminate. -/
  out : Option O
  /-- The verifier accepts the claim read from the output. -/
  accepted : Prop

/-- **The extractor returns a witness for `x` from the state `D`** (a database, or the final state of
an oracle simulator): some witness `ext x D` returns is a witness of `x` in `rel`. -/
def ExtractsAt {St Stmt Wit : Type} (rel : Set (Stmt × Wit)) (ext : Stmt → St → Multiset Wit)
    (x : Stmt) (D : St) : Prop :=
  ∃ w ∈ ext x D, (x, w) ∈ rel

end GordieHowe.NARG
