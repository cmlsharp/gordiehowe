-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.OnlineExtract

@[expose] public section

/-!
# Knowledge soundness of a compiled verifier for algorithms with any output, with a test

The knowledge bound of `GordieHowe/SPBCS/Extraction/OnlineExtract.lean` (CMS19 Theorem 8.6 (2)) for a compiled verifier
`V : GordieHowe.NARG.QROM.Verifier` and an algorithm whose output is not a claim but any value `o` (for example all
the classical registers of an interactive adversary composed with its challenger) from which a
claim `c o` is read, jointly with a classical test `ok o` of the same output. The probability that
the algorithm's output passes the test and the verifier accepts its claim is at most the
probability that, in the simulated run of the expanded algorithm, the measured output passes the
test and the database extractor returns a witness for its claim's statement, plus the knowledge
error `V.knowledgeError β (b + kq)` at a per-branch query count `b`. The test is intersected with
the base game and with the extraction event; the oracle simulation (CMS19 Lemma 4.9) and the
database bound (`GordieHowe.NARG.QROM.Verifier.KnowledgeBound.dbProb_le`) hold for every base game and every output.

- `expansionVia V c`: the verifier's query expansion (`BCSExpand`) on the claim `c o`.
- `extAdvVia V c A`: the core algorithm `A` (its coherent pure form, non-termination read
  as `A.defaultOut`) followed by `expansionVia c`.
- `acceptsTest_le_pure_of_queryCount`: the bound for a pure algorithm whose branches query
  at no more than `b` of its steps (`QueryCount`).
-/

namespace GordieHowe.SPBCS.QROM

open GordieHowe.QROM IOP GordieHowe.NARG
open scoped NNReal ENNReal

variable {m k e : ℕ} {Cl Stmt : Type} (V : NARG.QROM.Verifier m k e Cl Stmt) {O : Type}

/-- **The verifier's query expansion on the claim read from an output** (`BCSExpand`, CMS19
p. 39): on an output `o`, the queries of `V.expansion` on the claim `c o`. -/
def expansionVia (c : O → Cl) : Expansion (Bits m) (Out k e) O :=
  ⟨fun o ans => V.expansion.next (c o) ans⟩

theorem run_expansionVia (c : O → Cl) (h : Bits m → Out k e) (o : O) :
    ∀ i, (expansionVia V c).run h o i = V.expansion.run h (c o) i
  | 0 => rfl
  | i + 1 => by
    simp only [Expansion.run, run_expansionVia c h o i]
    rfl

/-- The expansion on `o` is the expansion on the claim `c o`, with the output `o`. -/
theorem expand_expansionVia (c : O → Cl) (h : Bits m → Out k e) (o : O) {K : ℕ} :
    (expansionVia V c).expand (k := K) h o =
      ⟨(V.expansion.expand (k := K) h (c o)).queries,
        (V.expansion.expand (k := K) h (c o)).answers, o⟩ := by
  have hq : (expansionVia V c).queries (k := K) h o = V.expansion.queries h (c o) := by
    funext i
    simp only [Expansion.queries, run_expansionVia]
  simp only [Expansion.expand, hq]

/-- **The base game with a test**: the output passes `ok`, and the tuple with the claim `c o` in
place of `o` is a win of the verifier's base game. -/
def gameVia (c : O → Cl) (ok : O → Prop) : BaseGame (Bits m) (Out k e) O V.kq :=
  {o | ok o.out ∧ (⟨o.queries, o.answers, c o.out⟩ : BaseGame.Tuple _ _ _ V.kq) ∈ V.game}

/-- **The expanded algorithm on outputs with a claim readout**: the coherent pure form of the core
algorithm `A` (`Alg.toQueryAlgCoh`, non-termination read as `A.defaultOut`), followed by the
verifier's queries on the claim `c o` of its output (`expansionVia`).

Running time: `A` in its pure serial form (the same queries, each Kraus map replaced by its
Stinespring unitary on registers of polynomial size in `A`'s), then the verifier's `kq` queries on
the claim, computed by the verifier's query program; polynomial when `A` and `c` are.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev extAdvVia (c : O → Cl) (A : Quantum.Alg (Bits m) (XOut k e) O) :
    Adv (Bits m) (XOut k e) (Out k e) O V.kq (A.depth + V.kq) :=
  expandAdv (outEquiv k e) (expansionVia V c) V.kq (A.toQueryAlgCoh.mapOut (·.getD A.defaultOut))

variable {Wit : Type} {rel : Set (Stmt × Wit)} {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit}
  {β : ℕ → ℝ≥0∞}

variable {V} in
/-- **Knowledge soundness jointly with a test, for a pure algorithm with a per-branch query
count** (CMS19 Theorem 8.6 (2) with a classical test of the output): the probability that the
output of `𝒜` passes `ok` and the verifier accepts its claim `c o` is at most the probability that,
in the simulated run of `𝒜` followed by the verifier's queries, the measured output passes `ok`
and `ext` returns a witness for the claim's statement from the measured database, plus
`knowledgeError β (b + kq)`, for a pure algorithm whose branches query at no more than `b` of its
steps (`QueryCount`). -/
theorem acceptsTest_le_pure_of_queryCount (K : V.KnowledgeBound rel ext β)
    (c : O → Cl)
    (ok : O → Prop) {t b : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t O)
    (h : QueryCount (outEquiv k e) 𝒜 b) :
    (𝒜.realLaw (outEquiv k e)).toOuterMeasure {p | ok p.out ∧ V.Accepted p.oracle (c p.out)} ≤
      simProb (outEquiv k e) (expandAdv (outEquiv k e) (expansionVia V c) V.kq 𝒜)
        (fun o D => ok o ∧ ExtractsAt rel ext (V.stmt (c o)) D) +
      V.knowledgeError β (b + V.kq) := by
  set Gm := gameVia V c ok
  set 𝒜' := expandAdv (outEquiv k e) (expansionVia V c) V.kq 𝒜
  have hexp : (𝒜.realLaw (outEquiv k e)).toOuterMeasure
      {p | ok p.out ∧ V.Accepted p.oracle (c p.out)} ≤ winO (outEquiv k e) 𝒜' Gm := by
    refine winO_expandAdv _ _ 𝒜 fun p hp => ?_
    refine ⟨hp.1, ?_⟩
    rw [expand_expansionVia]
    exact (V.expand_mem_game_iff p.oracle (c p.out)).2 hp.2
  have hO := le_add_two_mul_of_esqrt_le (winO_le_one (outEquiv k e) 𝒜' Gm)
    (Lifting.oracle_sim_card (outEquiv k e) 𝒜' Gm)
  have hS : winS (outEquiv k e) 𝒜' Gm ≤
      simProb (outEquiv k e) 𝒜' (fun o D => ok o ∧ ExtractsAt rel ext (V.stmt (c o)) D) +
      β (b + V.kq) := by
    refine (winS_le_simProb_add (outEquiv k e) 𝒜' Gm fun o ho D hD => ?_).trans
      (add_le_add le_rfl (K.dbProb_le 𝒜'
        (QueryCount.expandAdv V.kq (outEquiv k e) (expansionVia V c) h)))
    obtain ⟨hok, hg⟩ := ho
    rcases K.mem_of_game _ hg D hD with hx | hx
    · exact Or.inl ⟨hok, hx⟩
    · exact Or.inr hx
  calc (𝒜.realLaw (outEquiv k e)).toOuterMeasure {p | ok p.out ∧ V.Accepted p.oracle (c p.out)}
      ≤ winS (outEquiv k e) 𝒜' Gm + 2 * esqrt (V.kq / Fintype.card (Out k e)) := hexp.trans hO
    _ ≤ _ := by
        rw [NARG.QROM.Verifier.knowledgeError]
        refine (add_le_add hS le_rfl).trans ?_
        rw [add_assoc, add_comm (β _) _]

end GordieHowe.SPBCS.QROM
