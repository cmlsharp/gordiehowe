-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.ROM

@[expose] public section

/-!
# Online extractability of a compiled verifier in the classical random-oracle model, generically

The ROM knowledge-soundness argument (online extractability against a lazily sampled oracle, DFMS22
Definition 3.1, p. 10, with classical adversaries), stated once for every verifier
(`GordieHowe.NARG.ROM.Verifier`) at a database extractor with a joint knowledge bound for
deterministic `t`-query algorithms (`GordieHowe.NARG.ROM.Verifier.JointBound`). The spBCS compiler
is an instance (`GordieHowe/SPBCS/KnowledgeROM.lean`).

- `onlineExtracts`: every classical `t`-query adversary (`GordieHowe.NARG.ROM.Adversary`) with an
  auxiliary output is online extractable at error `β (t + kq)`;
- `soundness`: the probability of an accepted claim for a statement without a witness is at most
  `β (t + kq)`.
-/

namespace GordieHowe.SPBCS.ROM

open GordieHowe.QROM GordieHowe.IOP GordieHowe.NARG
open scoped NNReal ENNReal

variable {A B Cl Stmt : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
  {V : NARG.ROM.Verifier A B Cl Stmt} {Wit : Type} {rel : Set (Stmt × Wit)}
  {ext : Stmt → DB A B → Multiset Wit} {β : ℕ → ℝ≥0∞}

/-- **Online extractability in the classical random-oracle model**: from the joint knowledge
bound, every classical `t`-query adversary with an auxiliary output is online extractable with the
law of the lazily sampled oracle (`NARG.ROM.OracleSampler.lazy`) and the extractor reading its
table, at simulation error `0` and extraction error `β (t + kq)`. -/
theorem onlineExtracts (hβ : V.JointBound rel ext β) {Z : Type} {t : ℕ}
    (𝒢 : NARG.ROM.Adversary A B (Cl × Z) t) :
    𝒢.OnlineExtracts V NARG.ROM.OracleSampler.lazy.law rel ext 0 (β (t + V.kq)) := by
  refine ⟨(𝒢.tvDist_extractionLaw_lazy V).le, 𝒢.tsum_le fun r => ?_⟩
  rw [NARG.ROM.Adversary.extractionRun, NARG.ROM.OracleSim.run_lazy, PMF.toOuterMeasure_map_apply]
  refine le_of_eq_of_le ?_ (hβ ((𝒢.queryAlg r).mapOut Prod.fst))
  unfold probUniform
  congr 1
  ext h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, NARG.ROM.Adversary.outputOf_answers,
    NARG.ROM.Adversary.verdictOf_answers]
  rw [GordieHowe.ROM.Alg.output_mapOut]

/-- **Soundness in the classical random-oracle model**: from the joint knowledge bound, a
classical `t`-query adversary outputs an accepted claim for a statement without a witness with
probability at most `β (t + kq)` (`lem:ks-sound`, `NARG.ROM.Adversary.acceptsFalse_le`, at the
online extractability of `onlineExtracts`, simulation error `0`). -/
theorem soundness (hβ : V.JointBound rel ext β) {t : ℕ} (𝒜 : NARG.ROM.Adversary A B Cl t) :
    𝒜.acceptsFalse V rel ≤ β (t + V.kq) :=
  (𝒜.acceptsFalse_le V (onlineExtracts hβ 𝒜.withUnit)).trans_eq (by simp)

end GordieHowe.SPBCS.ROM
