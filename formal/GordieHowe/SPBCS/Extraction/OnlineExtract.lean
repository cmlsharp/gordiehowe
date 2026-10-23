-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.QROM

@[expose] public section

/-!
# Online extractability of a compiled verifier, generically

The QROM knowledge-soundness argument (CMS19 Theorem 8.6 (2), DFMS22 Definition 3.1), stated once
for every verifier (`GordieHowe.NARG.QROM.Verifier`) with its base game
(`GordieHowe.NARG.Verifier.game`), a database extractor and a database bound
(`GordieHowe.NARG.QROM.Verifier.KnowledgeBound`). The spBCS compiler
(`GordieHowe/SPBCS/Online.lean`) is an instance.

- `acceptsAnswers_expand`, `simLaw_verdict`: the verdict on an expanded output is the verifier's.
- `extractionOutputState_eq`: the extraction run leaves `(output, Z)` in the real run's state.
- `cohOnlineExtracts_of_queryCount`, `cohOnlineExtracts_requestFree`: online extractability
  (`GordieHowe.NARG.QROM.Verifier.CohOnlineExtracts`) at error
  `knowledgeError β (t + kq) = 2√(kq/|Out|) + β (t + kq)`.
- `onlineExtracts`, `soundness`: the bounds for the adversaries `GordieHowe.NARG.QROM.Adversary`.
-/

namespace GordieHowe.SPBCS.QROM

open IOP GordieHowe.QROM GordieHowe.NARG
open GordieHowe.NARG.QROM (compressedSim compressedExt)
open GordieHowe.Quantum (QueryReg ketBra blockOn ptraceAlong mask reduce)
open scoped NNReal ENNReal

variable {m k e : ℕ} {Cl Stmt : Type}

/-! ### The extraction run -/

section

variable (V : NARG.QROM.Verifier m k e Cl Stmt) {O : Type} (claimOf : O → Cl)

theorem queries_expansionOpt (o₀ : O) (h : Bits m → Out k e) (o : Option O) {K : ℕ} (i : Fin K) :
    (V.expansionOpt claimOf o₀).queries h o i = V.expansion.queries h (claimOf (o.getD o₀)) i :=
  Expansion.queries_eq_of_next_eq (X := V.expansion) (X' := V.expansionOpt claimOf o₀) h
    (fun _ => rfl) i

end

variable (V : NARG.QROM.Verifier m k e Cl Stmt) {O : Type} (claimOf : O → Cl)

/-- **The verdict on an expanded output is the verifier's verdict.** -/
theorem acceptsAnswers_expand (o₀ : O) (h : Bits m → Out k e) (o : Option O) :
    V.AcceptsAnswers claimOf ((V.expansionOpt claimOf o₀).expand h o) ↔
      ∃ c ∈ o, V.Accepted h (claimOf c) := by
  refine exists_congr fun c => and_congr_right fun hc => ?_
  rw [Option.mem_def] at hc
  subst hc
  rw [← V.expand_mem_game_iff]
  have hq : ((V.expansionOpt claimOf o₀).queries h (some c) : Fin V.kq → _) =
      V.expansion.queries h (claimOf c) :=
    funext (queries_expansionOpt V claimOf o₀ h (some c))
  simp only [Expansion.expand, hq]

theorem acceptsAnswers_of_acceptsNotExtracts {Wit : Type} {rel : Set (Stmt × Wit)}
    {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit}
    {o : BaseGame.Tuple (Bits m) (Out k e) (Option O) V.kq} {D : DB (Bits m) (Out k e)}
    (h : V.AcceptsNotExtracts claimOf rel ext o D) : V.AcceptsAnswers claimOf o :=
  let ⟨c, hc, hg, _⟩ := h
  ⟨c, hc, hg⟩

/-- **The output and verdict of the extraction run have the real law** (DFMS22 Definition 3.1,
p. 10, first condition, with `εsim = 0`). -/
theorem simLaw_verdict (o₀ : O) {t : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O))
    (S : Set (VerifiedOutput O)) :
    simLaw (outEquiv k e) (V.expandedOpt claimOf o₀ 𝒜)
        {p | (⟨p.1.out, V.AcceptsAnswers claimOf p.1⟩ : VerifiedOutput O) ∈ S} =
      (𝒜.realLaw (outEquiv k e)).toOuterMeasure
        {p | (⟨p.out, ∃ c ∈ p.out, V.Accepted p.oracle (claimOf c)⟩ : VerifiedOutput O) ∈ S} := by
  classical
  rw [show {p : BaseGame.Tuple _ _ _ V.kq × DB _ _ |
      (⟨p.1.out, V.AcceptsAnswers claimOf p.1⟩ : VerifiedOutput O) ∈ S} =
      {p | p.1 ∈ {o | (⟨o.out, V.AcceptsAnswers claimOf o⟩ : VerifiedOutput O) ∈ S}} from rfl,
    simLaw_out, expand_adversary, PMF.toOuterMeasure_map_apply]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [propext (acceptsAnswers_expand V claimOf o₀ p.oracle p.out)]
  rfl

/-- **The queries of the extraction run are computed from their answers, almost surely**: the
outcomes whose queries are not the verifier's queries on the answers (`Expansion.queriesOn`) have
probability `0`. -/
theorem simLaw_queries_ne (o₀ : O) {t : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O)) :
    simLaw (outEquiv k e) (V.expandedOpt claimOf o₀ 𝒜)
        {p | p.1.queries ≠ (V.expansionOpt claimOf o₀).queriesOn p.1.out p.1.answers} = 0 := by
  classical
  rw [show {p : BaseGame.Tuple _ _ _ V.kq × DB _ _ |
      p.1.queries ≠ (V.expansionOpt claimOf o₀).queriesOn p.1.out p.1.answers} =
      {p | p.1 ∈ {o | o.queries ≠ (V.expansionOpt claimOf o₀).queriesOn o.out o.answers}} from rfl,
    simLaw_out, expand_adversary, PMF.toOuterMeasure_map_apply]
  exact MeasureTheory.measure_mono_null
    (fun p hp => (hp (funext fun i => Expansion.queries_eq_queriesOn _ _ _ i)).elim)
    MeasureTheory.measure_empty

/-! ### The joint bound for a pure algorithm with a per-branch query count -/

variable {Wit : Type} {rel : Set (Stmt × Wit)} {ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit}
  {β : ℕ → ℝ≥0∞}

/-- **The joint knowledge bound in the extraction run of a pure algorithm with a per-branch
query count `b`**: the verifier accepts the claim of its output on the answers it received while
the extractor returns no witness with probability at most `knowledgeError β (b + kq)`. -/
theorem simLaw_acceptsNotExtracts_le_of_queryCount (K : V.KnowledgeBound rel ext β) (o₀ : O)
    {t b : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O))
    (hb : QueryCount (outEquiv k e) 𝒜 b) :
    simLaw (outEquiv k e) (V.expandedOpt claimOf o₀ 𝒜)
        {p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2} ≤ V.knowledgeError β (b + V.kq) := by
  set B := V.expandedOpt claimOf o₀ 𝒜
  have hB : QueryCount (outEquiv k e) B (b + V.kq) :=
    QueryCount.expandAdv V.kq (outEquiv k e) (V.expansionOpt claimOf o₀) hb
  set Gm : BaseGame (Bits m) (Out k e) (Option O) V.kq := {o | V.AcceptsAnswers claimOf o}
  set T : Set (BaseGame.Tuple (Bits m) (Out k e) (Option O) V.kq × DB (Bits m) (Out k e)) :=
    {p | p.1.InDB p.2}
  have hin : simLaw (outEquiv k e) B ({p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2} ∩ T) ≤
      β (b + V.kq) := by
    refine (MeasureTheory.measure_mono fun p hp => ?_).trans (K.dbProb_le B hB)
    obtain ⟨⟨c, hc, hg, hne⟩, hD⟩ := hp
    rcases K.mem_of_game _ hg p.2 hD with h | h
    · exact absurd h hne
    · exact h
  have hG : simLaw (outEquiv k e) B {p | p.1 ∈ Gm} = winO (outEquiv k e) B Gm := by
    rw [simLaw_out, winO, expand_adversary, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext p
    exact (and_iff_left fun _ => rfl).symm
  have hwin := le_add_two_mul_of_esqrt_le (winO_le_one (outEquiv k e) B Gm)
    (Lifting.oracle_sim_card (outEquiv k e) B Gm)
  have hS : winS (outEquiv k e) B Gm = simLaw (outEquiv k e) B ({p | p.1 ∈ Gm} ∩ T) := rfl
  have hout : simLaw (outEquiv k e) B ({p | p.1 ∈ Gm} \ T) ≤
      2 * esqrt (V.kq / Fintype.card (Out k e)) := by
    have hfin : winS (outEquiv k e) B Gm ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ((hS.trans_le (MeasureTheory.measure_mono
        Set.inter_subset_left)).trans (hG.trans_le (winO_le_one (outEquiv k e) B Gm)))
    refine (ENNReal.add_le_add_iff_left hfin).1 ?_
    rw [hS, ← simLaw_eq_add_diff, hG, ← hS]
    exact hwin
  calc simLaw (outEquiv k e) B {p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2}
      = simLaw (outEquiv k e) B ({p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2} ∩ T) +
          simLaw (outEquiv k e) B ({p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2} \ T) :=
        simLaw_eq_add_diff ..
    _ ≤ β (b + V.kq) + 2 * esqrt (V.kq / Fintype.card (Out k e)) :=
        add_le_add hin ((MeasureTheory.measure_mono (Set.sdiff_subset_sdiff_left fun p hp =>
          acceptsAnswers_of_acceptsNotExtracts V claimOf hp)).trans hout)
    _ = V.knowledgeError β (b + V.kq) := add_comm _ _

/-! ### Pure algorithms: the state clause -/

section Pure

variable (o₀ : O) {t : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O))

/-- **The register of a pure algorithm at an outcome of the real run**: for a uniformly random
oracle `h`, the projector onto `𝒜^h` masked to the basis states whose output and verdict are
`vo`, averaged over `h`. -/
noncomputable def pureRealState (vo : VerifiedOutput O) :
    Matrix (QueryReg 𝒜.W 1 (Bits m) (XOut k e)) (QueryReg 𝒜.W 1 (Bits m) (XOut k e)) ℂ :=
  ∑ h : Bits m → XOut k e, ((Fintype.card (Bits m → XOut k e) : ℂ)⁻¹) •
    ketBra (mask {r | (⟨𝒜.out r.1, ∃ c ∈ 𝒜.out r.1,
        V.Accepted (outEquiv k e ∘ h) (claimOf c)⟩ : VerifiedOutput O) = vo} (𝒜.final h))

/-- **The extraction run leaves a pure algorithm's register in the real run's state** at every
value of the output and the verdict. -/
theorem pureExtractionState_eq (vo : VerifiedOutput O) :
    V.pureExtractionState claimOf (compressedSim) o₀ 𝒜 vo = pureRealState V claimOf 𝒜 vo := by
  have h2 := ExpandAdv.ptraceAlong_blockOn_realState (outEquiv k e)
    (V.expansionOpt claimOf o₀) 𝒜
    (P := fun τ => (⟨τ.out, V.AcceptsAnswers claimOf τ⟩ : VerifiedOutput O) = vo) (c := vo.out)
    fun τ hτ => congrArg VerifiedOutput.out hτ
  have h1 : reduce (simState (outEquiv k e) (V.expandedOpt claimOf o₀ 𝒜)) =
      (V.expandedOpt claimOf o₀ 𝒜).realState :=
    reduce_simState (outEquiv k e) (V.expandedOpt claimOf o₀ 𝒜)
  unfold NARG.QROM.Verifier.pureExtractionState
  rw [QROM.state_compressed]
  erw [h1]
  refine h2.trans ?_
  refine Finset.sum_congr rfl fun h _ => ?_
  have hset : {r : QueryReg 𝒜.W 1 (Bits m) (XOut k e) |
      (⟨((V.expansionOpt claimOf o₀).expand (k := V.kq) (outEquiv k e ∘ h) (𝒜.out r.1)).out,
        V.AcceptsAnswers claimOf ((V.expansionOpt claimOf o₀).expand
          (outEquiv k e ∘ h) (𝒜.out r.1))⟩ : VerifiedOutput O) = vo} =
      {r | (⟨𝒜.out r.1, ∃ c ∈ 𝒜.out r.1,
        V.Accepted (outEquiv k e ∘ h) (claimOf c)⟩ : VerifiedOutput O) = vo} := by
    ext r
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, acceptsAnswers_expand V claimOf _ (outEquiv k e ∘ h)]
    rfl
  rw [hset]

end Pure

/-! ### Core algorithms, with the auxiliary register unmeasured -/

/-- **The extraction run leaves `(output, Z)` in the real run's state** (DFMS22 Definition 3.1,
p. 10, first condition, with `εsim = 0` and a quantum auxiliary output). -/
theorem extractionOutputState_eq (A : Quantum.Alg (Bits m) (XOut k e) O) (o₀ : O)
    (vo : VerifiedOutput O) :
    V.extractionOutputState claimOf (compressedSim) A o₀ vo = V.realOutputState claimOf A vo := by
  unfold NARG.QROM.Verifier.extractionOutputState
  rw [pureExtractionState_eq V claimOf o₀ A.toQueryAlgCoh vo]
  unfold pureRealState
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun h _ => ?_)
  refine (map_smul _ _ _).trans ?_
  exact congrArg _ (A.pureToMixed_ketBra_mask_finalCoh
    (fun o => (⟨o, ∃ c ∈ o, V.Accepted (outEquiv k e ∘ h) (claimOf c)⟩ :
      VerifiedOutput O) = vo) h)

/-! ### Families of core algorithms: the knowledge-soundness bundle -/

section Family

variable {α : Type} (aux : PMF α) (A : α → Quantum.Alg (Bits m) (XOut k e) O) (o₀ : α → O)

/-- **The probability that the extractor returns a witness, in the coherent extraction run.** -/
noncomputable def cohExtracts (rel : Set (Stmt × Wit))
    (ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit) : ℝ≥0∞ :=
  ∑' a, aux a * simLaw (outEquiv k e) (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
    {p | ∃ c ∈ p.1.out, ExtractsAt rel ext (V.stmt (claimOf c)) p.2}

/-- **The compressed oracle's acceptance without extraction is the extraction run's** (`simLaw`),
for the extractor `ext` read on the register's database. -/
theorem cohAcceptsNotExtracts_compressed (rel : Set (Stmt × Wit))
    (ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit) :
    V.cohAcceptsNotExtracts claimOf aux A o₀ (compressedSim) rel (compressedExt ext) =
      ∑' a, aux a * simLaw (outEquiv k e) (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
        {p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2} := by
  refine tsum_congr fun a => congrArg _ ?_
  rw [← QROM.law_compressed, MeasureTheory.OuterMeasure.map_apply]
  rfl

/-- **The probability of an event of the output and the verdict in the coherent extraction
run.** -/
noncomputable def cohVerdictProb (T : Set (VerifiedOutput O)) : ℝ≥0∞ :=
  ∑' a, aux a * simLaw (outEquiv k e) (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
    {p | (⟨p.1.out, V.AcceptsAnswers claimOf p.1⟩ : VerifiedOutput O) ∈ T}

/-- **The coherent extraction run has the real run's law of output and verdict** (DFMS22
Definition 3.1, p. 10, first condition, with `εsim = 0`). -/
theorem cohVerdictProb_eq_real (T : Set (VerifiedOutput O)) :
    cohVerdictProb V claimOf aux A o₀ T =
      ∑' a, aux a * ((A a).realLaw (outEquiv k e)).toOuterMeasure
        {p | (⟨p.out, ∃ c ∈ p.out, V.Accepted p.oracle (claimOf c)⟩ : VerifiedOutput O) ∈ T} :=
  tsum_congr fun a => by rw [simLaw_verdict, Quantum.Alg.realLaw_toQueryAlgCoh]

/-- **Acceptance is at most extraction plus acceptance without extraction**, in the coherent
extraction run. -/
theorem cohVerdictProb_accepted_le (rel : Set (Stmt × Wit))
    (ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit) :
    cohVerdictProb V claimOf aux A o₀ {v | v.accepted} ≤
      cohExtracts V claimOf aux A o₀ rel ext +
        V.cohAcceptsNotExtracts claimOf aux A o₀ (compressedSim) rel (compressedExt ext) := by
  rw [cohVerdictProb, cohExtracts, cohAcceptsNotExtracts_compressed,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  gcongr
  refine (MeasureTheory.measure_mono fun p hp => ?_).trans (MeasureTheory.measure_union_le _ _)
  obtain ⟨c, hc, hg⟩ := hp
  by_cases hx : ExtractsAt rel ext (V.stmt (claimOf c)) p.2
  · exact Or.inl ⟨c, hc, hx⟩
  · exact Or.inr ⟨c, hc, hg, hx⟩

/-- **Online extractability for algorithms with per-branch query counts**: if the coherent pure
form of every `A a` queries at no more than `b a ≤ t` of its steps on every branch, the error is
`knowledgeError β (t + kq)`. -/
theorem cohOnlineExtracts_of_queryCount (K : V.KnowledgeBound rel ext β) {b : α → ℕ}
    (hA : ∀ a, QueryCount (outEquiv k e) (A a).toQueryAlgCoh (b a)) {t : ℕ} (hb : ∀ a, b a ≤ t) :
    V.CohOnlineExtracts claimOf aux A o₀ (compressedSim) rel (compressedExt ext) 0
      (V.knowledgeError β (t + V.kq)) := by
  refine .of_eq (fun a vo => extractionOutputState_eq V claimOf (A a) (o₀ a) vo) ?_
  rw [cohAcceptsNotExtracts_compressed]
  calc ∑' a, aux a * simLaw (outEquiv k e) (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
        {p | V.AcceptsNotExtracts claimOf rel ext p.1 p.2}
      ≤ ∑' a, aux a * V.knowledgeError β (t + V.kq) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
          ((simLaw_acceptsNotExtracts_le_of_queryCount V claimOf K (o₀ a) _ (hA a)).trans
            (V.knowledgeError_mono K.mono (Nat.add_le_add_right (hb a) V.kq))) zero_le
    _ = V.knowledgeError β (t + V.kq) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Family

/-! ### Query-bounded adversaries without proof queries -/

variable {t : ℕ}

/-- **Online extractability against a query-bounded adversary without proof queries** (DFMS22
Definition 3.1, p. 10, with the compressed oracle `compressedSim` at `εsim = 0`), its output read
as a claim by `claimOf`: error `knowledgeError β (t + kq)`. Non-termination is read as the default output for the verifier's
queries. -/
theorem cohOnlineExtracts_requestFree (K : V.KnowledgeBound rel ext β)
    (𝒢 : NARG.QROM.Adversary m k e O t) :
    V.CohOnlineExtracts claimOf 𝒢.aux 𝒢.run (fun a => (𝒢.run a).defaultOut) (compressedSim)
      rel (compressedExt ext) 0 (V.knowledgeError β (t + V.kq)) :=
  cohOnlineExtracts_of_queryCount V claimOf 𝒢.aux 𝒢.run _ K (𝒢.cohQueryCount (outEquiv k e))
    𝒢.queryCount_le

/-- **Online extractability against query-bounded adversaries** (DFMS22 Definition 3.1, p. 10,
with the compressed oracle `compressedSim` at `εsim = 0`): every `t`-query adversary of
`def:adversary` without proof queries with an auxiliary output is online extractable with error
`knowledgeError β (t + kq)`. -/
theorem onlineExtracts (K : V.KnowledgeBound rel ext β) {Z : Type}
    (𝒢 : NARG.QROM.Adversary m k e (Cl × Z) t) :
    𝒢.OnlineExtracts V (compressedSim) rel (compressedExt ext) 0
      (V.knowledgeError β (t + V.kq)) :=
  cohOnlineExtracts_requestFree V Prod.fst K 𝒢

/-- **Soundness against query-bounded adversaries** (CMS19 Theorem 8.6 (1), with the statement
chosen by the adversary): every `t`-query adversary without proof queries outputs a statement without a
witness and a claim the verifier accepts with probability at most `knowledgeError β (t + kq)`
(`NARG.QROM.Adversary.acceptsFalse_le` at the compressed oracle). -/
theorem soundness (K : V.KnowledgeBound rel ext β) (𝒜 : NARG.QROM.Adversary m k e Cl t) :
    𝒜.acceptsFalse V rel ≤ V.knowledgeError β (t + V.kq) := by
  simpa using NARG.QROM.Adversary.acceptsFalse_le (cohOnlineExtracts_requestFree V id K 𝒜)
