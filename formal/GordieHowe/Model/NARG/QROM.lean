-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.Verifier
public import GordieHowe.Model.NARG.Prover
public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.QROM.QueryBoundedRun
public import GordieHowe.Model.QROM.OutputStateCoh
public import GordieHowe.Model.QROM.QueryCountExpand
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedZK
public import GordieHowe.Model.NARG.Encoding
public import GordieHowe.Model.QROM.OracleSim
public import GordieHowe.Model.Quantum.Core.TraceDistance

@[expose] public section

/-!
# A non-interactive argument in the quantum random-oracle model

The notions of the paper's `def:narg-ks` and `def:narg-sound` for a verifier
(`GordieHowe.NARG.Verifier`) with oracle `{0,1}^m → Out k e`, against the query-bounded adversaries of
`def:adversary` without proof queries. The zero-knowledge notion of `def:narg-zk` is
`ZeroKnowledge`, in `GordieHowe/Model/Quantum/Interactive/QueryBoundedZK.lean`.

- `Verifier m k e Cl Stmt`: a verifier with oracle `Bits m → Out k e`.
- `NARG.Verifier.game V`: the base game of `V` (CMS19 Definition 8.1, p. 39), the tuples on whose
  answers the verifier accepts; in the extraction run the verifier's verdict is its decision on the
  answers it receives (`NARG.Verifier.expand_mem_game_iff`, CMS19 Proposition 8.11).
- `Adversary m k e O t`: the `t`-query adversaries of `def:adversary` without proof queries with
  output in `O` (a claim and the auxiliary output `Z` of `def:narg-ks` for knowledge soundness, a
  claim for soundness).
- `OracleSim m k e`, `compressedSim`: an oracle simulator (`QROM.OracleSim`) and CMS19's
  compressed oracle.
- `Adversary.OnlineExtracts V S rel ext εsim εks`: online extractability with a quantum auxiliary
  register, the oracle simulator `S` and the extractor `ext` reading its register (DFMS22
  Definition 3.1, p. 10), through the family-level `Verifier.CohOnlineExtracts`: trace distance
  `εsim` of the joint states (`Quantum.TraceDistLE`) and extraction error `εks`.
- `Adversary.acceptsFalse V rel`: the probability that the adversary outputs an accepted claim for a
  statement without a witness.
- `Verifier.KnowledgeBound`, `Verifier.knowledgeError`: CMS19 Proposition 8.12 for a database
  extractor and the lifted database bound, and the knowledge error `2√(kq/|Out|) + β b`.

The theorems that a knowledge bound gives online extractability and soundness are
`GordieHowe.SPBCS.QROM.onlineExtracts` and `GordieHowe.SPBCS.QROM.soundness`.
-/

namespace GordieHowe.NARG.QROM

open IOP GordieHowe.QROM
open GordieHowe.Quantum (QueryReg ketBra blockOn ptraceAlong mask reduce Outcome trace_blockOn
  sum_trace_blockOn_fiber trace_ptraceAlong re_blockOn_apply_self_nonneg
  re_ptraceAlong_apply_self_nonneg re_reduce_apply_self_nonneg ofReal_re_trace_blockOn_reduce)
open scoped NNReal ENNReal

/-- **A verifier in the quantum random-oracle model**: a verifier (`GordieHowe.NARG.Verifier`)
with oracle `{0,1}^m → Out k e`, on claims `Cl` with statements in `Stmt`. -/
abbrev Verifier (m k e : ℕ) (Cl Stmt : Type) : Type :=
  NARG.Verifier (Bits m) (Out k e) Cl Stmt

/-- **An oracle simulator for the oracle `{0,1}^m → Out k e`** (`QROM.OracleSim`, the interface `S`
of an online extractor, DFMS22 Definition 3.1, p. 10), on queries in `Bits m` with answers in
the group `XOut k e`. -/
abbrev OracleSim (m k e : ℕ) : Type 1 :=
  GordieHowe.QROM.OracleSim (Bits m) (XOut k e)

/-- **CMS19's compressed oracle** (`QROM.compressed`) for the oracle `{0,1}^m → Out k e`, answers
read through `outEquiv`. -/
noncomputable abbrev compressedSim {m k e : ℕ} : OracleSim m k e :=
  GordieHowe.QROM.compressed (m := m) (outEquiv k e)

/-- **A database extractor reading the compressed oracle's register**: `ext` on the database of
the register's slots (`slotsDB`). -/
def compressedExt {m k e : ℕ} {Stmt Wit : Type} (ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit) :
    ∀ t, Stmt → (compressedSim (m := m) (k := k) (e := e)).Reg t → Multiset Wit :=
  fun _ x s => ext x (slotsDB (outEquiv k e) s)

namespace Verifier

variable {m k e : ℕ} {Cl Stmt : Type} (V : Verifier m k e Cl Stmt)

/-- **The knowledge error** at the database bound `β` and `b` queries: `2√(kq/|Out|) + β b`. -/
noncomputable def knowledgeError (β : ℕ → ℝ≥0∞) (b : ℕ) : ℝ≥0∞ :=
  2 * esqrt (V.kq / Fintype.card (Out k e)) + β b

theorem knowledgeError_mono {β : ℕ → ℝ≥0∞} (hβ : Monotone β) {b b' : ℕ} (h : b ≤ b') :
    V.knowledgeError β b ≤ V.knowledgeError β b' :=
  add_le_add le_rfl (hβ h)

/-- **The knowledge bound of a database extractor** for the base game of the verifier (`game`): CMS19 Proposition 8.12
(p. 42, knowledge form p. 44) for `ext`, a database recording a winning tuple of the base game
extracts a witness for its statement or lies in the set `bad`; and the lifted database bound
(CMS19 Lemmas 5.9–5.10 with the instability of `bad`): an algorithm whose branches query at no
more than `b` of its steps measures a database in `bad` with probability at most `β b`, `β`
monotone. -/
structure KnowledgeBound {Wit : Type} (rel : Set (Stmt × Wit))
    (ext : Stmt → DB (Bits m) (Out k e) → Multiset Wit) (β : ℕ → ℝ≥0∞) where
  /-- The bad databases. -/
  bad : Set (DB (Bits m) (Out k e))
  /-- CMS19 Proposition 8.12. -/
  mem_of_game : ∀ o ∈ V.game, ∀ D, o.InDB D → ExtractsAt rel ext (V.stmt o.out) D ∨ D ∈ bad
  /-- The database bound. -/
  dbProb_le : ∀ {C : Type} {K t b : ℕ} (𝒜 : Adv (Bits m) (XOut k e) (Out k e) C K t),
    QueryCount (outEquiv k e) 𝒜 b → dbProb (outEquiv k e) 𝒜 bad ≤ β b
  /-- The bound grows with the query count. -/
  mono : Monotone β

/-! ### The extraction run -/

variable {O : Type} (claimOf : O → Cl)

/-- **The verifier's query expansion on an output that may be missing**: on `some o` the
expansion on `claimOf o`, on `none` the expansion on `claimOf o₀`. -/
def expansionOpt (o₀ : O) : Expansion (Bits m) (Out k e) (Option O) :=
  ⟨fun o ans => V.expansion.next (claimOf (o.getD o₀)) ans⟩

/-- **The algorithm of the extraction run** for a pure algorithm `𝒜` whose output may be
missing: `𝒜`, then the verifier's queries on the claim of its output, `t + kq` queries in all
(CMS19 Proposition 8.11, p. 42).

Running time: that of `𝒜`, then the verifier's `kq` queries on the claim of its output.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev expandedOpt (o₀ : O) {t : ℕ} (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O)) :
    Adv (Bits m) (XOut k e) (Out k e) (Option O) V.kq (t + V.kq) :=
  expandAdv (outEquiv k e) (V.expansionOpt claimOf o₀) V.kq 𝒜

/-- **The verifier accepts the claim of the output on the answers it received** (DFMS22's verdict
`v`, Definition 3.1, p. 10): the output is `some c` and the claim with the tuple's queries and
answers wins the base game. -/
def AcceptsAnswers (o : BaseGame.Tuple (Bits m) (Out k e) (Option O) V.kq) : Prop :=
  ∃ c ∈ o.out, (⟨o.queries, o.answers, claimOf c⟩ : BaseGame.Tuple (Bits m) (Out k e) Cl V.kq) ∈
    V.game

/-- **The accepted claim and the extraction failure** at the expanded output `o` and the state `D`
that the extractor reads (DFMS22 Definition 3.1, p. 10, `v = accept ∧ (inst, w) ∉ R`). -/
def AcceptsNotExtracts {Wit St : Type} (rel : Set (Stmt × Wit)) (ext : Stmt → St → Multiset Wit)
    (o : BaseGame.Tuple (Bits m) (Out k e) (Option O) V.kq) (D : St) : Prop :=
  ∃ c ∈ o.out, (⟨o.queries, o.answers, claimOf c⟩ : BaseGame.Tuple (Bits m) (Out k e) Cl V.kq) ∈
    V.game ∧ ¬ ExtractsAt rel ext (V.stmt (claimOf c)) D

/-- **The register of a pure algorithm at an outcome of its extraction run**: the expanded run (the
algorithm, then the verifier's queries) with its queries answered by the oracle simulator `S`, the
simulator's register traced out, its block on the outcomes whose output and verdict are `vo`, and
the verifier's registers traced out. -/
noncomputable def pureExtractionState (S : OracleSim m k e) (o₀ : O) {t : ℕ}
    (𝒜 : Quantum.QueryAlg (Bits m) (XOut k e) t (Option O)) (vo : VerifiedOutput O) :
    Matrix (QueryReg 𝒜.W 1 (Bits m) (XOut k e)) (QueryReg 𝒜.W 1 (Bits m) (XOut k e)) ℂ :=
  ptraceAlong (ExpandAdv.adversarySplit V.kq 𝒜.W)
    (blockOn {r | (⟨((V.expandedOpt claimOf o₀ 𝒜).out r.1).out,
        V.AcceptsAnswers claimOf ((V.expandedOpt claimOf o₀ 𝒜).out r.1)⟩ : VerifiedOutput O) = vo}
      (reduce (S.state (V.expandedOpt claimOf o₀ 𝒜))))

/-- **The state of `(output, Z)` at an outcome of the real run** (DFMS22 Definition 3.1, p. 10):
the block of the final state of `A` on the basis states whose output and verdict are `vo`, only
the output measured, averaged over a uniformly random oracle. -/
noncomputable def realOutputState (A : Quantum.Alg (Bits m) (XOut k e) O) (vo : VerifiedOutput O) :
    Matrix (QueryReg A.V 1 (Bits m) (XOut k e)) (QueryReg A.V 1 (Bits m) (XOut k e)) ℂ :=
  ∑ h : Bits m → XOut k e, ((Fintype.card (Bits m → XOut k e) : ℂ)⁻¹) •
    A.outputState h {r | (⟨some (A.out r.1), ∃ c ∈ some (A.out r.1),
      V.Accepted (outEquiv k e ∘ h) (claimOf c)⟩ : VerifiedOutput O) = vo}

/-- **The state of `(output, Z)` at an outcome of the extraction run** with the oracle simulator
`S`: the register of the coherent pure form `A.toQueryAlgCoh` in its extraction run, the dilation's
ancilla traced out. -/
noncomputable def extractionOutputState (S : OracleSim m k e) (A : Quantum.Alg (Bits m) (XOut k e) O)
    (o₀ : O) (vo : VerifiedOutput O) :
    Matrix (QueryReg A.V 1 (Bits m) (XOut k e)) (QueryReg A.V 1 (Bits m) (XOut k e)) ℂ :=
  A.pureToMixed (V.pureExtractionState claimOf S o₀ A.toQueryAlgCoh vo)

/-! ### Online extractability of a family of core algorithms -/

section Family

variable {Wit : Type} {α : Type} (aux : PMF α) (A : α → Quantum.Alg (Bits m) (XOut k e) O)
  (o₀ : α → O)

variable (S : OracleSim m k e)

/-- **The probability that the verifier accepts and extraction fails, in the coherent extraction
run** with the oracle simulator `S`, of a family of core algorithms over auxiliary inputs
`a ← aux`; the extractor `ext` reads the simulator's register. -/
noncomputable def cohAcceptsNotExtracts (rel : Set (Stmt × Wit))
    (ext : ∀ t, Stmt → S.Reg t → Multiset Wit) : ℝ≥0∞ :=
  ∑' a, aux a * S.law (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
    {p | V.AcceptsNotExtracts claimOf rel (ext _) p.1 p.2}

/-- **Online extractability with a quantum auxiliary register** (the paper's `def:narg-ks`; DFMS22
Definition 3.1, p. 10), for a family of core algorithms over auxiliary inputs, with the oracle
simulator `S` and the extractor `ext` reading its register: the joint states of `(output, Z,
verdict)` in the coherent extraction run and in the real run are within trace distance `δ a` at
every auxiliary input, with `Σ_a aux a · δ a ≤ εsim` (`traceDist_le`); and the verifier accepts
while extraction fails with probability at most `εks` (`acceptsNotExtracts_le`).

The work register of an algorithm, which holds `Z`, has a type that depends on its auxiliary
input, so the joint state over the auxiliary input is block diagonal in it, and `traceDist_le`
bounds the trace distance with the auxiliary input as a classical label. That bound can be
stronger than the paper's, whose trace distance hides the auxiliary input. Soundness
(`CohOnlineExtracts.acceptsFalse_le`) uses only the consequence `OutcomeDistLE`, a measurement
of the output and the verdict that does not depend on the auxiliary input, which the paper's
trace distance also implies. -/
structure CohOnlineExtracts (rel : Set (Stmt × Wit)) (ext : ∀ t, Stmt → S.Reg t → Multiset Wit)
    (εsim : ℝ≥0) (εks : ℝ≥0∞) : Prop where
  /-- The joint states of `(output, Z, verdict)` are within trace distance `εsim`, on average over
  the auxiliary input. -/
  traceDist_le : ∃ δ : α → ℝ≥0, (∀ a, Quantum.TraceDistLE
      (V.extractionOutputState claimOf S (A a) (o₀ a)) (V.realOutputState claimOf (A a)) (δ a)) ∧
    ∑' a, aux a * (δ a : ℝ≥0∞) ≤ εsim
  /-- Acceptance with failed extraction has probability at most `εks`. -/
  acceptsNotExtracts_le : V.cohAcceptsNotExtracts claimOf aux A o₀ S rel ext ≤ εks

variable {V claimOf aux A o₀ S} in
/-- Online extractability at an error holds at every larger error. -/
theorem CohOnlineExtracts.mono {rel : Set (Stmt × Wit)} {ext : ∀ t, Stmt → S.Reg t → Multiset Wit}
    {εsim εsim' : ℝ≥0} {εks εks' : ℝ≥0∞}
    (h : V.CohOnlineExtracts claimOf aux A o₀ S rel ext εsim εks) (hsim : εsim ≤ εsim')
    (hks : εks ≤ εks') : V.CohOnlineExtracts claimOf aux A o₀ S rel ext εsim' εks' := by
  obtain ⟨δ, hδ, hsum⟩ := h.traceDist_le
  exact ⟨⟨δ, hδ, hsum.trans (by exact_mod_cast hsim)⟩, h.acceptsNotExtracts_le.trans hks⟩

variable {V claimOf aux A o₀ S} in
/-- **Equal joint states are at simulation error `0`.** -/
theorem CohOnlineExtracts.of_eq {rel : Set (Stmt × Wit)} {ext : ∀ t, Stmt → S.Reg t → Multiset Wit}
    {εks : ℝ≥0∞}
    (heq : ∀ a vo, V.extractionOutputState claimOf S (A a) (o₀ a) vo = V.realOutputState claimOf (A a) vo)
    (hks : V.cohAcceptsNotExtracts claimOf aux A o₀ S rel ext ≤ εks) :
    V.CohOnlineExtracts claimOf aux A o₀ S rel ext 0 εks :=
  ⟨⟨0, fun a => Quantum.TraceDistLE.of_eq (funext (heq a)), by simp⟩, hks⟩

end Family

/-! ### Weights of the joint states -/

/-- **The extraction run's states of `(output, Z)` weigh at most the simulated run's law** on every
finite set of outcomes: the trace of the state at an outcome is the probability of the outcome in
the simulated run, less the weight the pure form leaves outside the core algorithm's run. -/
theorem ofReal_sum_re_trace_extractionOutputState_le (S : OracleSim m k e)
    (A : Quantum.Alg (Bits m) (XOut k e) O) (o₀ : O) (s : Finset (VerifiedOutput O)) :
    ENNReal.ofReal (∑ vo ∈ s, (V.extractionOutputState claimOf S A o₀ vo).trace.re) ≤
      S.law (V.expandedOpt claimOf o₀ A.toQueryAlgCoh)
        {p | (⟨p.1.out, V.AcceptsAnswers claimOf p.1⟩ : VerifiedOutput O) ∈ s} := by
  set B := V.expandedOpt claimOf o₀ A.toQueryAlgCoh
  set f : QueryReg B.W 1 (Bits m) (XOut k e) → VerifiedOutput O :=
    fun r => ⟨(B.out r.1).out, V.AcceptsAnswers claimOf (B.out r.1)⟩
  have hd : ∀ (T : Set (QueryReg B.W 1 (Bits m) (XOut k e))) i,
      0 ≤ (blockOn T (reduce (S.state B)) i i).re := fun T =>
    re_blockOn_apply_self_nonneg T (re_reduce_apply_self_nonneg _)
  calc ENNReal.ofReal (∑ vo ∈ s, (V.extractionOutputState claimOf S A o₀ vo).trace.re)
      ≤ ENNReal.ofReal (∑ vo ∈ s, (blockOn {r | f r = vo} (reduce (S.state B))).trace.re) := by
        refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun vo _ => ?_)
        refine (A.re_trace_pureToMixed_le
          (M := V.pureExtractionState claimOf S o₀ A.toQueryAlgCoh vo)
          (re_ptraceAlong_apply_self_nonneg _ (hd _))).trans ?_
        exact (congrArg Complex.re (trace_ptraceAlong _ _)).le
    _ = ENNReal.ofReal (blockOn {r | f r ∈ s} (reduce (S.state B))).trace.re := by
        rw [← Complex.re_sum, sum_trace_blockOn_fiber]
    _ = _ := by
        rw [ofReal_re_trace_blockOn_reduce, OracleSim.law, MeasureTheory.OuterMeasure.map_apply]
        rfl

open scoped ComplexOrder in
/-- **The real run's states of `(output, Z)` carry the real law**: for every set `E` of outcomes
there is a finite set of outcomes in `E` (those the run can reach) whose states weigh, in trace,
the probability that `A` terminates with an outcome in `E`. -/
theorem exists_ofReal_sum_re_trace_realOutputState (A : Quantum.Alg (Bits m) (XOut k e) O)
    (E : Set (VerifiedOutput O)) :
    ∃ s : Finset (VerifiedOutput O), (∀ vo ∈ s, vo ∈ E) ∧
      ENNReal.ofReal (∑ vo ∈ s, (V.realOutputState claimOf A vo).trace.re) =
        (A.realLaw (outEquiv k e)).toOuterMeasure {p | ∃ c, p.out = some c ∧
          (⟨some c, ∃ c' ∈ some c, V.Accepted p.oracle (claimOf c')⟩ : VerifiedOutput O) ∈ E} := by
  classical
  let g : (Bits m → XOut k e) → QueryReg A.V 1 (Bits m) (XOut k e) → VerifiedOutput O :=
    fun h r => ⟨some (A.out r.1), ∃ c ∈ some (A.out r.1), V.Accepted (outEquiv k e ∘ h) (claimOf c)⟩
  let s : Finset (VerifiedOutput O) := (Finset.univ.image
    fun q : (Bits m → XOut k e) × QueryReg A.V 1 (Bits m) (XOut k e) => g q.1 q.2).filter (· ∈ E)
  refine ⟨s, fun vo hvo => (Finset.mem_filter.1 hvo).2, ?_⟩
  have hs : ∀ h r, g h r ∈ s ↔ g h r ∈ E := fun h r => by
    simp only [s, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact and_iff_right ⟨(h, r), rfl⟩
  have hc : ((Fintype.card (Bits m → XOut k e) : ℂ)⁻¹) =
      (((Fintype.card (Bits m → XOut k e) : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hd : ∀ h i, 0 ≤ (A.final h i i).re := fun h i =>
    (Complex.nonneg_iff.1 ((A.posSemidef_stage h _).diag_nonneg (i := i))).1
  have hsum : ∑ vo ∈ s, (V.realOutputState claimOf A vo).trace.re =
      ∑ h, (Fintype.card (Bits m → XOut k e) : ℝ)⁻¹ *
        ∑ r, {r | g h r ∈ E}.indicator (fun r => (A.final h r r).re) r := by
    have h1 : ∀ vo, (V.realOutputState claimOf A vo).trace.re =
        ∑ h, (Fintype.card (Bits m → XOut k e) : ℝ)⁻¹ *
          (blockOn {r | g h r = vo} (A.final h)).trace.re := fun vo => by
      rw [realOutputState, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Matrix.trace_smul, smul_eq_mul, hc, Complex.re_ofReal_mul]
      rfl
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_trace_blockOn_fiber (g h), trace_blockOn,
      Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : g h r ∈ E
    · rw [Set.indicator_of_mem (s := {i | g h i ∈ s}) ((hs h r).2 hr),
        Set.indicator_of_mem (s := {r | g h r ∈ E}) hr]
    · rw [Set.indicator_of_notMem (s := {i | g h i ∈ s}) (mt (hs h r).1 hr),
        Set.indicator_of_notMem (s := {r | g h r ∈ E}) hr, Complex.zero_re]
  rw [hsum, Quantum.Alg.toOuterMeasure_realLaw_out A (outEquiv k e)
      (fun c o => (⟨some c, ∃ c' ∈ some c, V.Accepted o (claimOf c')⟩ : VerifiedOutput O) ∈ E),
    tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg fun h _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun r _ => Set.indicator_nonneg (fun r _ => hd h r) r)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
      fun r _ => Set.indicator_nonneg (fun r _ => hd h r) r, PMF.uniformOfFintype_apply,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : g h r ∈ E
  · rw [Set.indicator_of_mem (s := {r | g h r ∈ E}) hr]
    exact (Set.indicator_of_mem (show r ∈ {i | g h i ∈ E} from hr)
      (fun i => ENNReal.ofReal (A.final h i i).re)).symm
  · rw [Set.indicator_of_notMem (s := {r | g h r ∈ E}) hr, ENNReal.ofReal_zero]
    exact (Set.indicator_of_notMem (show r ∉ {i | g h i ∈ E} from hr)
      (fun i => ENNReal.ofReal (A.final h i i).re)).symm

open scoped ComplexOrder in
/-- The real run's state of `(output, Z)` at an outcome has a nonnegative trace. -/
theorem re_trace_realOutputState_nonneg (A : Quantum.Alg (Bits m) (XOut k e) O)
    (vo : VerifiedOutput O) : 0 ≤ (V.realOutputState claimOf A vo).trace.re := by
  classical
  rw [realOutputState, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun h _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, Quantum.Alg.outputState, trace_blockOn]
  have hc : ((Fintype.card (Bits m → XOut k e) : ℂ)⁻¹) =
      (((Fintype.card (Bits m → XOut k e) : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  rw [Set.indicator_apply]
  split_ifs
  · exact (Complex.nonneg_iff.1 ((A.posSemidef_stage h _).diag_nonneg (i := i))).1
  · simp

/-- The extraction run's state of `(output, Z)` at an outcome has a nonnegative trace. -/
theorem re_trace_extractionOutputState_nonneg (S : OracleSim m k e)
    (A : Quantum.Alg (Bits m) (XOut k e) O) (o₀ : O) (vo : VerifiedOutput O) :
    0 ≤ (V.extractionOutputState claimOf S A o₀ vo).trace.re := by
  unfold extractionOutputState Quantum.Alg.pureToMixed
  change 0 ≤ (Quantum.KrausMap.ffBlock (ptraceAlong _ _)).trace.re
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => re_ptraceAlong_apply_self_nonneg _
    (re_ptraceAlong_apply_self_nonneg _ (re_blockOn_apply_self_nonneg _
      (re_reduce_apply_self_nonneg _))) (i, false)

/-! ### Knowledge soundness implies soundness -/

section Family

variable {Wit : Type} {α : Type} (aux : PMF α) (A : α → Quantum.Alg (Bits m) (XOut k e) O)
  (o₀ : α → O) (S : OracleSim m k e)

/-- **The weight of the real run's states of `(output, Z)` on a set `T` of outcomes**: the sum of
their traces, the probability that measuring the output and the verdict gives an outcome in
`T`. -/
noncomputable def realWeight (A : Quantum.Alg (Bits m) (XOut k e) O) (T : Set (VerifiedOutput O)) :
    ℝ≥0∞ :=
  ∑' vo, T.indicator (fun vo => ENNReal.ofReal (V.realOutputState claimOf A vo).trace.re) vo

/-- **The weight of the extraction run's states of `(output, Z)` on a set `T` of outcomes.** -/
noncomputable def extractionWeight (A : Quantum.Alg (Bits m) (XOut k e) O) (o₀ : O)
    (T : Set (VerifiedOutput O)) : ℝ≥0∞ :=
  ∑' vo, T.indicator
    (fun vo => ENNReal.ofReal (V.extractionOutputState claimOf S A o₀ vo).trace.re) vo

/-- **The output and the verdict of the real run are at most `ε` more likely in every set than in
the extraction run**, with the auxiliary input hidden: the measurement of the outcome alone, which
acts on the registers the paper's `def:narg-ks` exposes and does not depend on the auxiliary
input. A trace distance at most `ε` of the joint states with the auxiliary input hidden implies
it. -/
def OutcomeDistLE (ε : ℝ≥0) : Prop :=
  ∀ T : Set (VerifiedOutput O), ∑' a, aux a * V.realWeight claimOf (A a) T ≤
    ∑' a, aux a * V.extractionWeight claimOf S (A a) (o₀ a) T + ε

variable {V claimOf aux A o₀ S}

/-- **The trace-distance clause implies the bound on outcomes.** -/
theorem CohOnlineExtracts.outcomeDistLE {rel : Set (Stmt × Wit)}
    {ext : ∀ t, Stmt → S.Reg t → Multiset Wit} {εsim : ℝ≥0} {εks : ℝ≥0∞}
    (h : V.CohOnlineExtracts claimOf aux A o₀ S rel ext εsim εks) :
    V.OutcomeDistLE claimOf aux A o₀ S εsim := by
  classical
  intro T
  obtain ⟨δ, hδ, hsum⟩ := h.traceDist_le
  have hext0 := fun a vo => V.re_trace_extractionOutputState_nonneg claimOf S (A a) (o₀ a) vo
  have hreal0 := fun a vo => V.re_trace_realOutputState_nonneg claimOf (A a) vo
  have hper : ∀ a, V.realWeight claimOf (A a) T ≤
      V.extractionWeight claimOf S (A a) (o₀ a) T + δ a := fun a => by
    rw [realWeight, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have hs := (hδ a).sum_re_trace_le (s.filter (· ∈ T))
    calc ∑ vo ∈ s, T.indicator
          (fun vo => ENNReal.ofReal (V.realOutputState claimOf (A a) vo).trace.re) vo
        = ENNReal.ofReal (∑ vo ∈ s.filter (· ∈ T), (V.realOutputState claimOf (A a) vo).trace.re) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun vo _ => hreal0 a vo, Finset.sum_filter]
          exact Finset.sum_congr rfl fun vo _ => Set.indicator_apply _ _ _
      _ ≤ ENNReal.ofReal (∑ vo ∈ s.filter (· ∈ T),
            (V.extractionOutputState claimOf S (A a) (o₀ a) vo).trace.re + δ a) :=
          ENNReal.ofReal_le_ofReal hs
      _ ≤ ENNReal.ofReal (∑ vo ∈ s.filter (· ∈ T),
            (V.extractionOutputState claimOf S (A a) (o₀ a) vo).trace.re) + δ a := by
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ V.extractionWeight claimOf S (A a) (o₀ a) T + δ a := by
          refine add_le_add_left ?_ _
          rw [ENNReal.ofReal_sum_of_nonneg fun vo _ => hext0 a vo, Finset.sum_filter]
          exact (Finset.sum_le_sum fun vo _ => by split_ifs <;> simp_all).trans
            (ENNReal.sum_le_tsum _)
  calc ∑' a, aux a * V.realWeight claimOf (A a) T
      ≤ ∑' a, aux a * (V.extractionWeight claimOf S (A a) (o₀ a) T + δ a) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hper a) _
    _ = ∑' a, aux a * V.extractionWeight claimOf S (A a) (o₀ a) T + ∑' a, aux a * (δ a : ℝ≥0∞) := by
        simp_rw [mul_add]
        exact ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl hsum

/-- **Knowledge soundness implies soundness** (the paper's `lem:ks-sound`, in the QROM), from the
bound on outcomes (`OutcomeDistLE`, implied by the paper's trace distance with the auxiliary input
hidden) and acceptance without extraction: a family of core algorithms outputs a claim for a
statement without a witness that the verifier accepts with probability at most `εsim + εks`. In
the extraction run such an outcome is acceptance without extraction, since no witness of the
statement exists. -/
theorem acceptsFalse_le_of_outcomeDistLE {rel : Set (Stmt × Wit)}
    {ext : ∀ t, Stmt → S.Reg t → Multiset Wit} {εsim : ℝ≥0} {εks : ℝ≥0∞}
    (hsim : V.OutcomeDistLE claimOf aux A o₀ S εsim)
    (hks : V.cohAcceptsNotExtracts claimOf aux A o₀ S rel ext ≤ εks) :
    ∑' a, aux a * ((A a).realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ c ∈ p.out, (∀ w, (V.stmt (claimOf c), w) ∉ rel) ∧ V.Accepted p.oracle (claimOf c)} ≤
      εsim + εks := by
  classical
  let E : Set (VerifiedOutput O) :=
    {vo | vo.accepted ∧ ∃ c ∈ vo.out, ∀ w, (V.stmt (claimOf c), w) ∉ rel}
  have hreal : ∀ a, ((A a).realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ c ∈ p.out, (∀ w, (V.stmt (claimOf c), w) ∉ rel) ∧ V.Accepted p.oracle (claimOf c)} ≤
      V.realWeight claimOf (A a) E := by
    intro a
    obtain ⟨s, hsE, hs⟩ := V.exists_ofReal_sum_re_trace_realOutputState claimOf (A a) E
    have hset : {p : Outcome (Option O) (Bits m) (Out k e) | ∃ c ∈ p.out,
        (∀ w, (V.stmt (claimOf c), w) ∉ rel) ∧ V.Accepted p.oracle (claimOf c)} =
        {p | ∃ c, p.out = some c ∧
          (⟨some c, ∃ c' ∈ some c, V.Accepted p.oracle (claimOf c')⟩ : VerifiedOutput O) ∈ E} := by
      ext p
      constructor
      · rintro ⟨c, hc, hf, ha⟩
        exact ⟨c, hc, ⟨c, rfl, ha⟩, c, rfl, hf⟩
      · rintro ⟨c, hc, ⟨c₁, hc₁, ha⟩, c₂, hc₂, hf⟩
        simp only [Option.mem_def, Option.some.injEq] at hc₁ hc₂
        subst hc₁ hc₂
        exact ⟨c, hc, hf, ha⟩
    rw [hset, ← hs, ENNReal.ofReal_sum_of_nonneg fun vo _ => V.re_trace_realOutputState_nonneg claimOf _ vo]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun vo hvo => ?_)) (ENNReal.sum_le_tsum s)
    rw [Set.indicator_of_mem (hsE vo hvo)]
  have hext : ∀ a, V.extractionWeight claimOf S (A a) (o₀ a) E ≤
      S.law (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
        {p | V.AcceptsNotExtracts claimOf rel (ext _) p.1 p.2} := by
    intro a
    rw [extractionWeight, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    calc ∑ vo ∈ s, E.indicator (fun vo => ENNReal.ofReal
            (V.extractionOutputState claimOf S (A a) (o₀ a) vo).trace.re) vo
        = ENNReal.ofReal (∑ vo ∈ s.filter (· ∈ E),
            (V.extractionOutputState claimOf S (A a) (o₀ a) vo).trace.re) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            fun vo _ => V.re_trace_extractionOutputState_nonneg claimOf S _ _ vo, Finset.sum_filter]
          exact Finset.sum_congr rfl fun vo _ => Set.indicator_apply _ _ _
      _ ≤ S.law (V.expandedOpt claimOf (o₀ a) (A a).toQueryAlgCoh)
            {p | (⟨p.1.out, V.AcceptsAnswers claimOf p.1⟩ : VerifiedOutput O) ∈ s.filter (· ∈ E)} :=
          V.ofReal_sum_re_trace_extractionOutputState_le claimOf S (A a) (o₀ a) _
      _ ≤ _ := by
          refine MeasureTheory.measure_mono fun p hp => ?_
          obtain ⟨⟨c, hc, hg⟩, c', hc', hf⟩ := (Finset.mem_filter.1 hp).2
          obtain rfl : c' = c := Option.mem_unique hc' hc
          exact ⟨c', hc, hg, fun ⟨w, _, hw⟩ => hf w hw⟩
  calc _ ≤ ∑' a, aux a * V.realWeight claimOf (A a) E :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hreal a) _
    _ ≤ ∑' a, aux a * V.extractionWeight claimOf S (A a) (o₀ a) E + εsim := hsim E
    _ ≤ V.cohAcceptsNotExtracts claimOf aux A o₀ S rel ext + εsim :=
        add_le_add_left (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hext a) _) _
    _ ≤ εsim + εks := by
        rw [add_comm]
        exact add_le_add le_rfl hks

/-- **Knowledge soundness implies soundness** (the paper's `lem:ks-sound`, in the QROM) for online
extractability (`acceptsFalse_le_of_outcomeDistLE` through `CohOnlineExtracts.outcomeDistLE`). -/
theorem CohOnlineExtracts.acceptsFalse_le {rel : Set (Stmt × Wit)}
    {ext : ∀ t, Stmt → S.Reg t → Multiset Wit} {εsim : ℝ≥0} {εks : ℝ≥0∞}
    (h : V.CohOnlineExtracts claimOf aux A o₀ S rel ext εsim εks) :
    ∑' a, aux a * ((A a).realLaw (outEquiv k e)).toOuterMeasure
      {p | ∃ c ∈ p.out, (∀ w, (V.stmt (claimOf c), w) ∉ rel) ∧ V.Accepted p.oracle (claimOf c)} ≤
      εsim + εks :=
  acceptsFalse_le_of_outcomeDistLE h.outcomeDistLE h.acceptsNotExtracts_le

end Family

end Verifier

/-! ### Query-bounded adversaries without proof queries -/

/-- **The `t`-query adversaries of `def:adversary` without proof queries, with output in `O`**
(`Quantum.QueryBoundedAdversary` with a one-element type of proof queries and no responses):
auxiliary input independent of the oracle, the kind of each slot chosen at run time, channels as
steps, at most `t` queries on every branch, output in `O`. For knowledge soundness `O` is a claim
and the auxiliary output `Z` of `def:narg-ks`; for soundness it is a claim. -/
abbrev Adversary (m k e : ℕ) (O : Type) (t : ℕ) : Type 1 :=
  Quantum.QueryBoundedAdversary (Bits m) (XOut k e) Unit Empty O t

namespace Adversary

variable {m k e : ℕ} {Cl Stmt : Type} {t : ℕ}

/-- **Online extractability of `𝒢` with a quantum auxiliary register** (the paper's `def:narg-ks`;
DFMS22 Definition 3.1, p. 10) for the verifier `V`, with the oracle simulator `S` and the extractor
`ext` reading its register: `CohOnlineExtracts` for the real runs of `𝒢`, its claim the first
component of its output, with non-termination read as their default output for the verifier's
queries. -/
abbrev OnlineExtracts {Z : Type} (𝒢 : Adversary m k e (Cl × Z) t) (V : Verifier m k e Cl Stmt)
    (S : OracleSim m k e) {Wit : Type} (rel : Set (Stmt × Wit))
    (ext : ∀ t, Stmt → S.Reg t → Multiset Wit) (εsim : ℝ≥0) (εks : ℝ≥0∞) : Prop :=
  V.CohOnlineExtracts Prod.fst 𝒢.aux 𝒢.run (fun a => (𝒢.run a).defaultOut) S rel ext εsim εks

/-- Online extractability at an error holds at every larger error. -/
theorem OnlineExtracts.mono {Z : Type} {𝒢 : Adversary m k e (Cl × Z) t}
    {V : Verifier m k e Cl Stmt} {S : OracleSim m k e} {Wit : Type} {rel : Set (Stmt × Wit)}
    {ext : ∀ t, Stmt → S.Reg t → Multiset Wit} {εsim εsim' : ℝ≥0} {εks εks' : ℝ≥0∞}
    (h : 𝒢.OnlineExtracts V S rel ext εsim εks) (hsim : εsim ≤ εsim') (hks : εks ≤ εks') :
    𝒢.OnlineExtracts V S rel ext εsim' εks' :=
  Verifier.CohOnlineExtracts.mono h hsim hks

/-- **The probability that `𝒜` outputs a claim that `V` accepts for a statement without a
witness**: the auxiliary input drawn, the real run of `𝒜` against a uniformly random oracle `h`,
its output a claim whose statement has no witness in `rel` and which the verifier accepts with
`h`. -/
noncomputable def acceptsFalse (𝒜 : Adversary m k e Cl t) (V : Verifier m k e Cl Stmt) {Wit : Type}
    (rel : Set (Stmt × Wit)) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * ((𝒜.run a).realLaw (outEquiv k e)).toOuterMeasure
    {p | ∃ c ∈ p.out, (∀ w, (V.stmt c, w) ∉ rel) ∧ V.Accepted p.oracle c}

/-- **Knowledge soundness implies soundness** (the paper's `lem:ks-sound`, in the QROM): if the
claims of `𝒜` are online extractable with the oracle simulator `S` at errors `εsim` and `εks`,
then `𝒜` outputs an accepted claim for a statement without a witness with probability at most
`εsim + εks` (`Verifier.CohOnlineExtracts.acceptsFalse_le`). -/
theorem acceptsFalse_le {𝒜 : Adversary m k e Cl t} {V : Verifier m k e Cl Stmt}
    {S : OracleSim m k e} {Wit : Type} {rel : Set (Stmt × Wit)}
    {ext : ∀ t, Stmt → S.Reg t → Multiset Wit} {εsim : ℝ≥0} {εks : ℝ≥0∞}
    (h : V.CohOnlineExtracts id 𝒜.aux 𝒜.run (fun a => (𝒜.run a).defaultOut) S rel ext εsim εks) :
    𝒜.acceptsFalse V rel ≤ εsim + εks :=
  h.acceptsFalse_le

/-- **Within the budget, the state of `(output, Z)` in the real run is the model's**: a
query-bounded adversary never asks for a query slot over its budget on a branch of positive weight
(`Quantum.QueryBoundedAdversary.withinBudget`), so its real run (`AdaptiveIAlg.tpRun`) and the
model's run (`AdaptiveIAlg.compose`) have the same final states
(`AdaptiveIAlg.WithinBudget.final_compose_eq`). -/
theorem realOutputState_eq_model {Z : Type} (V : Verifier m k e Cl Stmt)
    (𝒢 : Adversary m k e (Cl × Z) t) (a : 𝒢.Aux) (vo : VerifiedOutput (Cl × Z)) :
    V.realOutputState Prod.fst (𝒢.run a) vo = V.realOutputState Prod.fst (𝒢.modelRun a) vo := by
  unfold Verifier.realOutputState Quantum.Alg.outputState
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [(𝒢.withinBudget a).final_compose_eq]
  rfl

end Adversary

/-! ### Completeness -/

/-- **The probability that the honest proof of the adversary's pair is rejected** (Unruh 2017
Definition 5, p. 14, in the quantum random-oracle model): over the auxiliary input of `𝒜`, the
honest prover's coins and the real run of `𝒜` against a uniformly random oracle `h`, the adversary
outputs a pair `(x, w)` in `rel`, and the verifier rejects the claim `claim x π` of the proof `π`
that the program `P` computes on `(x, w)` against `h` with its queries encoded by `enc`
(`Prover.encode`, run classically on the measured oracle). -/
noncomputable def Adversary.rejectsHonest {m k e : ℕ} {A Cl Stmt Wit Proof Coins : Type} {t : ℕ}
    (𝒜 : Adversary m k e (ProofQuery Stmt Wit) t)
    (enc : OracleEncoding A (Out k e) (Bits m) (XOut k e))
    (P : NARG.Prover A (Out k e) Stmt Wit Proof Coins) (V : Verifier m k e Cl Stmt)
    (claim : Stmt → Proof → Cl) (rel : Stmt → Wit → Prop) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * ∑' c, P.coins c * ((𝒜.run a).realLaw (outEquiv k e)).toOuterMeasure
    {p | ∃ o ∈ p.out, rel o.stmt o.wit ∧
      ¬ V.Accepted p.oracle (claim o.stmt
        ((P.encode enc).toFn.prove ((outEquiv k e).symm ∘ p.oracle) o.stmt o.wit c))}

/-- **Completeness in the quantum random-oracle model** (the paper's `def:narg-complete`, Unruh
2017 Definition 5, p. 14, with the pair chosen by the adversary after its queries): every
`t`-query adversary of `def:adversary` without proof queries that outputs a statement and a witness
makes the honest proof of a pair in `rel` rejected with probability at most `ε t`
(`Adversary.rejectsHonest`). -/
def Complete {m k e : ℕ} {A Cl Stmt Wit Proof Coins : Type}
    (enc : OracleEncoding A (Out k e) (Bits m) (XOut k e))
    (P : NARG.Prover A (Out k e) Stmt Wit Proof Coins) (V : Verifier m k e Cl Stmt)
    (claim : Stmt → Proof → Cl) (rel : Stmt → Wit → Prop) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (t : ℕ) (𝒜 : Adversary m k e (ProofQuery Stmt Wit) t), 𝒜.rejectsHonest enc P V claim rel ≤ ε t

/-! ### Zero knowledge -/

section ZeroKnowledge

variable {m k e : ℕ} {A Stmt Wit Proof Coins SimCoins : Type} (rel : Stmt → Wit → Prop)
  [DecidableRel rel] [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] [Fintype Coins] [DecidableEq Coins] [Fintype SimCoins]
  [DecidableEq SimCoins]

/-- **Zero knowledge in the quantum random-oracle model** (the paper's `def:narg-zk`, Unruh 2017
Definition 6, p. 14, over the paper's `(t, Q)`-adversaries, `def:adversary`, all of whose queries
are counted): the programs `P` and `S` run query by query in the experiment with their queries
encoded by `enc` (`Prover.encode`, `Simulator.encode`); a valid proof query is answered in the
finite proof-query register by the prover's proof, or by the simulator's optional proof (`none`
where the simulator fails) (`GordieHowe.QROM.ZeroKnowledge`). -/
def ZeroKnowledge (enc : OracleEncoding A (Out k e) (Bits m) (XOut k e))
    (P : NARG.Prover A (Out k e) Stmt Wit Proof Coins)
    (S : NARG.Simulator A (Out k e) Stmt (Option Proof) SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  GordieHowe.QROM.ZeroKnowledge rel ((P.mapOutput some).encode enc) (S.encode enc) ε

/-- **Everlasting zero knowledge in the quantum random-oracle model** (the paper's
`def:narg-zk-post`): as `ZeroKnowledge`, against adversaries with at most `t` queries before their
last proof query and any number after it (`GordieHowe.QROM.EverlastingZeroKnowledge`). -/
def EverlastingZeroKnowledge (enc : OracleEncoding A (Out k e) (Bits m) (XOut k e))
    (P : NARG.Prover A (Out k e) Stmt Wit Proof Coins)
    (S : NARG.Simulator A (Out k e) Stmt (Option Proof) SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  GordieHowe.QROM.EverlastingZeroKnowledge rel ((P.mapOutput some).encode enc) (S.encode enc) ε

variable {rel}

/-- Everlasting zero knowledge gives zero knowledge at the same error. -/
theorem EverlastingZeroKnowledge.zeroKnowledge
    {enc : OracleEncoding A (Out k e) (Bits m) (XOut k e)}
    {P : NARG.Prover A (Out k e) Stmt Wit Proof Coins}
    {S : NARG.Simulator A (Out k e) Stmt (Option Proof) SimCoins} {ε : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledge rel enc P S ε) : ZeroKnowledge rel enc P S ε :=
  GordieHowe.QROM.EverlastingZeroKnowledge.zeroKnowledge h

/-- A larger error bound. -/
theorem ZeroKnowledge.mono {enc : OracleEncoding A (Out k e) (Bits m) (XOut k e)}
    {P : NARG.Prover A (Out k e) Stmt Wit Proof Coins}
    {S : NARG.Simulator A (Out k e) Stmt (Option Proof) SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : ZeroKnowledge rel enc P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    ZeroKnowledge rel enc P S ε' :=
  GordieHowe.QROM.ZeroKnowledge.mono h hε

end ZeroKnowledge

end GordieHowe.NARG.QROM
