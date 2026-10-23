-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.Verifier
public import GordieHowe.Model.NARG.Prover
public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.ROM.Interactive
public import GordieHowe.Model.ROM.Lazy
public import GordieHowe.Model.ROM.Encode
public import GordieHowe.Model.NARG.Simulator

@[expose] public section

/-!
# A non-interactive argument in the classical random-oracle model

The notions of the paper's `def:narg-ks` and `def:narg-sound` for a verifier
(`GordieHowe.NARG.Verifier`) with oracle `A → B`, against classical query-bounded adversaries without
proof queries, the extraction run against a lazily sampled oracle. The zero-knowledge notion of
`def:narg-zk` is `ZeroKnowledge`, in `GordieHowe/Model/ROM/InteractiveNIZKLastProofQuery.lean`.

- `Verifier A B Cl Stmt`: a verifier with oracle `A → B`.
- `Verifier.JointBound V rel ext β`: for every deterministic `t`-query algorithm, the verifier
  accepts its claim while `ext` returns no witness from the log of the algorithm followed by the
  verifier's queries with probability at most `β (t + kq)` (CY24 Definition 5.1.1, p. 48).
- `Adversary A B O t`: the classical `t`-query adversaries (`ROM.QueryBoundedAdversary` without
  proof queries) with output in `O` (a claim and the auxiliary output `Z` of `def:narg-ks` for
  knowledge soundness, a claim for soundness).
- `OracleSim A B`: a classical oracle simulator, the interface `S` of an online extractor
  (DFMS22 Definition 3.1, p. 10): a stateful randomized oracle, given by its laws.
- `OracleSampler A B`: a classical oracle simulator as a computable randomized algorithm, each
  answer a function of the state, the query and coins drawn uniformly from a finite type;
  `OracleSampler.law`, its law as an `OracleSim`. `OracleSampler.lazy`, the lazily sampled oracle,
  is computable; the extraction runs use its law (`OracleSim.run_lazy`).
- `Adversary.OnlineExtracts V S rel ext εsim εks`: online extractability with the simulator `S` and
  the extractor `ext` reading its final state (DFMS22 Definition 3.1 with classical adversaries):
  the joint law of the claim, the auxiliary output and the verdict in the extraction run
  (`Adversary.extractionRun`) is within statistical distance `εsim` of the real run's, and the
  verifier accepts while extraction fails with probability at most `εks`. The lazily sampled oracle
  has `εsim = 0` (`Adversary.tvDist_extractionLaw_lazy`).
- `Adversary.acceptsFalse V rel`: the probability of an accepted claim for a statement without a
  witness; `Adversary.acceptsFalse_le` is the paper's `lem:ks-sound` in the classical model.

The theorems that a joint bound gives online extractability and soundness are
`GordieHowe.SPBCS.ROM.onlineExtracts` and `GordieHowe.SPBCS.ROM.soundness`.
-/

namespace GordieHowe.NARG.ROM

open GordieHowe.QROM GordieHowe.IOP
open scoped NNReal ENNReal

/-- **A verifier in the classical random-oracle model**: a verifier (`GordieHowe.NARG.Verifier`)
with oracle `A → B`, on claims `Cl` with statements in `Stmt`. -/
abbrev Verifier (A B Cl Stmt : Type) : Type :=
  NARG.Verifier A B Cl Stmt

variable {A B Cl Stmt : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]

/-- **The joint knowledge bound of a database extractor** (CY24 Definition 5.1.1, p. 48, for
deterministic algorithms): for every deterministic `t`-query algorithm `𝒜`, over a uniformly random
oracle `h`, the verifier accepts the claim of `𝒜` while `ext` returns no witness from the log of `𝒜`
followed by the verifier's `kq` queries with probability at most `β (t + kq)`. -/
def Verifier.JointBound (V : Verifier A B Cl Stmt) {Wit : Type} (rel : Set (Stmt × Wit))
    (ext : Stmt → DB A B → Multiset Wit) (β : ℕ → ℝ≥0∞) : Prop :=
  ∀ {t : ℕ} (𝒜 : ROM.Alg A B Cl t), Pr[h ← (A → B) : V.Accepted h (𝒜.output h) ∧
    ¬ ExtractsAt rel ext (V.stmt (𝒜.output h)) ((𝒜.append V.expansion V.kq).log h (t + V.kq))] ≤
      β (t + V.kq)

/-! ### Oracle simulators -/

/-- **A classical oracle simulator** (the interface `S` of an online extractor, DFMS22 Definition
3.1, p. 10, with classical adversaries): a state, its initial law, and the answer to a query with
the state after it, both drawn at random from the state before. -/
structure OracleSim (A B : Type) where
  /-- The state. -/
  St : Type
  /-- The law of the initial state. -/
  init : PMF St
  /-- The answer to the query `a` at the state `s`, with the state after it. -/
  answer : St → A → PMF (B × St)

/-- **A classical oracle simulator as a randomized algorithm** (the interface `S` of an online
extractor, DFMS22 Definition 3.1, p. 10, with classical adversaries, as a probabilistic algorithm
whose coins are explicit): a state, its initial value, and the answer to a query with the state
after it, a function of the state before, the query and coins drawn uniformly from the finite type
`Coins` at each query. Its law is the oracle simulator `OracleSampler.law`, which the statements
read.

Every definition of this type must document, in a "Running time" paragraph, what the procedure
computes and why each answer takes polynomial time, bounding its state and its coins, and it must be
a computable definition (`scripts/CostLint.lean`). -/
structure OracleSampler (A B : Type) where
  /-- The state. -/
  St : Type
  /-- The coins drawn at each query. -/
  Coins : Type
  /-- The coins are drawn uniformly from a finite type. -/
  [fintypeCoins : Fintype Coins]
  /-- The coins are drawn uniformly (`OracleSampler.law`), so there is at least one. -/
  coins_nonempty : Nonempty Coins
  /-- The initial state. -/
  init : St
  /-- The answer to the query `a` at the state `s` with the coins `c`, with the state after it. -/
  answer : St → A → Coins → B × St

attribute [instance] OracleSampler.fintypeCoins

namespace OracleSampler

/-- **The law of an oracle sampler**: the initial state, and at each query the answer and the state
after it, on coins drawn uniformly. -/
noncomputable abbrev law (S : OracleSampler A B) : OracleSim A B where
  St := S.St
  init := PMF.pure S.init
  answer s a :=
    haveI := S.coins_nonempty
    (PMF.uniformOfFintype S.Coins).map (S.answer s a)

/-- **The lazily sampled oracle** (CY24 section 2.2, p. 22; CMS19 footnote 5, p. 18): the table of
the queries so far, initially empty; a query in the table is answered from it, a fresh query by the
coins, a uniform value of `B` that the table records.

Running time: each answer looks up the query in the table and, for a fresh query, inserts one entry;
after `n` queries the table has at most `n` entries, so an answer takes time polynomial in `n` and
in the size of the encodings of `A` and `B`. The coins of an answer are one element of `B`. This
running time is argued here, not proved in Lean. -/
abbrev lazy : OracleSampler A B where
  St := DB A B
  Coins := B
  coins_nonempty := inferInstance
  init := ∅
  answer D a y := match D.lookup a with
    | some z => (z, D)
    | none => (y, D.extend a y)

end OracleSampler

namespace OracleSim

variable (S : OracleSim A B)

/-- **The run of a deterministic algorithm against the simulator** for `n` steps: the answers to
its queries and the simulator's state. -/
noncomputable def run {C : Type} {t : ℕ} (𝒜 : GordieHowe.ROM.Alg A B C t) : ℕ → PMF (List B × S.St)
  | 0 => S.init.map fun s => ([], s)
  | i + 1 => (run 𝒜 i).bind fun p =>
      (S.answer p.2 (𝒜.next p.1)).map fun q => (p.1 ++ [q.1], q.2)

/-- **The lazily sampled oracle's run is the lazy run** (`Alg.lazyLaw`): after `n` steps its
answers and table are those of the lazy run. -/
theorem lazy_run_eq_lazyLaw {C : Type} {t : ℕ} (𝒜 : GordieHowe.ROM.Alg A B C t) :
    ∀ n, OracleSampler.lazy.law.run 𝒜 n = (𝒜.lazyLaw n).map fun s => (s.ans, s.log)
  | 0 => by
    simp only [run, GordieHowe.ROM.Alg.lazyLaw, PMF.pure_map]
  | n + 1 => by
    rw [run, lazy_run_eq_lazyLaw 𝒜 n, GordieHowe.ROM.Alg.lazyLaw, PMF.bind_map, PMF.map_bind]
    congr 1
    funext s
    simp only [Function.comp, GordieHowe.ROM.Alg.lazyStep, PMF.map_comp]
    congr 1
    funext y
    simp only [Function.comp, GordieHowe.ROM.Alg.lazyNext]
    cases s.log.lookup (𝒜.next s.ans) <;> rfl

/-- **The lazily sampled oracle answers as a uniformly random oracle** (`Alg.lazyLaw_eq`): after
`n` steps its answers and table have the law of the answers and the query log against a uniform
oracle. -/
theorem run_lazy {C : Type} {t : ℕ} (𝒜 : GordieHowe.ROM.Alg A B C t) (n : ℕ) :
    OracleSampler.lazy.law.run 𝒜 n =
      (PMF.uniformOfFintype (A → B)).map fun h => ((𝒜.queries h n).map h, 𝒜.log h n) := by
  rw [lazy_run_eq_lazyLaw, GordieHowe.ROM.Alg.lazyLaw_eq, PMF.map_comp]
  rfl

end OracleSim

/-! ### Adversaries -/

/-- **The classical `t`-query adversaries with output in `O`** (`ROM.QueryBoundedAdversary` without
proof queries): coins independent of the oracle, then a deterministic classical oracle algorithm
with at most `t` queries. For knowledge soundness `O` is a claim and the auxiliary output `Z` of
`def:narg-ks`; for soundness it is a claim. -/
abbrev Adversary (A B O : Type) (t : ℕ) : Type 1 :=
  GordieHowe.ROM.QueryBoundedAdversary A B Empty Empty O t

namespace Adversary

variable {Z : Type} {t : ℕ} (𝒢 : Adversary A B (Cl × Z) t) (V : Verifier A B Cl Stmt)

/-- The `t`-query form of `𝒢`'s algorithm at the coins `r` (`IAlg.toAlg`). -/
abbrev queryAlg (r : 𝒢.Coins) : GordieHowe.ROM.Alg A B (Cl × Z) t :=
  (𝒢.alg r).toAlg t

/-- **The extraction run's algorithm** at the coins `r`: `𝒢`'s queries, then the verifier's `kq`
queries on its claim. -/
noncomputable abbrev extAlg (r : 𝒢.Coins) : GordieHowe.ROM.Alg A B Cl (t + V.kq) :=
  ((𝒢.queryAlg r).mapOut Prod.fst).append V.expansion V.kq

/-- **`𝒢`'s output read from the answers** of the extraction run. -/
def outputOf (r : 𝒢.Coins) (ans : List B) : Cl × Z :=
  (𝒢.queryAlg r).out (ans.take t)

/-- **The verifier's verdict in the extraction run** (DFMS22's `v`, with the verifier's queries
answered by the simulator): the answers to the verifier's `kq` queries, after `𝒢`'s `t`, are some
`a` on which the verifier accepts the claim read from the answers. -/
def verdictOf (r : 𝒢.Coins) (ans : List B) : Prop :=
  ∃ a : Fin V.kq → B, (∀ i : Fin V.kq, ans[t + i]? = some (a i)) ∧
    V.AcceptsOn (𝒢.outputOf r ans).1 a

variable (S : OracleSim A B)

/-- **The extraction run** at the coins `r` (DFMS22 Definition 3.1, p. 10, `V^S ∘ A^S`): `𝒢`'s
queries and the verifier's queries on its claim, all answered by the simulator `S`; the answers and
the simulator's final state, which the extractor reads. -/
noncomputable abbrev extractionRun (r : 𝒢.Coins) : PMF (List B × S.St) :=
  S.run (𝒢.extAlg V r) (t + V.kq)

/-- **The law of the claim, the auxiliary output and the verdict in the extraction run** at the
coins `r`. -/
noncomputable def extractionLaw (r : 𝒢.Coins) : PMF (VerifiedOutput (Cl × Z)) :=
  (𝒢.extractionRun V S r).map fun p => ⟨some (𝒢.outputOf r p.1), 𝒢.verdictOf V r p.1⟩

/-- **The law of the outcome in the real run** at the coins `r`: `𝒢`'s output against a uniformly
random oracle `h` and whether the verifier accepts its claim with `h`. -/
noncomputable def realLaw (r : 𝒢.Coins) : PMF (VerifiedOutput (Cl × Z)) :=
  (PMF.uniformOfFintype (A → B)).map fun h =>
    ⟨some ((𝒢.alg r).output GordieHowe.ROM.IAlg.noRequests h),
      V.Accepted h ((𝒢.alg r).output GordieHowe.ROM.IAlg.noRequests h).1⟩

/-- **The probability that the verifier accepts and the extractor returns no witness, in the
extraction run**: the extractor `ext` reads the simulator's final state. -/
noncomputable def acceptsNotExtracts {Wit : Type} (rel : Set (Stmt × Wit))
    (ext : Stmt → S.St → Multiset Wit) : ℝ≥0∞ :=
  ∑' r, 𝒢.coins r * (𝒢.extractionRun V S r).toOuterMeasure
    {p | 𝒢.verdictOf V r p.1 ∧ ¬ ExtractsAt rel ext (V.stmt (𝒢.outputOf r p.1).1) p.2}

/-- **Online extractability in the classical random-oracle model** of `𝒢` for the verifier `V`,
with the oracle simulator `S` and the extractor `ext` reading its final state (the paper's
`def:narg-ks`; DFMS22 Definition 3.1, p. 10, with classical adversaries): the joint law of the
claim, the auxiliary output and the verdict in the extraction run, averaged over the coins, is
within statistical distance `εsim` of the real run's (`tvDist_le`); and in the extraction run the
verifier accepts while the extractor fails with probability at most `εks`
(`acceptsNotExtracts_le`). -/
structure OnlineExtracts {Wit : Type} (rel : Set (Stmt × Wit)) (ext : Stmt → S.St → Multiset Wit)
    (εsim : ℝ≥0) (εks : ℝ≥0∞) : Prop where
  /-- The extraction run's joint law is within `εsim` of the real run's. -/
  tvDist_le : PMF.tvDist (𝒢.coins.bind (𝒢.extractionLaw V S)) (𝒢.coins.bind (𝒢.realLaw V)) ≤ εsim
  /-- Acceptance with failed extraction, in the extraction run, has probability at most `εks`. -/
  acceptsNotExtracts_le : 𝒢.acceptsNotExtracts V S rel ext ≤ εks

variable {𝒢 V S} in
/-- Online extractability at an error holds at every larger error. -/
theorem OnlineExtracts.mono {Wit : Type} {rel : Set (Stmt × Wit)}
    {ext : Stmt → S.St → Multiset Wit} {εsim εsim' : ℝ≥0} {εks εks' : ℝ≥0∞}
    (h : 𝒢.OnlineExtracts V S rel ext εsim εks) (hsim : εsim ≤ εsim') (hks : εks ≤ εks') :
    𝒢.OnlineExtracts V S rel ext εsim' εks' :=
  ⟨h.tvDist_le.trans (by exact_mod_cast hsim), h.acceptsNotExtracts_le.trans hks⟩

omit [Fintype A] [Fintype B] [Nonempty B] in
/-- **The output read from the extraction run's answers is `𝒢`'s output** against the same
oracle. -/
theorem outputOf_answers (r : 𝒢.Coins) (h : A → B) :
    𝒢.outputOf r (((𝒢.extAlg V r).queries h (t + V.kq)).map h) = (𝒢.queryAlg r).output h := by
  rw [outputOf, ← List.map_take,
    GordieHowe.ROM.Alg.take_queries _ _ (Nat.le_add_right _ _),
    GordieHowe.ROM.Alg.queries_append_of_le _ _ _ _ le_rfl, GordieHowe.ROM.Alg.queries_mapOut]
  rfl

omit [Fintype A] [Fintype B] [Nonempty B] in
/-- **Against an oracle, the verdict is the verifier's acceptance** of `𝒢`'s claim. -/
theorem verdictOf_answers (r : 𝒢.Coins) (h : A → B) :
    𝒢.verdictOf V r (((𝒢.extAlg V r).queries h (t + V.kq)).map h) ↔
      V.Accepted h ((𝒢.queryAlg r).output h).1 := by
  rw [verdictOf, outputOf_answers]
  have hq := GordieHowe.ROM.Alg.queries_append_add ((𝒢.queryAlg r).mapOut Prod.fst) V.expansion
    V.kq h V.kq
  rw [GordieHowe.ROM.Alg.output_mapOut] at hq
  have hlen : (((𝒢.queryAlg r).mapOut Prod.fst).queries h t).length = t := by simp
  have hget : ∀ i : Fin V.kq, (((𝒢.extAlg V r).queries h (t + V.kq)).map h)[t + i]? =
      some (V.answers h ((𝒢.queryAlg r).output h).1 i) := by
    intro i
    rw [hq, List.map_append, List.getElem?_append_right (by simp [hlen])]
    simp [hlen, NARG.Verifier.answers, QROM.Expansion.queries]
  constructor
  · rintro ⟨a, ha, hacc⟩
    have : a = V.answers h ((𝒢.queryAlg r).output h).1 := funext fun i => by
      have := (ha i).symm.trans (hget i)
      exact Option.some.inj this
    rw [this] at hacc
    exact hacc
  · intro hacc
    exact ⟨_, hget, hacc⟩

/-- **The lazily sampled oracle simulates with error `0`**: at every value of the coins the
extraction run with the law of `OracleSampler.lazy` has the real run's law of the output and the
verdict. -/
theorem extractionLaw_lazy (r : 𝒢.Coins) :
    𝒢.extractionLaw V OracleSampler.lazy.law r = 𝒢.realLaw V r := by
  rw [extractionLaw, extractionRun, OracleSim.run_lazy, PMF.map_comp, realLaw]
  congr 1
  funext h
  simp only [Function.comp]
  rw [outputOf_answers, (𝒢.alg r).output_toAlg ((𝒢.alg r).steps_le (𝒢.budget r))]
  congr 1
  rw [← (𝒢.alg r).output_toAlg ((𝒢.alg r).steps_le (𝒢.budget r))]
  exact propext (𝒢.verdictOf_answers V r h)

/-- **Simulation error `0` for the lazily sampled oracle.** -/
theorem tvDist_extractionLaw_lazy :
    PMF.tvDist (𝒢.coins.bind (𝒢.extractionLaw V OracleSampler.lazy.law))
      (𝒢.coins.bind (𝒢.realLaw V)) = 0 := by
  rw [show 𝒢.extractionLaw V OracleSampler.lazy.law = 𝒢.realLaw V from
    funext (𝒢.extractionLaw_lazy V)]
  exact PMF.tvDist_self _

end Adversary

/-- **The probability that `𝒜` outputs a claim that `V` accepts for a statement without a
witness**, over its coins and a uniformly random oracle. -/
noncomputable def Adversary.acceptsFalse {t : ℕ} (𝒜 : Adversary A B Cl t) (V : Verifier A B Cl Stmt)
    {Wit : Type} (rel : Set (Stmt × Wit)) : ℝ≥0∞ :=
  ∑' r, 𝒜.coins r * Pr[h ← (A → B) :
    (∀ w, (V.stmt ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h), w) ∉ rel) ∧
      V.Accepted h ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h)]

/-- **The adversary with a trivial auxiliary output**: its claim and `()`. -/
def Adversary.withUnit {t : ℕ} (𝒜 : Adversary A B Cl t) : Adversary A B (Cl × Unit) t where
  steps := 𝒜.steps
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).mapOut fun c => (c, ())
  budget r := (𝒜.alg r).budget_mapOut _ (𝒜.budget r)

/-- **Soundness from knowledge soundness** (the paper's `lem:ks-sound` in the classical
random-oracle model): if `𝒜` with a trivial auxiliary output is online extractable with
simulation error `εsim` and extraction error `εks`, it outputs an accepted claim for a statement
without a witness with probability at most `εsim + εks`. The event is one of the claim and the
verdict, so its probabilities in the real and the extraction run differ by at most their
statistical distance; in the extraction run it implies acceptance with failed extraction. -/
theorem Adversary.acceptsFalse_le {t : ℕ} (𝒜 : Adversary A B Cl t) (V : Verifier A B Cl Stmt)
    {S : OracleSim A B} {Wit : Type} {rel : Set (Stmt × Wit)} {ext : Stmt → S.St → Multiset Wit}
    {εsim : ℝ≥0} {εks : ℝ≥0∞} (h : 𝒜.withUnit.OnlineExtracts V S rel ext εsim εks) :
    𝒜.acceptsFalse V rel ≤ εsim + εks := by
  set T : Set (VerifiedOutput (Cl × Unit)) :=
    {vo | vo.accepted ∧ ∃ c ∈ vo.out, ∀ w, (V.stmt c.1, w) ∉ rel} with hT
  have h1 : 𝒜.acceptsFalse V rel =
      (𝒜.withUnit.coins.bind (𝒜.withUnit.realLaw V)).toOuterMeasure T := by
    rw [PMF.toOuterMeasure_bind_apply, acceptsFalse]
    refine tsum_congr fun r => congrArg _ ?_
    simp only [Adversary.realLaw, PMF.toOuterMeasure_map_apply]
    unfold probUniform
    congr 1
    ext g
    have hout : (𝒜.withUnit.alg r).output GordieHowe.ROM.IAlg.noRequests g =
        ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests g, ()) :=
      (𝒜.alg r).output_mapOut (fun c => (c, ())) _ _
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hT, Option.mem_def, Option.some.injEq,
      exists_eq_left', hout]
    exact ⟨fun ⟨hw, ha⟩ => ⟨ha, hw⟩, fun ⟨ha, hw⟩ => ⟨hw, ha⟩⟩
  have h2 : (𝒜.withUnit.coins.bind (𝒜.withUnit.realLaw V)).toOuterMeasure T ≤
      (𝒜.withUnit.coins.bind (𝒜.withUnit.extractionLaw V S)).toOuterMeasure T + εsim := by
    refine (PMF.toOuterMeasure_le_add_tsum_tsub _ _ T).trans (add_le_add le_rfl ?_)
    rw [← ENNReal.ofReal_toReal (PMF.tsum_tsub_ne_top _ _), ← PMF.tvDist_eq_toReal_tsum_tsub,
      PMF.tvDist_comm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal h.tvDist_le
  have h3 : (𝒜.withUnit.coins.bind (𝒜.withUnit.extractionLaw V S)).toOuterMeasure T ≤ εks := by
    refine le_trans ?_ h.acceptsNotExtracts_le
    rw [PMF.toOuterMeasure_bind_apply, Adversary.acceptsNotExtracts]
    refine ENNReal.tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
    rw [Adversary.extractionLaw, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ fun p hp => ?_
    obtain ⟨hp, -⟩ := hp
    simp only [hT, Set.mem_preimage, Set.mem_ofPred_eq, Option.mem_def, Option.some.injEq,
      exists_eq_left'] at hp
    exact ⟨hp.1, fun ⟨w, _, hw⟩ => hp.2 w hw⟩
  calc 𝒜.acceptsFalse V rel = _ := h1
    _ ≤ _ := h2
    _ ≤ εks + εsim := by gcongr
    _ = εsim + εks := add_comm _ _

/-- **Soundness from knowledge soundness at a fixed online extractor** (the paper's `lem:ks-sound`
in the classical random-oracle model): if every classical `t`-query adversary with an auxiliary
output is online extractable with the simulator `S` and the extractor `ext` at errors `εsim` and
`εks`, the argument has soundness error `εsim + εks` at `t` queries. -/
theorem soundness_of_onlineExtracts {t : ℕ} (V : Verifier A B Cl Stmt) {S : OracleSim A B}
    {Wit : Type} {rel : Set (Stmt × Wit)} {ext : Stmt → S.St → Multiset Wit} {εsim : ℝ≥0}
    {εks : ℝ≥0∞} (h : ∀ 𝒢 : Adversary A B (Cl × Unit) t, 𝒢.OnlineExtracts V S rel ext εsim εks)
    (𝒜 : Adversary A B Cl t) : 𝒜.acceptsFalse V rel ≤ εsim + εks :=
  𝒜.acceptsFalse_le V (h _)

/-! ### Completeness -/

/-- **The probability that the honest proof of the adversary's pair is rejected** (Unruh 2017
Definition 5, p. 14, in the classical random-oracle model): over the coins of `𝒜`, the honest
prover's coins and a uniformly random oracle `h`, the adversary outputs a pair `(x, w)` in `rel`
after its queries, and the verifier rejects the claim `claim x π` of the proof `π` that the program `P`
computes on `(x, w)` against `h` (the classical semantics `Prover.toFn`). -/
noncomputable def Adversary.rejectsHonest {Wit Proof Coins : Type} {t : ℕ}
    (𝒜 : Adversary A B (QROM.ProofQuery Stmt Wit) t) (P : NARG.Prover A B Stmt Wit Proof Coins)
    (V : Verifier A B Cl Stmt) (claim : Stmt → Proof → Cl) (rel : Stmt → Wit → Prop) : ℝ≥0∞ :=
  ∑' r, 𝒜.coins r * ∑' c, P.coins c * Pr[h ← (A → B) :
    rel ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h).stmt
        ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h).wit ∧
      ¬ V.Accepted h (claim ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h).stmt
        (P.toFn.prove h ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h).stmt
          ((𝒜.alg r).output GordieHowe.ROM.IAlg.noRequests h).wit c))]

/-- **Completeness in the classical random-oracle model** (the paper's `def:narg-complete`, Unruh
2017 Definition 5, p. 14, with the pair chosen by the adversary after its queries): every classical
`t`-query adversary without proof queries that outputs a statement and a witness makes the honest
proof of a pair in `rel` rejected with probability at most `ε t` (`Adversary.rejectsHonest`). -/
def Complete {Wit Proof Coins : Type} (P : NARG.Prover A B Stmt Wit Proof Coins)
    (V : Verifier A B Cl Stmt) (claim : Stmt → Proof → Cl) (rel : Stmt → Wit → Prop)
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (t : ℕ) (𝒜 : Adversary A B (QROM.ProofQuery Stmt Wit) t), 𝒜.rejectsHonest P V claim rel ≤ ε t

/-! ### Zero knowledge -/

section ZeroKnowledge

variable {Wit Proof Coins SimCoins : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype Coins] [Fintype SimCoins]

/-- **Zero knowledge in the classical random-oracle model** (the paper's `def:narg-zk`, Unruh 2017
Definition 6, p. 14, with classical adversaries all of whose queries are counted): the programs `P`
and `S` run against the oracle (`Prover.toFn`, `Simulator.toFn`); a valid proof query is answered
by the prover's proof itself, or by the simulator's optional proof (`none` where the simulator
fails); every classical adversary with a budget of `t` queries whose output does not read the final
oracle, answered on `Q` proof queries, has advantage at most `ε t Q`
(`GordieHowe.ROM.ZeroKnowledge`). -/
def ZeroKnowledge (P : NARG.Prover A B Stmt Wit Proof Coins)
    (S : NARG.Simulator A B Stmt (Option Proof) SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  GordieHowe.ROM.ZeroKnowledge rel (P.mapOutput some).toFn S.toFn ε

/-- **Everlasting zero knowledge in the classical random-oracle model** (the paper's
`def:narg-zk-post`): as `ZeroKnowledge`, against adversaries with at most `t` queries before each
proof query and any number after the last one (`GordieHowe.ROM.EverlastingZeroKnowledge`). -/
def EverlastingZeroKnowledge (P : NARG.Prover A B Stmt Wit Proof Coins)
    (S : NARG.Simulator A B Stmt (Option Proof) SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  GordieHowe.ROM.EverlastingZeroKnowledge rel (P.mapOutput some).toFn S.toFn ε

variable {rel}

/-- Everlasting zero knowledge gives zero knowledge at the same error. -/
theorem EverlastingZeroKnowledge.zeroKnowledge {P : NARG.Prover A B Stmt Wit Proof Coins}
    {S : NARG.Simulator A B Stmt (Option Proof) SimCoins} {ε : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledge rel P S ε) : ZeroKnowledge rel P S ε :=
  GordieHowe.ROM.EverlastingZeroKnowledge.zeroKnowledge h

/-- A larger error bound. -/
theorem ZeroKnowledge.mono {P : NARG.Prover A B Stmt Wit Proof Coins}
    {S : NARG.Simulator A B Stmt (Option Proof) SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : ZeroKnowledge rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) : ZeroKnowledge rel P S ε' :=
  GordieHowe.ROM.ZeroKnowledge.mono h hε

/-- A larger error bound. -/
theorem EverlastingZeroKnowledge.mono {P : NARG.Prover A B Stmt Wit Proof Coins}
    {S : NARG.Simulator A B Stmt (Option Proof) SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledge rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    EverlastingZeroKnowledge rel P S ε' :=
  fun T t Q 𝒜 h𝒜 => (h T t Q 𝒜 h𝒜).trans (hε t Q)

section Encode

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (enc : OracleEncoding A B X Y) {P : NARG.Prover A B Stmt Wit Proof Coins}
  {S : NARG.Simulator A B Stmt (Option Proof) SimCoins}

/-- The prover run through an encoding agrees with the prover through it. -/
theorem proverDecode_encode :
    GordieHowe.ROM.ProverDecode enc id (rel := rel) ((P.mapOutput some).encode enc).toFn
      (P.mapOutput some).toFn :=
  ⟨rfl, fun O' x w c _ => by rw [Prover.toFn_encode_prove]; rfl⟩

/-- The simulator run through an encoding agrees with the simulator through it. -/
theorem simulatorDecode_encode :
    GordieHowe.ROM.SimulatorDecode enc id (rel := rel) (S.encode enc).toFn S.toFn :=
  fun O' x c _ => by
    rw [Simulator.toFn_encode_run]
    exact ⟨rfl, enc.decode_reprogram _ _⟩

/-- **Zero knowledge of the programs run through an encoded oracle gives zero knowledge of the
programs** (`GordieHowe.ROM.ZeroKnowledge.of_decode`). -/
theorem ZeroKnowledge.of_encode {ε : ℕ → ℕ → ℝ}
    (h : GordieHowe.ROM.ZeroKnowledge rel ((P.mapOutput some).encode enc).toFn (S.encode enc).toFn ε) :
    ZeroKnowledge rel P S ε :=
  GordieHowe.ROM.ZeroKnowledge.of_decode (proverDecode_encode enc) (simulatorDecode_encode enc) h

/-- **Everlasting zero knowledge of the programs run through an encoded oracle gives everlasting
zero knowledge of the programs** (`GordieHowe.ROM.EverlastingZeroKnowledge.of_decode`). -/
theorem EverlastingZeroKnowledge.of_encode {ε : ℕ → ℕ → ℝ}
    (h : GordieHowe.ROM.EverlastingZeroKnowledge rel ((P.mapOutput some).encode enc).toFn
      (S.encode enc).toFn ε) :
    EverlastingZeroKnowledge rel P S ε :=
  GordieHowe.ROM.EverlastingZeroKnowledge.of_decode (proverDecode_encode enc)
    (simulatorDecode_encode enc) h

end Encode

end ZeroKnowledge

end GordieHowe.NARG.ROM
