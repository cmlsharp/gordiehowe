-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.InteractiveNIZK
public import GordieHowe.Model.ROM.SaltedZKLastProofQuery
public import GordieHowe.Model.ROM.LeafZK

@[expose] public section

/-!
# Everlasting zero knowledge against query-bounded classical adversaries

The query bound of the paper's everlasting zero knowledge (Definition 6.2, `def:narg-zk-post`) for
the query-bounded classical adversaries of `GordieHowe/Model/ROM/Interactive.lean`: every proof query comes after at
most `t` queries of the run (`IAlg.RequestBudget`), and the queries after the last proof query are not
charged. The adversary's own budget of queries over all its steps is not charged.

- `GordieHowe.ROM.EverlastingZeroKnowledge`, implied by
  `GordieHowe.ROM.NIZK.EverlastingZeroKnowledge` (`GordieHowe.ROM.QueryBoundedAdversary.everlastingZeroKnowledge_of_nizk`) and implying
  `GordieHowe.ROM.ZeroKnowledge` (`GordieHowe.ROM.EverlastingZeroKnowledge.zeroKnowledge`).
- `GordieHowe.ROM.ZeroKnowledge`: Unruh 2017 Definition 6 with all queries counted: the
  adversary's budget of `t` queries covers all its queries and its output does not read the final
  oracle (`OutputOracleFree`); implied by `ROM.NIZK.ZeroKnowledgeQueryBounded`
  (`zeroKnowledge_of_queryBounded`).
-/

namespace GordieHowe.ROM

open GordieHowe.Quantum GordieHowe.QROM
open scoped ENNReal

namespace IAlg

variable {A B Req Resp Out : Type} {m : ℕ} (𝒜 : IAlg A B Req Resp Out m)

/-- **The number of queries before step `k`** of the run of `𝒜` against `R` from `O`, for any
response type (`IAlg.queriesBefore` of `GordieHowe/Model/ROM/SimExtract.lean` is the same count for optional
responses). -/
def queryCountBefore (R : Responder A B Req Resp) (O : A → B) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => (𝒜.next (𝒜.run R O i).hist).IsQuery).card

/-- **A budget of `t` queries before each proof query**: against every responder and every oracle, every
proof query of `𝒜` comes after at most `t` queries of its run. The queries after the last proof query of a
run are not charged. -/
def RequestBudget (t : ℕ) : Prop :=
  ∀ R O, ∀ k < m, ∀ r, 𝒜.next (𝒜.run R O k).hist = .request r → 𝒜.queryCountBefore R O k ≤ t

variable {𝒜}

/-- A budget of `t` queries is a budget of `t` queries before each proof query. -/
theorem Budget.requestBudget {t : ℕ} (h : 𝒜.Budget t) : 𝒜.RequestBudget t :=
  fun R O k hk _ _ => (Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩).trans (h R O)

end IAlg

variable {X Y Stmt Wit Proof : Type}

namespace IAlg

variable {m : ℕ} (𝒜 : IAlg X Y (ProofQuery Stmt Wit) (Option Proof) ((X → Y) → Bool) m)

theorem next_toNIZK_run (R : NIZK.Responder X Y Stmt Wit Proof) (O : X → Y) (k : ℕ) :
    𝒜.toNIZK.next (𝒜.toNIZK.run R O k).hist = (𝒜.next (𝒜.run (toResponder R) O k).hist).toNIZK := by
  rw [run_toNIZK]
  simp [toNIZK, Function.comp_def, Reply.ofNIZK_toNIZK]

theorem queriesBefore_toNIZK (R : NIZK.Responder X Y Stmt Wit Proof) (O : X → Y) (k : ℕ) :
    𝒜.toNIZK.queriesBefore R O k = 𝒜.queryCountBefore (toResponder R) O k := by
  unfold NIZK.IAlg.queriesBefore queryCountBefore
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  rw [next_toNIZK_run]
  cases 𝒜.next (𝒜.run (toResponder R) O i).hist <;> rfl

/-- The conversion keeps a budget of queries before each proof query. -/
theorem requestBudget_toNIZK {t : ℕ} (h : 𝒜.RequestBudget t) : 𝒜.toNIZK.RequestBudget t := by
  intro R O k hk req hr
  rw [queriesBefore_toNIZK]
  rw [next_toNIZK_run] at hr
  cases hn : 𝒜.next (𝒜.run (toResponder R) O k).hist with
  | query x => rw [hn] at hr; cases hr
  | request r => exact h _ O k hk r hn

end IAlg

namespace QueryBoundedAdversary

variable {T : ℕ} (𝒜 : QueryBoundedAdversary X Y (ProofQuery Stmt Wit) (Option Proof)
  ((X → Y) → Bool) T)

/-- **At most `t` queries before the last proof query** (the query bound of the paper's Definition 6.2,
`def:narg-zk-post`): every algorithm of `𝒜` makes at most `t` queries before each of its proof queries
on every run (`IAlg.RequestBudget`). -/
def QueriesBeforeLastProofQuery (t : ℕ) : Prop :=
  ∀ r, (𝒜.alg r).RequestBudget t

/-- The budget of `𝒜` bounds its queries before the last proof query. -/
theorem queriesBeforeLastRequestLE_self : 𝒜.QueriesBeforeLastProofQuery T :=
  fun r => (𝒜.budget r).requestBudget

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins] [Fintype SimCoins]

/-- **Everlasting zero knowledge in the classical random-oracle model, over query-bounded
adversaries** (Unruh 2017 Definition 6, p. 14, with classical adversaries and the query bound of the
paper's Definition 6.2, `def:narg-zk-post`): for all `t` and `Q`, every query-bounded classical
adversary with at most `t` queries before each of its proof queries on every run
(`QueriesBeforeLastProofQuery`), and any number after the last one, whose first `Q` proof queries are
answered, has advantage at most `ε t Q` between the prover `P` and the simulator `S`. -/
def _root_.GordieHowe.ROM.EverlastingZeroKnowledge (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (T t Q : ℕ) (𝒜 : QueryBoundedAdversary X Y (ProofQuery Stmt Wit) (Option Proof)
    ((X → Y) → Bool) T), 𝒜.QueriesBeforeLastProofQuery t → 𝒜.advantage rel P S Q ≤ ε t Q

/-- **The output does not read the final oracle**: every algorithm's output is a function of its
replies alone, so its budget of queries covers all its queries. -/
def OutputOracleFree : Prop :=
  ∀ r hist O O', (𝒜.alg r).out hist O = (𝒜.alg r).out hist O'

/-- **Zero knowledge in the classical random-oracle model over query-bounded adversaries**
(Unruh 2017 Definition 6, p. 14, with classical adversaries, all of whose queries are counted):
for all `t` and `Q`, every query-bounded classical adversary with a budget of `t` queries over all
its steps whose output does not read the final oracle (`OutputOracleFree`), with its first `Q`
proof queries answered, has advantage at most `ε t Q` between the prover `P` and the simulator `S`. -/
def _root_.GordieHowe.ROM.ZeroKnowledge (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (S : NARG.SimulatorFn X Y Stmt Proof SimCoins)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t Q : ℕ) (𝒜 : QueryBoundedAdversary X Y (ProofQuery Stmt Wit) (Option Proof)
    ((X → Y) → Bool) t), 𝒜.OutputOracleFree → 𝒜.advantage rel P S Q ≤ ε t Q

variable {rel}

/-- **The definition over the adversaries of `ROM.NIZK` gives the definition over query-bounded
adversaries**, by the map `toNIZK`, which preserves the advantage and the budget before each
proof query. -/
theorem everlastingZeroKnowledge_of_nizk {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε : ℕ → ℕ → ℝ}
    (h : NIZK.EverlastingZeroKnowledge rel P S ε) :
    GordieHowe.ROM.EverlastingZeroKnowledge rel P S ε := fun T t Q 𝒜 h𝒜 =>
  (𝒜.advantage_toNIZK rel P S Q).symm.trans_le
    (h 𝒜.steps T t Q 𝒜.toNIZK fun r => (𝒜.alg r).requestBudget_toNIZK (h𝒜 r))

/-- With an oracle-free output, the algorithms of `toNIZK` have oracle-free outputs. -/
theorem postOracleFree_toNIZK {t : ℕ} {𝒜 : QueryBoundedAdversary X Y (ProofQuery Stmt Wit) (Option Proof)
    ((X → Y) → Bool) t} (h : 𝒜.OutputOracleFree) (r : 𝒜.Coins) : (𝒜.toNIZK.alg r).PostOracleFree :=
  fun O O' hist => h r _ O O'

/-- **Query-counted zero knowledge over the adversaries of `ROM.NIZK` gives zero knowledge over
query-bounded adversaries**, by the map `toNIZK`. -/
theorem zeroKnowledge_of_queryBounded {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε : ℕ → ℕ → ℝ}
    (h : NIZK.ZeroKnowledgeQueryBounded rel P S ε) : GordieHowe.ROM.ZeroKnowledge rel P S ε := fun t Q 𝒜 h𝒜 =>
  (𝒜.advantage_toNIZK rel P S Q).symm.trans_le
    (h 𝒜.steps t Q 𝒜.toNIZK (postOracleFree_toNIZK h𝒜))

/-- **Everlasting zero knowledge gives zero knowledge**, at the same error: an
adversary with a budget of `t` queries makes at most `t` queries before each proof query. -/
theorem _root_.GordieHowe.ROM.EverlastingZeroKnowledge.zeroKnowledge {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε : ℕ → ℕ → ℝ}
    (h : GordieHowe.ROM.EverlastingZeroKnowledge rel P S ε) : GordieHowe.ROM.ZeroKnowledge rel P S ε := fun t Q 𝒜 _ =>
  h t t Q 𝒜 𝒜.queriesBeforeLastRequestLE_self

/-- A larger error bound. -/
theorem _root_.GordieHowe.ROM.ZeroKnowledge.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ} (h : GordieHowe.ROM.ZeroKnowledge rel P S ε)
    (hε : ∀ t Q, ε t Q ≤ ε' t Q) : GordieHowe.ROM.ZeroKnowledge rel P S ε' :=
  fun t Q 𝒜 h𝒜 => (h t Q 𝒜 h𝒜).trans (hε t Q)

end QueryBoundedAdversary

end GordieHowe.ROM
