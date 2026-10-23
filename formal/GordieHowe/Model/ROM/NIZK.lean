-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.NIZK

@[expose] public section

/-!
# Zero knowledge of a non-interactive argument in the classical random-oracle model

The classical counterpart of `GordieHowe/Model/QROM/NIZK.lean`: the same provers, simulators and
environments (`GordieHowe.NARG.ProverFn`, `GordieHowe.NARG.SimulatorFn`, `GordieHowe.QROM.realEnv`,
`GordieHowe.QROM.simEnv`), against classical interactive adversaries.

**The adversaries** (`IAlg`, `Adversary`). A deterministic classical interactive algorithm with
`m` steps chooses at each step, from the replies so far, whether to query the oracle at a point
or to make a proof query, a statement with a witness (`Action`), and receives the oracle's answer
or the response (`Reply`). After its `m` steps it outputs a bit computed from the replies and the
whole oracle in force at the end (`IAlg.post`), so it may make any number of classical queries
after its steps. An adversary draws coins independently of the oracle and runs a deterministic
algorithm for each value of the coins, as in `GordieHowe/Model/ROM/Model.lean`. Its query budget
(`IAlg.Budget t`) is per run: against every environment and every oracle, at most `t` of its `m`
steps are queries; proof queries are not counted.

**The game** (`IAlg.run`). The state of a run is the list of replies, the oracle in force and the
number of proof queries made (`GameState`). A query reads the oracle in force; proof query number `i`
is answered by the environment's reply to proof query `i` on the oracle in force, which gives the
response and the oracle after it (`envResponder`); proof queries from number `Q` on are answered by
`none` and leave the oracle unchanged, in both games.

`ZeroKnowledge rel P S ε`: for all `m`, `t` and `Q`, every adversary with `m` steps and a budget
of `t` queries has advantage (`GordieHowe.advantage`) at most `ε t Q` between the real environment of
`P` and the simulated environment of `S`.

The definition is Unruh 2017 Definition 6 (ePrint 2017/398, p. 14) with classical adversaries,
the knob settings of `GordieHowe/Model/QROM/NIZK.lean` with K5 classical: many proof queries (K1), adaptive
statements and an adaptive choice of query or proof query at each step (K2), at most `t` classical
queries before the last proof query (K3) and unbounded after it (K4, Fractal's definition, ePrint
2019/1076, pp. 38–39), and a simulator that programs the oracle in force by an assignment list
(K6). The simulator is a single one for all bounds (`∃ S ∀ A`, Unruh 2017's order). CY24
Definition 7.1.8 (p. 74) is the classical one-statement form with a programming simulator
`(π, µ) ← S^f(x)`, which reads the oracle in force; invalid proof queries are answered by `⊥` as in
Unruh 2015 Definition 2 (p. 6).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type}

/-- **An action of a classical zero-knowledge adversary**: a query of the oracle at `x`, or a
proof query (Unruh 2017 Definition 6, p. 14: the adversary has oracle access to `H` and to
the prover or the simulator). -/
inductive Action (X Stmt Wit : Type) where
  /-- A query of the oracle at `x`. -/
  | query (x : X)
  /-- A proof query: a statement with a witness. -/
  | request (req : ProofQuery Stmt Wit)

/-- **What a classical zero-knowledge adversary receives**: the oracle's answer to a query, or the
response to a proof query (`none` for a refused proof query). -/
inductive Reply (Y Proof : Type) where
  /-- The oracle's answer to a query. -/
  | answer (y : Y)
  /-- The response to a proof query. -/
  | response (π : Option Proof)

/-- The action is a query. -/
def Action.IsQuery : Action X Stmt Wit → Prop
  | .query _ => True
  | .request _ => False

instance (a : Action X Stmt Wit) : Decidable a.IsQuery := by
  cases a <;> unfold Action.IsQuery <;> infer_instance

/-- **A deterministic classical interactive algorithm with `m` steps**: at each step the action
`next replies` computed from the replies so far, and after the `m` steps the output bit
`post O replies` computed from the replies and the whole oracle in force `O` at the end (the
adversary may make any number of classical queries after its steps). -/
structure IAlg (X Y Stmt Wit Proof : Type) (m : ℕ) where
  /-- The next action, from the replies so far. -/
  next : List (Reply Y Proof) → Action X Stmt Wit
  /-- The output bit, from the oracle in force at the end and the replies. -/
  post : (X → Y) → List (Reply Y Proof) → Bool

/-- **A responder**: the reply to proof query number `i` with proof query `req` on the oracle in force
`O`, the response and the oracle after the proof query. -/
abbrev Responder (X Y Stmt Wit Proof : Type) : Type :=
  ℕ → ProofQuery Stmt Wit → (X → Y) → EnvReply Proof (X → Y)

/-- **The state of a run**: the replies so far, the oracle in force and the number of proof queries
made. -/
@[ext]
structure GameState (X Y Proof : Type) where
  /-- The replies so far. -/
  hist : List (Reply Y Proof)
  /-- The oracle in force. -/
  oracle : X → Y
  /-- The number of proof queries made. -/
  nreq : ℕ

namespace IAlg

variable {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)

/-- **One step of a run against the responder `R`**: a query reads the oracle in force; proof query
number `s.nreq` is answered by `R`, which gives the response and the oracle after it. -/
def step (R : Responder X Y Stmt Wit Proof) (s : GameState X Y Proof) : GameState X Y Proof :=
  match A.next s.hist with
  | .query x => ⟨s.hist ++ [.answer (s.oracle x)], s.oracle, s.nreq⟩
  | .request req =>
    ⟨s.hist ++ [.response (R s.nreq req s.oracle).response], (R s.nreq req s.oracle).state,
      s.nreq + 1⟩

/-- **The run of `A` against the responder `R` from the oracle `O`**: the state after `k` steps. -/
def run (R : Responder X Y Stmt Wit Proof) (O : X → Y) : ℕ → GameState X Y Proof
  | 0 => ⟨[], O, 0⟩
  | k + 1 => A.step R (run R O k)

/-- **The output of `A` against `R` from `O`**: its output bit on the oracle in force and the
replies after its `m` steps. -/
def accepts (R : Responder X Y Stmt Wit Proof) (O : X → Y) : Bool :=
  A.post (A.run R O m).oracle (A.run R O m).hist

/-- **The number of queries of the run of `A` against `R` from `O`**: the steps below `m` whose
action is a query. -/
def queryCount (R : Responder X Y Stmt Wit Proof) (O : X → Y) : ℕ :=
  ((range m).filter fun k => (A.next (A.run R O k).hist).IsQuery).card

/-- **A budget of `t` queries**: against every responder and every oracle, at most `t` of the
`m` steps of `A` are queries; proof queries are not counted. -/
def Budget (t : ℕ) : Prop :=
  ∀ R O, A.queryCount R O ≤ t

variable {A}

theorem step_of_query {R : Responder X Y Stmt Wit Proof} {s : GameState X Y Proof} {x : X}
    (h : A.next s.hist = .query x) :
    A.step R s = ⟨s.hist ++ [.answer (s.oracle x)], s.oracle, s.nreq⟩ := by
  rw [step, h]

theorem step_of_request {R : Responder X Y Stmt Wit Proof} {s : GameState X Y Proof}
    {req : ProofQuery Stmt Wit} (h : A.next s.hist = .request req) :
    A.step R s = ⟨s.hist ++ [.response (R s.nreq req s.oracle).response],
      (R s.nreq req s.oracle).state, s.nreq + 1⟩ := by
  rw [step, h]

/-! ### Runs -/

variable {R R' : Responder X Y Stmt Wit Proof} {O O' : X → Y}

theorem run_succ (k : ℕ) : A.run R O (k + 1) = A.step R (A.run R O k) := rfl

/-- A step makes at most one proof query. -/
theorem nreq_le_nreq_step (s : GameState X Y Proof) : s.nreq ≤ (A.step R s).nreq := by
  unfold step
  split <;> simp

theorem nreq_step_of_request {s : GameState X Y Proof} {req : ProofQuery Stmt Wit}
    (h : A.next s.hist = .request req) : (A.step R s).nreq = s.nreq + 1 := by
  rw [step_of_request h]

/-- The number of proof queries made grows along a run. -/
theorem nreq_run_mono {k k' : ℕ} (h : k ≤ k') : (A.run R O k).nreq ≤ (A.run R O k').nreq := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (A.nreq_le_nreq_step _)

/-- After a proof query at step `k`, every later step has made more proof queries than step `k`. -/
theorem nreq_lt_of_request {k k' : ℕ} {req : ProofQuery Stmt Wit}
    (h : A.next (A.run R O k).hist = .request req) (hk : k < k') :
    (A.run R O k).nreq < (A.run R O k').nreq := by
  have h1 : (A.run R O (k + 1)).nreq = (A.run R O k).nreq + 1 := A.nreq_step_of_request h
  have h2 := A.nreq_run_mono (R := R) (O := O) (show k + 1 ≤ k' from hk)
  omega

/-- **Two steps that are proof queries with the same number are the same step.** -/
theorem eq_of_request_of_nreq_eq {k k' : ℕ} {req req' : ProofQuery Stmt Wit}
    (h : A.next (A.run R O k).hist = .request req) (h' : A.next (A.run R O k').hist = .request req')
    (hn : (A.run R O k).nreq = (A.run R O k').nreq) : k = k' := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · exact absurd hn (A.nreq_lt_of_request h hk).ne
  · exact hk
  · exact absurd hn (A.nreq_lt_of_request h' hk).ne'

/-- A step depends on the responder only through the reply to its own proof query. -/
theorem step_congr {s : GameState X Y Proof}
    (h : ∀ req, A.next s.hist = .request req → R s.nreq req s.oracle = R' s.nreq req s.oracle) :
    A.step R s = A.step R' s := by
  cases hn : A.next s.hist with
  | query x => rw [step_of_query hn, step_of_query hn]
  | request req => rw [step_of_request hn, step_of_request hn, h req hn]

/-- **Runs agree up to proof query `j`**: responders that agree on the proof queries numbered below `j`
give the same states while fewer than `j + 1` proof queries are made. -/
theorem run_eq_of_forall_lt {j : ℕ} (hR : ∀ i < j, R i = R' i) :
    ∀ k, (A.run R O k).nreq ≤ j → A.run R' O k = A.run R O k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : (A.run R O k).nreq ≤ j := (A.nreq_le_nreq_step _).trans h
    rw [run_succ, run_succ, run_eq_of_forall_lt hR k hk]
    refine (A.step_congr fun req hreq => ?_).symm
    have : (A.run R O k).nreq + 1 ≤ j := by
      rw [← A.nreq_step_of_request (R := R) hreq]
      exact h
    rw [hR _ (by omega)]

/-- **Runs that agree at a step agree later** when the responders agree on every proof query numbered
from the proof queries made at that step on. -/
theorem run_eq_of_forall_ge {k₀ j : ℕ} (h₀ : A.run R O k₀ = A.run R' O' k₀)
    (hj : j ≤ (A.run R O k₀).nreq) (hR : ∀ i, j ≤ i → R i = R' i) :
    ∀ k, k₀ ≤ k → A.run R O k = A.run R' O' k := by
  intro k hk
  induction hk with
  | refl => exact h₀
  | @step k hk ih =>
    rw [run_succ, run_succ, ← ih]
    refine A.step_congr fun req _ => ?_
    rw [hR _ (hj.trans (A.nreq_run_mono hk))]

/-- **A run depends on the reply to proof query `j` only at the step that makes it**: responders that
agree on every other proof query number, and on proof query `j` at every step of the run that makes it,
give the same states. -/
theorem run_eq_of_forall_ne {j : ℕ} (hR : ∀ i, i ≠ j → R i = R' i)
    (hj : ∀ k < m, ∀ req, (A.run R O k).nreq = j → A.next (A.run R O k).hist = .request req →
      R j req (A.run R O k).oracle = R' j req (A.run R O k).oracle) :
    ∀ k ≤ m, A.run R O k = A.run R' O k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [run_succ, run_succ, ← run_eq_of_forall_ne hR hj k (by omega)]
    refine A.step_congr fun req hreq => ?_
    by_cases hn : (A.run R O k).nreq = j
    · rw [hn]
      exact hj k (by omega) req hn hreq
    · rw [hR _ hn]

theorem accepts_eq_of_run_eq (h : A.run R O m = A.run R' O' m) : A.accepts R O = A.accepts R' O' := by
  rw [accepts, accepts, h]

end IAlg

/-- **The responder of an environment at the tape `ω`**: proof query number `i < Q` is answered by
the environment's reply to proof query `i`; later proof queries are answered by `none` and leave the oracle
unchanged. -/
def envResponder {Ω : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) (ω : Ω) :
    Responder X Y Stmt Wit Proof :=
  fun i req O => if h : i < Q then E.respond ω ⟨i, h⟩ req O else ⟨none, O⟩

/-- **The probability that `A` outputs `true` against the environment `E`**, over its tape. -/
noncomputable def IAlg.acceptProb {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Ω : Type} {Q : ℕ}
    (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) : ℝ≥0∞ :=
  Pr[ω ~ E.μ : A.accepts (envResponder E ω) (E.oracle₀ ω) = true]

/-- **A classical zero-knowledge adversary with `m` steps and a budget of `t` queries**: coins
drawn from `coins`, independently of the oracle and of the environment's tape, then the
deterministic algorithm `alg r`, which has a budget of `t` queries for every value `r` of the
coins. -/
structure Adversary (X Y Stmt Wit Proof : Type) (m t : ℕ) where
  /-- The coins. -/
  Coins : Type
  /-- The law of the coins. -/
  coins : PMF Coins
  /-- The algorithm at each value of the coins. -/
  alg : Coins → IAlg X Y Stmt Wit Proof m
  /-- Every algorithm makes at most `t` queries. -/
  budget : ∀ r, (alg r).Budget t

namespace Adversary

variable {m t : ℕ} (𝒜 : Adversary X Y Stmt Wit Proof m t)

/-- **The probability that `𝒜` outputs `true` against the environment `E`**, over its coins and
the environment's tape. -/
noncomputable def acceptProb {Ω : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) : ℝ :=
  (∑' r, 𝒜.coins r * (𝒜.alg r).acceptProb E).toReal

/-- **Averaging over the coins**: a bound on the difference of the acceptance probabilities of
every algorithm of `𝒜` against two environments bounds the difference of `𝒜`'s. -/
theorem abs_acceptProb_sub_le {Ω Ω' : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q)
    (E' : Env Ω' (ProofQuery Stmt Wit) Proof X Y Q) {ε : ℝ}
    (h : ∀ r, |((𝒜.alg r).acceptProb E).toReal - ((𝒜.alg r).acceptProb E').toReal| ≤ ε) :
    |𝒜.acceptProb E - 𝒜.acceptProb E'| ≤ ε :=
  PMF.abs_toReal_tsum_mul_sub_le 𝒜.coins (fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.toOuterMeasure_apply_le_one _ _) h

end Adversary

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins] [Fintype SimCoins]

/-- **The advantage of a classical adversary** with `Q` proof queries answered: the difference
(`GordieHowe.advantage`) of its acceptance probabilities against the real environment of the prover `P`
and the simulated environment of the simulator `S` (`GordieHowe.QROM.realEnv`,
`GordieHowe.QROM.simEnv`). -/
noncomputable def Adversary.advantage {m t : ℕ} (𝒜 : Adversary X Y Stmt Wit Proof m t)
    (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (Q : ℕ) : ℝ :=
  GordieHowe.advantage (𝒜.acceptProb (realEnv rel P Q)) (𝒜.acceptProb (simEnv rel S Q))

/-- **Zero knowledge in the classical random-oracle model** (Unruh 2017 Definition 6, p. 14, with
classical adversaries; the module docstring lists the knob settings): for all `m`, `t` and `Q`,
every classical adversary with `m` steps and a budget of `t` queries, whose first `Q` proof queries are
answered, has advantage at most `ε t Q` between the honest prover `P` and the simulator `S`. After
its steps the adversary reads the whole oracle in force, so its queries after the last proof query are
unbounded. -/
def ZeroKnowledge (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (S : NARG.SimulatorFn X Y Stmt Proof SimCoins)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (m t Q : ℕ) (𝒜 : Adversary X Y Stmt Wit Proof m t), 𝒜.advantage rel P S Q ≤ ε t Q

variable {rel} in
/-- A larger error bound. -/
theorem ZeroKnowledge.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ} (h : ZeroKnowledge rel P S ε)
    (hε : ∀ t Q, ε t Q ≤ ε' t Q) : ZeroKnowledge rel P S ε' :=
  fun m t Q 𝒜 => (h m t Q 𝒜).trans (hε t Q)

end GordieHowe.ROM.NIZK
