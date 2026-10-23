-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.Model

@[expose] public section

/-!
# Query-bounded classical adversaries

The one adversary class of the classical random-oracle model (the paper's Definition 6.1,
`def:adversary`: in the ROM, a classical probabilistic oracle algorithm with coins sampled
independently of the oracle and the same bounds for every choice of its coins; CY24 Remark 5.1.4, p.
49, for the coins): a law on coins independent of the oracle, and for each value of the coins a
deterministic interactive algorithm that, at each of its `steps` steps, chooses from the replies so
far whether to query the oracle in force at a point or to send a request, and after its steps
outputs a value computed from the replies. Its query budget is per run: against every responder and
every oracle at most `t` of its steps are queries; requests are not counted. The name follows the
paper's "query-bounded adversaries" (Definition 6.1).

- `Action A Req`, `Reply B Resp`: a query or a request, and the oracle's answer or the response.
- `IAlg A B Req Resp Out m`: the deterministic algorithm with `m` steps (`next`, `out`).
- `Responder`: the answer to request number `i` on the oracle in force, with the oracle after it
  (a simulator may reprogram it).
- `IAlg.run`, `IAlg.output`, `IAlg.queryCount`, `IAlg.Budget`: the run, its output, its number of
  queries and the budget.
- `QueryBoundedAdversary A B Req Resp Out t`: coins, then an algorithm with a budget of `t`.

The other forms are instances or derived by proved maps:
- knowledge soundness: requests in `Empty` (`IAlg.toAlg`, `QueryBoundedAdversary.toAdversary`:
  a request-free member is a `ROM.Adversary` of `GordieHowe/Model/ROM/Model.lean` with the same output against
  every oracle, `output_toAlg`);
- zero knowledge: `GordieHowe/Model/ROM/InteractiveNIZK.lean` (the equivalence with `ROM.NIZK.Adversary`);
- simulation-sound extractability: `GordieHowe/Model/ROM/SimExtract.lean` (the map to `SEProg`).

`QueryBoundedAdversary.tsum_le_tsum_add` is the averaging over the coins that reduces every bound
to the deterministic algorithms.
-/

namespace GordieHowe.ROM

open scoped ENNReal

/-- **An action of an interactive classical adversary**: a query of the oracle in force at `a`,
or a request `r`. -/
inductive Action (A Req : Type) where
  /-- A query of the oracle in force at `a`. -/
  | query (a : A)
  /-- A request. -/
  | request (r : Req)

/-- **What an interactive classical adversary receives**: the oracle's answer to a query, or the
response to a request. -/
inductive Reply (B Resp : Type) where
  /-- The oracle's answer to a query. -/
  | answer (b : B)
  /-- The response to a request. -/
  | response (o : Resp)

/-- The action is a query. -/
def Action.IsQuery {A Req : Type} : Action A Req → Prop
  | .query _ => True
  | .request _ => False

instance {A Req : Type} (a : Action A Req) : Decidable a.IsQuery := by
  cases a <;> unfold Action.IsQuery <;> infer_instance

/-- **A deterministic interactive classical algorithm with `m` steps**: at each step the action
`next replies` computed from the replies so far, and after the `m` steps the output `out replies`.
-/
structure IAlg (A B Req Resp Out : Type) (m : ℕ) where
  /-- The next action, from the replies so far. -/
  next : List (Reply B Resp) → Action A Req
  /-- The output, from the replies. -/
  out : List (Reply B Resp) → Out

/-- **A responder**: the response to request number `i` with request `r` on the oracle in force
`O`, and the oracle after the request. -/
abbrev Responder (A B Req Resp : Type) : Type :=
  ℕ → Req → (A → B) → Resp × (A → B)

/-- **The state of a run**: the replies so far, the oracle in force and the number of requests
made. -/
@[ext]
structure GameState (A B Resp : Type) where
  /-- The replies so far. -/
  hist : List (Reply B Resp)
  /-- The oracle in force. -/
  oracle : A → B
  /-- The number of requests made. -/
  nreq : ℕ

namespace IAlg

variable {A B Req Resp Out : Type} {m : ℕ} (𝒜 : IAlg A B Req Resp Out m)

/-- **One step against the responder `R`**: a query reads the oracle in force; request number
`s.nreq` is answered by `R`, which gives the response and the oracle after it. -/
def step (R : Responder A B Req Resp) (s : GameState A B Resp) : GameState A B Resp :=
  match 𝒜.next s.hist with
  | .query a => ⟨s.hist ++ [.answer (s.oracle a)], s.oracle, s.nreq⟩
  | .request r => ⟨s.hist ++ [.response (R s.nreq r s.oracle).1], (R s.nreq r s.oracle).2, s.nreq + 1⟩

/-- **The run of `𝒜` against `R` from the oracle `O`**: the state after `k` steps. -/
def run (R : Responder A B Req Resp) (O : A → B) : ℕ → GameState A B Resp
  | 0 => ⟨[], O, 0⟩
  | k + 1 => 𝒜.step R (run R O k)

/-- **The output of `𝒜` against `R` from `O`**: `out` of the replies after its `m` steps. -/
def output (R : Responder A B Req Resp) (O : A → B) : Out := 𝒜.out (𝒜.run R O m).hist

/-- **The number of queries of the run**: the steps below `m` whose action is a query. -/
def queryCount (R : Responder A B Req Resp) (O : A → B) : ℕ :=
  ((Finset.range m).filter fun k => (𝒜.next (𝒜.run R O k).hist).IsQuery).card

/-- **A budget of `t` queries**: against every responder and every oracle, at most `t` of the `m`
steps are queries; requests are not counted. -/
def Budget (t : ℕ) : Prop := ∀ R O, 𝒜.queryCount R O ≤ t

theorem run_succ (R : Responder A B Req Resp) (O : A → B) (k : ℕ) :
    𝒜.run R O (k + 1) = 𝒜.step R (𝒜.run R O k) := rfl


section MapOut

variable {Out' : Type}

/-- **The algorithm with its output relabelled by `f`**: the same actions. -/
def mapOut (f : Out → Out') (𝒜 : IAlg A B Req Resp Out m) : IAlg A B Req Resp Out' m :=
  ⟨𝒜.next, fun l => f (𝒜.out l)⟩

variable (f : Out → Out')

/-- Relabelling the output keeps the run. -/
theorem run_mapOut (R : Responder A B Req Resp) (O : A → B) :
    ∀ k, (𝒜.mapOut f).run R O k = 𝒜.run R O k
  | 0 => rfl
  | k + 1 => by
    rw [run_succ, run_succ, run_mapOut R O k]
    rfl

/-- Relabelling the output keeps the budget. -/
theorem budget_mapOut {t : ℕ} (h : 𝒜.Budget t) : (𝒜.mapOut f).Budget t := fun R O => by
  have hc : (𝒜.mapOut f).queryCount R O = 𝒜.queryCount R O := by
    simp only [queryCount, run_mapOut]
    rfl
  rw [hc]
  exact h R O

/-- The output of the relabelled algorithm is the relabelled output. -/
theorem output_mapOut (R : Responder A B Req Resp) (O : A → B) :
    (𝒜.mapOut f).output R O = f (𝒜.output R O) := by
  rw [output, output, run_mapOut]
  rfl

end MapOut

end IAlg

/-- **A query-bounded classical adversary** with queries in `A`, answers in `B`, requests in
`Req`, responses in `Resp` and output in `Out`: coins drawn from `coins`, independently of the
oracle (and of any responder's randomness), then the deterministic algorithm `alg r` with `steps`
steps and a budget of `t` queries for every value `r` of the coins. -/
structure QueryBoundedAdversary (A B Req Resp Out : Type) (t : ℕ) where
  /-- The number of steps. -/
  steps : ℕ
  /-- The coins. -/
  Coins : Type
  /-- The law of the coins. -/
  coins : PMF Coins
  /-- The algorithm at each value of the coins. -/
  alg : Coins → IAlg A B Req Resp Out steps
  /-- Every algorithm makes at most `t` queries on every run. -/
  budget : ∀ r, (alg r).Budget t

namespace QueryBoundedAdversary

variable {A B Req Resp Out : Type} {t : ℕ} (𝒜 : QueryBoundedAdversary A B Req Resp Out t)

/-- **Averaging over the coins**: bounds `x r ≤ y r + c` at every value of the coins give
`∑ x ≤ ∑ y + c`, so a bound on every deterministic algorithm bounds the adversary. -/
theorem tsum_le_tsum_add {x y : 𝒜.Coins → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ r, x r ≤ y r + c) :
    ∑' r, 𝒜.coins r * x r ≤ ∑' r, 𝒜.coins r * y r + c := by
  calc ∑' r, 𝒜.coins r * x r ≤ ∑' r, (𝒜.coins r * y r + 𝒜.coins r * c) :=
        ENNReal.tsum_le_tsum fun r => by rw [← mul_add]; gcongr; exact h r
    _ = ∑' r, 𝒜.coins r * y r + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Averaging over the coins, without a second term**: `x r ≤ c` at every value of the coins
gives `∑ x ≤ c`. -/
theorem tsum_le {x : 𝒜.Coins → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ r, x r ≤ c) :
    ∑' r, 𝒜.coins r * x r ≤ c := by
  have := 𝒜.tsum_le_tsum_add (y := fun _ => 0) (c := c) fun r => (h r).trans_eq (zero_add c).symm
  simpa using this

end QueryBoundedAdversary

/-! ### Request-free algorithms -/

/-- **An algorithm with its output mapped by `f`**: the same queries.

Running time: that of `𝒜`, then one evaluation of `f`; polynomial when both are. This running time
is argued here, not proved in Lean. -/
def Alg.mapOut {A B C C' : Type*} {t : ℕ} (f : C → C') (𝒜 : Alg A B C t) : Alg A B C' t :=
  ⟨𝒜.next, f ∘ 𝒜.out⟩

theorem Alg.queries_mapOut {A B C C' : Type*} {t : ℕ} (f : C → C') (𝒜 : Alg A B C t)
    (h : A → B) : ∀ i, (𝒜.mapOut f).queries h i = 𝒜.queries h i
  | 0 => rfl
  | i + 1 => by
    rw [Alg.queries_succ, Alg.queries_succ, Alg.queryAt, Alg.queryAt, Alg.queries_mapOut f 𝒜 h i]
    rfl

theorem Alg.output_mapOut {A B C C' : Type*} {t : ℕ} (f : C → C') (𝒜 : Alg A B C t)
    (h : A → B) : (𝒜.mapOut f).output h = f (𝒜.output h) := by
  rw [Alg.output, Alg.output, Alg.queries_mapOut]
  rfl

/-- The first `i ≤ j` of the first `j` queries are the first `i` queries. -/
theorem Alg.take_queries {A B C : Type*} {t : ℕ} (𝒜 : Alg A B C t) (h : A → B) {i j : ℕ}
    (hij : i ≤ j) : (𝒜.queries h j).take i = 𝒜.queries h i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [Alg.queries_succ, List.take_append_of_le_length (by simp; omega), ih]

namespace IAlg

variable {A B Resp Out : Type} {m : ℕ} (𝒜 : IAlg A B Empty Resp Out m)

/-- The responder of a request-free algorithm (there are no requests). -/
def noRequests : Responder A B Empty Resp := fun _ r _ => r.elim

/-- The query of a request-free action. -/
def Action.queryOf {A : Type} : Action A Empty → A
  | .query a => a
  | .request r => r.elim

theorem Action.eq_query_queryOf {A : Type} : ∀ a : Action A Empty, a = .query (Action.queryOf a)
  | .query _ => rfl
  | .request r => r.elim

/-- **A request-free algorithm as a `t`-query algorithm** (`ROM.Alg`): query `i` is the query of
the action at the answers so far; the output reads the first `m` answers. For `m ≤ t` the queries
after step `m` are the algorithm's actions on the longer histories, whose answers `out` ignores. -/
def toAlg (t : ℕ) : Alg A B Out t where
  next ans := Action.queryOf (𝒜.next (ans.map .answer))
  out ans := 𝒜.out ((ans.take m).map .answer)

/-- **The run of a request-free algorithm is the run of `toAlg`**: after `k` steps the replies are
the answers to the first `k` queries of `toAlg`, the oracle is unchanged and no request was made. -/
theorem run_eq_toAlg (R : Responder A B Empty Resp) (O : A → B) (t : ℕ) :
    ∀ k, 𝒜.run R O k = ⟨((𝒜.toAlg t).queries O k).map fun a => .answer (O a), O, 0⟩
  | 0 => rfl
  | k + 1 => by
    rw [run_succ, run_eq_toAlg R O t k, Alg.queries_succ, step]
    split
    · rename_i a ha
      have hqa : (𝒜.toAlg t).queryAt O k = a := by
        change Action.queryOf (𝒜.next ((((𝒜.toAlg t).queries O k).map O).map .answer)) = a
        rw [List.map_map]
        exact congrArg Action.queryOf ha
      simp only [List.map_append, List.map_cons, List.map_nil, hqa]
    · rename_i r _
      exact r.elim

/-- Every step of a request-free algorithm is a query. -/
theorem queryCount_eq (R : Responder A B Empty Resp) (O : A → B) : 𝒜.queryCount R O = m := by
  rw [queryCount, Finset.filter_true_of_mem, Finset.card_range]
  intro k _
  rw [Action.eq_query_queryOf (𝒜.next _)]
  trivial

/-- **A request-free algorithm with a budget of `t` has at most `t` steps.** -/
theorem steps_le [Nonempty B] {t : ℕ} (h : 𝒜.Budget t) : m ≤ t := by
  have hO : Nonempty (A → B) := inferInstance
  have := h noRequests hO.some
  rwa [queryCount_eq] at this

/-- **`toAlg` has the output of the algorithm** against every oracle, for `m ≤ t`. -/
theorem output_toAlg {t : ℕ} (hm : m ≤ t) (R : Responder A B Empty Resp) (O : A → B) :
    (𝒜.toAlg t).output O = 𝒜.output R O := by
  rw [Alg.output, output, run_eq_toAlg 𝒜 R O t]
  change 𝒜.out ((((𝒜.toAlg t).queries O t).map O).take m |>.map .answer) = _
  rw [← List.map_take, Alg.take_queries _ _ hm, List.map_map]
  rfl

end IAlg

namespace QueryBoundedAdversary

variable {A B Resp Out : Type} {t : ℕ} (𝒜 : QueryBoundedAdversary A B Empty Resp Out t)

/-- **A request-free query-bounded adversary as a `ROM.Adversary`**: the same coins, and
`IAlg.toAlg` at each value. -/
def toAdversary : Adversary A B Out t where
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).toAlg t

end QueryBoundedAdversary

end GordieHowe.ROM
