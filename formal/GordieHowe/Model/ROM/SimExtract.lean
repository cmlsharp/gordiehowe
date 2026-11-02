-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.Interactive
public import GordieHowe.SPBCS.SEProg
public import GordieHowe.Headline

@[expose] public section

/-!
# Simulation-sound extractability against query-bounded classical adversaries

The classical adversaries of the simulation-extraction game are the query-bounded adversaries of
`GordieHowe/Model/ROM/Interactive.lean` with proof queries in `X'` (statements sent to the simulation oracle) and
responses `Option Resp` (a simulated proof, or `none` once the proof queries are exhausted): coins
independent of the oracle, and at each step a run-time choice of a query or a proof query.

- `IAlg.tree`, `IAlg.toSEProg`: a deterministic algorithm unfolded into the tree `SEProg` of the
  simulation-extraction game (`GordieHowe/SPBCS/SEProg.lean`), with the queries along a branch cut at `t`
  (`queryBound_toSEProg`: every branch makes at most `t` queries). On a run that some oracle and
  the simulation oracle produce, a budget of `t` means the cut never applies.
- `IAlg.simResponder`: the simulation oracle as a responder on the oracle in force: proof query number
  `i < Q` runs the simulator with coins `c i` on the oracle in force, returns its proof and
  reprograms the oracle by its assignments; later proof queries are answered by `none`.
- `IAlg.out_compose_toSEProg`, `IAlg.reprogram_compose_toSEProg`: the composed run of the tree
  against a base oracle `h` (`SEProg.compose`) has the output of the interactive run against
  `simResponder` from `h`, and its final assignments give that run's final oracle in force. So the
  game run on `toSEProg` is the interactive game.
- `QueryBoundedAdversary.tsum_le` averages the deterministic bound over the coins.
- `GordieHowe.SPBCS.SimExtractionAdversaryROM`: these adversaries in the game of the spBCS
  compiler, with their trees (`prog`) and the probability that one
  wins while the straight-line extractor fails (`winsNotExtracts`,
  `GordieHowe/SPBCS/SimExtractROM.lean`). `GordieHowe.SPBCS.weak_online_simulation_extractability_rom_basic`
  (`GordieHowe/SPBCS/SimExtractROM.lean`) bounds them for the spBCS compiler, and
  `GordieHowe.SPBCS.KnowledgeGuarantees.simExtractabilityROM` states the headline.
-/

namespace GordieHowe.ROM

open GordieHowe.SPBCS GordieHowe.QROM Quantum GordieHowe.QROM
open scoped ENNReal NNReal

namespace IAlg

variable {A B Req Resp Out : Type} {m : ℕ} (𝒜 : IAlg A B Req (Option Resp) Out m)

/-! ### The tree of a deterministic algorithm -/

/-- **The tree of the remaining `j` steps** from the replies `hist` after `used` queries, with the
queries cut at `t`: a query when `used < t`, otherwise the output; a proof query with a branch for
every response; after the steps, the output. -/
def tree (t : ℕ) : ℕ → List (Reply B (Option Resp)) → ℕ → SEProg A B Req Resp Out
  | 0, hist, _ => .done (𝒜.out hist)
  | j + 1, hist, used =>
    match 𝒜.next hist with
    | .query a =>
      if used < t then .query a fun b => tree t j (hist ++ [.answer b]) (used + 1)
      else .done (𝒜.out hist)
    | .request r => .request r fun o => tree t j (hist ++ [.response o]) used

/-- **The algorithm as a tree** with at most `t` queries on every branch. -/
def toSEProg (t : ℕ) : SEProg A B Req Resp Out := 𝒜.tree t m [] 0

theorem queryBound_tree (t : ℕ) :
    ∀ j hist used, used ≤ t → (𝒜.tree t j hist used).QueryBound (t - used)
  | 0, hist, used, _ => .done _ _
  | j + 1, hist, used, hu => by
    unfold tree
    split
    · split_ifs with hlt
      · have he : t - used = (t - (used + 1)) + 1 := by omega
        rw [he]
        exact .query _ _ _ fun b => queryBound_tree t j _ _ (by omega)
      · exact .done _ _
    · exact .request _ _ _ fun o => queryBound_tree t j _ _ hu

/-- **Every branch of `toSEProg t` makes at most `t` queries.** -/
theorem queryBound_toSEProg (t : ℕ) : (𝒜.toSEProg t).QueryBound t := by
  simpa [toSEProg] using 𝒜.queryBound_tree t m [] 0 (Nat.zero_le _)

/-! ### The interactive run against the simulation oracle -/

variable (R : Responder A B Req (Option Resp)) (O : A → B)

/-- **The number of queries among the first `k` steps** of the run. -/
def queriesBefore (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun k' => (𝒜.next (𝒜.run R O k').hist).IsQuery).card

theorem queriesBefore_succ (k : ℕ) :
    𝒜.queriesBefore R O (k + 1) =
      𝒜.queriesBefore R O k + if (𝒜.next (𝒜.run R O k).hist).IsQuery then 1 else 0 := by
  rw [queriesBefore, queriesBefore, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem queriesBefore_mono {k k' : ℕ} (h : k ≤ k') : 𝒜.queriesBefore R O k ≤ 𝒜.queriesBefore R O k' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem queriesBefore_steps : 𝒜.queriesBefore R O m = 𝒜.queryCount R O := rfl

variable [DecidableEq A] {SC : Type} (Sim : Req → SC → OracleProg A B (NARG.SimOutput A B Resp))
  {Q : ℕ} (c : Fin Q → SC)

/-- **The simulation oracle as a responder**: proof query number `i < Q` runs the simulator with coins
`c i` on the oracle in force `O`, returns its proof and reprograms `O` by its assignments; later
proof queries are answered by `none` and leave the oracle unchanged. -/
def simResponder : Responder A B Req (Option Resp) := fun i r O =>
  if hi : i < Q then
    (some ((Sim r (c ⟨i, hi⟩)).run O).proof, O.reprogram ((Sim r (c ⟨i, hi⟩)).run O).assignments)
  else (none, O)

/-- **The composed run of the tree from step `k`**: with the assignments `ass` giving the oracle in
force at step `k` and a proof query counter `i` that agrees with the run's below `Q`, the composed run
of the remaining `m - k` steps has the interactive run's output, and its final assignments give the
final oracle in force, when the run has at most `t` queries. -/
theorem compose_tree {t : ℕ} (ht : 𝒜.queryCount (simResponder Sim c) O ≤ t) :
    ∀ j k (ass : List (Assignment A B)) (i : ℕ) (qs : List Req), k + j = m →
      (𝒜.run (simResponder Sim c) O k).oracle = O.reprogram ass →
      min i Q = min (𝒜.run (simResponder Sim c) O k).nreq Q →
      ((SEProg.compose Sim c (𝒜.tree t j (𝒜.run (simResponder Sim c) O k).hist
          (𝒜.queriesBefore (simResponder Sim c) O k)) ass i qs).run O).out =
          𝒜.output (simResponder Sim c) O ∧
      O.reprogram ((SEProg.compose Sim c (𝒜.tree t j (𝒜.run (simResponder Sim c) O k).hist
          (𝒜.queriesBefore (simResponder Sim c) O k)) ass i qs).run O).ass =
          (𝒜.run (simResponder Sim c) O m).oracle
  | 0, k, ass, i, qs, hk, hO, _ => by
    obtain rfl : k = m := by omega
    exact ⟨rfl, hO.symm⟩
  | j + 1, k, ass, i, qs, hk, hO, hi => by
    set R := simResponder Sim c
    have hstep := 𝒜.run_succ R O k
    have hqb := 𝒜.queriesBefore_succ R O k
    unfold tree
    split
    · rename_i a ha
      have hq : (Action.query a : Action A Req).IsQuery := trivial
      have hu : 𝒜.queriesBefore R O (k + 1) = 𝒜.queriesBefore R O k + 1 := by
        rw [hqb, ha]
        simp [hq]
      have hlt : 𝒜.queriesBefore R O k < t := by
        have h1 := 𝒜.queriesBefore_mono R O (show k + 1 ≤ m by omega)
        rw [hu, queriesBefore_steps] at h1
        omega
      simp only [hlt, ↓reduceIte, SEProg.compose, OracleProg.run_query]
      have hans : (lastAssign ass a).getD (O a) = (𝒜.run R O k).oracle a := by
        rw [hO, reprogram_apply_eq_lastAssign]
      have hk1 : 𝒜.run R O (k + 1) =
          ⟨(𝒜.run R O k).hist ++ [.answer ((lastAssign ass a).getD (O a))], (𝒜.run R O k).oracle,
            (𝒜.run R O k).nreq⟩ := by
        rw [hstep, step, ha, hans]
      have ih := compose_tree ht j (k + 1) ass i qs (by omega) (by rw [hk1]; exact hO)
        (by rw [hk1]; exact hi)
      rw [hk1, hu] at ih
      exact ih
    · rename_i r hr
      have hu : 𝒜.queriesBefore R O (k + 1) = 𝒜.queriesBefore R O k := by
        rw [hqb, hr]
        simp [Action.IsQuery]
      simp only [SEProg.compose]
      split_ifs with hiQ
      · have hn : (𝒜.run R O k).nreq = i := by omega
        rw [OracleProg.run_bind, SEProg.run_inForce, ← hO]
        set so := (Sim r (c ⟨i, hiQ⟩)).run (𝒜.run R O k).oracle
        have hk1 : 𝒜.run R O (k + 1) =
            ⟨(𝒜.run R O k).hist ++ [.response (some so.proof)],
              O.reprogram (ass ++ so.assignments), (𝒜.run R O k).nreq + 1⟩ := by
          rw [hstep, step, hr]
          simp only [R, simResponder, hn, hiQ, ↓reduceDIte, reprogram_append, ← hO]
          rfl
        have ih := compose_tree ht j (k + 1) (ass ++ so.assignments) (i + 1) (qs ++ [r])
          (by omega) (by rw [hk1]) (by rw [hk1]; simp only; omega)
        rw [hk1, hu] at ih
        exact ih
      · have hn : ¬ (𝒜.run R O k).nreq < Q := by omega
        have hk1 : 𝒜.run R O (k + 1) =
            ⟨(𝒜.run R O k).hist ++ [.response none], (𝒜.run R O k).oracle,
              (𝒜.run R O k).nreq + 1⟩ := by
          rw [hstep, step, hr]
          simp only [R, simResponder, hn, ↓reduceDIte]
        have ih := compose_tree ht j (k + 1) ass i qs (by omega) (by rw [hk1]; exact hO)
          (by rw [hk1]; simp only; omega)
        rw [hk1, hu] at ih
        exact ih

/-- **The composed run of `toSEProg` has the output of the interactive run** against the
simulation oracle from the base oracle `O`, for an algorithm with a budget of `t`. -/
theorem out_compose_toSEProg {t : ℕ} (ht : 𝒜.Budget t) :
    ((SEProg.compose Sim c (𝒜.toSEProg t) [] 0 []).run O).out = 𝒜.output (simResponder Sim c) O :=
  (𝒜.compose_tree O Sim c (ht _ O) m 0 [] 0 [] (by omega) rfl rfl).1

/-- **The final assignments of the composed run of `toSEProg` give the interactive run's final
oracle in force.** -/
theorem reprogram_compose_toSEProg {t : ℕ} (ht : 𝒜.Budget t) :
    O.reprogram ((SEProg.compose Sim c (𝒜.toSEProg t) [] 0 []).run O).ass =
      (𝒜.run (simResponder Sim c) O m).oracle :=
  (𝒜.compose_tree O Sim c (ht _ O) m 0 [] 0 [] (by omega) rfl rfl).2

end IAlg

end GordieHowe.ROM

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t} {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

/-- **The query-bounded classical adversaries of the simulation-extraction game with output in
`O`** (`def:adversary` in the ROM, `ROM.QueryBoundedAdversary`): coins independent of the oracle,
then at each step a query of the oracle in force or a proof query of a statement in `X'` (answered
by a simulated proof, or `none` once the proof queries are exhausted), at most `tq` queries on every
run, and an output in `O`: a claim, or a claim and the auxiliary output `Z` of `def:bcs-se`. -/
abbrev SimExtractionAdversaryROM (X' O : Type) (tq : ℕ) : Type 1 :=
  ROM.QueryBoundedAdversary (Query k kN kS L) (Out k e) X' (Option (M.Response B)) O tq

namespace SimExtractionAdversaryROM

variable {M B} {X' O : Type} {tq : ℕ} (𝒜 : M.SimExtractionAdversaryROM B X' O tq)

/-- **The algorithm at the coins `r` as a tree of the simulation-extraction game**
(`ROM.IAlg.toSEProg`): its run in the game is the interactive run against the simulation oracle
(`ROM.IAlg.out_compose_toSEProg`, `ROM.IAlg.reprogram_compose_toSEProg`). -/
abbrev prog (r : 𝒜.Coins) : SEProg (Query k kN kS L) (Out k e) X' (M.Response B) O :=
  (𝒜.alg r).toSEProg tq

end SimExtractionAdversaryROM

end

end GordieHowe.SPBCS
