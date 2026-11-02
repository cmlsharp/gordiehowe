-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractROM
public import GordieHowe.Model.ROM.Lazy
public import GordieHowe.SPBCS.Extraction.OnlineExtract
public import GordieHowe.Headline

@[expose] public section

/-!
# Weak online simulation extractability of the spBCS compiler in the classical ROM

The paper's `def:bcs-se` in the ROM, for the spBCS compiler (paper `thm:bcs-se`(2)): against
the query-bounded classical adversaries of `def:adversary` (`ROM.QueryBoundedAdversary`) with an
auxiliary output `Z`, an extractor that serves as the oracle of the execution satisfies the oracle
simulation condition with error `0` and the extraction condition with the classical error
`simExtractionErrorROM`.

- `GordieHowe.OracleProg.runAnswers`, `runAnswers_of_prefix`: a classical oracle program run on a list
  of answers; on a list that starts with the answers of an oracle at its queries it returns its
  result against that oracle.
- `SEProg.mapOut`, `SEProg.Result.mapOut`, `run_compose_mapOut`, `trace_compose_mapOut`;
  `ROM.IAlg.mapOut`, `ROM.IAlg.toSEProg_mapOut`, `ROM.QueryBoundedAdversary.mapOut`: relabelling
  the adversary's output, which changes neither the queries nor the simulation oracle's answers.
- `GordieHowe.SPBCS.SimExtractionAdversaryROM`: the classical adversaries of the game with output in `O` (a
  claim and an auxiliary output in `Z`).
- `romGameAux`: the game of such an adversary as one classical program against the base oracle:
  the composed run with the simulation oracle (`SEProg.compose`), then the verifier's queries.
- `SimExtractionAdversaryROM.simLaw`: the law of the simulated execution's output (claim,
  auxiliary output, queried statements) and verdict, over a uniform base oracle.
- `SimExtractionAdversaryROM.extractionRun`, `extractionLaw`: the extractor's execution, which
  lazily samples the base oracle at the game's queries (`ROM.Alg.lazyRun`), answers the assigned
  inputs from the assignment list as the game does, and reads the output from the answers; the
  extractor `dbExtract` reads the table of the lazy run.
- `GordieHowe.SPBCS.WeakOnlineSimExtractsROM`, `GordieHowe.SPBCS.WeakOnlineSimulationExtractableROM`: the two conditions of
  `def:bcs-se` in the ROM, the oracle simulation condition as the equality of the two laws at every
  value of the adversary's and the simulator's coins.
- `GordieHowe.SPBCS.weak_online_simulation_extractability_rom` (paper `thm:bcs-se`(2)): the spBCS compiler
  satisfies them at error `simExtractionErrorROM kq (maxError ε) q`.
-/

namespace GordieHowe.OracleProg

variable {A B R : Type*}

/-- **A program run on a list of answers**: the answers are given to its queries in order; `none`
when they run out before it returns. -/
def runAnswers : OracleProg A B R → List B → Option R
  | pure r, _ => some r
  | query _ _, [] => none
  | query _ k, b :: l => runAnswers (k b) l

/-- **A program run on answers that start with an oracle's answers at its queries** returns its
result against the oracle. -/
theorem runAnswers_of_prefix (h : A → B) :
    ∀ (p : OracleProg A B R) {l : List B}, (p.trace h).map h <+: l → p.runAnswers l = some (p.run h)
  | pure _, _, _ => rfl
  | query a k, [], hl => by
    simp only [trace_query, List.map_cons, List.prefix_nil] at hl
    exact absurd hl (List.cons_ne_nil _ _)
  | query a k, b :: l, hl => by
    rw [trace_query, List.map_cons, List.cons_prefix_cons] at hl
    obtain ⟨rfl, hl⟩ := hl
    exact runAnswers_of_prefix h (k (h a)) hl

/-- **The first queries of a program's padded trace** are the queries of a prefix of its trace. -/
theorem prefix_map_paddedTrace (h : A → B) (pad : A) (p : OracleProg A B R) {l l' : List A}
    (hp : p.trace h = l ++ l') {K : ℕ} (hK : l.length ≤ K) :
    l <+: (List.range K).map (p.paddedTrace h pad) := by
  have ht : ((List.range K).map (p.paddedTrace h pad)).take l.length = l := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left hK]
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.getElem_map, List.getElem_range, paddedTrace, hp,
      List.getElem?_append_left h₂, List.getElem?_eq_getElem h₂, Option.getD_some]
  rw [← ht]
  exact List.take_prefix _ _

end GordieHowe.OracleProg

namespace GordieHowe.SPBCS.SEProg

open GordieHowe.QROM Quantum GordieHowe.QROM

variable {A B Req Resp C C' : Type}

/-- **The adversary tree with its output relabelled by `f`**: the same queries and proof queries. -/
def mapOut (f : C → C') : SEProg A B Req Resp C → SEProg A B Req Resp C'
  | .done c => .done (f c)
  | .query a k => .query a fun b => mapOut f (k b)
  | .request r k => .request r fun o => mapOut f (k o)

/-- **The result of a composed run with its output relabelled by `f`.** -/
def Result.mapOut (f : C → C') (res : Result A B Req C) : Result A B Req C' :=
  ⟨f res.out, res.ass, res.queried⟩

variable [DecidableEq A] {SC : Type} (Sim : Req → SC → OracleProg A B (NARG.SimOutput A B Resp))
  {Q : ℕ} (c : Fin Q → SC) (f : C → C') (h : A → B)

/-- **The composed run of a relabelled tree** has the relabelled result. -/
theorem run_compose_mapOut : ∀ (p : SEProg A B Req Resp C) ass i qs,
    (compose Sim c (p.mapOut f) ass i qs).run h = ((compose Sim c p ass i qs).run h).mapOut f
  | .done _, _, _, _ => rfl
  | .query a k, ass, i, qs => by
    simp only [mapOut, compose, OracleProg.run_query]
    exact run_compose_mapOut (k _) ass i qs
  | .request r k, ass, i, qs => by
    simp only [mapOut, compose]
    split_ifs
    · rw [OracleProg.run_bind, OracleProg.run_bind]
      exact run_compose_mapOut (k _) _ _ _
    · exact run_compose_mapOut (k none) ass i qs

/-- **The composed run of a relabelled tree makes the same queries.** -/
theorem trace_compose_mapOut : ∀ (p : SEProg A B Req Resp C) ass i qs,
    (compose Sim c (p.mapOut f) ass i qs).trace h = (compose Sim c p ass i qs).trace h
  | .done _, _, _, _ => rfl
  | .query a k, ass, i, qs => by
    simp only [mapOut, compose, OracleProg.trace_query]
    rw [trace_compose_mapOut (k _) ass i qs]
  | .request r k, ass, i, qs => by
    simp only [mapOut, compose]
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_bind, trace_compose_mapOut (k _) _ _ _]
    · exact trace_compose_mapOut (k none) ass i qs

end GordieHowe.SPBCS.SEProg

namespace GordieHowe.ROM

/-! ### Relabelling an adversary's output -/

namespace IAlg

variable {A B Req Resp Out Out' : Type} {m : ℕ}

variable (f : Out → Out')

variable {Resp' : Type} (𝒜' : IAlg A B Req (Option Resp') Out m)

theorem tree_mapOut (t : ℕ) :
    ∀ j hist used, (𝒜'.mapOut f).tree t j hist used = (𝒜'.tree t j hist used).mapOut f
  | 0, _, _ => rfl
  | j + 1, hist, used => by
    change (match 𝒜'.next hist with
      | .query a =>
        if used < t then .query a fun b => (𝒜'.mapOut f).tree t j (hist ++ [.answer b]) (used + 1)
        else .done (f (𝒜'.out hist))
      | .request r => .request r fun o => (𝒜'.mapOut f).tree t j (hist ++ [.response o]) used) =
      SPBCS.SEProg.mapOut f (match 𝒜'.next hist with
      | .query a =>
        if used < t then .query a fun b => 𝒜'.tree t j (hist ++ [.answer b]) (used + 1)
        else .done (𝒜'.out hist)
      | .request r => .request r fun o => 𝒜'.tree t j (hist ++ [.response o]) used)
    split
    · split_ifs
      · simp only [SPBCS.SEProg.mapOut, tree_mapOut t j]
      · rfl
    · simp only [SPBCS.SEProg.mapOut, tree_mapOut t j]

/-- **The tree of the relabelled algorithm** is the tree with its output relabelled. -/
theorem toSEProg_mapOut (t : ℕ) : (𝒜'.mapOut f).toSEProg t = (𝒜'.toSEProg t).mapOut f :=
  𝒜'.tree_mapOut f t m [] 0

end IAlg

namespace QueryBoundedAdversary

variable {A B Req Resp Out Out' : Type} {t : ℕ}

/-- **The adversary with its output relabelled by `f`**: the same coins and algorithms with their
outputs relabelled. -/
def mapOut (f : Out → Out') (𝒜 : QueryBoundedAdversary A B Req Resp Out t) :
    QueryBoundedAdversary A B Req Resp Out' t where
  steps := 𝒜.steps
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).mapOut f
  budget r := (𝒜.alg r).budget_mapOut f (𝒜.budget r)

end QueryBoundedAdversary

end GordieHowe.ROM

namespace GordieHowe.SPBCS

/-- **The output of an execution of the simulation-extraction game**: the adversary's claim and
auxiliary output, and the statements it queried. -/
structure SimExtractionView (Cl Z X' : Type) where
  /-- The adversary's claim. -/
  claim : Cl
  /-- The adversary's auxiliary output. -/
  aux : Z
  /-- The statements sent to the simulator. -/
  queried : List X'

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e) (B : ℕ) [∀ j i, Fintype ((M.comp j).MessageWrite i)]

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' Z : Type} {C : Type}
  (sp : X' → SaltedCoins (FiatShamirSalt kS) C →
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)))
  {Q : ℕ} (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C)

/-- **The game of an adversary tree with an auxiliary output, as a classical program**: the
composed run with the simulation oracle, then the spBCS verifier's queries on the claim under
the final oracle. -/
noncomputable def romGameAux
    (p : SEProg (Query k kN kS L) (Out k e) X' (M.Response B) (Claim X M.NIProof × Z)) :
    OracleProg (Query k kN kS L) (Out k e)
      (SEProg.Result (Query k kN kS L) (Out k e) X' (Claim X M.NIProof × Z)) :=
  (SEProg.compose sp c p [] 0 []).bind fun res =>
    (SEProg.inForce res.ass (M.queryProg res.out.1.stmt res.out.1.proof (Qs res.out.1.stmt))).bind
      fun _ => .pure res

/-- **The output and verdict of a composed run's result** against the base oracle `O`: the claim,
the auxiliary output and the queried statements, and whether the spBCS verifier accepts
the claim under the final oracle `O` reprogrammed by the run's assignments; `none` when there is
no result. -/
def outcomeOf (O : Query k kN kS L → Out k e) :
    Option (SEProg.Result (Query k kN kS L) (Out k e) X' (Claim X M.NIProof × Z)) →
      NARG.VerifiedOutput (SimExtractionView (Claim X M.NIProof) Z X')
  | some res => ⟨some ⟨res.out.1, res.out.2, res.queried⟩,
      M.Accepts (O.reprogram res.ass) res.out.1.stmt res.out.1.proof (Qs res.out.1.stmt)⟩
  | none => ⟨none, False⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable {M B Qs sp c} in
/-- **The game of a tree makes the queries of the game of the tree without its auxiliary
output.** -/
theorem trace_romGameAux
    (p : SEProg (Query k kN kS L) (Out k e) X' (M.Response B) (Claim X M.NIProof × Z))
    (h : Query k kN kS L → Out k e) :
    (M.romGameAux B Qs sp c p).trace h = (M.romGame B Qs sp c (p.mapOut Prod.fst)).trace h := by
  simp only [romGameAux, romGame, OracleProg.trace_bind, OracleProg.trace_pure,
    SEProg.trace_compose_mapOut]
  rw [SEProg.run_compose_mapOut]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The queries of a program padded to `K` queries** (`OracleProg.toExpansion` after the trivial
algorithm `SPBCS.baseAlg`) are the program's padded trace. -/
theorem queries_baseAlg_append {R : Type} (G : OracleProg (Query k kN kS L) (Out k e) R)
    (pad : Query k kN kS L) (K : ℕ) (h : Query k kN kS L → Out k e) :
    ((SPBCS.baseAlg (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).append
        (OracleProg.toExpansion (fun _ : Unit => G) pad) K).queries h (0 + K) =
      (List.range K).map (G.paddedTrace h pad) := by
  rw [ROM.Alg.queries_append_add]
  exact (Expansion.run_eq_of_next _ h _ (G.paddedTrace_eq_next h pad) K)

namespace SimExtractionAdversaryROM

variable {M B} {tq : ℕ} (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof × Z) tq)

/-- **The adversary without its auxiliary output**, an adversary of
`SPBCS.weak_online_simulation_extractability_rom_basic`. -/
abbrev claims : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof) tq :=
  𝒜.mapOut Prod.fst

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem claims_prog (r : 𝒜.Coins) :
    𝒜.claims.prog r = (𝒜.prog r).mapOut Prod.fst :=
  (𝒜.alg r).toSEProg_mapOut Prod.fst tq

variable [DecidableEq X]

/-- **The simulated execution** (`def:bcs-se`) at the adversary's coins `r` and the simulator's
coins `c`: over a uniform base oracle `h`, the law of the claim, the auxiliary output, the
queried statements and the verdict of the spBCS verifier under the final oracle `h`
reprogrammed by the simulator's assignments, in the composed run of the adversary with the
simulation oracle (`SEProg.compose`; its output and final oracle are those of the interactive run,
`ROM.IAlg.out_compose_toSEProg`, `ROM.IAlg.reprogram_compose_toSEProg`). -/
noncomputable def simLaw (r : 𝒜.Coins) :
    PMF (NARG.VerifiedOutput (SimExtractionView (Claim X M.NIProof) Z X')) :=
  (PMF.uniformOfFintype (Query k kN kS L → Out k e)).map fun h =>
    M.outcomeOf Qs h (some ((SEProg.compose sp c (𝒜.prog r) [] 0 []).run h))

/-- **The game at the coins `r` as a classical `K`-query algorithm**: the game's queries padded to
`K` (`OracleProg.toExpansion`), as in `gameLog`. -/
noncomputable abbrev gameAlg (r : 𝒜.Coins) (K : ℕ) :
    ROM.Alg (Query k kN kS L) (Out k e) Unit (0 + K) :=
  (SPBCS.baseAlg (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).append
    (OracleProg.toExpansion (fun _ : Unit => M.romGameAux B Qs sp c (𝒜.prog r))
      (.xof (fun _ => 0) fun _ => 0)) K

/-- **The extractor's execution** (`def:bcs-se`) at the adversary's coins `r` and the simulator's
coins `c`, with a table of `K` queries: the extractor answers the queries of the game (the
adversary's, the simulator's and the verifier's, each assigned input from the assignment list as
the game does) by lazy sampling, recording the queries and answers in a table, and the unqueried
points are then filled with uniform values (`ROM.Alg.lazyRun`). The extractor `dbExtract` reads the
table.

Running time: the game's `K` queries, each answered by a table lookup or one uniform sample, and the
game's own computation (the adversary, `Q` runs of the simulator and the verifier); polynomial when
these are. The filling is not part of the extractor's computation: it only gives the oracle that
answers any later query, so every point is answered lazily on demand. This running time is argued
here, not proved in Lean. -/
noncomputable abbrev extractionRun (r : 𝒜.Coins) (K : ℕ) :
    PMF (ROM.Alg.LazyState (Query k kN kS L) (Out k e) × (Query k kN kS L → Out k e)) :=
  (𝒜.gameAlg Qs sp c r K).lazyRun (0 + K)

/-- **The outcome of the extractor's execution**: the claim, the auxiliary output and the queried
statements read from the answers of the lazy run (`OracleProg.runAnswers` of the composed run), and
the verdict under the filled oracle reprogrammed by the run's assignments. -/
def extractionOutcome (r : 𝒜.Coins)
    (p : ROM.Alg.LazyState (Query k kN kS L) (Out k e) × (Query k kN kS L → Out k e)) :
    NARG.VerifiedOutput (SimExtractionView (Claim X M.NIProof) Z X') :=
  M.outcomeOf Qs p.2 ((SEProg.compose sp c (𝒜.prog r) [] 0 []).runAnswers p.1.ans)

/-- **The law of the outcome of the extractor's execution** at the coins `r` and `c`. -/
noncomputable def extractionLaw (r : 𝒜.Coins) (K : ℕ) :
    PMF (NARG.VerifiedOutput (SimExtractionView (Claim X M.NIProof) Z X')) :=
  (𝒜.extractionRun Qs sp c r K).map (𝒜.extractionOutcome Qs sp c r)

/-- **The extractor's execution wins without extraction**: its outcome is a statement none of the
proof queries was, with a proof the verifier accepts, and `dbExtract` at `E` returns no witness for the
statement from the table. -/
def WinsNotExtracts (fx : X' → X) {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (r : 𝒜.Coins)
    (p : ROM.Alg.LazyState (Query k kN kS L) (Out k e) × (Query k kN kS L → Out k e)) : Prop :=
  ∃ v ∈ (𝒜.extractionOutcome Qs sp c r p).out, (∀ x' ∈ v.queried, fx x' ≠ v.claim.stmt) ∧
    (𝒜.extractionOutcome Qs sp c r p).accepted ∧ p.1.log ∉ M.extracts rel E v.claim.stmt

variable [Fintype C] [Nonempty C]

/-- **The probability that the extractor's execution wins without extraction**, over the
adversary's coins, the simulator's uniform coins and the lazy run, with a table of `K` queries. -/
noncomputable def extractionWinsNotExtracts (fx : X' → X) {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (Q K : ℕ) : ℝ≥0∞ :=
  ∑' c : Fin Q → SaltedCoins (FiatShamirSalt kS) C, PMF.uniformOfFintype _ c *
    ∑' r, 𝒜.coins r * (𝒜.extractionRun Qs sp c r K).toOuterMeasure
      {p | 𝒜.WinsNotExtracts Qs sp c fx rel E r p}

end SimExtractionAdversaryROM

/-! ### The two conditions -/

variable {M B} [DecidableEq X] [Fintype C] [Nonempty C]

/-- **Weak online simulation extractability in the ROM at one adversary** (the paper's
`def:bcs-se` in the ROM), with the classical simulator program `sp` answering `Q` proof queries, the
database extractor `dbExtract` at `E` reading a table of `tq + Q q + kq` queries:

* `extractionLaw_eq` (the oracle simulation condition, with error `0`): at every value of the
  adversary's coins and the simulator's coins, the extractor's execution has the simulated
  execution's law of the claim, the auxiliary output, the queried statements and the verdict;
* `winsNotExtracts_le` (the extraction condition): averaged over the adversary's coins and the
  simulator's uniform coins, the extractor's execution outputs a statement none of the proof queries
  was with a proof the verifier accepts while `dbExtract` returns no witness, with probability at
  most `ε`. -/
structure WeakOnlineSimExtractsROM {tq : ℕ} (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof × Z) tq)
    (Q kq q : ℕ) (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (ε : ℝ≥0∞) : Prop where
  /-- The oracle simulation condition. -/
  extractionLaw_eq : ∀ (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) r,
    𝒜.extractionLaw Qs sp c r (tq + Q * q + kq) = 𝒜.simLaw Qs sp c r
  /-- The extraction condition. -/
  winsNotExtracts_le : 𝒜.extractionWinsNotExtracts Qs sp fx rel E Q (tq + Q * q + kq) ≤ ε

variable (M B) in
/-- **Weak online simulation extractability of the spBCS compiler in the ROM** (the paper's
`def:bcs-se` in the ROM; `WeakOnlineSimExtractsROM`): for every type of queried statements read
through `fx`, every type `Z` of auxiliary outputs and every query-bounded classical adversary with
at most `tq` queries whose first `Q` proof queries are answered by the classical simulator program `Sim`
(making at most `q` queries per proof query), the extractor's execution of the database extractor
`dbExtract` at `E` has the simulated execution's law of the output and the verdict, and wins
without extraction with probability at most `ε tq Q`. -/
def WeakOnlineSimulationExtractableROM {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : X → SaltedCoins (FiatShamirSalt kS) C →
      OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)))
    (q : ℕ) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' Z : Type) (fx : X' → X) (tq Q : ℕ) (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof × Z) tq),
    WeakOnlineSimExtractsROM Qs (fun r a => Sim (fx r) a) 𝒜 Q kq q fx rel E (ε tq Q)

/-! ### The spBCS compiler satisfies them -/

namespace SimExtractionAdversaryROM

variable {Qs} {sp} {fx : X' → X} {tq : ℕ} (𝒜 : M.SimExtractionAdversaryROM B X' (Claim X M.NIProof × Z) tq)
  (c : Fin Q → SaltedCoins (FiatShamirSalt kS) C) (r : 𝒜.Coins) (K : ℕ)
  (h : Query k kN kS L → Out k e)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  [DecidableEq X] [Fintype C] [Nonempty C] in
/-- **The table of the extractor's execution is the game's query table** of the adversary without
its auxiliary output (`gameLog`). -/
theorem log_stateOf_gameAlg :
    ((𝒜.gameAlg Qs sp c r K).stateOf h (0 + K)).log = M.gameLog B Qs sp c (𝒜.claims.prog r) K h := by
  change ROM.logOf h ((𝒜.gameAlg Qs sp c r K).queries h (0 + K)) =
    ROM.logOf h (((SPBCS.baseAlg (k := k) (kN := kN) (kS := kS) (L := L) (e := e)).append
      (OracleProg.toExpansion (fun _ : Unit => M.romGame B Qs sp c (𝒜.claims.prog r))
        (.xof (fun _ => 0) fun _ => 0)) K).queries h (0 + K))
  rw [queries_baseAlg_append, queries_baseAlg_append, 𝒜.claims_prog r]
  congr 2
  funext i
  simp only [OracleProg.paddedTrace, trace_romGameAux]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq X] [Fintype C] [Nonempty C] in
/-- **On a table long enough for the composed run, the extractor's execution reads the composed
run's result from its answers.** -/
theorem extractionOutcome_stateOf
    (hK : ((SEProg.compose sp c (𝒜.prog r) [] 0 []).trace h).length ≤ K) :
    𝒜.extractionOutcome Qs sp c r ((𝒜.gameAlg Qs sp c r K).stateOf h (0 + K), h) =
      M.outcomeOf Qs h (some ((SEProg.compose sp c (𝒜.prog r) [] 0 []).run h)) := by
  have hpre := OracleProg.prefix_map_paddedTrace h (.xof (fun _ => 0) fun _ => 0)
    (M.romGameAux B Qs sp c (𝒜.prog r)) (by rw [romGameAux, OracleProg.trace_bind]) hK
  have hans : ((𝒜.gameAlg Qs sp c r K).stateOf h (0 + K)).ans =
      ((List.range K).map ((M.romGameAux B Qs sp c (𝒜.prog r)).paddedTrace h
        (.xof (fun _ => 0) fun _ => 0))).map h := by
    change ((𝒜.gameAlg Qs sp c r K).queries h (0 + K)).map h = _
    rw [queries_baseAlg_append]
  rw [extractionOutcome, hans, OracleProg.runAnswers_of_prefix h _ (hpre.map h)]

variable {q : ℕ} (hqs : ∀ r a G, ((sp r a).trace G).length ≤ q) {kq : ℕ}
include hqs

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  [DecidableEq X] [Fintype C] [Nonempty C] in
/-- **The composed run makes at most `tq + Q q` queries.** -/
theorem length_trace_compose_prog :
    ((SEProg.compose sp c (𝒜.prog r) [] 0 []).trace h).length ≤ tq + Q * q + kq := by
  have := SEProg.length_trace_compose sp c hqs (𝒜.prog r) tq ((𝒜.alg r).queryBound_toSEProg tq)
    [] 0 [] h (Nat.zero_le _)
  rw [Nat.sub_zero] at this
  omega

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq X] [Fintype C] [Nonempty C] in
/-- **The oracle simulation condition, with error `0`**: the extractor's execution has the
simulated execution's law of the output and the verdict (lazy sampling, `ROM.Alg.lazyRun_eq`). -/
theorem extractionLaw_eq_simLaw :
    𝒜.extractionLaw Qs sp c r (tq + Q * q + kq) = 𝒜.simLaw Qs sp c r := by
  rw [extractionLaw, extractionRun, ROM.Alg.lazyRun_eq, PMF.map_comp, simLaw]
  congr 1
  funext h
  exact 𝒜.extractionOutcome_stateOf c r _ h (𝒜.length_trace_compose_prog c r h hqs)

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype C] [Nonempty C] in
/-- **A win without extraction in the extractor's execution** is a win of the adversary without
its auxiliary output, against the base oracle at which the lazy run is taken, whose query table
the extractor fails on. -/
theorem winsROM_of_winsNotExtracts {Wit : Type} {rel : Set (X × Wit)}
    {E : CausalExtractor P t X Wit}
    (hw : 𝒜.WinsNotExtracts Qs sp c fx rel E r
      ((𝒜.gameAlg Qs sp c r (tq + Q * q + kq)).stateOf h (0 + (tq + Q * q + kq)), h)) :
    M.WinsROM B Qs fx sp c (𝒜.claims.prog r) h ∧
      M.gameLog B Qs sp c (𝒜.claims.prog r) (tq + Q * q + kq) h ∉
        M.extracts rel E (M.romResult B sp c (𝒜.claims.prog r) h).out.stmt := by
  obtain ⟨v, hv, hfresh, hacc, hlog⟩ := hw
  rw [𝒜.extractionOutcome_stateOf c r _ h (𝒜.length_trace_compose_prog c r h hqs)] at hv hacc
  obtain rfl := Option.some_inj.1 hv.symm
  rw [log_stateOf_gameAlg] at hlog
  have hres : M.romResult B sp c (𝒜.claims.prog r) h =
      ((SEProg.compose sp c (𝒜.prog r) [] 0 []).run h).mapOut Prod.fst := by
    rw [romResult, 𝒜.claims_prog r, SEProg.run_compose_mapOut]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hres]
    exact hfresh
  · rw [hres]
    exact hacc
  · rw [hres]
    exact hlog

variable (hA : ∀ r a, M.AssignsAtKeys (sp r a) ⟨a.salt, fx r⟩) {Wit : Type}
  {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
  {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
  (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
include hA hrbr hkq

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The extraction condition**: the extractor's execution wins without extraction with
probability at most `simExtractionErrorROM kq (maxError ε) q tq Q`, at every value of the
simulator's coins (`SPBCS.weak_online_simulation_extractability_rom_basic` for the adversary without its auxiliary
output), so also averaged over them. -/
theorem winsNotExtracts_le :
    𝒜.extractionWinsNotExtracts Qs sp fx rel E Q (tq + Q * q + kq) ≤
      M.simExtractionErrorROM kq (maxError ε) q tq Q := by
  have key : ∀ c : Fin Q → SaltedCoins (FiatShamirSalt kS) C,
      ∑' r, 𝒜.coins r * (𝒜.extractionRun Qs sp c r (tq + Q * q + kq)).toOuterMeasure
        {p | 𝒜.WinsNotExtracts Qs sp c fx rel E r p} ≤
        M.simExtractionErrorROM kq (maxError ε) q tq Q := fun c => by
    refine le_trans (ENNReal.tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le)
      (SPBCS.weak_online_simulation_extractability_rom_basic (Qs := Qs) (fx := fx) hA hqs hrbr hkq c 𝒜.claims)
    rw [extractionRun, ROM.Alg.lazyRun_eq, PMF.toOuterMeasure_map_apply]
    exact MeasureTheory.measure_mono fun h hh =>
      𝒜.winsROM_of_winsNotExtracts c r h hqs hh
  calc 𝒜.extractionWinsNotExtracts Qs sp fx rel E Q (tq + Q * q + kq)
      ≤ ∑' c : Fin Q → SaltedCoins (FiatShamirSalt kS) C, PMF.uniformOfFintype _ c *
          M.simExtractionErrorROM kq (maxError ε) q tq Q :=
        ENNReal.tsum_le_tsum fun c => mul_le_mul_of_nonneg_left (key c) zero_le
    _ = M.simExtractionErrorROM kq (maxError ε) q tq Q := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Weak online simulation extractability in the ROM at one adversary**
(`WeakOnlineSimExtractsROM`), with oracle simulation error `0` and extraction error
`simExtractionErrorROM kq (maxError ε) q tq Q`. -/
theorem weakOnlineSimExtractsROM :
    WeakOnlineSimExtractsROM Qs sp 𝒜 Q kq q fx rel E (M.simExtractionErrorROM kq (maxError ε) q tq Q) :=
  ⟨fun c r => 𝒜.extractionLaw_eq_simLaw c r hqs, 𝒜.winsNotExtracts_le hqs hA hrbr hkq⟩

end SimExtractionAdversaryROM

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Weak online simulation extractability of the spBCS compiler in the classical
random-oracle model** (paper `thm:bcs-se`(2); `def:bcs-se` in the ROM,
`WeakOnlineSimulationExtractableROM`): for a composite causally round-by-round knowledge sound at
the causal extractor `E` with errors `ε` (`hrbr`), query phases whose accepting runs make at most
`kq` verifier queries (`hkq`), and a classical simulator program `Sim` that assigns only at the keys
of its chain inputs (`hA`) and makes at most `q` queries (`hqs`), with uniform coins for each
proof query: against every query-bounded classical adversary with an auxiliary output, the extractor's
execution (lazy sampling of the game's queries, the database extractor `dbExtract` on its table)
has the simulated execution's law of the claim, the auxiliary output, the queried statements and
the verdict, at every value of the adversary's and the simulator's coins (oracle simulation error
`0`), and wins without extraction with probability at most `simExtractionErrorROM kq (maxError ε)
q tq Q`, the classical knowledge error with merges at `tq + Q q + kq` queries. -/
@[headline]
theorem weak_online_simulation_extractability_rom
    {Sim : X → SaltedCoins (FiatShamirSalt kS) C →
      OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B))}
    (hA : ∀ x a, M.AssignsAtKeys (Sim x a) ⟨a.salt, x⟩) {q : ℕ}
    (hqs : ∀ x a G, ((Sim x a).trace G).length ≤ q) {Wit : Type} {rel : Set (X × Wit)}
    {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound rel V E St ε) {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) :
    M.WeakOnlineSimulationExtractableROM B Qs rel E kq Sim q
      (M.simExtractionErrorROM kq (maxError ε) q) := fun _ _ fx _ _ 𝒜 =>
  𝒜.weakOnlineSimExtractsROM (fun r a G => hqs (fx r) a G) (fun r a => hA (fx r) a) hrbr hkq

end

end GordieHowe.SPBCS
