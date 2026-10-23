-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtractTest
public import GordieHowe.SPBCS.FullPast.Targeted
public import GordieHowe.SPBCS.FullPast.Online
public import GordieHowe.Model.QROM.BridgeClasses
public import GordieHowe.Model.QROM.ExtractAt
public import GordieHowe.Model.QROM.AdaptiveTestClasses
public import GordieHowe.Model.QROM.QueryCountExpandAt

@[expose] public section

/-!
# The test answered by the simulated oracle: the series–parallel base model

The variant of Unruh 2017 (ePrint 2017/398), Definition 14, p. 21, eq. (6) in which the test's
queries after extraction are answered by the extractor's simulated oracle: Prove is
the adversary followed by its test (`GordieHowe.SPBCS.acceptsQTest`); in Extract′ the adversary runs
against CMS19's compressed oracle with the simulation challenger, the targeted extractor `E_T`
(`GordieHowe/SPBCS/FullPast/Targeted.lean`) runs its classical queries and measures
its output, and then the test runs with its queries answered by the same compressed oracle,
patched by the simulator's assignments. The shape is CDHZ26's (ePrint 2025/2166) Definition 10.3,
p. 71, whose relation deciders query the emulated oracle after extraction.

This file holds the pieces at the series–parallel base model (`GordieHowe.SPBCS.FullPast`):

- `Ctrl`, `ctrlOf`: the control of the extraction (the adversary's output and the challenger's
  registers); `finalAnswerOf`, `finalAnswerOf_eq`, `simQueryInputsOf`,
  `simQueryInputsOf_length_le`, `queriedOf`, `tupleOracleOf`, `tupleOracle`, `tupleOracle_eq`:
  the final oracle, the simulator's queries and the queried statements read from the
  challenger's registers; `FreshOf`, `fresh_iff_freshOf`: freshness of a control.
- `pureWithTest`, `splitStep`, `pureCtrl`: the pure algorithm of the adversary followed by its
  test, the step after which the extraction runs, and the control read from its work register.
- `swapError`, `swapError_mono`: the swap error `tTest √(24 V / 2^(8k))` at `tTest` test queries.

The namespace `GordieHowe.SPBCS` states the variant for the spBCS compiler with them (`GordieHowe/SPBCS/SimOracle.lean`: the expansion
`GordieHowe.SPBCS.ctrlExpansion`, the targeted extractor `GordieHowe.SPBCS.targetedExtractor` with its cover
`GordieHowe.SPBCS.cover_simExtGame_targeted`, the bound at one adversary and one test
`GordieHowe.SPBCS.winTestProb_withTest_le`, and the bundled notion
`GordieHowe.SPBCS.simulation_sound_extractability_sim_oracle`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM QROM.ExpandAdv
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : Base P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### The control and the targeted extractor -/

section Control

variable (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {K : ℕ}

/-- **The control of the extraction at `slots` slots**: the adversary's output and the challenger's
registers. -/
abbrev CtrlAt (slots : ℕ) : Type :=
  Claim X M.NIProof ×
    ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins

/-- **The control of the extraction**: the adversary's output and the challenger's registers. -/
abbrev Ctrl : Type :=
  Claim X M.NIProof ×
    ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots (simExtChallenger Psim Q).q
      (simExtChallenger Psim Q).Coins

/-- The control read from the composed registers. -/
def ctrlOf (v : M.Register B A Psim Q) : Ctrl A Psim Q :=
  (advOut A Psim Q v, v.chal)

/-- The final answer at `q` from the base answer `y`, read from the challenger's registers of
`slots` slots (`finalAnswer`): the last assignment at `q` of the simulator's replies
(`Challenger.regStateOf`). -/
def finalAnswerAt (slots : ℕ) (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) (q : (Bits (queryBits k kN kS L)))
    (y : Out k e) : Out k e :=
  (lastAssign ((Challenger.regStateOf Q (simExtRespond Psim Q) ch.coins ch.logs
    (fun j => List.ofFn (n := Psim.q) fun i => (ch.queries j i).2) slots).assignments.map
      (Assignment.mapOutput (outEquiv k e))) q).getD y

/-- The final answer at `q` from the base answer `y`, read from the challenger's registers
(`finalAnswerAt` at the adversary's slots). -/
abbrev finalAnswerOf (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) (q : (Bits (queryBits k kN kS L))) (y : Out k e) :
    Out k e :=
  finalAnswerAt Psim Q A.slots ch q y

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The final answer read through the post-phase assignments** (`KindAlg.postAss`). -/
theorem finalAnswerOf_eq_postAss (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X'
    A.slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins)
    (q : Bits (queryBits k kN kS L)) (y : Out k e) :
    finalAnswerOf A Psim Q ch q y =
      (lastAssign ((A.postAss _ ch).map (Assignment.mapOutput (outEquiv k e))) q).getD y := by
  rw [finalAnswerOf, finalAnswerAt, KindAlg.postAss_eq_regStateOf]
  rfl

/-- The simulator's query inputs read from the challenger's registers of `slots` slots
(`simQueryInputs`). -/
def simQueryInputsAt (slots : ℕ) (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X'
    slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) :
    List (Bits (queryBits k kN kS L)) :=
  (List.finRange slots).flatMap fun j =>
    if (ch.logs j).isSome ∧ (requestsBefore ch.logs j).length < Q then
      List.ofFn fun i : Fin Psim.q => (ch.queries j i).1
    else []

/-- The statements sent to the simulator, read from the challenger's registers (`queried`). -/
noncomputable def queriedOf (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) : List X' :=
  (A.stateAt (simExtChallenger Psim Q) ch A.slots).history.map HistoryEntry.request

/-- **The statement of a control is fresh**: no statement sent to the simulator, read through
`fx`, is the statement of the adversary's output `c.1`, with the statements read from the
challenger's registers `c.2` (`Fresh`, `fresh_iff_freshOf`). -/
def FreshOf (fx : X' → X) (c : Ctrl A Psim Q) : Prop :=
  ∀ x' ∈ queriedOf A Psim Q c.2, fx x' ≠ c.1.stmt

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- Freshness on the composed registers is freshness of their control. -/
theorem fresh_iff_freshOf
    {A₀ : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof)}
    (fx : X' → X) (v : Reg A₀ Psim Q) :
    Fresh A₀ Psim Q fx v ↔ FreshOf A₀.toTPKindAlg Psim Q fx (ctrlOf A₀.toTPKindAlg Psim Q v) :=
  Iff.rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The final answer read from the control of the composed registers is the final answer**
(`finalAnswer`). -/
theorem finalAnswerOf_ctrlOf (v : M.Register B A Psim Q) (q : Bits (queryBits k kN kS L))
    (y : Out k e) : finalAnswerAt Psim Q A.slots (ctrlOf A Psim Q v).2 q y = finalAnswer A Psim Q v q y := by
  rw [← finalAnswerOf, finalAnswerOf_eq_postAss]
  rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The final answer read from the base oracle's answer is the final oracle's answer**, with the
assignments read from the challenger's registers (`finalAnswer_eq`). -/
theorem finalAnswerOf_eq (H : Bits (queryBits k kN kS L) → XOut k e)
    (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
      (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) (q : Query k kN kS L) :
    finalAnswerOf A Psim Q ch (Query.toBits q) (outEquiv k e (H (Query.toBits q))) =
      chainOracle (H.reprogram (A.postAss (simExtChallenger Psim Q) ch)) q := by
  rw [finalAnswerOf_eq_postAss, lastAssign_map, chainOracle, reprogram_apply_eq_lastAssign]
  cases lastAssign (A.postAss (simExtChallenger Psim Q) ch) (Query.toBits q) <;> rfl

/-- **The verifier's oracle read from recorded queries and answers**: at a recorded query, the
answer of its first occurrence read through the final assignments of the challenger's registers
`ch` of `slots` slots (`finalAnswerAt`); the default answer at a query not recorded. -/
def tupleOracleAt (slots : ℕ) (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins)
    (qs : Fin K → Bits (queryBits k kN kS L)) (as : Fin K → Out k e) : Query k kN kS L → Out k e :=
  fun q =>
    match (List.finRange K).find? fun i => qs i = Query.toBits q with
    | some i => finalAnswerAt Psim Q slots ch (qs i) (as i)
    | none => default

end Control

/-! ### Extract′ at one adversary and one test -/

section SimOracle

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (T : A.QTest) (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
  (Q : ℕ) {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) [DecidableEq X]

/-- **The pure algorithm of the adversary followed by its test**, with the simulation challenger
and its classical registers as output (the algorithm `extAdv` expands).

Running time: that of the adversary followed by its test (`AdaptiveIAlg.withTest`) with the simulation
challenger (each answered proof query one run of the simulator program), in coherent pure serial form
(`Alg.toQueryAlgCoh`). This running time is argued here, not proved in Lean. -/
noncomputable abbrev pureWithTest :
    QueryAlg (Bits (queryBits k kN kS L)) (XOut k e) ((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth
      (M.Register B (A.withTest T).toTPKindAlg Psim Q) :=
  ((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toQueryAlgCoh.mapOut
    (·.getD ((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)

/-- **The step after which the extraction runs**: the queries before the test's,
`T₀ − T.queries`. -/
noncomputable abbrev splitStep : ℕ :=
  ((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth - T.queries

/-- **The control read from the work register of the pure algorithm**: the adversary's output and
the challenger's registers (`ctrlOf`) of the pure algorithm's output, which the coherent form reads
from its system register (those of the default output on halted runs). -/
noncomputable def pureCtrl (w : (pureWithTest A T Psim Q).W) : Ctrl (A.withTest T).toTPKindAlg Psim Q :=
  ctrlOf (A.withTest T).toTPKindAlg Psim Q ((pureWithTest A T Psim Q).out w)

variable {Wit : Type} (E : CausalExtractor P t X Wit)

variable (M) in
/-- **The swap error** at `tTest` test queries: `tTest √(24 V / 2^(8k))` with
`V = visitBound`, the digests `E_T` reads (CDHZ26 Corollary 5.6, p. 31, with the constant `24` of
`abs_foldedProb_sub_extractAtProb_le` and the generalized instability `V / 2^(8k)` of `E_T`'s
output, `instabPart_targetedExtractorOf_le`). -/
noncomputable def swapError (tTest : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (tTest * Real.sqrt (24 * (M.visitBound / 2 ^ (8 * k))))

end SimOracle

/-! ### The bundled notion -/

section Notion

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
variable (M) in
/-- The swap error grows with the number of test queries. -/
theorem swapError_mono {tTest tTest' : ℕ} (h : tTest ≤ tTest') :
    M.swapError tTest ≤ M.swapError tTest' := by
  unfold swapError
  gcongr

end Notion

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : FullPast P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### The control and the targeted extractor -/

section Control

variable (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {K : ℕ}

/-- The simulator's query inputs read from the challenger's registers (`simQueryInputsAt` at the
adversary's slots). -/
abbrev simQueryInputsOf (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) : List (Bits (queryBits k kN kS L)) :=
  simQueryInputsAt Psim Q A.slots ch

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The simulator's query inputs read from the challenger's registers number at most `Q · q`. -/
theorem simQueryInputsOf_length_le (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X'
    A.slots (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) :
    (simQueryInputsOf A Psim Q ch).length ≤ Q * Psim.q :=
  length_flatMap_logged_le ch.logs _ fun _ => List.length_ofFn

/-- **The verifier's oracle read from recorded queries and answers** (`tupleOracleAt` at the
adversary's slots). -/
abbrev tupleOracleOf (ch : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
    (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) (qs : Fin K → Bits (queryBits k kN kS L))
    (as : Fin K → Out k e) : Query k kN kS L → Out k e :=
  tupleOracleAt Psim Q A.slots ch qs as

/-- **The verifier's oracle read from a tuple** (`tupleOracleOf` at the tuple's registers,
queries and answers). -/
noncomputable def tupleOracle (o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K) :
    Query k kN kS L → Out k e :=
  tupleOracleOf A Psim Q o.out.chal o.queries o.answers

variable {A Psim Q}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- On a tuple consistent with a database, the recorded answer at any occurrence of a query is
the oracle the tuple records. -/
theorem tupleOracle_eq {o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    {D : DB (Bits (queryBits k kN kS L)) (Out k e)} (hD : o.InDB D) {q : Query k kN kS L} {i : Fin K}
    (hi : o.queries i = Query.toBits q) :
    tupleOracle A Psim Q o q = finalAnswer A Psim Q o.out (o.queries i) (o.answers i) := by
  obtain ⟨j, hj⟩ : ∃ j, (List.finRange K).find? (fun i => o.queries i = Query.toBits q) = some j := by
    refine Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨i, List.mem_finRange _, ?_⟩)
    simpa using hi
  have hjq : o.queries j = Query.toBits q := by simpa using List.find?_some hj
  have hans : o.answers j = o.answers i := by
    have h1 := hD j
    have h2 := hD i
    rw [hjq, ← hi, h2] at h1
    exact (Option.some_inj.1 h1).symm
  simp only [tupleOracle, tupleOracleOf, tupleOracleAt, hj]
  rw [hjq, hans, ← hi, ← finalAnswerOf, finalAnswerOf_eq_postAss]
  rfl

variable (A Psim Q)

end Control

end FullPast

end GordieHowe.SPBCS
