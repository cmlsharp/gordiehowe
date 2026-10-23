-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractTest
public import GordieHowe.SPBCS.Targeted
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.FullPast.SimOracle

@[expose] public section

/-!
# Simulation-sound extractability of the spBCS compiler with the test answered by the simulated oracle

The variant of Unruh 2017 (ePrint 2017/398), Definition 14, p. 21, eq. (6) in which the test's
queries after extraction are answered by the extractor's simulated oracle, patched by the
simulator's assignments, for the spBCS compiler, from the parts in `GordieHowe/SPBCS/FullPast/SimOracle.lean`, with the spBCS verifier
(`Accepts`, `queries`), its challenges (`chV`) and its bad set (`bad`), for a counted
simulator program that assigns only at the keys of its chain inputs (`SimAssignsAtKeys`):

- `ctrlExpansion`, `trace_extractionProgOf` (the extraction queries of a control),
  `targetedExtractor`, `cover_simExtGame_targeted`, `instabPart_targetedExtractorOf_le`: the
  expansion of the verifier's and the simulator's queries on the control, the targeted extractor on
  the tuple's control (the targeted extractor of the compiler over the term at the challenges with
  merges, `GordieHowe/SPBCS/Targeted.lean`), the cover of `simExtGame` with it, and the generalized
  instability `visitBound / 2^(8k)` of its output;
- `winTestProb_withTest_le`: at one adversary and one test, Prove is at most Extract′ plus the
  spBCS knowledge error with the test's queries counted plus the swap error;
- `simulation_sound_extractability_sim_oracle`: the bundled notion
  (`SimulationSoundExtractableSimOracle`) against query-bounded adversaries.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM QROM.ExpandAdv
open Base (SimExtractionAdversary)
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

/-! ### The control and the targeted extractor -/

section Control

variable (A : KindAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {K : ℕ}

/-- **The extraction queries of a control at `slots` slots** (`extractionProg`). -/
def extractionProgAt (slots : ℕ) (c : Base.CtrlAt Psim Q slots) :
    GordieHowe.OracleProg (Bits (queryBits k kN kS L)) (Out k e) (List (Out k e)) :=
  (OracleProg.translate Query.toBits
      (fun q y => Base.finalAnswerAt Psim Q slots c.2 (Query.toBits q) y)
      (M.queryProg c.1.stmt c.1.proof (Qs c.1.stmt))).bind fun _ =>
    OracleProg.queryAll (Base.simQueryInputsAt Psim Q slots c.2)

/-- **The extraction queries of a control** (`extractionProgAt` at the adversary's slots). -/
abbrev extractionProgOf (c : Base.Ctrl A Psim Q) :
    GordieHowe.OracleProg (Bits (queryBits k kN kS L)) (Out k e) (List (Out k e)) :=
  extractionProgAt Psim Q Qs A.slots c

/-- **The expansion for extraction on a control at `slots` slots** (`simExtractionExpansion`). -/
def ctrlExpansionAt (slots : ℕ) :
    Expansion (Bits (queryBits k kN kS L)) (Out k e) (Base.CtrlAt Psim Q slots) :=
  OracleProg.toExpansion (extractionProgAt Psim Q Qs slots) (Base.padQuery (kS := kS))

/-- **The expansion for extraction on the control** (`ctrlExpansionAt` at the adversary's slots). -/
abbrev ctrlExpansion : Expansion (Bits (queryBits k kN kS L)) (Out k e) (Base.Ctrl A Psim Q) :=
  ctrlExpansionAt Psim Q Qs A.slots

/-- **The expansion for extraction reads the control only.** -/
theorem comapIn_ctrlExpansion :
    (ctrlExpansion A Psim Q Qs).comapIn (Base.ctrlOf A Psim Q) =
      simExtractionExpansion A Psim Q Qs := by
  simp only [Expansion.comapIn, ctrlExpansion, ctrlExpansionAt, simExtractionExpansion,
    OracleProg.toExpansion, extractionProgAt, extractionProg, Base.finalAnswerOf_ctrlOf]
  rfl

/-- **The extraction queries of a control** under the base oracle `H`: the spBCS verifier's
queries on the output `c.1` under the final oracle, then the simulator's query inputs, both read
from the challenger's registers `c.2` (`trace_extProg`). -/
theorem trace_extractionProgOf (H : Bits (queryBits k kN kS L) → XOut k e)
    (c : Base.Ctrl A Psim Q) :
    (extractionProgOf A Psim Q Qs c).trace (fun a => outEquiv k e (H a)) =
      (M.queries c.1.stmt c.1.proof
        (chainOracle (H.reprogram (A.postAss (simExtChallenger Psim Q) c.2)))
        (Qs c.1.stmt)).map Query.toBits ++ FullPast.simQueryInputsOf A Psim Q c.2 := by
  rw [extractionProgOf, extractionProgAt, OracleProg.trace_bind, OracleProg.trace_translate,
    OracleProg.trace_queryAll]
  have hf : (fun a => Base.finalAnswerAt Psim Q A.slots c.2 (Query.toBits a)
      (outEquiv k e (H (Query.toBits a)))) =
      chainOracle (H.reprogram (A.postAss (simExtChallenger Psim Q) c.2)) :=
    funext (Base.finalAnswerOf_eq A Psim Q H c.2)
  rw [hf]
  rfl

variable {Wit : Type}

/-- **The targeted extractor on a control at `slots` slots** (`targetedExtractor` reads its tuple
through this): `targetedExtract` along the proof of the control's output, at the challenges the
verifier derives from the oracle the recorded queries and answers give (`tupleOracleOf`), on the
database restricted to the encoded queries. Running time: that of `targetedExtractor`. This running
time is argued here, not proved in Lean. -/
def targetedExtractorAt (slots : ℕ) (E : CausalExtractor P t X Wit) (c : Base.CtrlAt Psim Q slots)
    (qs : Fin K → Bits (queryBits k kN kS L)) (as : Fin K → Out k e)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Multiset Wit :=
  M.targetedExtract (D.restrictBy Query.toBits Query.ofBits fun _ _ => Query.ofBits_eq_some_iff)
    c.1.proof
    (M.chV (Base.tupleOracleAt Psim Q slots c.2 qs as) (M.ssOf c.1.stmt c.1.proof)
      c.1.proof.writes) E
    c.1.stmt

/-- **The targeted extractor on a control** (`targetedExtractorAt` at the adversary's slots).

Running time: that of `targetedExtractor`. This running time is argued here, not proved in Lean. -/
abbrev targetedExtractorOf (E : CausalExtractor P t X Wit) (c : Base.Ctrl A Psim Q)
    (qs : Fin K → Bits (queryBits k kN kS L)) (as : Fin K → Out k e)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Multiset Wit :=
  targetedExtractorAt Psim Q A.slots E c qs as D

/-- **The targeted extractor `E_T`**: the causal extractor `E` at every challenge's causal past in
the composite transcript along the proof the adversary output in the tuple `o`, with the challenges
the verifier derives from the oracle the tuple records (`tupleOracle`) and the prover messages read
from the Merkle views of the database restricted to the encoded queries.

Running time, in the database size `|D|`, the number `K` of recorded queries,
the round count `n` and the proof size: reading the tuple's oracle at a query is one scan of the
`K` recorded queries (`find?`) and one scan of the final assignment list (at most `Q · q`
assignments); the verifier's challenges `chVFullPast` make `2 · t.size n` such reads; `targetedExtract`
reads at most `visitBound` digests from `D` (each one scan of `D`) and calls `E` once per challenge;
the restriction to encoded queries is one pass over `D` (`DB.restrictBy`). In the extraction game `|D| ≤ T = t + tTest + Q · q + K` with
`K = kq + Q · q`, so `E_T` is polynomial in `t`, `tTest`, `Q` and the proof size when `E` is.
This running time is argued here, not proved in Lean. -/
def targetedExtractor (E : CausalExtractor P t X Wit)
    (o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Multiset Wit :=
  targetedExtractorOf A Psim Q E (Base.ctrlOf A Psim Q o.out) o.queries o.answers D

/-- **`E_T` returns a witness for the output statement.** -/
def TargetedExtracts (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ w ∈ targetedExtractor A Psim Q E o D, ((Base.advOut A Psim Q o.out).stmt, w) ∈ rel

variable {A Psim Q} (fx : X' → X) {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit}
  (St : CausalStateFn P t X) {ε : ChIdx P t → ℝ≥0}

/-- **A database consistent with a tuple of `simExtGame` lets `E_T` extract, is in `bad`, or has
a digest collision** (the `E_T` form of `cover_simExtGame`): without a collision the database
answers the spBCS verifier's queries as the tuple's oracle
(`lookup_of_mem_queries_of_no_collision`), and `mem_of_verify_targeted` applies along the output
proof, whose challenges under the tuple's oracle are the verifier's (`chV_eq_of_eqOn_queries`). -/
theorem cover_simExtGame_targeted [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {o : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A Psim Q) K}
    (ho : o ∈ simExtGame A Psim Q Qs fx K) {D : DB (Bits (queryBits k kN kS L)) (Out k e)}
    (hD : o.InDB D) :
    TargetedExtracts A Psim Q rel E o D ∨
      D.restrict Query.toBits ∈ M.bad rel E St ∪ digestCollision := by
  by_cases hcol : D.restrict Query.toBits ∈ digestCollision
  · exact Or.inr (Or.inr hcol)
  obtain ⟨h, hv, hcov⟩ := ho.2.1
  have hQ := lookup_of_mem_queries_of_no_collision A Psim Q fx ho hD hcol hcov
  have hh : ∀ q ∈ M.queries (Base.advOut A Psim Q o.out).stmt
      (Base.advOut A Psim Q o.out).proof h (Qs (Base.advOut A Psim Q o.out).stmt),
      FullPast.tupleOracle A Psim Q o q = h q := fun q hq => by
    obtain ⟨i, hi1, hi2⟩ := hcov q hq
    rw [FullPast.tupleOracle_eq hD hi1, hi2]
  rcases mem_of_verify_targeted rel E St hrbr hv (D := D.restrict Query.toBits) hQ with hE | hrest
  · obtain ⟨w, hw, hrel⟩ := hE
    refine Or.inl ⟨w, ?_, hrel⟩
    rw [targetedExtractor, targetedExtractorOf, targetedExtractorAt, DB.restrictBy_eq]
    show w ∈ M.targetedExtract (D.restrict Query.toBits) (Base.advOut A Psim Q o.out).proof
      (M.chV (FullPast.tupleOracle A Psim Q o)
        (M.ssOf (Base.advOut A Psim Q o.out).stmt (Base.advOut A Psim Q o.out).proof)
        (Base.advOut A Psim Q o.out).proof.writes) E (Base.advOut A Psim Q o.out).stmt
    rw [chV_eq_of_eqOn_queries hh]
    exact hw
  · exact Or.inr hrest

variable (A Psim Q E) in
/-- **The instability of `E_T`'s outcome** at a fixed control and record: one more recorded query
changes the output of `E_T` with probability at most `visitBound / 2^(8k)`, for every database (an
input outside the encoded queries changes nothing; `FullPast.prob_targetedExtract_change_le`).
-/
theorem instabPart_targetedExtractorOf_le (c : Base.Ctrl A Psim Q) (qs : Fin K → Bits (queryBits k kN kS L))
    (as : Fin K → Out k e) (tq : ℕ) :
    instabPart (targetedExtractorOf A Psim Q E c qs as) tq ≤ M.visitBound / 2 ^ (8 * k) := by
  refine instabPart_le fun D _ x hx => ?_
  by_cases hr : x ∈ Set.range Query.toBits
  · obtain ⟨q, rfl⟩ := hr
    have hq : q ∉ D.restrict Query.toBits := fun h => hx (DB.mem_restrict.1 h)
    simp only [targetedExtractorOf, targetedExtractorAt, DB.restrictBy_eq, DB.restrict_extend_image]
    exact M.toFullPast.prob_targetedExtract_change_le _ _ _ E _ hq
  · refine (probUniform_eq_zero fun y hy => hy ?_).trans_le zero_le
    simp only [targetedExtractorOf, targetedExtractorAt, DB.restrictBy_eq, DB.restrict_extend_of_notMem_range hr]

end Control

/-! ### Extract′ at one adversary and one test -/

section SimOracle

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (T : A.QTest) (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
  (Q : ℕ) {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) (kq : ℕ) [DecidableEq X]

/-- **The algorithm with the extraction inserted before the test** (`expandAt`), with the
spBCS verifier's extraction queries (`ctrlExpansion`).

Running time: that of `Base.pureWithTest`, plus the `kq + Q · Psim.q` extraction queries
computed from the measured registers by the query program with merges.
This running time is argued here, not proved in Lean. -/
noncomputable abbrev extAt :
    QueryAlg (Bits (queryBits k kN kS L)) (XOut k e)
      (((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth + (kq + Q * Psim.q))
      (BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B (A.withTest T).toTPKindAlg Psim Q)
        ((kq + Q * Psim.q))) :=
  expandAt (outEquiv k e) ((ctrlExpansion (A.withTest T).toTPKindAlg Psim Q Qs)) ((kq + Q * Psim.q))
    (Base.pureWithTest A T Psim Q) (Base.splitStep A T Psim Q) (Base.pureCtrl A T Psim Q)

variable {Wit : Type} (E : CausalExtractor P t X Wit)

/-- **The label of a database** at a control and recorded answers: the statement of the control's
output and the output of `E_T` (`targetedExtractorOf`), with the queries recomputed from the
control and the answers by the expansion.

Running time: the `K = kq + Q · q` queries are `K` steps of the expansion
(`ctrlExpansion`: the verifier's query program and the simulator's recorded inputs, each read from
the control), then one run of `E_T`, whose cost is `targetedExtractor`'s; polynomial in `t`,
`tTest`, `Q` and the proof size when `E` is. The projective measurement of this label on the
sparse encoding of the database (sorted pairs, Zha19 p. 7) is implemented in time linear in that
classical running time (DFMS22, ePrint 2021/280, App. B, Lemma B.1, p. 26: coherent evaluation,
copy of the output, uncomputation). This running time is argued here, not proved in Lean. -/
def extractLabel (c : Base.Ctrl (A.withTest T).toTPKindAlg Psim Q)
    (as : Fin ((kq + Q * Psim.q)) → Out k e) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) :
    X × Multiset Wit :=
  (c.1.stmt, targetedExtractorAt Psim Q A.slots E c
    (fun j => (ctrlExpansionAt Psim Q Qs A.slots).next c ((List.ofFn as).take j)) as D)

open Classical in
/-- The values the label takes on the basis states of the simulated registers of `𝒜_E`. -/
noncomputable def labelRange : Finset (X × Multiset Wit) :=
  Finset.univ.image fun b : SimRegister (extAt A T Psim Q Qs kq).W (Fin (k + e)) (Fin 8)
      (queryBits k kN kS L)
      (((A.withTest T).toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth + (kq + Q * Psim.q)) =>
    extractLabel A T Psim Q Qs kq E (Base.pureCtrl A T Psim Q b.1.1.1) (fun j => outEquiv k e (b.1.1.2.2 j))
      (slotsDB (outEquiv k e) b.2)

open Classical in
/-- **The label restricted to its finite range**: `some` of the label where it lies in
`labelRange` (on every basis state of the simulated registers), `none` elsewhere.

Running time: on the basis states of the simulated registers, the only inputs
the measurement sees, it is `some` of `extractLabel`, so measuring it is measuring `extractLabel`,
whose running time is polynomial in `t`, `tTest`, `Q` and the proof size when `E` is; the
restriction (a membership test over all basis states, not efficient) is a device of the proof
that makes the label type finite, and it changes no outcome of the measurement.
This running time is argued here, not proved in Lean. -/
noncomputable def extractLabelR (c : Base.Ctrl (A.withTest T).toTPKindAlg Psim Q)
    (as : Fin ((kq + Q * Psim.q)) → Out k e) (D : DB (Bits (queryBits k kN kS L)) (Out k e)) :
    Option (labelRange A T Psim Q Qs kq E) :=
  if h : extractLabel A T Psim Q Qs kq E c as D ∈ labelRange A T Psim Q Qs kq E then some ⟨_, h⟩ else none

/-- **The extraction succeeds**: the label is a statement and an output of `E_T` containing a
witness for it. -/
def labelSucceeds (rel : Set (X × Wit)) : Set (Option (labelRange A T Psim Q Qs kq E)) :=
  {o | ∃ l ∈ o, ∃ w ∈ l.1.2, (l.1.1, w) ∈ rel}

/-- **The test's outcome at the end of the run of `𝒜_E`**: the test's predicate on the residual
workspace in the output of `𝒜`. -/
def testAccepts (w : (extAt A T Psim Q Qs kq).W) : Prop :=
  T.ok (Base.advWorkspace (A.withTest T).toTPKindAlg Psim Q ((Base.pureWithTest A T Psim Q).out w.1)).1.1

/-- **The probability that the straight-line extractor `E_T` returns a witness and the test accepts,
in the Extract′ game** (the game of eq. (6) with the test's queries answered by the simulated
oracle): the simulated run of the adversary with the simulation challenger (CMS19's compressed phase
oracle), the extraction queries of `E_T` (the verifier's and the simulator's recorded queries)
answered by the same oracle, the measurement of `E_T`'s output (the partition of the database by
`extractLabelR`), then the test's steps and queries answered by the compressed oracle patched by the
simulator's assignments (`segRun`), then the measurement of the test's outcome (`extractAtProb`).

This definition is a probability and has no running time of its own. Running time of the procedure
it measures, the output-only extractor `ESL^out`: `ESL^out` is the database extractor's run up to
the appended queries (the compressed oracle on the sorted sparse encoding, Zha19 p. 7 and pp. 13–14;
DFMS22 App. B), with `K = kq + Q · q` classical queries computed from the output and the
challenger's registers (`ctrlExpansion`), followed by the measurement of `E_T`'s output
(`extractLabel`). That measurement takes time linear in the classical running time of `E_T` on the
sparse encoding of the database (DFMS22, ePrint 2021/280, App. B, Lemma B.1, p. 26: coherent
evaluation, copy of the output, uncomputation); `E_T` reads at most `visitBound` digests, each a
scan of the at most `T₀ + K ≤ t + tTest + Q · q + K` entries, makes `2n` oracle reads of the
recorded queries and answers (each a scan of the `K` queries and the `Q · q` assignments) and calls
`E` at most `n + 1` times (`targetedExtractor`). The test's queries are answered by the same
compressed oracle, patched by the assignment list. By the argument above, `ESL^out` runs in quantum
polynomial time under the conditions of the database extractor's running time: when the adversary,
the simulator, `E`, the statement decoder and membership in the relation are polynomial-time and the
input bit length `m`, `k` and `e` are polynomial in the input length. This running time is argued
here, not proved in Lean. -/
noncomputable def extractQTestProb (rel : Set (X × Wit)) : ℝ≥0∞ :=
  ENNReal.ofReal <| extractAtProb (outEquiv k e) ((ctrlExpansion (A.withTest T).toTPKindAlg Psim Q Qs)) ((kq + Q * Psim.q))
    (Base.pureWithTest A T Psim Q) (Base.splitStep A T Psim Q) (Base.pureCtrl A T Psim Q) (extractLabelR A T Psim Q Qs kq E)
    (testAccepts A T Psim Q Qs kq) (labelSucceeds A T Psim Q Qs kq E rel)

/-- **The generalized instability of the restricted label** is at most `V / 2^(8k)`: the label
changes only where `E_T`'s output does (`instabPart_le_instabPart`,
`instabPart_targetedExtractorOf_le`). -/
theorem instabPart_extractLabelR_le (c : Base.Ctrl (A.withTest T).toTPKindAlg Psim Q)
    (as : Fin ((kq + Q * Psim.q)) → Out k e) (t : ℕ) :
    (instabPart (extractLabelR A T Psim Q Qs kq E c as) t).toReal ≤ M.visitBound / 2 ^ (8 * k) := by
  have h := (instabPart_le_instabPart (t := t) (L := extractLabelR A T Psim Q Qs kq E c as)
    (L' := targetedExtractorOf (A.withTest T).toTPKindAlg Psim Q E c
      (fun j => ((ctrlExpansion (A.withTest T).toTPKindAlg Psim Q Qs)).next c ((List.ofFn as).take j)) as)
    fun D D' hne heq => hne (by
      have hl : extractLabel A T Psim Q Qs kq E c as D = extractLabel A T Psim Q Qs kq E c as D' := by
        rw [extractLabel, extractLabel]
        exact congrArg (Prod.mk _) heq
      unfold extractLabelR
      generalize extractLabel A T Psim Q Qs kq E c as D = l at hl ⊢
      subst hl
      rfl)).trans
    (instabPart_targetedExtractorOf_le (A.withTest T).toTPKindAlg Psim Q E c _ as t)
  have hfin : (M.visitBound / 2 ^ (8 * k) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  refine (ENNReal.toReal_mono hfin h).trans_eq ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]

variable {A T E} {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]
  (fx : X' → X)

/-- **Prove against Extract′ at one adversary and one test**: the probability that `A` wins Prove and its test,
run on the residual state with the final oracle, accepts (`winTestProb` of `A^Π` at the test's
outcome) is at most the probability that `E_T` returns a witness in Extract′ with the test
accepting (`extractQTestProb`), plus the knowledge error at `kq + Q · q` appended queries and
`b + kq + Q · q` queries in all (`b = branchQueries` of `A^Π`, its per-branch query count with the
simulation challenger, which includes the test's queries), plus
the swap error at `T.queries`. The chain: `winO_expandAt` with `expand_mem_simExtGame`,
`oracle_sim_card`, the cover with `E_T` (`cover_simExtGame_targeted`),
`dbProb_bad_union_le_of_queryCount` at `QueryCount.expandAt`,
the event at the end of the simulated run bounded by `foldedProb` on the support of the simulated
state (`simLaw_le_ofReal_foldedProb`, `simState_expandAt_eq_zero`), and the swap
(`abs_foldedProb_sub_extractAtProb_le` with `instabPart_extractLabelR_le`). Hypotheses: `hkq`,
the verifier's query bound; `hrbr`, causal round-by-round knowledge soundness of the composite;
`hA`, the simulator program assigns only at the keys of its chain inputs. -/
theorem winTestProb_withTest_le
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq)
    {rel : Set (X × Wit)} {St : CausalStateFn P t X} {ε : ChIdx P t → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)}
    (hA : M.SimAssignsAtKeys B Psim fx) :
    winTestProb Qs (A.withTest T) Psim Q fx (fun w => T.ok w.1) ≤
      extractQTestProb A T Psim Q Qs kq E rel +
      knowledgeError k e (kq + Q * Psim.q)
        (FullPast.branchQueries (A.withTest T) Psim Q + (kq + Q * Psim.q))
        M.senc.digestsPerInput Mg.nJ (maxError ε) +
      M.swapError T.queries := by
  classical
  set ee := outEquiv k e
  set A' := A.withTest T
  set K := kq + Q * Psim.q
  set ok' : A'.W → Prop := fun w => T.ok w.1
  set G := simExtGame A'.toTPKindAlg Psim Q Qs fx K ∩ {o | ok' (Base.advWorkspace A'.toTPKindAlg Psim Q o.out).1}
  set 𝒜 := Base.pureWithTest A T Psim Q
  set s := Base.splitStep A T Psim Q
  set κ := Base.pureCtrl A T Psim Q
  set 𝒜E := extAt A T Psim Q Qs kq
  have hs : s ≤ (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth := Nat.sub_le _ _
  have hκ : KeepsClasses 𝒜 s κ :=
    Alg.keepsClasses_toQueryAlgCoh _ (Base.ctrlOf A'.toTPKindAlg Psim Q)
      ((AdaptiveIAlg.stepsKeep_composeBothOut_withTest T
        (simExtChallenger Psim Q) id).map fun p => ((A.out p.1 : Claim X M.NIProof), p.2))
  have hout : ∀ (H : (Bits (queryBits k kN kS L)) → (XOut k e)) r, 𝒜.final H r ≠ 0 →
      κ r.1 = Base.ctrlOf A'.toTPKindAlg Psim Q (𝒜.out r.1) := fun _ _ _ => rfl
  -- Prove's event lies in the expanded game of `𝒜_E`
  have hexpand : winTestProb Qs A' Psim Q fx ok' ≤ winO ee 𝒜E G := by
    set Acc : Set (Outcome (M.Register B A'.toTPKindAlg Psim Q) (Bits (queryBits k kN kS L)) (Out k e)) :=
      {p | (Wins A'.toTPKindAlg Psim Q Qs fx (ee.symm ∘ p.oracle) p.out ∧
        ok' (Base.advWorkspace A'.toTPKindAlg Psim Q p.out).1) ∧
        A'.toTPKindAlg.Consistent (simExtChallenger Psim Q) (ee.symm ∘ p.oracle) p.out}
    have hdom := A'.realLaw_composeBothOut_le (simExtChallenger Psim Q) id ee
      {p | ∃ v, p.out = some v ∧ Wins A'.toTPKindAlg Psim Q Qs fx (ee.symm ∘ p.oracle) v ∧
        ok' (Base.advWorkspace A'.toTPKindAlg Psim Q v).1} (fun p ⟨v, hv, _⟩ => by rw [hv]; simp)
    refine hdom.trans ?_
    have hinter := A'.toTPKindAlg.realLaw_composeBothOut_inter (simExtChallenger Psim Q) ee
      (fun v f => Wins A'.toTPKindAlg Psim Q Qs fx (ee.symm ∘ f) v ∧
        ok' (Base.advWorkspace A'.toTPKindAlg Psim Q v).1)
    refine le_of_eq_of_le (by convert hinter using 1) ?_
    refine le_trans (MeasureTheory.measure_mono
      (t := {p : Outcome (Option (M.Register B A'.toTPKindAlg Psim Q)) (Bits (queryBits k kN kS L)) (Out k e) |
        ∃ o ∈ p.out, ⟨o, p.oracle⟩ ∈ Acc}) ?_) ?_
    · rintro p ⟨v, hv, hw, hc⟩
      exact ⟨v, hv, hw, hc⟩
    refine ((A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).toOuterMeasure_realLaw_le_coh ee
      (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut Acc).trans ?_
    refine winO_expandAt ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)) K 𝒜 κ (Base.ctrlOf A'.toTPKindAlg Psim Q)
      hs hκ hout fun p hp => ⟨?_, hp.1.2⟩
    rw [comapIn_ctrlExpansion]
    have hm := expand_mem_simExtGame Q Qs fx A'.toTPKindAlg hkq hA hp.2 hp.1.1
    have he : (fun a => ee ((ee.symm ∘ p.oracle) a)) = p.oracle :=
      funext fun a => ee.apply_symm_apply _
    rwa [he] at hm
  have hsimulation : winO ee 𝒜E G ≤ winS ee 𝒜E G + 2 * esqrt (K / Fintype.card (Out k e)) :=
    le_add_two_mul_of_esqrt_le (winO_le_one ee 𝒜E G) (Lifting.oracle_sim_card ee 𝒜E G)
  -- the cover with `E_T`
  set R' : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A'.toTPKindAlg Psim Q) K →
      DB (Bits (queryBits k kN kS L)) (Out k e) → Prop :=
    fun o D => TargetedExtracts A'.toTPKindAlg Psim Q rel E o D ∧ ok' (Base.advWorkspace A'.toTPKindAlg Psim Q o.out).1
  have hcover : winS ee 𝒜E G ≤ simLaw ee 𝒜E {p | R' p.1 p.2} +
      dbProb ee 𝒜E (DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)) := by
    refine (MeasureTheory.measure_mono fun p hp => ?_).trans (MeasureTheory.measure_union_le
      {p : BaseGame.Tuple (Bits (queryBits k kN kS L)) (Out k e) (M.Register B A'.toTPKindAlg Psim Q) K ×
        DB (Bits (queryBits k kN kS L)) (Out k e) | R' p.1 p.2}
      {p | p.2 ∈ DB.restrict Query.toBits ⁻¹' (M.bad rel E St ∪ digestCollision)})
    rcases cover_simExtGame_targeted Qs fx St hrbr hp.1.1 hp.2 with hE | hbad
    · exact Or.inl ⟨hE, hp.1.2⟩
    · exact Or.inr hbad
  have hpost : ∀ i, s ≤ i → i < (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth →
      (AdaptiveIAlg.tpQueryCount ee A' (simExtChallenger Psim Q) id
        (·.getD (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)).C i =
        Set.univ := by
    intro i hi _
    have hS : A'.toTPKindAlg.slots * ((simExtChallenger Psim Q).q + A'.toTPKindAlg.width) ≤ i := by
      refine le_trans ?_ hi
      show _ ≤ (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth - T.queries
      rw [KindAlg.composeBothOut, Circuit.toAlg_depth, ReprogrammedCircuit.queries_toCircuit,
        KindAlg.queries_fullCircBoth]
      change _ ≤ _ + A.width * (A.post + T.batches) - A.width * T.batches
      have hw : A.width * (A.post + T.batches) = A.width * A.post + A.width * T.batches := by ring
      omega
    ext w
    simp only [Set.mem_univ, iff_true]
    show w.1.1.1 ∈ A'.recSet (simExtChallenger Psim Q) i
    rw [A'.recSet_post (simExtChallenger Psim Q) hS]
    trivial
  have hcount := QueryCount.expandAt K ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)) s κ
    (AdaptiveIAlg.tpQueryCount ee A' (simExtChallenger Psim Q) id
      (·.getD (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)) hs hpost
  have hbad := dbProb_bad_union_le_of_queryCount (M := M) hrbr 𝒜E hcount
  -- the event at the end of the simulated run is the folded event
  have hfold : simLaw ee 𝒜E {p | R' p.1 p.2} ≤ ENNReal.ofReal (foldedProb ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs))
      K 𝒜 s κ (extractLabelR A T Psim Q Qs kq E) (testAccepts A T Psim Q Qs kq) (labelSucceeds A T Psim Q Qs kq E rel)) := by
    refine simLaw_le_ofReal_foldedProb ee _ K 𝒜 s κ _ _ _ fun b hb ⟨hT, hok⟩ => ⟨hok, ?_⟩
    have hc : κ b.1.1.1 = Base.ctrlOf A'.toTPKindAlg Psim Q (𝒜.out b.1.1.1) := by
      by_contra hne
      exact hb (simState_expandAt_eq_zero ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)) K 𝒜 κ hs hκ
        (Q := fun w => κ w = Base.ctrlOf A'.toTPKindAlg Psim Q (𝒜.out w)) hout hne)
    have hmem : extractLabel A T Psim Q Qs kq E (κ b.1.1.1) (fun j => ee (b.1.1.2.2 j)) (slotsDB ee b.2) ∈
        labelRange A T Psim Q Qs kq E :=
      Finset.mem_image_of_mem _ (Finset.mem_univ b)
    show extractLabelR A T Psim Q Qs kq E (κ b.1.1.1) (fun j => ee (b.1.1.2.2 j)) (slotsDB ee b.2) ∈
      labelSucceeds A T Psim Q Qs kq E rel
    rw [extractLabelR, dite_eq_left_of_eq_true (eq_true hmem)]
    obtain ⟨w, hw, hrel⟩ := hT
    refine ⟨_, rfl, w, ?_, ?_⟩
    · have hw' : w ∈ targetedExtractorOf A'.toTPKindAlg Psim Q E (Base.ctrlOf A'.toTPKindAlg Psim Q (𝒜.out b.1.1.1))
          (fun j => ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)).next (κ b.1.1.1)
            ((List.ofFn fun i => ee (b.1.1.2.2 i)).take j))
          (fun j => ee (b.1.1.2.2 j)) (slotsDB ee b.2) := hw
      rw [← hc] at hw'
      exact hw'
    · show ((κ b.1.1.1).1.stmt, w) ∈ rel
      rw [hc]
      exact hrel
  -- the swap
  have : Nonempty (Base.Ctrl A'.toTPKindAlg Psim Q) :=
    ⟨Base.ctrlOf A'.toTPKindAlg Psim Q (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut⟩
  have hswap := abs_foldedProb_sub_extractAtProb_le ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)) K 𝒜 s κ
    (extractLabelR A T Psim Q Qs kq E) (testAccepts A T Psim Q Qs kq) (labelSucceeds A T Psim Q Qs kq E rel) hs hκ
    (fun c a => instabPart_extractLabelR_le A T Psim Q Qs kq E c a _)
  have hTq : (((A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth - s : ℕ) : ℝ) ≤ T.queries := by
    have hsdef : s = (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth - T.queries := rfl
    exact_mod_cast (show (A'.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth - s ≤ T.queries by omega)
  have hfold' : ENNReal.ofReal (foldedProb ee ((ctrlExpansion A'.toTPKindAlg Psim Q Qs)) K 𝒜 s κ
      (extractLabelR A T Psim Q Qs kq E) (testAccepts A T Psim Q Qs kq) (labelSucceeds A T Psim Q Qs kq E rel)) ≤
      extractQTestProb A T Psim Q Qs kq E rel + M.swapError T.queries := by
    rw [extractQTestProb, Base.swapError]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    have h1 := (le_abs_self _).trans hswap
    linarith [mul_le_mul_of_nonneg_right hTq
      (Real.sqrt_nonneg (24 * (M.visitBound / 2 ^ (8 * k))))]
  calc winTestProb Qs A' Psim Q fx ok'
      ≤ winS ee 𝒜E G + 2 * esqrt (K / Fintype.card (Out k e)) := hexpand.trans hsimulation
    _ ≤ extractQTestProb A T Psim Q Qs kq E rel + M.swapError T.queries +
          6 * ((FullPast.branchQueries A' Psim Q + K : ℕ) : ℝ≥0∞) ^ 2 *
            ((maxError ε : ℝ≥0∞) + (((max 2 M.senc.digestsPerInput + Mg.nJ + 1) *
              (FullPast.branchQueries A' Psim Q + K) : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) +
          2 * esqrt (K / Fintype.card (Out k e)) := by
        gcongr
        exact hcover.trans (add_le_add (hfold.trans hfold') hbad)
    _ = _ := by
        rw [knowledgeError]
        ring

end SimOracle

/-! ### The bundled notion -/

section Notion

variable {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x)

/-- **The probability that `E_T` returns a witness in Extract′ of the spBCS compiler and the
test accepts**, averaged over the auxiliary input (`extractQTestProb`). -/
noncomputable def extractsQTest [DecidableEq X] {tq Q tTest : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (kq : ℕ)
    {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (T : 𝒜.QTest tTest) :
    ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * extractQTestProb (𝒜.alg a) (T.test a) Psim Q Qs kq E rel

variable (M B) in
/-- **Simulation-sound extractability with the test answered by the simulated oracle, for the
spBCS compiler over the game's adversaries** (proof-internal; the
headline form is `SimulationSoundExtractableSimOracle`, over the query-bounded adversaries). -/
def SimulationSoundExtractableSimOracleGame [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq tTest Q : ℕ)
    (𝒜 : M.SimExtractionAdversary B X' tq Q) (T : 𝒜.QTest tTest),
    acceptsQTest Qs 𝒜 (Sim.comap fx) fx T ≤ extractsQTest Qs 𝒜 (Sim.comap fx) kq rel E T +
      ε tq tTest Q

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS compiler for tests that query the
oracle, with the test answered by the simulated oracle after extraction** (Unruh 2017, Definition 14, p. 21, eq. (6) with `d = 1`, `p = 1`, with Extract′ for the
extraction game; the shape of CDHZ26, ePrint 2025/2166, Definition 10.3, p. 71): for every finite
type `X'` of queried statements, every query-bounded adversary (`Quantum.QueryBoundedAdversary`)
with at most `tq` queries of its own whose first `Q` proof queries are answered, and every test of its
residual state with at most `tTest` queries to the final oracle, the probability that the
adversary outputs a fresh statement with a proof the spBCS verifier accepts under the final
oracle and the test accepts (`acceptsQTest`) is at most the probability that, in Extract′, `E_T`
returns a witness for that statement and the test, run after the extraction with its queries
answered by the simulated oracle patched by the simulator's assignments, accepts
(`extractsQTest`), plus `ε tq tTest Q`. -/
def SimulationSoundExtractableSimOracle [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq tTest Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq) (T : (𝒜.toSimExtraction Q).QTest tTest),
    acceptsQTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) fx T ≤
      extractsQTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) kq rel E T + ε tq tTest Q

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **Simulation-sound extractability with the test answered by the simulated oracle, for the
spBCS compiler over the game's adversaries** (proof-internal): the
bound of `simulation_sound_extractability_sim_oracle` for every adversary of the game. -/
theorem simulation_sound_extractability_sim_oracle_game [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableSimOracleGame B Qs rel E kq Sim
      fun tq tTest Q => M.simExtractionError kq (maxError ε) Sim.q (tq + tTest) Q +
        M.swapError tTest := by
  intro X' _ _ fx tq tTest Q 𝒜 T
  set Psim := Sim.comap fx
  have hq : Psim.q = Sim.q := rfl
  rw [← hq]
  beta_reduce
  refine Base.SimExtractionAdversary.tsum_le_tsum_add (𝒜.withTest T) fun a => ?_
  refine (winTestProb_withTest_le Q Qs kq fx hkq hrbr (hA.comap fx)).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl (add_le_add ?_ (M.swapError_mono (T.queries_le a)))
  unfold simExtractionError knowledgeError
  set B' := (𝒜.alg a).withTest (T.test a)
  have h2 : B'.width * (B'.budget + B'.post) ≤ tq + tTest := (𝒜.withTest T).queries_le a
  have hb : FullPast.branchQueries B' Psim Q + (kq + Q * Psim.q) ≤
      tq + tTest + Q * Psim.q + (kq + Q * Psim.q) := by
    change B'.width * B'.budget + Q * Psim.q + B'.width * B'.post + (kq + Q * Psim.q) ≤
      tq + tTest + Q * Psim.q + (kq + Q * Psim.q)
    nlinarith
  gcongr

/-- **Weak simulation-sound extractability of the spBCS compiler for tests that query the
oracle** (Unruh 2017, Definition 14, p. 21, weak variant, eq. (6) with `d = 1`, `p = 1`,
with the test in Extract′ answered by the simulated oracle after extraction;
`SimulationSoundExtractableSimOracle`): at the hypotheses of `simulation_sound_extractability`
(causal round-by-round knowledge soundness `hrbr`, the verifier's query bound `hkq`, a counted
simulator program `Sim` that assigns only at the keys of its chain inputs `hA`), for every
query-bounded adversary with at most `tq` queries and `Q` proof queries and every test of
its residual state with at most `tTest` queries to the final oracle, the probability that the
adversary outputs a fresh statement with a proof the spBCS verifier accepts under the final
reprogrammed oracle and the test accepts is at most the probability that the targeted extractor
`E_T` (built from `E`, independent of the test) returns a witness for that statement in Extract′
and the test accepts, plus `simExtractionError kq (max_c ε c) q (tq + tTest) Q + swapError tTest`
with `q` the queries of one run of `Sim`: the spBCS knowledge error with the test's queries
counted as adversary queries, and `tTest √(24 V / 2^(8k))` for measuring `E_T`'s output before
the test (`V = visitBound`). -/
theorem simulation_sound_extractability_sim_oracle [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableSimOracle B Qs rel E kq Sim
      fun tq tTest Q => M.simExtractionError kq (maxError ε) Sim.q (tq + tTest) Q +
        M.swapError tTest :=
  fun X' _ _ fx tq tTest Q 𝒜 T =>
    simulation_sound_extractability_sim_oracle_game Qs hkq hrbr Sim hA X' fx tq tTest Q
      (𝒜.toSimExtraction Q) T

end Notion

end

end GordieHowe.SPBCS
