-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtractTest
public import GordieHowe.SPBCS.FullPast.SimExtractUnruh

@[expose] public section

/-!
# Simulation-sound extractability of the spBCS compiler, in Unruh's form

The step on Unruh's Extract of the implication from `def:bcs-se` to Unruh's Definition 14 (the
paper's Section 6.1.2), for the coherent database extractor of the spBCS compiler (`extAdv`)
and trace-preserving adversaries, from the model-independent density-matrix argument
(`GordieHowe/SPBCS/Extraction/CohTest.lean`).

- `extractQFTestProbAt`: Unruh's Extract with a query-free test at `extAdv`;
  `extractQFTestProbAt_eq_simProb`: the per-event equality with the run of `A^Π`;
  `extractsFreshQFTest_eq`: averaged, at the fresh extraction event.
- `simulation_sound_extractability_query_free_unruh` (paper `thm:bcs-se`(1)): for every
  query-bounded adversary and every query-free test, Unruh's Prove and Unruh's Extract with the test
  (`SimulationSoundExtractableQueryFreeUnruh`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM QROM.ExpandAdv
open Base (SimExtractionAdversary)
open scoped NNReal ENNReal ComplexOrder

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- The basis of the simulated run of the coherent database extractor. -/
abbrev ExtBasis : Type :=
  SimRegister (extAdv Qs A Psim Q kq).W (Fin (k + e)) (Fin 8) (queryBits k kN kS L)
    ((A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).depth + (kq + Q * Psim.q))

/-- **The composed registers read from a basis state of the extractor's run** (the classical output
of the run, `extAdv`). -/
noncomputable abbrev extOut (b : ExtBasis Qs A Psim Q kq) : Base.Reg A Psim Q :=
  ((extAdv Qs A Psim Q kq).out b.1.1).out

/-- **The query-free test on the registers of the coherent extractor's run**: the test's channel on
the adversary's registers (`AdaptiveIAlg.testOnComposed`), the identity on the challenger's
registers, the extractor's registers, the database and the ancilla of the purification. -/
noncomputable def testOnExtract (T : A.QFTest) :
    KrausMap T.R (ExtBasis Qs A Psim Q kq) (ExtBasis Qs A Psim Q kq) :=
  testFull (outEquiv k e) (simExtractionExpansion A.toTPKindAlg Psim Q Qs)
    (kq + Q * Psim.q) (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id)
    (·.getD (A.toTPKindAlg.composeBothOut (simExtChallenger Psim Q) id).defaultOut)
    (AdaptiveIAlg.testOnComposed T (simExtChallenger Psim Q))

open Classical in
/-- **Unruh's Extract with a query-free test, at the coherent database extractor** (Unruh 2017,
ePrint 2017/398, Definition 14, p. 21, eq. (6), left-hand side, for a test without oracle queries):
the coherent database extractor runs on `A` (`extAdv`); the adversary's output `o` is measured; the
test's channel acts on the adversary's registers of the unmeasured run; then all registers are
measured, and the event `F` of `o`, the challenger's registers and the database holds and the test
accepts on the adversary's workspace. -/
noncomputable def extractQFTestProbAt (T : A.QFTest)
    (F : Claim X M.NIProof → Base.ChalRegs A Psim Q → DB (Bits (queryBits k kN kS L)) (Out k e) → Prop) :
    ℝ≥0∞ :=
  ∑ o ∈ AdaptiveIAlg.outputs A, ∑ b : ExtBasis Qs A Psim Q kq, Set.indicator
    {b | F o (extOut Qs A Psim Q kq b).chal (slotsDB (outEquiv k e) b.2) ∧
      T.ok (Base.advWorkspace A.toTPKindAlg Psim Q (extOut Qs A Psim Q kq b)).1}
    (fun b => ENNReal.ofReal ((testOnExtract Qs A Psim Q kq T
      (cutTo {b | Base.advOut A.toTPKindAlg Psim Q (extOut Qs A Psim Q kq b) = o}
        (pureMat (simState (outEquiv k e) (extAdv Qs A Psim Q kq))))) b b).re) b

variable {A} in
/-- **The extraction queries of `A^Π` at copy value `c`** are those of `A` when the output of `c`
is `A`'s output: the expansion reads only the output and the challenger's registers. -/
theorem extractionProg_withTest (T : A.QFTest) (u : Base.Reg A Psim Q) (c : A.W)
    (h : A.out c = Base.advOut A.toTPKindAlg Psim Q u) :
    extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T (simExtChallenger Psim Q)).symm (u, c)) =
      extractionProg A.toTPKindAlg Psim Q Qs u := by
  have hadv : Base.advOut (A.withTest T.toQTest).toTPKindAlg Psim Q
      ((AdaptiveIAlg.cwCopy T (simExtChallenger Psim Q)).symm (u, c)) =
      Base.advOut A.toTPKindAlg Psim Q u := h
  unfold extractionProg
  rw [hadv]
  congr 2

variable {A} in
theorem extractionProg_withTest_congr (T : A.QFTest) {u u' : Base.Reg A Psim Q} (c : A.W)
    (h : u.chal = u'.chal) :
    extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T (simExtChallenger Psim Q)).symm (u, c)) =
      extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T (simExtChallenger Psim Q)).symm (u', c)) := by
  obtain ⟨adv, chal⟩ := u
  obtain ⟨adv', chal'⟩ := u'
  change chal = chal' at h
  subst h
  rfl

/-- **Test absorption in Extract** (at the coherent database extractor): for a trace-preserving
adversary, every query-free test and every event `F` of the measured output, the challenger's
registers and the database, the probability of Unruh's Extract with the test (`extractQFTestProbAt`:
the coherent extractor on `A`, the output measured, then the test's channel on the unmeasured
registers) is the probability of the event in the coherent extractor's run on the adversary followed
by the test (`A^Π`), with the test's outcome read from the workspace of `A^Π`. -/
theorem extractQFTestProbAt_eq_simProb (hA : A.TracePreserving) (T : A.QFTest)
    (F : Claim X M.NIProof → Base.ChalRegs A Psim Q → DB (Bits (queryBits k kN kS L)) (Out k e) → Prop) :
    extractQFTestProbAt Qs A Psim Q kq T F =
      simProb (outEquiv k e) (extAdv Qs (A.withTest T.toQTest) Psim Q kq) fun c D =>
        F (Base.advOut _ Psim Q c) c.chal D ∧ T.ok (Base.advWorkspace _ Psim Q c).1.1 := by
  set C := simExtChallenger Psim Q
  set 𝒜 := A.toTPKindAlg.composeBothOut C id
  set 𝒜' := (A.withTest T.toQTest).toTPKindAlg.composeBothOut C id
  have h𝒜 : 𝒜.TracePreserving :=
    (AdaptiveIAlg.stepsTP_toTPKindAlg A).tracePreserving_composeBothOut C id
  have h𝒜' : 𝒜'.TracePreserving :=
    (AdaptiveIAlg.stepsTP_toTPKindAlg _).tracePreserving_composeBothOut C id
  -- Unruh's game
  have hL := sum_testFull_eq (outEquiv k e) (outEquiv k e)
    (simExtractionExpansion A.toTPKindAlg Psim Q Qs) (kq + Q * Psim.q) 𝒜
    (·.getD 𝒜.defaultOut) h𝒜 (AdaptiveIAlg.testOnComposed T C) (AdaptiveIAlg.outputs A)
    (fun o => {x | Base.advOut A.toTPKindAlg Psim Q (cohOut 𝒜 (·.getD 𝒜.defaultOut) x.1.1.1) = o})
    (fun o x => @ite _ (F o (cohOut 𝒜 (·.getD 𝒜.defaultOut) x.1.1.1).chal
        (slotsDB (outEquiv k e) x.2) ∧
      T.ok (Base.advWorkspace A.toTPKindAlg Psim Q (cohOut 𝒜 (·.getD 𝒜.defaultOut) x.1.1.1)).1)
      (Classical.dec _) 1 0)
  refine (Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun b _ => ?_).trans
    (hL.trans ?_)
  · simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with h1 h2 h2
    · rw [one_mul]
      rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rw [zero_mul]
  -- the run of `A^Π`
  symm
  rw [simProb_expandCoh_eq (outEquiv k e)
    (simExtractionExpansion (A.withTest T.toQTest).toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    𝒜' h𝒜' (·.getD 𝒜'.defaultOut)]
  refine (sum_densityRun_testFold (outEquiv k e) (outEquiv k e)
    (simExtractionExpansion A.toTPKindAlg Psim Q Qs)
    (simExtractionExpansion (A.withTest T.toQTest).toTPKindAlg Psim Q Qs) (kq + Q * Psim.q)
    𝒜 𝒜' (AdaptiveIAlg.testFold C T hA) (fun v => (some (𝒜.out v)).getD 𝒜.defaultOut)
    (fun v => (some (𝒜'.out v)).getD 𝒜'.defaultOut) (fun v c hl => ?_) (fun c v v' hv => ?_)
    (fun v D => @ite _ (F (Base.advOut _ Psim Q ((some (𝒜'.out v)).getD 𝒜'.defaultOut))
        ((some (𝒜'.out v)).getD 𝒜'.defaultOut).chal D ∧
      T.ok (Base.advWorkspace _ Psim Q ((some (𝒜'.out v)).getD 𝒜'.defaultOut)).1.1)
      (Classical.dec _) 1 0)).trans ?_
  · show (extractionProg A.toTPKindAlg Psim Q Qs v.1).next (Base.padQuery (kS := kS)) =
      (extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T C).symm (v.1, c))).next (Base.padQuery (kS := kS))
    rw [extractionProg_withTest Qs Psim Q T v.1 c (by
      rw [← hl]
      exact A.out_outRep _)]
  · show (extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T C).symm (v.1, c))).next (Base.padQuery (kS := kS)) =
      (extractionProg (A.withTest T.toQTest).toTPKindAlg Psim Q Qs
        ((AdaptiveIAlg.cwCopy T C).symm (v'.1, c))).next (Base.padQuery (kS := kS))
    rw [extractionProg_withTest_congr Qs Psim Q T c (congrArg (fun r => r.1.2) hv)]
  · let Fn : Claim X M.NIProof → Set (DReg A.W A.width (Bits (queryBits k kN kS L)) (XOut k e) X'
        (M.Response B)) → ℝ≥0∞ := fun o Sd => ∑ y, (@ite _ (F o y.1.1.1.1.chal
          (slotsDB (outEquiv k e) y.2) ∧ T.ok y.1.1.1.1.adv.workspace.1)
          (Classical.dec _) 1 0) *
        ENNReal.ofReal (((liftKraus (kq + Q * Psim.q)
          (AdaptiveIAlg.testOnComposed T C)).tensorId _)
          (cutTo {y | (A.cntSplit y.1.1.1.1.adv).1 ∈ Sd}
            (densityRun (outEquiv k e) (expKraus (outEquiv k e)
              (simExtractionExpansion A.toTPKindAlg Psim Q Qs) (kq + Q * Psim.q) 𝒜.step
              fun v => (some (𝒜.out v)).getD 𝒜.defaultOut)
              ((𝒜.init.mat ⊗ₖ Matrix.single (fresh (X := (Bits (queryBits k kN kS L))) (Y := (XOut k e))
                (kq + Q * Psim.q)) (fresh _) (1 : ℂ)).submatrix
                (registerSplit _ 𝒜.V) (registerSplit _ 𝒜.V))
                (𝒜.depth + (kq + Q * Psim.q)))) y y).re
    have h0 : ∀ o, Fn o ∅ = 0 := fun o => by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [cutTo_eq_zero_of_forall_notMem (S := {y : SimRegister (ExpansionRegister
        (X := (Bits (queryBits k kN kS L))) (Y := (XOut k e)) (kq + Q * Psim.q) 𝒜.V) (Fin (k + e))
        (Fin 8) (queryBits k kN kS L) (𝒜.depth + (kq + Q * Psim.q)) |
        (A.cntSplit y.1.1.1.1.adv).1 ∈ (∅ : Set (DReg A.W A.width (Bits (queryBits k kN kS L)) (XOut k e)
          X' (M.Response B)))}) fun x hx => hx]
      simp [KrausMap.apply]
    refine (Finset.sum_congr rfl fun c _ => ?_).trans
      ((AdaptiveIAlg.sum_repIs (A₀ := A) Fn h0).trans (Finset.sum_congr rfl fun o _ => ?_))
    · rfl
    · rfl

open Classical in
/-- **The fresh variant**: with the statement fresh in the extraction experiment as well (no proof query
of the challenger's registers reads as the measured statement). -/
theorem extractQFTestProbAt_extractsFresh [DecidableEq X] (hA : A.TracePreserving) (T : A.QFTest)
    (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) :
    extractQFTestProbAt Qs A Psim Q kq T (fun o u D => M.extractsAt rel E o.stmt D ∧
        ∀ x' ∈ (A.toTPKindAlg.stateAt (simExtChallenger Psim Q) u A.slots).history.map
          HistoryEntry.request, fx x' ≠ o.stmt) =
      extractFreshTestProb Qs (A.withTest T.toQTest) Psim Q kq fx rel E fun w => T.ok w.1 := by
  rw [extractQFTestProbAt_eq_simProb Qs A Psim Q kq hA, extractFreshTestProb, simProb, simProb]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, and_assoc]
  rfl

variable {A Psim Q}

variable {tq : ℕ}

open Classical in
/-- **Unruh's Extract with a query-free test, with freshness in the extraction experiment, at the
coherent database extractor of the spBCS compiler**, averaged over the auxiliary input (Unruh
2017, Definition 14, p. 21, eq. (6), left-hand side, weak variant, for a test without oracle
queries). -/
noncomputable def extractsFreshQFTest [DecidableEq X] (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (kq : ℕ)
    (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (T : 𝒜.QFTest) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * extractQFTestProbAt Qs (𝒜.alg a) Psim Q kq (T a) fun o u D =>
    M.extractsAt rel E o.stmt D ∧
      ∀ x' ∈ ((𝒜.alg a).toTPKindAlg.stateAt (simExtChallenger Psim Q) u (𝒜.alg a).slots).history.map
        HistoryEntry.request, fx x' ≠ o.stmt

/-- **Test absorption in Extract, averaged, for the spBCS compiler**: for an adversary whose
steps are channels, Unruh's Extract with a query-free test at `extAdv`, with freshness, is the fresh
extraction event of the adversary followed by the test. -/
theorem extractsFreshQFTest_eq [DecidableEq X] (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (h𝒜 : ∀ a, (𝒜.alg a).TracePreserving)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (kq : ℕ)
    (fx : X' → X) {Wit : Type} (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit)
    (T : 𝒜.QFTest) :
    extractsFreshQFTest Qs 𝒜 Psim kq fx rel E T =
      extractsFreshTest Qs (𝒜.withTest T.toQTest) Psim kq fx rel E T.toQTest.okWithTest := by
  refine tsum_congr fun a => ?_
  rw [extractQFTestProbAt_extractsFresh Qs _ Psim Q kq (h𝒜 a)]
  rfl

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS compiler for query-free tests, in
Unruh's form** (Unruh 2017, Definition 14, p. 21, eq. (6) with `d = 1`, `p = 1`, weak variant, for
residual-state tests without oracle queries; the paper's `def:bcs-se` with freshness in both
experiments): for every finite type `X'` of queried statements, every query-bounded adversary with
at most `tq` queries of its own and every query-free test of its residual state, the probability of
Unruh's Prove with the test (`acceptsQFTest`) is at most the probability of Unruh's Extract with the
test at the coherent database extractor (`extractsFreshQFTest`), plus `ε tq Q`. -/
def SimulationSoundExtractableQueryFreeUnruh [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.QBSimExtractionAdversary B X' tq) (T : (𝒜.toSimExtraction Q).QFTest),
    acceptsQFTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) fx T ≤
      extractsFreshQFTest Qs (𝒜.toSimExtraction Q) (Sim.comap fx) kq fx rel E T + ε tq Q

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **Simulation-sound extractability of the spBCS compiler for query-free tests, in Unruh's
form** (`SimulationSoundExtractableQueryFreeUnruh`): at the hypotheses of
`simulation_sound_extractability`, for every query-bounded adversary with at most `tq` queries and
`Q` proof queries and every query-free test of its residual state, the probability of
Unruh's Prove with the test is at most the probability of Unruh's Extract with the test at the
coherent database extractor (the extractor runs, the statement is measured, then the test acts on
the unmeasured registers; `dbExtract` returns a witness, the statement is fresh and the test
accepts), plus `simExtractionError kq (max_c ε c) q tq Q` with
`q` the queries of one run of `Sim`. -/
theorem simulation_sound_extractability_query_free_unruh [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableQueryFreeUnruh B Qs rel E kq
      Sim
      (M.simExtractionError kq (maxError ε)
        Sim.q) :=
  fun X' _ _ fx tq Q 𝒜 Tt => by
    rw [← acceptsQTest_toQTest, extractsFreshQFTest_eq Qs _ 𝒜.tracePreserving]
    exact simulation_sound_extractability_game Qs hkq hrbr Sim hA X' fx (tq + 0) Q
      ((𝒜.toSimExtraction Q).withTest Tt.toQTest) Tt.toQTest.okWithTest

end

end GordieHowe.SPBCS
