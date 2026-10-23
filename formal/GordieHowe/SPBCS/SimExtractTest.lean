-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.SimExtract
public import GordieHowe.SPBCS.FullPast.SimExtractTest

@[expose] public section

/-!
# Simulation-sound extractability of the spBCS compiler with tests

The test forms of simulation-sound extractability (paper `thm:bcs-se`(1) and the implication from
`def:bcs-se` to Unruh's Definition 14 in the paper's Section 6.1.2; Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6)) for the spBCS compiler, from
`simulation_sound_extractability_game` (`GordieHowe/SPBCS/SimExtract.lean`), with the tests and the
adversary followed by the test of the compiler over the term
(`GordieHowe.SPBCS.Base.SimExtractionAdversary.QTest`, `withTest`, `QFTest`,
`GordieHowe/SPBCS/FullPast/SimExtractTest.lean`).

- `simulation_sound_extractability_folded`: for tests that query the final oracle, folded into the
  adversary on both sides (`SimulationSoundExtractableFolded`).
- `acceptsQFTest`, `acceptsQTest_toQTest`: Unruh's Prove with a query-free test, and its equality
  with Prove of `A^Π`.
- `simulation_sound_extractability_query_free`: for every query-free test, Unruh's Prove with the
  test on the left and the extraction event of `A^Π` on the right
  (`SimulationSoundExtractableQueryFree`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open Base (SimExtractionAdversary)
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC] {tq Q : ℕ}

/-! ### Tests that query the oracle, folded into the adversary -/

/-- **The probability that `𝒜` wins Prove of the spBCS compiler and the test accepts** (Unruh
2017, Definition 14, p. 21, eq. (6), right-hand side, weak variant): `acceptsTest` of `A^Π`. -/
noncomputable def acceptsQTest {tTest : ℕ} (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (T : 𝒜.QTest tTest) : ℝ≥0∞ :=
  acceptsTest Qs (𝒜.withTest T) Psim fx T.okWithTest

/-- **The probability that `dbExtract` returns a witness, the statement is fresh and the test
accepts, with the test inside the simulation**: `extractsFreshTest` of `A^Π`. -/
noncomputable def extractsFolded [DecidableEq X] {tTest : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (kq : ℕ) (fx : X' → X) {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (T : 𝒜.QTest tTest) : ℝ≥0∞ :=
  extractsFreshTest Qs (𝒜.withTest T) Psim kq fx rel E T.okWithTest

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS compiler for tests that query the
oracle, with the test folded into the adversary** (a variant of Unruh 2017, Definition 14, p. 21,
eq. (6) with `d = 1`, `p = 1`, except that the extraction event is that of the simulated run of
the adversary followed by the test): for every finite type `X'` of queried statements, every
adversary with at most `tq` queries of its own and at most `Q` simulation queries and every test of
its residual state with at most `tTest` queries to the final oracle, the probability that the
adversary outputs a fresh statement with a proof the spBCS verifier accepts under the final
oracle and the test accepts is at most the probability that `dbExtract` at `E` extracts a witness
from the simulated run of the adversary followed by the test, the statement is fresh and the test
accepts, plus `ε (tq + tTest) Q`. -/
def SimulationSoundExtractableFolded [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq tTest Q : ℕ)
    (𝒜 : M.SimExtractionAdversary B X' tq Q) (T : 𝒜.QTest tTest),
    acceptsQTest Qs 𝒜 (Sim.comap fx) fx T ≤ extractsFolded Qs 𝒜 (Sim.comap fx) kq fx rel E T +
      ε (tq + tTest) Q

variable {Qs} in
/-- **The bound over the game's adversaries gives the folded bound** at the same error, applied
to the adversary followed by the test, with `tq + tTest` queries. -/
theorem SimulationSoundExtractableFreshGame.toFolded [DecidableEq X] {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {kq : ℕ}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC}
    {ε : ℕ → ℕ → ℝ≥0∞} (h : M.SimulationSoundExtractableFreshGame B Qs rel E kq Sim ε) :
    M.SimulationSoundExtractableFolded B Qs rel E kq Sim ε := fun X' _ _ fx tq tTest Q 𝒜 T =>
  h X' fx (tq + tTest) Q (𝒜.withTest T) T.okWithTest

/-! ### Query-free tests: Unruh's Prove -/

/-- **The event of Prove of the spBCS compiler** on the measured output `o` and the
challenger's registers `u`, with base oracle `H`: no statement sent to the simulator is the
statement of `o`, and the spBCS verifier accepts `o` under `H` reprogrammed by the simulator's
assignments. `Wins` is this event at the registers' output (`wins_iff_winsAt`). -/
def WinsAt (fx : X' → X)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
    (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (Claim X M.NIProof))
    (H : Bits (queryBits k kN kS L) → XOut k e) (o : Claim X M.NIProof)
    (u : ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots
      (simExtChallenger Psim Q).q (simExtChallenger Psim Q).Coins) : Prop :=
  (∀ x' ∈ (A.toTPKindAlg.stateAt (simExtChallenger Psim Q) u A.slots).history.map
      HistoryEntry.request, fx x' ≠ o.stmt) ∧
    M.Accepts (chainOracle (H.reprogram (A.toTPKindAlg.postAss (simExtChallenger Psim Q) u)))
      o.stmt o.proof (Qs o.stmt)

theorem wins_iff_winsAt (fx : X' → X)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q : ℕ)
    (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
      (Claim X M.NIProof))
    (H : Bits (queryBits k kN kS L) → XOut k e) (v : M.Register B A.toTPKindAlg Psim Q) :
    Wins A.toTPKindAlg Psim Q Qs fx H v ↔
      WinsAt Qs fx Psim Q A H (Base.advOut A.toTPKindAlg Psim Q v) v.chal :=
  Iff.rfl

/-- **Unruh's Prove with a query-free test for the spBCS compiler** (Unruh 2017,
Definition 14, p. 21, eq. (6), right-hand side, weak variant, for a test without oracle queries):
averaged over the auxiliary input, `𝒜` runs against the simulation challenger; its output is
measured; the statement is fresh and the spBCS verifier accepts under the final oracle
(`WinsAt`); then the test's channel acts on the unmeasured registers and the test accepts on the
measured workspace (`AdaptiveIAlg.proveTestProb`). -/
noncomputable def acceptsQFTest (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (T : 𝒜.QFTest) : ℝ≥0∞ :=
  ∑' a, 𝒜.aux a * (𝒜.alg a).proveTestProb (T a) (simExtChallenger Psim Q)
    fun o u H => WinsAt Qs fx Psim Q (𝒜.alg a) H o u

/-- **Test absorption in Prove for the spBCS compiler**: Prove of the adversary followed by
the query-free test (`A^Π`), reading the recorded outcome, is Unruh's Prove with the test. -/
theorem acceptsQTest_toQTest (𝒜 : M.SimExtractionAdversary B X' tq Q)
    (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC)
    (fx : X' → X) (T : 𝒜.QFTest) :
    acceptsQTest Qs 𝒜 Psim fx T.toQTest = acceptsQFTest Qs 𝒜 Psim fx T := by
  refine tsum_congr fun a => ?_
  congr 1
  exact AdaptiveIAlg.proveFoldedProb_eq (T a) (simExtChallenger Psim Q) (outEquiv k e)
    fun o u H => WinsAt Qs fx Psim Q (𝒜.alg a) H o u

variable (M B) in
/-- **Weak simulation-sound extractability of the spBCS compiler for query-free tests, with
Unruh's Prove** (a variant of Unruh 2017, Definition 14, p. 21, eq. (6) with `d = 1`, `p = 1`, for
residual-state tests without oracle queries, with the extraction event of the adversary followed by
the test): for every finite type `X'` of queried statements, every adversary with at most `tq`
queries of its own and at most `Q` simulation queries and every query-free test of its residual
state, the probability of Unruh's Prove with the test (`acceptsQFTest`) is at most the probability
that `dbExtract` at `E` extracts a witness from the simulated run of the adversary followed by the
test, the statement is fresh and the test accepts (`extractsFolded`), plus `ε tq Q`. -/
def SimulationSoundExtractableQueryFree [DecidableEq X] {Wit : Type} (rel : Set (X × Wit))
    (E : CausalExtractor P t X Wit) (kq : ℕ)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (X' : Type) [Fintype X'] [DecidableEq X'] (fx : X' → X) (tq Q : ℕ)
    (𝒜 : M.SimExtractionAdversary B X' tq Q) (T : 𝒜.QFTest),
    acceptsQFTest Qs 𝒜 (Sim.comap fx) fx T ≤
      extractsFolded Qs 𝒜 (Sim.comap fx) kq fx rel E T.toQTest + ε tq Q

variable {Qs} in
/-- **The folded bound gives the bound for query-free tests** at the same error, at `tTest = 0`. -/
theorem SimulationSoundExtractableFolded.toQueryFree [DecidableEq X] {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {kq : ℕ}
    {Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B) SC}
    {ε : ℕ → ℕ → ℝ≥0∞} (h : M.SimulationSoundExtractableFolded B Qs rel E kq Sim ε) :
    M.SimulationSoundExtractableQueryFree B Qs rel E kq Sim ε := fun X' _ _ fx tq Q 𝒜 T => by
  rw [← acceptsQTest_toQTest]
  exact h X' fx tq 0 Q 𝒜 T.toQTest

/-! ### The theorems -/

variable {C : Type} [Fintype C] [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)]

/-- **Simulation-sound extractability of the spBCS compiler with a test that queries the
oracle, folded into the adversary** (`SimulationSoundExtractableFolded`): at the hypotheses of
`simulation_sound_extractability`, the bound `simExtractionError kq (max_c ε c) q (tq + tTest) Q`
with `q` the queries of one run of `Sim`; the test's queries count as adversary queries. The
extractor depends on the test, so this is not Unruh's Extract game. -/
theorem simulation_sound_extractability_folded [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableFolded B Qs rel E kq
      Sim
      (M.simExtractionError kq (maxError ε)
        Sim.q) :=
  (simulation_sound_extractability_game Qs hkq hrbr Sim hA).toFolded

/-- **Simulation-sound extractability of the spBCS compiler for query-free tests, with
Unruh's Prove** (`SimulationSoundExtractableQueryFree`): at the hypotheses of
`simulation_sound_extractability`, for every adversary with at most `tq` queries and `Q`
proof queries and every query-free test `Π` of its residual state, the probability of
Unruh's Prove with the test is at most the probability that `dbExtract` at `E`, run on the
simulated adversary followed by the test (`A^Π`), returns a witness, the statement is fresh and
the test accepts, plus `simExtractionError kq (max_c ε c) q tq Q`. -/
theorem simulation_sound_extractability_query_free [DecidableEq X] {kq : ℕ}
    (hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kq) {Wit : Type}
    {rel : Set (X × Wit)} {E : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    (Sim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) C)) (hA : M.SimAssignsAtKeys B Sim id) :
    M.SimulationSoundExtractableQueryFree B Qs rel E kq
      Sim
      (M.simExtractionError kq (maxError ε)
        Sim.q) :=
  (simulation_sound_extractability_folded Qs hkq hrbr Sim hA).toQueryFree

end

end GordieHowe.SPBCS
