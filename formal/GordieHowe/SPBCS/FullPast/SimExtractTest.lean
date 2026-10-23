-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtract
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTest
public import GordieHowe.Model.Quantum.Interactive.QueryFreeTest

@[expose] public section

/-!
# Tests of the residual state in the series–parallel base model

The tests of the test forms of simulation-sound extractability (Unruh 2017, ePrint 2017/398,
Definition 14, p. 21, eq. (6)) at the series–parallel base model (`GordieHowe.SPBCS.FullPast`). The namespace
`GordieHowe.SPBCS` states the test forms for the spBCS compiler with them (`GordieHowe/SPBCS/SimExtractTest.lean`:
`GordieHowe.SPBCS.simulation_sound_extractability_folded`,
`GordieHowe.SPBCS.simulation_sound_extractability_query_free`, with Unruh's Prove with a query-free test
`GordieHowe.SPBCS.acceptsQFTest`).

- `SimExtractionAdversary.QTest`, `withTest`, `QTest.okWithTest`: a test of the residual state
  with at most `tTest` queries to the final oracle, and the adversary followed by the test
  (`A^Π`), with `tq + tTest` queries.
- `SimExtractionAdversary.QFTest`, `QFTest.toQTest`: a query-free test, as a test with no query
  batch.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : Base P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {X' : Type} [Fintype X'] [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC] {tq Q : ℕ}

/-! ### Tests of the residual state -/

/-- **A residual-state test with at most `tTest` queries** (Unruh 2017, Definition 14, p. 21, the
test `Π^{H_final}_{x‖π}`): for each auxiliary value `a`, a test of the residual state of
`𝒜.alg a` (`AdaptiveIAlg.QTest`: channels on its registers alternating with batches of queries to
the final oracle, and an outcome predicate of its measured workspace) making at most `tTest`
queries. -/
structure SimExtractionAdversary.QTest (𝒜 : M.SimExtractionAdversary B X' tq Q) (tTest : ℕ) where
  /-- The test at each auxiliary value. -/
  test : (a : 𝒜.Aux) → (𝒜.alg a).QTest
  /-- At most `tTest` queries. -/
  queries_le : ∀ a, (test a).queries ≤ tTest

/-- **The adversary followed by the test** (`A^Π`): at each auxiliary value,
`AdaptiveIAlg.withTest`; it makes at most `tq + tTest` queries of its own on every branch.

Running time: at each auxiliary value that of `AdaptiveIAlg.withTest`, the adversary followed by
the test. This running time is argued here, not proved in Lean. -/
noncomputable def SimExtractionAdversary.withTest {tTest : ℕ}
    (𝒜 : M.SimExtractionAdversary B X' tq Q) (T : 𝒜.QTest tTest) :
    M.SimExtractionAdversary B X' (tq + tTest) Q where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  alg a := (𝒜.alg a).withTest (T.test a)
  queries_le a := by
    rw [AdaptiveIAlg.withTest_queries]
    exact add_le_add (𝒜.queries_le a) (T.queries_le a)

/-- **The test's outcome on the workspace of `A^Π`**: its predicate on `A`'s part of the
workspace (the copy register holds the output). -/
def SimExtractionAdversary.QTest.okWithTest {tTest : ℕ} {𝒜 : M.SimExtractionAdversary B X' tq Q}
    (T : 𝒜.QTest tTest) : (a : (𝒜.withTest T).Aux) → ((𝒜.withTest T).alg a).W → Prop :=
  fun a w => (T.test a).ok w.1

/-- **A query-free test of the residual state** of `𝒜` (Unruh 2017, Definition 14, p. 21, the test
`Π_{x‖π}`, without oracle queries): at each auxiliary value, a channel on the adversary's registers
and an outcome predicate of the workspace measured afterwards. -/
abbrev SimExtractionAdversary.QFTest (𝒜 : M.SimExtractionAdversary B X' tq Q) : Type 1 :=
  (a : 𝒜.Aux) → (𝒜.alg a).QFTest

/-- **A query-free test as a test with no query batch**: `𝒜.withTest T.toQTest` is the adversary
followed by the test (`A^Π`), with the queries of `𝒜`. -/
noncomputable def SimExtractionAdversary.QFTest.toQTest {𝒜 : M.SimExtractionAdversary B X' tq Q}
    (T : 𝒜.QFTest) : 𝒜.QTest 0 where
  test a := (T a).toQTest
  queries_le a := (AdaptiveIAlg.QFTest.queries_toQTest (T a)).le

end Base
end GordieHowe.SPBCS
