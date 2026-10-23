-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.SimExtractTest
public import GordieHowe.SPBCS.Extraction.CohTest

@[expose] public section

/-!
# The challenger's registers for Unruh's form, in the series–parallel base model

`ChalRegs`: the challenger's registers of the composition of an adversary with the simulation
challenger, at the series–parallel base model (`GordieHowe.SPBCS.FullPast`). The namespace `GordieHowe.SPBCS` states with them, for the spBCS compiler, the
implication to Unruh's Definition 14 for tests that make no oracle queries (the paper's Section
6.1.2, Weak online simulation extractability) (`GordieHowe/SPBCS/SimExtractUnruh.lean`: Unruh's Extract
with a query-free test, `GordieHowe.SPBCS.extractQFTestProbAt`, its per-event equality
`GordieHowe.SPBCS.extractQFTestProbAt_eq_simProb`, `GordieHowe.SPBCS.extractQFTestProbAt_extractsFresh`,
`GordieHowe.SPBCS.extractsFreshQFTest_eq`, and the headline
`GordieHowe.SPBCS.simulation_sound_extractability_query_free_unruh`), from the model-independent
density-matrix argument (`GordieHowe/SPBCS/Extraction/CohTest.lean`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM QROM.ExpandAdv
open scoped NNReal ENNReal ComplexOrder

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  {M : Base P t X k kN kS L e} {B : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {V : X → FullTr P t → Bool} (Qs : ∀ x, M.IOPQueries V x) {X' : Type} [Fintype X']
  [DecidableEq X'] {SC : Type} [Fintype SC] [DecidableEq SC]

variable (A : AdaptiveIAlg (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B)
    (Claim X M.NIProof))
  (Psim : NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X' (M.Response B) SC) (Q kq : ℕ)

/-- The challenger's registers of the composition of `A` with the simulation challenger. -/
abbrev ChalRegs : Type :=
  ChallengerRegs (Bits (queryBits k kN kS L)) (XOut k e) X' A.slots (simExtChallenger Psim Q).q
    (simExtChallenger Psim Q).Coins

end Base
end GordieHowe.SPBCS
