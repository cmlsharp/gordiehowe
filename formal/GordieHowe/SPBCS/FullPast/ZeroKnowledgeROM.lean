-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.Model.ROM.SaltedZKLastProofQuery
public import GordieHowe.Model.ROM.InteractiveNIZKLastProofQuery

@[expose] public section

/-!
# The zero-knowledge error of the series–parallel base model in the ROM

`zkErrorROM`: the error of adaptive multi-theorem statistical zero knowledge of the compiled
composite against classical adversaries with a budget of `t` queries before each proof query
(`GordieHowe.ROM.NIZK.EverlastingZeroKnowledge`). The theorem for the spBCS compiler is
`GordieHowe.SPBCS.zeroKnowledgeROM` (`GordieHowe/SPBCS/ZeroKnowledgeROM.lean`), with the prover
`GordieHowe.SPBCS.niProverZKM`, the simulator `GordieHowe.SPBCS.niJointSimulator` and the hypothesis
`GordieHowe.IOP.CausalHVZK`, by the generic classical argument
(`GordieHowe.ROM.NIZK.everlastingZeroKnowledge_of_sliceCloseAt`) at the locality in the salt
(`GordieHowe.SPBCS.saltedLocal`) and the one-proof bound at every fixed salt (`GordieHowe.SPBCS.sliceCloseAt`).
The error `zkErrorROM` is
`Q t / 2^(8kS) + Q (Q - 1) / (2 · 2^(8kS)) + Q · (keyCollision (t.size n) k + overrun + δ +
|Pos| · leafBound k kN L)`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-- **The zero-knowledge error of the composite in the classical random-oracle model.** -/
noncomputable def zkErrorROM (δ : ℝ≥0) (tq Q : ℕ) : ℝ :=
  Q * tq / 2 ^ (8 * kS) + Q * (Q - 1) / (2 * 2 ^ (8 * kS)) +
    Q * ((SPBCS.keyCollision (t.size n) k).toReal + M.overrun.toReal + δ +
      Fintype.card M.Pos * SPBCS.leafBound k kN L)

end Base
end GordieHowe.SPBCS
