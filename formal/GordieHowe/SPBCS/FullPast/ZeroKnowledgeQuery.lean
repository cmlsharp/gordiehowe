-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledgeROMQuery
public import GordieHowe.SPBCS.FullPast.ProverProg
public import GordieHowe.Model.QROM.LeafZK

@[expose] public section

/-!
# Query-counted zero knowledge of the compiler over a composition in the QROM

Zero knowledge of the compiled argument of a composition against quantum adversaries all of whose
queries are counted (Unruh 2017 Definition 6, p. 14, `NIZK.ZeroKnowledgeQueryBounded`, with the pure
form `GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure`): the honest prover `GordieHowe.SPBCS.niProverZKM` and the
simulator `GordieHowe.SPBCS.niJointSimulator` of `GordieHowe.SPBCS.everlastingZeroKnowledge`,
with the leaf term charged per query instead of statistically. The error (`GordieHowe.SPBCS.Base.zkErrorQuery`) is

    4 Q t / 2^(4kS) + Q (Q - 1) / 2^(8kS)                (Fiat–Shamir salts, as `zkError`)
    + Q · keyCollision (t.size n) k                       (lazy sampling of the streams)
    + Q (4 t √U / 2^(4kN) + 3 (U + Q U² + U²) / 2^(8kN))  (hidden leaf digests, `U = |Pos|`)
    + Q · (overrun + δ)                                   (the observation)

in place of `Q · U · leafBound k kN L`.

**The argument** (`GordieHowe.QROM.zeroKnowledgeQueryBoundedPure_comap_of_leafKernel`), with the leaf kernel,
its laws and the lazy kernel of the classical proof (`GordieHowe/SPBCS/FullPast/ZeroKnowledgeROMQuery.lean`):
1. the honest prover against the lazily sampled honest reply `lazyKernel`, by the salted QROM
   theorem (`GordieHowe.QROM.zeroKnowledgeAfterAdaptive_of_sliceClose`) with the one-proof bound
   `keyCollision (t.size n) k` at every salt (`sliceCloseAt_lazy`);
2. the honest-digest kernel against the uniform-digest kernel (`GordieHowe/Model/QROM/HiddenLeaves.lean`);
3. the uniform-digest kernel against the simulator, at `overrun + δ` per proof query
   (`tvDist_kD_joint_le`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

/-- The square root of a power of two with an exponent divisible by eight. -/
theorem sqrt_two_pow_eight_mul (a : ℕ) : √((2 : ℝ) ^ (8 * a)) = 2 ^ (4 * a) := by
  rw [show 8 * a = 4 * a * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-- **The query-counted zero-knowledge error of the composite in the QROM** at the HVZK error
`δ`, `t` queries and `Q` proof queries: `4 Q t / 2^(4kS) + Q (Q - 1) / 2^(8kS) +
Q · keyCollision (t.size n) k + Q (4 t √U / 2^(4kN) + 3 (U + Q U² + U²) / 2^(8kN)) +
Q · (overrun + δ)` with `U = |Pos|` (`zeroKnowledgeQuery`). -/
noncomputable def zkErrorQuery (δ : ℝ≥0) (tq Q : ℕ) : ℝ :=
  4 * Q * tq / 2 ^ (4 * kS) + Q * (Q - 1) / 2 ^ (8 * kS) +
    Q * (SPBCS.keyCollision (t.size n) k).toReal +
    Q * (4 * tq * √(Fintype.card M.Pos) / 2 ^ (4 * kN) +
      3 * ((Fintype.card M.Pos + Q * Fintype.card M.Pos ^ 2 + Fintype.card M.Pos ^ 2) /
        2 ^ (8 * kN))) + Q * (M.overrun.toReal + δ)

end Base
end GordieHowe.SPBCS
