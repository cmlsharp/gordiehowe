-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ZeroKnowledgeROMQuery
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.ZeroKnowledgeROMQuery
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.Model.QROM.LeafZK

@[expose] public section

/-!
# Query-counted zero knowledge of the spBCS compiler in the QROM

Zero knowledge of the spBCS compiler against quantum adversaries all of whose queries are
counted (Unruh 2017 Definition 6, p. 14, `NIZK.ZeroKnowledgeQueryBounded`, with the pure form
`GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure`): the prover `niProverZKM` and simulator `niJointSimulator`
of `GordieHowe.SPBCS.everlastingZeroKnowledge`, with the leaf term charged per query. The argument uses the pieces
below with the merge chain inputs: the leaf kernel `leafKernel`, its laws and the lazy kernel `lazyKernel` of the classical
proof (`GordieHowe/SPBCS/ZeroKnowledgeROMQuery.lean`). The error is the compiler's
`SPBCS.zkErrorQuery δ`:

    4 Q t / 2^(4kS) + Q (Q - 1) / 2^(8kS) + Q · keyCollision (t.size n) k
    + Q (4 t √U / 2^(4kN) + 3 (U + Q U² + U²) / 2^(8kN)) + Q · (overrun + δ)    (`U = |Pos|`).
-/

/-! ### The error

Zero knowledge against quantum adversaries all of whose
queries are counted (Unruh 2017 Definition 6, p. 14, `NIZK.ZeroKnowledgeQueryBounded`, with the pure
form `GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure`): the honest prover `GordieHowe.SPBCS.niProverZKM` and the
simulator `GordieHowe.SPBCS.niJointSimulator` of `GordieHowe.SPBCS.everlastingZeroKnowledge`,
with the leaf term charged per query instead of statistically. The error (`GordieHowe.SPBCS.zkErrorQuery`) is

    4 Q t / 2^(4kS) + Q (Q - 1) / 2^(8kS)                (Fiat–Shamir salts, as `zkError`)
    + Q · keyCollision (t.size n) k                       (lazy sampling of the streams)
    + Q (4 t √U / 2^(4kN) + 3 (U + Q U² + U²) / 2^(8kN))  (hidden leaf digests, `U = |Pos|`)
    + Q · (overrun + δ)                                   (the observation)

in place of `Q · U · leafBound k kN L`.

**The argument** (`GordieHowe.QROM.zeroKnowledgeQueryBoundedPure_comap_of_leafKernel`), with the leaf kernel,
its laws and the lazy kernel of the classical proof (`GordieHowe/SPBCS/ZeroKnowledgeROMQuery.lean`):
1. the honest prover against the lazily sampled honest reply `lazyKernel`, by the salted QROM
   theorem (`GordieHowe.QROM.zeroKnowledgeAfterAdaptive_of_sliceClose`) with the one-proof bound
   `keyCollision (t.size n) k` at every salt (`sliceCloseAt_lazy`);
2. the honest-digest kernel against the uniform-digest kernel (`GordieHowe/Model/QROM/HiddenLeaves.lean`);
3. the uniform-digest kernel against the simulator, at `overrun + δ` per proof query
   (`tvDist_kD_joint_le`).
-/

section

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

/-- The square root of a power of two with an exponent divisible by eight. -/
theorem sqrt_two_pow_eight_mul (a : ℕ) : √((2 : ℝ) ^ (8 * a)) = 2 ^ (4 * a) := by
  rw [show 8 * a = 4 * a * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

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

end
end GordieHowe.SPBCS

end

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  {M : SPBCS Mg P X k kN kS L e} [∀ j i, Nonempty ((P j).Challenge i)]
  {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) (B : ℕ)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Wit R : Type} [Fintype R] [Nonempty R]
  {honest : Wit → R → CausalProver P t X} {Pub : Type} {pub : X → Pub}
  {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}
  (Λ : SiteLayout Mg)

open Classical in
/-- **Query-counted zero knowledge of the spBCS compiler in the QROM, pure form** (module
docstring; Unruh 2017 Definition 6, p. 14, every query counted): at honest-verifier zero
knowledge of the composite in the form of CY24 Definition 23.1.8 (`hvzk`), for all finite
statement and witness types read in through `fx` and `fw`, every distinguisher with a budget of
`q` query slots of `n` parallel queries, `n * q ≤ tq`, and no final unitary, against environments
answering `Q` proof queries, distinguishes the prover `niProverZKM` from the simulator
`niJointSimulator` with advantage at most `zkErrorQuery δ tq Q`. -/
theorem zeroKnowledgeQuery {X' W' : Type} [Fintype X'] [DecidableEq X'] [Fintype W']
    [DecidableEq W'] (fx : X' → X) (fw : W' → Wit) (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    ZeroKnowledgeQueryBoundedPure (fun x w => (fx x, fw w) ∈ rel)
      ((M.niProverZKM B honest E Qs).comap fx fw)
      ((M.niJointSimulator VE.toViewRead B pub Sim T).comap fx) (M.zkErrorQuery δ) := by
  have hε₃ : (0 : ℝ) ≤ M.overrun.toReal + δ := add_nonneg ENNReal.toReal_nonneg δ.2
  refine (zeroKnowledgeQueryBoundedPure_comap_of_leafKernel (rel₀ := fun x w => (x, w) ∈ rel)
    (P := M.niProverZKM B honest E Qs) (S := M.niJointSimulator VE.toViewRead B pub Sim T)
    (L := leafKernel VE B honest) (K₁ := lazyKernel VE B honest) (leafKernel_laws VE B honest)
    (M.lazyEquiv R) (fun _ _ _ => rfl) (saltedLocal_lazy VE B honest)
    (sliceCloseAt_lazy VE B honest) hε₃
    (fun req O hr => tvDist_kD_joint_le VE B honest pub T hvzk req O hr) fx fw).mono
    fun tq Q => le_of_eq ?_
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have hN : (Fintype.card (MerkleSalt kN) : ℝ) = 2 ^ (8 * kN) := by
    rw [show Fintype.card (MerkleSalt kN) = 2 ^ (8 * kN) from Out.card_digest]
    push_cast
    ring
  have hE : 𝔼[_H ← (Bits (queryBits k kN kS L) → XOut k e) :
      (SPBCS.keyCollision (t.size n) k).toReal] =
      (SPBCS.keyCollision (t.size n) k).toReal :=
    Finset.expect_const Finset.univ_nonempty _
  rw [hsalt, hN, hE, Finset.card_singleton, Real.sqrt_div' _ (by positivity),
    sqrt_two_pow_eight_mul, sqrt_two_pow_eight_mul,
    SPBCS.zkErrorQuery]
  push_cast
  ring

open Classical in
/-- **Query-counted zero knowledge of the spBCS compiler in the QROM against query-bounded
adversaries** (`NARG.QROM.ZeroKnowledge`, Unruh 2017 Definition 6, p. 14, over the paper's
`(t, Q)`-adversaries, `def:adversary`, all of whose queries are counted): the prover `niProver`
and the simulator `niSimulator`, with proofs in the format `B` of the format bounds `hb`, run
through `queryEncoding` and answering `Q` proof queries; every `tq`-query adversary has advantage
at most `zkErrorQuery δ tq Q`. -/
theorem zeroKnowledgeQuery_queryBounded (hb : M.FormatBounds Qs B B) {X' W' : Type} [Fintype X']
    [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → X) (fw : W' → Wit)
    (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    GordieHowe.NARG.QROM.ZeroKnowledge (fun x w => (fx x, fw w) ∈ rel) queryEncoding
      ((M.niProver Λ honest E hb).comap fx fw)
      ((M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).comap fx)
      (M.zkErrorQuery δ) := by
  apply ZeroKnowledgeQueryBoundedPure.zeroKnowledgeQueryBounded
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    NARG.Prover.toFn_comap, NARG.Simulator.toFn_comap, M.toFn_encode_niProver Λ honest E VE hb,
    M.encode_niSimulator Λ E VE hb, toFn_niJointSimulatorProg]
  exact zeroKnowledgeQuery VE B T fx fw hvzk

end

end GordieHowe.SPBCS
