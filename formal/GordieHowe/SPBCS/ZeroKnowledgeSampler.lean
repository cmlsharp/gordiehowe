-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.FullPast.Sampler

@[expose] public section

/-!
# Zero knowledge of the spBCS compiler at witnesses drawn by the prover

Zero knowledge of the spBCS compiler when the prover draws its witness with a witness sampler
(`WitnessSampler`), at the error of `everlastingZeroKnowledge` plus `Q · η`
(`GordieHowe/SPBCS/FullPast/Sampler.lean`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped ENNReal NNReal BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X : Type} {M : SPBCS Mg P X k kN kS L e}
  (Λ : SiteLayout Mg)

variable [∀ j i, Fintype ((M.comp j).MessageWrite i)]

open Classical in
/-- **Everlasting zero knowledge of the spBCS compiler at drawn witnesses** (QROM): the zero
knowledge of `everlastingZeroKnowledge` when each proof query `(x, u)` of
`relU` is answered at a witness the prover draws with the sampler `D`, which misses `rel` with
probability at most `η` (`hD`): the honest prover of `drawProver honest D.draw` against the
simulator `niJointSimulator`, with error `zkError δ tq Q + Q · η`
(`GordieHowe.QROM.SliceClose.of_draw`). -/
theorem everlastingZeroKnowledge_of_sampler {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs)
    (B : ℕ) {Wit R U : Type} [Fintype R] [Nonempty R]
    {honest : Wit → R → CausalProver P t X} {Pub : Type} {pub : X → Pub}
    {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}
    (D : WitnessSampler U Wit) {relU : Set (X × U)} {η : ℝ≥0} (hD : D.MissesAtMost rel relU η)
    {X' W' : Type} [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → X)
    (fw : W' → U) (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    EverlastingZeroKnowledgePure (fun x u => (fx x, fw u) ∈ relU)
      ((M.niProverZKM B (drawProver honest D.draw) E Qs).comap fx fw)
      ((M.niJointSimulator VE.toViewRead B pub Sim T).comap fx)
      (fun tq Q => M.zkError δ tq Q + Q * η) := by
  have hcl : SliceClose M.saltOfBits (fun x u => (x, u) ∈ relU)
      (M.niProverZKM B (drawProver honest D.draw) E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) fun H => M.toFullPast.oneProofBound δ H + η :=
    SliceClose.of_draw (e := M.toFullPast.drawCoinsEquiv D.Coins R) (fun _ _ _ _ _ _ => rfl)
      (sliceClose B VE honest pub Sim T hvzk) hD
  have hzk := everlastingZeroKnowledgePure_of_sliceClose _ _ _ _
    ((saltedLocal B VE (drawProver honest D.draw) pub Sim T).comap fx fw) (hcl.comap fx fw)
  refine EverlastingZeroKnowledgePure.mono hzk fun tq Q => ?_
  unfold Base.zkError
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  have hsqrt : √(Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (4 * kS) := by
    rw [hsalt, show 8 * kS = 4 * kS * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]
  have hE := M.toFullPast.expect_oneProofBound_le δ
  rw [hsqrt, hsalt, Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hE hQ]

variable (M) in
open Classical in
/-- **Zero knowledge of the spBCS compiler at witnesses drawn by a sampler, against
query-bounded adversaries** (the statement form; `NARG.QROM.EverlastingZeroKnowledge` at every
finite statement and proof query types): the prover `niProver` at `drawProver honest D.draw`,
which answers a proof query `u` at the witness `D.draw u r` for fresh coins `r`, against the
simulator `niSimulator`, both with proofs in the format `B` of the format bounds `hb`, on the proof
queries of `relU`, with error `ε`. -/
def ZeroKnowledgeOfSampler {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs)
    {B : ℕ} (hb : M.FormatBounds Qs B B) {Wit R U : Type} [Fintype R] [Nonempty R]
    (honest : Wit → R → CausalProver P t X) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) (D : WitnessSampler U Wit)
    (relU : Set (X × U)) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (X' W' : Type) [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → X)
    (fw : W' → U),
    GordieHowe.NARG.QROM.EverlastingZeroKnowledge (fun x u => (fx x, fw u) ∈ relU) queryEncoding
      ((M.niProver Λ (drawProver honest D.draw) E hb).comap fx fw)
      ((M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).comap fx) ε

open Classical in
/-- **Zero knowledge of the spBCS compiler at drawn witnesses, in the statement form**
(`ZeroKnowledgeOfSampler`), at `zkError δ + Q · η` (`everlastingZeroKnowledge_of_sampler`). -/
theorem zeroKnowledgeOfSampler {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs)
    {B : ℕ} (hb : M.FormatBounds Qs B B) {Wit R U : Type} [Fintype R] [Nonempty R]
    {honest : Wit → R → CausalProver P t X} {Pub : Type} {pub : X → Pub}
    {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}
    (D : WitnessSampler U Wit) {relU : Set (X × U)} {η : ℝ≥0} (hD : D.MissesAtMost rel relU η)
    (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    M.ZeroKnowledgeOfSampler Λ VE hb honest pub Sim T D relU
      (fun tq Q => M.zkError δ tq Q + Q * η) := by
  intro X' W' _ _ _ _ fx fw
  apply EverlastingZeroKnowledgePure.everlastingZeroKnowledge
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    NARG.Prover.toFn_comap, NARG.Simulator.toFn_comap,
    M.toFn_encode_niProver Λ (drawProver honest D.draw) E VE hb,
    M.encode_niSimulator Λ E VE hb, toFn_niJointSimulatorProg]
  exact everlastingZeroKnowledge_of_sampler VE B T D hD fx fw hvzk

end

end GordieHowe.SPBCS
