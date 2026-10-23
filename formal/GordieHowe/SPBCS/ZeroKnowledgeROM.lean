-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ZeroKnowledge
public import GordieHowe.SPBCS.FullPast.ZeroKnowledgeROM
public import GordieHowe.Model.ROM.SaltedZKLastProofQuery
public import GordieHowe.Model.ROM.InteractiveNIZKLastProofQuery

@[expose] public section

/-!
# Zero knowledge of the spBCS compiler in the ROM

Adaptive multi-theorem statistical zero knowledge of the spBCS compiler against classical
adversaries with a budget of `t` queries before each proof query (`GordieHowe.ROM.NIZK.EverlastingZeroKnowledge`),
with the prover `niProverZKM` and the simulator `niJointSimulator` of the quantum theorem
(`GordieHowe/SPBCS/ZeroKnowledge.lean`) and the same hypothesis `GordieHowe.IOP.CausalHVZK`. The proof is the
generic classical argument (`GordieHowe.ROM.NIZK.everlastingZeroKnowledge_of_sliceCloseAt`) at the
locality in the salt (`saltedLocal`) and the one-proof bound at every fixed salt
(`sliceCloseAt`). The error is the compiler's `zkErrorROM δ`:
`Q t / 2^(8k) + Q (Q - 1) / (2 · 2^(8k)) + Q · (keyCollision (t.size n) k + overrun + δ +
|Pos| · leafBound k kN L)`.
-/

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
  (honest : Wit → R → CausalProver P t X) {Pub : Type} (pub : X → Pub)
  {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}

open Classical in
/-- **One merge proof is simulated on a fresh slice at every salt.** -/
theorem sliceCloseAt (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    ROM.NIZK.SliceCloseAt M.saltOfBits (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.toFullPast.oneProofBound δ) where
  close σ H x w hw := by
    change PMF.tvDist (innerR (E := E) (Qs := Qs) B H x (honest w) σ)
      (innerSJ B VE pub Sim T H x σ) ≤ _
    exact tvDist_innerR_innerSJ_le B VE honest pub Sim T H x hvzk hw σ
  nonneg := (sliceClose B VE honest pub Sim T hvzk).nonneg
  congr := (sliceClose B VE honest pub Sim T hvzk).congr

open Classical in
/-- **Everlasting zero knowledge of the spBCS compiler in the classical random-oracle model**:
against adversaries with a budget of `tq` queries before each proof query, the prover
`niProverZKM` and the simulator `niJointSimulator` at the joint simulator `Sim` of the composite
view (`CausalHVZK`, CY24 Definition 23.1.8) are indistinguishable with error `zkErrorROM δ`, the
error of the compiler over the term. -/
theorem zeroKnowledgeROM (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    ROM.NIZK.EverlastingZeroKnowledge (fun x w => (x, w) ∈ rel) (M.niProverZKM B honest E Qs)
      (M.niJointSimulator VE.toViewRead B pub Sim T) (M.zkErrorROM δ) := by
  refine (ROM.NIZK.everlastingZeroKnowledge_of_sliceCloseAt (saltedLocal B VE honest pub Sim T)
    (sliceCloseAt VE B honest pub T hvzk)).mono fun tq Q => ?_
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    ring
  rw [hsalt, Base.zkErrorROM]
  gcongr
  exact M.toFullPast.expect_oneProofBound_le δ

open Classical in
/-- **Zero knowledge of the spBCS compiler in the classical random-oracle model against
query-bounded adversaries** (`ROM.QueryBoundedAdversary`, Unruh 2017 Definition 6, p. 14, with
classical adversaries and the query bound of `def:narg-zk-post`), from `zeroKnowledgeROM`. -/
theorem everlastingZeroKnowledge_rom_games (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    GordieHowe.ROM.EverlastingZeroKnowledge (fun x w => (x, w) ∈ rel)
      (M.niProverZKM B honest E Qs) (M.niJointSimulator VE.toViewRead B pub Sim T)
      (M.zkErrorROM δ) :=
  ROM.QueryBoundedAdversary.everlastingZeroKnowledge_of_nizk
    (zeroKnowledgeROM VE B honest pub T hvzk)

end

end GordieHowe.SPBCS
