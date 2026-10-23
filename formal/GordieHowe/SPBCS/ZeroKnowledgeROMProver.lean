-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.ZeroKnowledgeROMQuery
public import GordieHowe.Model.NARG.ROM

@[expose] public section

/-!
# Zero knowledge of the spBCS compiler's prover in the ROM

The classical zero-knowledge theorems of the compiler (`GordieHowe/SPBCS/ZeroKnowledgeROM.lean`,
`GordieHowe/SPBCS/ZeroKnowledgeROMQuery.lean`) are proved for the prover and simulator of the games,
functions of an oracle on query bits. Through the bridges `toFn_encode_niProver` and
`encode_niSimulator` they are the prover `niProver` and the simulator `niSimulator` run through
`queryEncoding`, and zero knowledge transfers to the compiler's oracle `Query → Out`
(`NARG.ROM.ZeroKnowledge.of_encode`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X : Type} {M : SPBCS Mg P X k kN kS L e}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (Λ : SiteLayout Mg)
  {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x}
  (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B) {Wit R : Type} [Fintype R]
  [Nonempty R] (honest : Wit → R → CausalProver P t X) {Pub : Type} (pub : X → Pub)
  {Sim : CausalJointSimulator VE.MV Pub} (T : M.Preimages) {rel : Set (X × Wit)} {δ : ℝ≥0}

open Classical in
/-- **Everlasting zero knowledge of the spBCS compiler in the classical random-oracle model**
(`NARG.ROM.EverlastingZeroKnowledge`; paper `thm:bcs-zk`(2)): against classical adversaries with a
budget of `tq` queries before each proof query, the prover `niProver` and the simulator
`niSimulator` at the joint simulator `Sim` of the composite view (`CausalHVZK`, CY24 Definition
23.1.8), with proofs in the format `B` of the format bounds `hb`, are indistinguishable with error
`zkErrorROM δ`. -/
theorem everlastingZeroKnowledge_rom (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    NARG.ROM.EverlastingZeroKnowledge (fun x w => (x, w) ∈ rel) (M.niProver Λ honest E hb)
      (M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T)
      (M.zkErrorROM δ) := by
  refine NARG.ROM.EverlastingZeroKnowledge.of_encode queryEncoding ?_
  rw [M.toFn_encode_niProver Λ honest E VE hb, M.encode_niSimulator Λ E VE hb,
    toFn_niJointSimulatorProg]
  exact everlastingZeroKnowledge_rom_games VE B honest pub T hvzk

open Classical in
/-- **Zero knowledge of the spBCS compiler in the classical random-oracle model**
(`NARG.ROM.ZeroKnowledge`, Unruh 2017 Definition 6, p. 14, with classical adversaries all of whose
queries are counted), at the error `zkErrorROMQuery δ`, with proofs in the format `B` of the
format bounds `hb`. -/
theorem zeroKnowledge_rom (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) :
    NARG.ROM.ZeroKnowledge (fun x w => (x, w) ∈ rel) (M.niProver Λ honest E hb)
      (M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T)
      (M.zkErrorROMQuery δ) := by
  refine NARG.ROM.ZeroKnowledge.of_encode queryEncoding ?_
  rw [M.toFn_encode_niProver Λ honest E VE hb, M.encode_niSimulator Λ E VE hb,
    toFn_niJointSimulatorProg]
  exact zeroKnowledgeROMQuery_games VE B honest pub T hvzk

end

end GordieHowe.SPBCS
