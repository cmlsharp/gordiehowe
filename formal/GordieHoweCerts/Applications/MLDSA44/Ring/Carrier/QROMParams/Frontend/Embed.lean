-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Embed
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.Certified
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Carrier.QROMParams` holds the proof of possession's parts

The ML-DSA-44 ring carrier at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core (`Ring.Carrier.CarrierHEmbed`) and the emulated
ML-DSA-44 program's domain `A` gadgets (`Ring.Carrier.CarrierAEmbed`), at the same parameters,
under the renamings of its checked embedding data, decided here.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts

/-- The native ML-DSA program at the QROM parameters, whose domain `H` core the carrier holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.QROMParams.Program.program

/-- The emulated ML-DSA program at the QROM parameters, whose domain `A` gadgets the carrier
holds. -/
abbrev emu : RealizedProgram := Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- **The checked embedding data** of the native program's domain `H` core. -/
abbrev dataH : RealizedProgram.EmbedData := Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data

/-- **The renaming of domain `H`**, the data's (`EmbedData.renamingAfter`). -/
abbrev σH : RealizedProgram.Renaming := dataH.renamingAfter

/-- **The carrier predicate of each held native predicate**, from the data's pairs. -/
def predH (k : ℕ) : ℕ := (dataH.equals.lookup k).getD k

/-- The checked embedding of domain `H` at the renaming. -/
theorem holdsH : dataH.Holds program σH :=
  embedding_native_2ecore_holds σH dataH.agrees_renamingAfter

/-- **The carrier holds the native program's domain `H` core** (`RealizedProgram.Embedding`). -/
theorem embeddingH : nat.Embedding program σH dataH.V dataH.R :=
  holdsH.embedding_at rfl rfl rfl

/-- **Native predicate `k` of domain `H`'s core is carrier predicate `predH k`**, renamed, a
source predicate. -/
theorem hPredCorr : ∀ k, corePredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σH dataH.V dataH.R (nat.predicate k).body
      (program.predicate (predH k)).body = true ∧
      predH k < program.predicates.length ∧
      program.inSource (program.predicate (predH k)) = true := by
  have hl : ∀ k ∈ List.range' 48 223, (k, predH k) ∈ dataH.equals := by decide +kernel
  intro k h48 h270
  exact holdsH.equals_at rfl rfl rfl (hl k (by simp only [corePredLo, hPredLo, hPredHi, List.mem_range'_1] at *; omega))

/-- **The core's typed values are renamed to node-typed source values of the carrier.** -/
theorem typedCorr : ∀ v ∈ MLDSA44.hTypedCore, v ∈ dataH.V ∧
    σH.val v < program.values.length ∧ program.IsSourceValue (σH.val v) ∧
    (program.value (σH.val v)).typeSource = .node := by
  intro v hv
  simp only [MLDSA44.hTypedCore, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide +kernel, ?_⟩
  · exact ⟨value_h2c_2esample_2eselect_2ej_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2eselect_2ej_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2eselect_2ej_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2eread_5fvalue_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2eread_5fvalue_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2eread_5fvalue_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2eread_5forigin_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2eread_5forigin_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2eread_5forigin_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2ec_5fenc_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2ec_5fenc_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2ec_5fenc_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2efinal_5forigin_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2efinal_5forigin_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2efinal_5forigin_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2eunit_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2eunit_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2eunit_header.2⟩
  · exact ⟨value_h2c_2esample_2emem_2eorigin_header.1,
      RealizedProgram.valueShape_role value_h2c_2esample_2emem_2eorigin_header.2,
      RealizedProgram.valueShape_typeSource value_h2c_2esample_2emem_2eorigin_header.2⟩

/-- The data's challenge images: `2 … 5`. -/
theorem chalsH : dataH.chals = List.range' 2 (3 + 1) := by decide +kernel

/-- **The native challenge `j` is the carrier's `j + 2`.** -/
theorem chal2H : ∀ j, σH.chal j = j + 2 := MLDSA44.renamingAfter_chal_of_range chalsH

/-- **The carrier's challenge `j + 2` has the native challenge `j`'s phase.** -/
theorem chalPhaseH : ∀ j, (program.challenge (σH.chal j)).phase = (nat.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holdsH.chalPhase j (by rw [chalsH, List.length_range']; exact hj)
  · rw [chal2H]
    have h1 : program.challenges.length = 6 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.challenges_length
    have h2 : nat.challenges.length = 4 := holdsH.chalCount.trans (by rw [chalsH]; rfl)
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the QROM parameters holds the native program's domain `H` core.** -/
instance : CarrierHEmbed program where
  nat := nat
  σ := σH
  V := dataH.V
  R := dataH.R
  pred := predH
  embedding := embeddingH
  hPredCorr := hPredCorr
  typedCorr := typedCorr
  chalPhase := chalPhaseH
  chal2 := chal2H
  readV := by decide +kernel
  readR := by decide +kernel
  held := dataH.equals
  pred_held := by decide +kernel

/-- **The checked embedding data** of the emulated program's domain `A` gadgets. -/
abbrev dataA : RealizedProgram.EmbedData := Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data

/-- **The renaming of domain `A`**, the data's (`EmbedData.renamingAfter`). -/
abbrev σA : RealizedProgram.Renaming := dataA.renamingAfter

/-- **The carrier predicate of each held emulated predicate**, from the data's pairs. -/
def predA (k : ℕ) : ℕ := (dataA.bodies.lookup k).getD k

/-- The checked embedding of domain `A` at the renaming. -/
theorem holdsA : dataA.Holds program σA :=
  embedding_emulated_2eA_holds σA dataA.agrees_renamingAfter

/-- **The carrier holds the emulated program's domain `A` gadgets** (`RealizedProgram.Embedding`). -/
theorem embeddingA : emu.Embedding program σA dataA.V dataA.R :=
  holdsA.embedding_at rfl rfl rfl

/-- **Emulated predicate `k` of domain `A`'s gadgets is carrier predicate `predA k`**, renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    emu.bodyCorrB program σA dataA.V dataA.R (emu.predicate k).body
      (program.predicate (predA k)).body = true ∧ predA k < program.predicates.length := by
  have hl : ∀ k ∈ aPreds, (k, predA k) ∈ dataA.bodies := by decide +kernel
  exact fun k hk => holdsA.bodies_at rfl rfl rfl (hl k hk)

/-- **The carrier predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predA k)) = true := by
  have hl : ∀ k ∈ aSource, predA k ∈ dataA.sources := by decide +kernel
  exact fun k hk => holdsA.sources _ (hl k hk)

/-- The data's challenge images: `2 … 5`. -/
theorem chalsA : dataA.chals = List.range' 2 (3 + 1) := by decide +kernel

/-- **The carrier's challenge `j + 2` has the emulated challenge `j`'s phase.** -/
theorem chalPhaseA : ∀ j, (program.challenge (σA.chal j)).phase = (emu.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holdsA.chalPhase j (by rw [chalsA, List.length_range']; exact hj)
  · rw [MLDSA44.renamingAfter_chal_of_range chalsA]
    have h1 : program.challenges.length = 6 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.challenges_length
    have h2 : emu.challenges.length = 4 := holdsA.chalCount.trans (by rw [chalsA]; rfl)
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the QROM parameters holds the emulated program's domain `A` gadgets.** -/
instance : CarrierAEmbed program where
  emu := emu
  σ := σA
  V := dataA.V
  R := dataA.R
  pred := predA
  embedding := embeddingA
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhaseA
  chalStrict := dataA.renamingAfter_chal_strictMono (by rw [chalsA]; decide)
  readV := by decide +kernel
  held := dataA.bodies
  pred_held := by decide +kernel

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
