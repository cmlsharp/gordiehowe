-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Embed
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Certified
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Carrier.QROMParams` holds the proof of possession's parts

The ML-DSA-44 ring carrier at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core under `Ring.Carrier.σH` (`Ring.Carrier.CarrierHEmbed`) and the emulated
ML-DSA-44 program's domain `A` gadgets under `Ring.Carrier.σA` (`Ring.Carrier.CarrierAEmbed`), at
the same parameters, decided here.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts

/-- The native ML-DSA program at the QROM parameters, whose domain `H` core the carrier holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.QROMParams.Program.program

/-- The emulated ML-DSA program at the QROM parameters, whose domain `A` gadgets the carrier
holds. -/
abbrev emu : RealizedProgram := Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- The renaming agrees with the checked embedding's lists. -/
theorem agreesH : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.Agrees σH :=
  RealizedProgram.EmbedData.agrees_of_checks (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The checked embedding of domain `H` at the renaming. -/
theorem holdsH : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.Holds program σH :=
  embedding_native_2ecore_holds σH agreesH

theorem dataH_V : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.V = hV :=
  eq_of_beq (by decide +kernel)
theorem dataH_R : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.R = hR :=
  eq_of_beq (by decide +kernel)

/-- **The carrier holds the native program's domain `H` core** (`RealizedProgram.Embedding`). -/
theorem embeddingH : nat.Embedding program σH hV hR :=
  holdsH.embedding_at rfl dataH_V dataH_R

/-- **Native predicate `k` of domain `H`'s core is carrier predicate `k − 25`**, renamed, a source
predicate. -/
theorem hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σH hV hR (nat.predicate k).body
      (program.predicate (k - 25)).body = true ∧
      k - 25 < program.predicates.length ∧
      program.inSource (program.predicate (k - 25)) = true := by
  have he : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.equals = (List.range' 48 223).map (fun k => (k, k - 25)) := rfl
  have hl : ∀ k ∈ List.range' 48 223, (k, k - 25) ∈ Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_native_2ecore_data.equals :=
    fun k hk => he ▸ List.mem_map_of_mem hk
  intro k h48 h270
  exact holdsH.equals_at rfl dataH_V dataH_R (hl k (by simp only [List.mem_range'_1]; omega))

/-- **The core's typed values are renamed to node-typed source values of the carrier.** -/
theorem typedCorr : ∀ v ∈ MLDSA44.hTypedCore, v ∈ hV ∧
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

/-- **The carrier's challenge `j + 1` has the native challenge `j`'s phase.** -/
theorem chalPhaseH : ∀ j, (program.challenge (σH.chal j)).phase = (nat.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holdsH.chalPhase j hj
  · change (program.challenge (j + 1)).phase = (nat.challenge j).phase
    have h1 : program.challenges.length = 5 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.challenges_length
    have h2 : nat.challenges.length = 4 := holdsH.chalCount
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the QROM parameters holds the native program's domain `H` core.** -/
instance : CarrierHEmbed program where
  nat := nat
  embedding := embeddingH
  hPredCorr := hPredCorr
  typedCorr := typedCorr
  chalPhase := chalPhaseH

/-- The renaming agrees with the checked embedding's lists. -/
theorem agreesA : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.Agrees σA :=
  RealizedProgram.EmbedData.agrees_of_checks (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The checked embedding of domain `A` at the renaming. -/
theorem holdsA : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.Holds program σA :=
  embedding_emulated_2eA_holds σA agreesA

theorem dataA_V : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.V = aV :=
  eq_of_beq (by decide +kernel)
theorem dataA_R : Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.R = aR :=
  eq_of_beq (by decide +kernel)

/-- **The carrier holds the emulated program's domain `A` gadgets** (`RealizedProgram.Embedding`). -/
theorem embeddingA : emu.Embedding program σA aV aR :=
  holdsA.embedding_at rfl dataA_V dataA_R

/-- **Emulated predicate `k` of domain `A`'s gadgets is carrier predicate `predMapA k`**,
renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    emu.bodyCorrB program σA aV aR (emu.predicate k).body
      (program.predicate (predMapA k)).body = true ∧
      predMapA k < program.predicates.length := by
  have hl : ∀ k ∈ aPreds, (k, predMapA k) ∈ Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.bodies := by decide +kernel
  exact fun k hk => holdsA.bodies_at rfl dataA_V dataA_R (hl k hk)

/-- **The carrier predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMapA k)) = true := by
  have hl : ∀ k ∈ aSource, predMapA k ∈ Generated.MLDSA44.Ring.Carrier.QROMParams.Shapes.embedding_emulated_2eA_data.sources := by decide +kernel
  exact fun k hk => holdsA.sources _ (hl k hk)

/-- **The carrier's challenge `j + 1` has the emulated challenge `j`'s phase.** -/
theorem chalPhaseA : ∀ j, (program.challenge (σA.chal j)).phase = (emu.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holdsA.chalPhase j hj
  · change (program.challenge (j + 1)).phase = (emu.challenge j).phase
    have h1 : program.challenges.length = 5 := Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts.challenges_length
    have h2 : emu.challenges.length = 4 := holdsA.chalCount
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the QROM parameters holds the emulated program's domain `A` gadgets.** -/
instance : CarrierAEmbed program where
  emu := emu
  embedding := embeddingA
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhaseA

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
