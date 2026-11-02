-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Embed
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Valid.WellFormed
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Valid.WellFormed
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Valid.WellFormed
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Carrier.ROMParams` holds the proof of possession's parts

The ML-DSA-44 ring carrier at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core under `Ring.Carrier.σH` (`Ring.Carrier.CarrierHEmbed`) and the emulated
ML-DSA-44 program's domain `A` gadgets under `Ring.Carrier.σA` (`Ring.Carrier.CarrierAEmbed`), at
the same parameters, decided here.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.ROMParams

open Generated.MLDSA44.Ring.Carrier.ROMParams.Program (program)

/-- The native ML-DSA program at the ROM parameters, whose domain `H` core the carrier holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- The emulated ML-DSA program at the ROM parameters, whose domain `A` gadgets the carrier
holds. -/
abbrev emu : RealizedProgram := Generated.MLDSA44.Emulated.ROMParams.Program.program

/-- **The carrier holds the native program's domain `H` core** (`RealizedProgram.Embedding`); both
programs read their values in identifier order by their well-formedness
(`RealizedProgram.WellFormed.valuesOrdered`). -/
theorem embeddingH : nat.Embedding program σH hV hR :=
  RealizedProgram.embedding_iff.2
    ⟨Generated.MLDSA44.Native.ROMParams.Valid.wellFormed.valuesOrdered,
      Generated.MLDSA44.Ring.Carrier.ROMParams.Valid.wellFormed.valuesOrdered, by decide +kernel⟩

/-- **Native predicate `k` of domain `H`'s core is carrier predicate `k − 25`**, renamed, a source
predicate. -/
theorem hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σH hV hR (nat.predicate k).body
      (program.predicate (k - 25)).body = true ∧
      k - 25 < program.predicates.length ∧
      program.inSource (program.predicate (k - 25)) = true := by
  decide +kernel

/-- **The core's typed values are renamed to node-typed source values of the carrier.** -/
theorem typedCorr : ∀ v ∈ MLDSA44.hTypedCore, v ∈ hV ∧
    σH.val v < program.values.length ∧ program.IsSourceValue (σH.val v) ∧
    (program.value (σH.val v)).typeSource = .node := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The carrier's challenge `j + 1` has the native challenge `j`'s phase.** -/
theorem chalPhaseH : ∀ j, (program.challenge (σH.chal j)).phase = (nat.challenge j).phase := by
  intro j
  change (program.challenge (j + 1)).phase = (nat.challenge j).phase
  rcases lt_or_ge j 4 with hj | hj
  · interval_cases j <;> decide +kernel
  · have h1 : program.challenges.length = 5 := by decide +kernel
    have h2 : nat.challenges.length = 4 := by decide +kernel
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the ROM parameters holds the native program's domain `H` core.** -/
instance : CarrierHEmbed program where
  nat := nat
  embedding := embeddingH
  hPredCorr := hPredCorr
  typedCorr := typedCorr
  chalPhase := chalPhaseH

/-- **The carrier holds the emulated program's domain `A` gadgets** (`RealizedProgram.Embedding`);
both programs read their values in identifier order by their well-formedness
(`RealizedProgram.WellFormed.valuesOrdered`). -/
theorem embeddingA : emu.Embedding program σA aV aR :=
  RealizedProgram.embedding_iff.2
    ⟨Generated.MLDSA44.Emulated.ROMParams.Valid.wellFormed.valuesOrdered,
      Generated.MLDSA44.Ring.Carrier.ROMParams.Valid.wellFormed.valuesOrdered, by decide +kernel⟩

/-- **Emulated predicate `k` of domain `A`'s gadgets is carrier predicate `predMapA k`**,
renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    emu.bodyCorrB program σA aV aR (emu.predicate k).body
      (program.predicate (predMapA k)).body = true ∧
      predMapA k < program.predicates.length := by
  decide +kernel

/-- **The carrier predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMapA k)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The carrier's challenge `j + 1` has the emulated challenge `j`'s phase.** -/
theorem chalPhaseA : ∀ j, (program.challenge (σA.chal j)).phase = (emu.challenge j).phase := by
  intro j
  change (program.challenge (j + 1)).phase = (emu.challenge j).phase
  rcases lt_or_ge j 4 with hj | hj
  · interval_cases j <;> decide +kernel
  · have h1 : program.challenges.length = 5 := by decide +kernel
    have h2 : emu.challenges.length = 4 := by decide +kernel
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The carrier at the ROM parameters holds the emulated program's domain `A` gadgets.** -/
instance : CarrierAEmbed program where
  emu := emu
  embedding := embeddingA
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhaseA

end GordieHowe.MLDSA44.Ring.Carrier.ROMParams
