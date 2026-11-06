-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Embed
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Certified
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.ROMParams` holds `MLDSA44.Native.ROMParams`'s core

The native ML-DSA-44 ring program at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core and domain `A` gadgets at the same parameters under the renaming
`Ring.Native.σR` (`Ring.Native.MldsaRingEmbed`, from the checked embedding).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)

/-- The native ML-DSA program at the ROM parameters, whose parts the ring program holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- The renaming agrees with the checked embedding's lists. -/
theorem agrees : Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.Agrees σR :=
  RealizedProgram.EmbedData.agrees_of_checks (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The checked embedding at the renaming. -/
theorem holds : Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.Holds program σR :=
  Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.embedding_native_2eparts_holds σR agrees

theorem data_V : Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.V = ringV :=
  eq_of_beq (by decide +kernel)
theorem data_R : Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.R = ringR :=
  eq_of_beq (by decide +kernel)

/-- **The ring program holds the native program's parts** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σR ringV ringR :=
  holds.embedding_at rfl data_V data_R

/-- **Native predicate `k` of domain `H`'s core is ring predicate `k − 24`**, renamed, a source
predicate. -/
theorem hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σR ringV ringR (nat.predicate k).body
      (program.predicate (k - 24)).body = true ∧
      k - 24 < program.predicates.length ∧
      program.inSource (program.predicate (k - 24)) = true := by
  have he : Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.equals = (List.range' 48 223).map (fun k => (k, k - 24)) := rfl
  have hl : ∀ k ∈ List.range' 48 223, (k, k - 24) ∈ Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.equals :=
    fun k hk => he ▸ List.mem_map_of_mem hk
  intro k h48 h270
  exact holds.equals_at rfl data_V data_R (hl k (by simp only [List.mem_range'_1]; omega))

/-- **Native predicate `k` of domain `A`'s gadgets is ring predicate `predMap k`**, renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    nat.bodyCorrB program σR ringV ringR (nat.predicate k).body
      (program.predicate (predMap k)).body = true ∧ predMap k < program.predicates.length := by
  have hl : ∀ k ∈ aPreds,
      (k, predMap k) ∈ Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.bodies := by decide +kernel
  exact fun k hk => holds.bodies_at rfl data_V data_R (hl k hk)

/-- **The ring predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMap k)) = true := by
  have hl : ∀ k ∈ aSource,
      predMap k ∈ Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data.sources := by decide +kernel
  exact fun k hk => holds.sources _ (hl k hk)

/-- **The ring program's challenge `j + 1` has the native challenge `j`'s phase.** -/
theorem chalPhase : ∀ j, (program.challenge (σR.chal j)).phase = (nat.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holds.chalPhase j hj
  · change (program.challenge (j + 1)).phase = (nat.challenge j).phase
    have h2 : nat.challenges.length = 4 := holds.chalCount
    have h1 : program.challenges.length = 5 := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.challenges_length
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The ring program at the ROM parameters holds the native program's parts.** -/
instance : MldsaRingEmbed program where
  nat := nat
  σ := σR
  embedding := embedding
  hPredCorr := hPredCorr
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhase
  chalMono := fun _ _ h => Nat.add_le_add_right h 1

end GordieHowe.MLDSA44.Ring.Native.ROMParams
