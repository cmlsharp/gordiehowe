-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Embed
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Certified
public import GordieHoweCerts.Generated.MLDSA44.Native.ROMParams.Certified
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.ROMParams` holds `MLDSA44.Native.ROMParams`'s core

The native ML-DSA-44 ring program at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core and domain `A` gadgets at the same parameters under the renaming of
its checked embedding data (`Ring.Native.MldsaRingEmbed`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)

/-- The native ML-DSA program at the ROM parameters, whose parts the ring program holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- **The checked embedding data** of the native program's parts. -/
abbrev embedData : RealizedProgram.EmbedData := Generated.MLDSA44.Ring.Native.ROMParams.Shapes.embedding_native_2eparts_data

/-- **The renaming**, the embedData's (`EmbedData.renamingAfter`). -/
abbrev σ : RealizedProgram.Renaming := embedData.renamingAfter

/-- **The ring predicate of each held native predicate**, from the embedData's pairs. -/
def heldPred (k : ℕ) : ℕ := ((embedData.equals ++ embedData.bodies).lookup k).getD k

/-- The checked embedding at the renaming. -/
theorem holds : embedData.Holds program σ :=
  Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.embedding_native_2eparts_holds σ
    embedData.agrees_renamingAfter

/-- **The ring program holds the native program's parts** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σ embedData.V embedData.R :=
  holds.embedding_at rfl rfl rfl

/-- **Native predicate `k` of domain `H`'s core is ring predicate `heldPred k`**, renamed, a source
predicate. -/
theorem hPredCorr : ∀ k, corePredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σ embedData.V embedData.R (nat.predicate k).body
      (program.predicate (heldPred k)).body = true ∧
      heldPred k < program.predicates.length ∧
      program.inSource (program.predicate (heldPred k)) = true := by
  have hl : ∀ k ∈ List.range' 48 223, (k, heldPred k) ∈ embedData.equals := by decide +kernel
  intro k h48 h270
  exact holds.equals_at rfl rfl rfl (hl k (by simp only [corePredLo, hPredLo, hPredHi, List.mem_range'_1] at *; omega))

/-- **Native predicate `k` of domain `A`'s gadgets is ring predicate `heldPred k`**, renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    nat.bodyCorrB program σ embedData.V embedData.R (nat.predicate k).body
      (program.predicate (heldPred k)).body = true ∧ heldPred k < program.predicates.length := by
  have hl : ∀ k ∈ aPreds, (k, heldPred k) ∈ embedData.bodies := by decide +kernel
  exact fun k hk => holds.bodies_at rfl rfl rfl (hl k hk)

/-- **The ring predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (heldPred k)) = true := by
  have hl : ∀ k ∈ aSource, heldPred k ∈ embedData.sources := by decide +kernel
  exact fun k hk => holds.sources _ (hl k hk)

/-- The embedData's challenge images increase: `2 … 5`. -/
theorem chals_eq : embedData.chals = List.range' 2 (3 + 1) := by decide +kernel

/-- **The native challenge `j` is the ring program's `j + 2`** (the ring draws the member table's
`γ` and the relation's `r` first). -/
theorem chal2 : ∀ j, σ.chal j = j + 2 := MLDSA44.renamingAfter_chal_of_range chals_eq

/-- **The ring program's challenge `j + 2` has the native challenge `j`'s phase.** -/
theorem chalPhase : ∀ j, (program.challenge (σ.chal j)).phase = (nat.challenge j).phase := by
  intro j
  rcases lt_or_ge j 4 with hj | hj
  · exact holds.chalPhase j (by rw [chals_eq, List.length_range']; exact hj)
  · rw [chal2]
    have h2 : nat.challenges.length = 4 := holds.chalCount.trans (by rw [chals_eq]; rfl)
    have h1 : program.challenges.length = 6 :=
      Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.challenges_length
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The ring program at the ROM parameters holds the native program's parts.** -/
instance : MldsaRingEmbed program where
  nat := nat
  σ := σ
  V := embedData.V
  R := embedData.R
  pred := heldPred
  embedding := embedding
  hPredCorr := hPredCorr
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhase
  chalMono := (embedData.renamingAfter_chal_strictMono (by rw [chals_eq]; decide)).monotone
  readV := by decide +kernel
  readR := by decide +kernel
  held := embedData.equals ++ embedData.bodies
  pred_held := by decide +kernel

end GordieHowe.MLDSA44.Ring.Native.ROMParams
