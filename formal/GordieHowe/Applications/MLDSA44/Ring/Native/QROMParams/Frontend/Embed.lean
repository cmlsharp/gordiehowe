-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Embed
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Valid.WellFormed
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Valid.WellFormed
public import GordieHowe.Language.Realizations.CircuitInput

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Ring.Native.QROMParams` holds `MLDSA44.Native.QROMParams`'s core

The native ML-DSA-44 ring program at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program`) holds the native ML-DSA-44
program's domain `H` core and domain `A` gadgets at the same parameters under the renaming
`Ring.Native.σQ` (`Ring.Native.MldsaRingEmbed`, decided here).
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program (program)

/-- The native ML-DSA program at the QROM parameters, whose parts the ring program holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.QROMParams.Program.program

/-- **The ring program holds the native program's parts** (`RealizedProgram.Embedding`); both
programs read their values in identifier order by their well-formedness
(`RealizedProgram.WellFormed.valuesOrdered`). -/
theorem embedding : nat.Embedding program σQ ringV ringR :=
  RealizedProgram.embedding_iff.2
    ⟨Generated.MLDSA44.Native.QROMParams.Valid.wellFormed.valuesOrdered,
      Generated.MLDSA44.Ring.Native.QROMParams.Valid.wellFormed.valuesOrdered, by decide +kernel⟩

/-- **Native predicate `k` of domain `H`'s core is ring predicate `k − 24`**, renamed, a source
predicate. -/
theorem hPredCorr : ∀ k, 48 ≤ k → k ≤ 270 →
    nat.equalCorrB program σQ ringV ringR (nat.predicate k).body
      (program.predicate (k - 24)).body = true ∧
      k - 24 < program.predicates.length ∧
      program.inSource (program.predicate (k - 24)) = true := by
  decide +kernel

/-- **Native predicate `k` of domain `A`'s gadgets is ring predicate `predMap k`**, renamed. -/
theorem aPredCorr : ∀ k ∈ aPreds,
    nat.bodyCorrB program σQ ringV ringR (nat.predicate k).body
      (program.predicate (predMap k)).body = true ∧ predMap k < program.predicates.length := by
  decide +kernel

/-- **The ring predicates of `aSource` are source predicates.** -/
theorem aSourceCorr : ∀ k ∈ aSource, program.inSource (program.predicate (predMap k)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The ring program's challenge `j + 1` has the native challenge `j`'s phase.** -/
theorem chalPhase : ∀ j, (program.challenge (σQ.chal j)).phase = (nat.challenge j).phase := by
  intro j
  change (program.challenge (j + 1)).phase = (nat.challenge j).phase
  rcases lt_or_ge j 4 with hj | hj
  · interval_cases j <;> decide +kernel
  · have h1 : program.challenges.length = 5 := by decide +kernel
    have h2 : nat.challenges.length = 4 := by decide +kernel
    simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [h1]; omega), List.getElem?_eq_none (by rw [h2]; exact hj)]

/-- **The ring program at the QROM parameters holds the native program's parts.** -/
instance : MldsaRingEmbed program where
  nat := nat
  σ := σQ
  embedding := embedding
  hPredCorr := hPredCorr
  aPredCorr := aPredCorr
  aSourceCorr := aSourceCorr
  chalPhase := chalPhase
  chalMono := fun _ _ h => Nat.add_le_add_right h 1

end GordieHowe.MLDSA44.Ring.Native.QROMParams
