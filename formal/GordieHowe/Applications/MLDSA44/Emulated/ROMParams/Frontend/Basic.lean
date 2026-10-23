-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Embed
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Sample
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Hash

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.ROMParams`, the relation and the composition

The emulated ML-DSA frontend (`GordieHowe/Applications/MLDSA44/Emulated/Frontend/Basic.lean`) at the
emulated ML-DSA-44 program at the ROM parameters (`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program.program`, export
`c825eb05`): its program facts (`GordieHowe.MLDSA44.Emulated.MldsaEMain`, decided here), domain `A` over
Goldilocks², domain `H` over `GF(2^128)`, and the frontend's statement, relation, extractor and
composition at this program (`KeyOf`, `rel`, `proj`, `extractor`, `rbr_of_views`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open HashField (interp)
open GordieHowe.Bits IOP
open scoped NNReal ENNReal

set_option maxRecDepth 4096 in
/-- The emulated program at the ROM parameters has the composition's facts. -/
instance : Emulated.MldsaEMain program where
  chal_phase := by
    intro j
    rcases lt_or_ge j 4 with hj | hj
    · interval_cases j <;> decide +kernel
    · have h1 : program.challenges.length = 4 := by decide +kernel
      have h2 : (Emulated.MldsaEmbed.nat program).challenges.length = 4 := by decide +kernel
      simp only [RealizedProgram.challenge, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by rw [h1]; exact hj), List.getElem?_eq_none (by rw [h2]; exact hj)]
  isSourceChal_iff := by
    intro j
    constructor
    · intro h
      have hj : j < 4 := h.1
      have key : ∀ j < 4, program.IsSourceChal j → j = 0 ∨ j = 1 := by decide +kernel
      exact key j hj h
    · rintro (rfl | rfl) <;> decide +kernel
  chalFacts := by
    decide +kernel
  kinds59_60 := by
    decide +kernel
  trFields := by decide +kernel
  projReadsN := by decide +kernel

/-- The native program's domain `H` facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHHash (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (Native.ROMParams.MldsaHHash nat)

/-- The native program's SampleInBall facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHSample (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (Native.ROMParams.MldsaHSample nat)

/-- The native program's constants over `GF(2^128)` at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHConsts (Emulated.MldsaEmbed.nat program) RealizedProgram.gf128 :=
  inferInstanceAs (Native.ROMParams.MldsaHConsts nat RealizedProgram.gf128)

/-- **The statement holds a key's preprocessing** (`Emulated.KeyOf`). -/
abbrev KeyOf (pk : MLDSA44.PublicKey44) (x : program.Valuation interp) : Prop :=
  Emulated.KeyOf pk x

/-- **The relation of the theorem at the realized program of `MLDSA44.Emulated.ROMParams`** (`Emulated.rel`). -/
abbrev rel : Set (program.Valuation interp × Native.ROMParams.VarWitness) :=
  Emulated.rel

/-- **The witness extracted from a statement and a committed assignment** (`Emulated.proj`).

Running time: `Emulated.proj`'s paragraph (polynomial in the program's size).
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    Native.ROMParams.VarWitness :=
  Emulated.proj x a

/-- **The extractor of `Π_P₀`** for `MLDSA44.Emulated.ROMParams` (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) Native.ROMParams.VarWitness :=
  program.sourceExtractor interp proj

/-- **The crossing wherever the source program holds** (`Emulated.CrossSound`). -/
abbrev CrossSound : Prop := Emulated.CrossSound (program := program)
  (F0 := RealizedProgram.gold2) (FH := RealizedProgram.gf128)

/-- **Domain `A`'s obligation** (`Emulated.AlgebraSound`). -/
abbrev AlgebraSound : Prop := Emulated.AlgebraSound (program := program)
  (F0 := RealizedProgram.gold2) (FH := RealizedProgram.gf128)

/-- **SampleInBall's events** (`Emulated.sampleEvent`). -/
abbrev sampleEvent (j : ℕ) (e : program.Env interp) : Prop :=
  Emulated.sampleEvent j e

/-- **The challenge-use rule** (`Emulated.sampleEvent_use`). -/
theorem sampleEvent_use : RealizedProgram.ChallengeUseAt program interp sampleEvent :=
  Emulated.sampleEvent_use

/-- **The relation from the source program without an event** (`Emulated.sound_of_views`). -/
theorem sound_of_views (hx : CrossSound) (hA : AlgebraSound) :
    ∀ e : program.Env interp, program.StatementOk interp e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ sampleEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  Emulated.sound_of_views hx hA

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Emulated.ROMParams`**, given the
crossing and the algebra (`Emulated.rbr_of_views`): SampleInBall's events with errors
`264/2^128` and `295/2^128`. -/
theorem rbr_of_views (hx : CrossSound) (hA : AlgebraSound) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use (sound_of_views hx hA))
      (program.roundError interp Native.ROMParams.sampleEps) :=
  Emulated.rbr_of_views hx hA

end GordieHowe.MLDSA44.Emulated.ROMParams
