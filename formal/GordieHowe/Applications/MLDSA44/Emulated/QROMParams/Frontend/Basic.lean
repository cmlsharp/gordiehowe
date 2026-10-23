-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Frontend.Shape
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.HashField

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Emulated.QROMParams`

The emulated ML-DSA frontend (`GordieHowe.MLDSA44.Emulated`) at the emulated ML-DSA-44 program at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`, export `c825eb05`): it holds the native
program's domain `H` under `Emulated.σ` (`MldsaEmbed`), its program facts (`MldsaEMain`,
`MldsaECross`, `MldsaEAlgebra`) are decided here, domain `A` is Goldilocks⁴ (`GordieHowe.MLDSA44.AField`), domain
`H` is `GF(2^256)` (`gf256`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open Generated.MLDSA44.Emulated.QROMParams.Program (program)
open HashField (interp)
open GordieHowe.Bits IOP
open scoped NNReal ENNReal

/-- The native ML-DSA program at the QROM parameters, whose domain `H` the emulated one holds. -/
abbrev nat : RealizedProgram := Generated.MLDSA44.Native.QROMParams.Program.program

/-- The renaming (`Emulated.σ`). -/
abbrev σ : RealizedProgram.Renaming := Emulated.σ

/-- The native shared expressions of domain `H`'s part (`Emulated.hR`). -/
abbrev hR : List ℕ := Emulated.hR

/-- **The emulated program holds the native program's domain `H`** (`RealizedProgram.Embedding`). -/
theorem embedding : nat.Embedding program σ Emulated.hV hR :=
  RealizedProgram.embedding_iff.2 (by decide +kernel)

/-- **Native predicate `k` of domain `H` is emulated predicate `k + 2`**, renamed. -/
theorem predCorr : ∀ k, 18 ≤ k → k ≤ 270 →
    nat.equalCorrB program σ Emulated.hV hR (nat.predicate k).body
      (program.predicate (k + 2)).body = true ∧
      k + 2 < program.predicates.length ∧ program.inSource (program.predicate (k + 2)) = true := by
  decide +kernel

/-- **The values the frontend reads by their node types** are renamed to node-typed source
values. -/
theorem typedCorr : ∀ v ∈ Native.ROMParams.hTyped, v ∈ Emulated.hV ∧
    σ.val v < program.values.length ∧ program.IsSourceValue (σ.val v) ∧
    (program.value (σ.val v)).typeSource = .node := by
  decide +kernel

/-- **The emulated program at the QROM parameters holds the native program's domain `H`.** -/
instance : Emulated.MldsaEmbed program where
  nat := nat
  embedding := embedding
  predCorr := predCorr
  typedCorr := typedCorr

/-- Goldilocks⁴ has domain `A`'s field facts. -/
instance : AField RealizedProgram.gold4 where
  charP := inferInstanceAs (CharP GoldilocksExt4 pGold)
  char_spec := rfl
  decode_eq _ := rfl
  toNat_natCast k hk := by
    change (goldilocksExt4Coords (k : GoldilocksExt4) 0).val = k
    rw [goldilocksExt4Coords_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has the composition's facts. -/
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

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has the crossing's facts. -/
instance : Emulated.MldsaECross program where
  expr6 := rfl
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  crossData := by
    decide +kernel
  crossPred := ⟨_, rfl⟩

/-- **The digit layout of `MLDSA44.Emulated.QROMParams`**: `w'`, `z + 130993`, the offset and the slack in
two base-`4096` digits each (`578`, `579`; `580`, `581`; `585`, `586`; `587`, `588`); the offset's
and the slack's bound `2^24`. -/
def layout : Emulated.MldsaELayout where
  w := ⟨4096, [578, 579]⟩
  z := ⟨4096, [580, 581]⟩
  offset := ⟨4096, [585, 586]⟩
  slack := ⟨4096, [587, 588]⟩
  offsetBound := 16777216

set_option maxRecDepth 4096 in
/-- The emulated program at the QROM parameters has domain `A`'s facts. -/
instance : Emulated.MldsaEAlgebra program where
  layout := layout
  offsetBound_lt := by decide
  lenWeight := by decide +kernel
  lenSigL := by decide +kernel
  pred0 := rfl
  pred1 := rfl
  pred2 := rfl
  pred11 := ⟨_, rfl⟩
  pred12 := ⟨_, rfl⟩
  pred13 := ⟨_, rfl⟩
  pred14 := ⟨_, rfl⟩
  pred15 := ⟨_, rfl⟩
  pred274 := ⟨_, rfl⟩
  expr7 := rfl
  expr8 := rfl
  expr0 := rfl
  expr1 := rfl
  expr2 := rfl
  expr3 := rfl
  expr4 := rfl
  expr5 := rfl
  inSource_A := by
    decide +kernel
  lensA := by
    decide +kernel
  boolChecks := by
    decide +kernel
  constsA := by
    decide +kernel
  constsU := by
    decide +kernel
  refsA := by decide +kernel
  lensU := by
    decide +kernel
  valsU := by
    decide +kernel
  sigData := by
    decide +kernel
  boundZW := by
    decide +kernel

/-- The native program's domain `H` facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHHash (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (Native.ROMParams.MldsaHHash nat)

/-- The native program's SampleInBall facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHSample (Emulated.MldsaEmbed.nat program) :=
  inferInstanceAs (Native.ROMParams.MldsaHSample nat)

/-- The native program's constants over `GF(2^256)` at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHConsts (Emulated.MldsaEmbed.nat program) RealizedProgram.gf256 :=
  inferInstanceAs (Native.ROMParams.MldsaHConsts nat RealizedProgram.gf256)

/-- **The round errors of SampleInBall's challenges** over `GF(2^256)`: `264/2^256` and
`295/2^256` (`Native.ROMParams.sampleEpsOf 256`). -/
noncomputable def sampleEps (j : ℕ) : NNReal := Native.ROMParams.sampleEpsOf 256 j

/-- **The statement holds a key's preprocessing** (`Emulated.KeyOf`). -/
abbrev KeyOf (pk : MLDSA44.PublicKey44) (x : program.Valuation interp) : Prop :=
  Emulated.KeyOf pk x

/-- **The relation of the theorem at the realized program of `MLDSA44.Emulated.QROMParams`** (`Emulated.rel`). -/
abbrev rel : Set (program.Valuation interp × Native.ROMParams.VarWitness) :=
  Emulated.rel

/-- **The witness extracted from a statement and a committed assignment** (`Emulated.proj`).

Running time: `Emulated.proj`'s paragraph (polynomial in the program's size).
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (x : program.Valuation interp) (a : program.Assignment interp) :
    Native.ROMParams.VarWitness :=
  Emulated.proj x a

/-- **The extractor of `Π_P₀`** for `MLDSA44.Emulated.QROMParams` (`RealizedProgram.sourceExtractor` at `proj`).

Running time: one read of the transcript's first round and one call of `proj` (polynomial,
`proj`'s paragraph). This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec interp) (program.Valuation interp) Native.ROMParams.VarWitness :=
  program.sourceExtractor interp proj

/-- **The crossing wherever the source program holds** (`Emulated.CrossSound`). -/
abbrev CrossSound : Prop := Emulated.CrossSound (program := program)
  (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256)

/-- **Domain `A`'s obligation** (`Emulated.AlgebraSound`). -/
abbrev AlgebraSound : Prop := Emulated.AlgebraSound (program := program)
  (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256)

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

/-- **Round-by-round knowledge soundness of `Π_P₀` for `MLDSA44.Emulated.QROMParams`**, given the
crossing and the algebra (`Emulated.rbr_of_views`): SampleInBall's events with errors
`264/2^256` and `295/2^256`. -/
theorem rbr_of_views (hx : CrossSound) (hA : AlgebraSound) :
    rbrKnowledgeSoundness rel (program.sourceVerifier interp) extractor
      (program.eventState interp rel proj sampleEvent sampleEvent_use (sound_of_views hx hA))
      (program.roundError interp sampleEps) :=
  Emulated.rbr_of_views hx hA

/-- **`mac.equal` gives the crossing** (`Emulated.crossSound`). -/
theorem crossSound : CrossSound := Emulated.crossSound

/-- **Domain `A`'s obligation** (`Emulated.algebraSound`). -/
theorem algebraSound : AlgebraSound := Emulated.algebraSound

end GordieHowe.MLDSA44.Emulated.QROMParams
