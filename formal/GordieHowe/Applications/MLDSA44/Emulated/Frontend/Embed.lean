-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Frontend.AField

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program holds a native one's domain `H`

An emulated ML-DSA program (`MLDSA44.Emulated.ROMParams`, `MLDSA44.Emulated.QROMParams`, export `c825eb05`)
holds domain `H` of the native program at the same parameters with every value identifier one larger and
every shared-expression identifier two larger (`σ`): the values `hV` (`7`, `9 … 55`, `67 … 567`) and
shared expressions `hR` (`11 … 525`, the crossing's `H` operand included) of the native program's
predicates `18 … 270` (the Keccak trace, `μ`'s padding, the selection, the memory check) are renamed
to the emulated program's, with their kinds, sizes, fields, types and phases, and native predicate
`k` is emulated predicate `k + 2` (`MldsaEmbed`, decided per pair of programs). So the native
frontend's facts about domain `H` (`GordieHowe.MLDSA44.Native.ROMParams.HSat`, `HashView`, `SampleView`) hold for the
emulated program through `GordieHowe.RealizedProgram.pullEnv` (`hSat`).
-/

namespace GordieHowe.MLDSA44.Emulated

/-- **The renaming**: value `v` of the native program is value `v + 1` of the emulated one, shared
expression `k` is `k + 2`. -/
def σ : RealizedProgram.Renaming := ⟨(· + 1), (· + 2)⟩

/-- **The native values of domain `H`'s part**: the zero constant `7`, the constants `9 … 55` and
`H`'s values `67 … 567`. -/
def hV : List ℕ := 7 :: List.range' 9 47 ++ List.range' 67 501

/-- **The native shared expressions of domain `H`'s part**: `11 … 525` (`522 … 525` the crossing's
operand). -/
def hR : List ℕ := List.range' 11 515

/-- **An emulated program holds a native program's domain `H`**: the embedding under `σ`
(`RealizedProgram.Embedding`), native predicate `k` of domain `H` is emulated predicate `k + 2`, renamed,
a source predicate, and the values the frontend reads by their node types are renamed to
node-typed source values. Each emulated program instantiates it by `decide`, naming its native
program (`nat`). -/
class MldsaEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The embedding. -/
  embedding : nat.Embedding program σ hV hR
  /-- Native predicate `k` of domain `H` is emulated predicate `k + 2`. -/
  predCorr : ∀ k, 18 ≤ k → k ≤ 270 →
    nat.equalCorrB program σ hV hR (nat.predicate k).body (program.predicate (k + 2)).body = true ∧
      k + 2 < program.predicates.length ∧ program.inSource (program.predicate (k + 2)) = true
  /-- The typed values. -/
  typedCorr : ∀ v ∈ Native.ROMParams.hTyped, v ∈ hV ∧ σ.val v < program.values.length ∧
    program.IsSourceValue (σ.val v) ∧ (program.value (σ.val v)).typeSource = .node

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaEmbed program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

/-- **An environment of the emulated program read as one of the native program** (through `σ`,
`RealizedProgram.pullEnv`). -/
abbrev pull (e : program.Env interp) : (nat).Env interp := (nat).pullEnv σ hV e

/-- **Domain `H`'s part holds** in the environment read as the native program's, where the emulated
source program holds. -/
theorem hSat {e : program.Env interp} (hs : program.SourceSatAt e) :
    Native.ROMParams.HSat (pull e) where
  preds k h1 h2 := by
    obtain ⟨hc, hl, hsrc⟩ := MldsaEmbed.predCorr (program := program) k h1 h2
    exact (RealizedProgram.holdsAt_pullEnv MldsaEmbed.embedding e hc).1
      (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc)
  types v hv i hi := by
    obtain ⟨hvV, hl, hsrc, hts⟩ := MldsaEmbed.typedCorr (program := program) v hv
    refine RealizedProgram.inType_pullEnv MldsaEmbed.embedding e hvV (hs.types _ hl hsrc hts i ?_)
    rw [((MldsaEmbed.embedding (program := program)).vals v hvV).2.2.2.1]
    exact hi

/-- **The readers agree on `hV`**: a native value of domain `H`'s part, read in the environment
read as the native program's, is the emulated value one larger. -/
theorem reader_pull (e : program.Env interp) {v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).reader (pull e) v i = RealizedProgram.castElt (program.reader e (v + 1) i) :=
  RealizedProgram.reader_pullEnv MldsaEmbed.embedding e hv i

end GordieHowe.MLDSA44.Emulated
