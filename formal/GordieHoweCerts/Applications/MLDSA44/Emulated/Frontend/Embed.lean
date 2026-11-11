-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Applications.MLDSA44.EmbedFacts
public import GordieHoweCerts.Applications.MLDSA44.Frontend.Basic
public import GordieHowe.Language.RealizedProgram.PrimeField
public import GordieHowe.Foundations.Fields.Goldilocks

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program holds a native one's domain `H`

An emulated ML-DSA program (`MLDSA44.Emulated.ROMParams`, `MLDSA44.Emulated.QROMParams`) holds
domain `H` of the native program at the same parameters: the values and shared expressions of the
native program's predicates `18 … 270` (the Keccak trace, `μ`'s padding, the selection, the memory
check) and of its crossing's operand of domain `H` are renamed to the emulated program's, with
their kinds, sizes, fields, types and phases, and native predicate `k` is an emulated predicate
(`MldsaEmbed`). The compiler computes the renaming, the part and the predicate pairs from the two
programs and exports them as the emulated program's checked embedding data (C++
`lib/gordiehowe/compiler/embedding.h`); each emulated program reads them from its data and decides
the layout facts the frontends read: the challenges keep their identifiers, and the held pairs
(native predicate, emulated predicate) are the data's. Where a native value lands is read through
the renaming and its inverse on the part (`eOf`), never by an identifier of the emulated program.
So the native frontend's facts about domain `H`
(`GordieHowe.MLDSA44.HSat`, `HashView`, `SampleView`) hold for the emulated program through
`GordieHowe.RealizedProgram.pullEnv` (`hSat`).
-/

namespace GordieHowe.MLDSA44.Emulated

/-- **An emulated program holds a native program's domain `H`**: the embedding under its renaming
`σ` of the part's values `V` and shared expressions `R` (`RealizedProgram.Embedding`), each read
from the program's checked embedding data; native predicate `k` of domain `H` is emulated predicate
`pred k`, renamed, a source predicate; the values the frontend reads by their node types are
renamed to node-typed source values; and the layout facts the frontends read, decided from the
data (`chalId`, `readV`, `held`). Each emulated program instantiates it, naming
its native program (`nat`). -/
class MldsaEmbed (program : RealizedProgram) where
  /-- The native program. -/
  nat : RealizedProgram
  /-- The renaming. -/
  σ : RealizedProgram.Renaming
  /-- The part's values. -/
  V : List ℕ
  /-- The part's shared expressions. -/
  R : List ℕ
  /-- The emulated predicate of each held native predicate. -/
  pred : ℕ → ℕ
  /-- The embedding. -/
  embedding : nat.Embedding program σ V R
  /-- Native predicate `k` of domain `H` is emulated predicate `pred k`. -/
  predCorr : ∀ k, hPredLo ≤ k → k ≤ hPredHi →
    nat.equalCorrB program σ V R (nat.predicate k).body (program.predicate (pred k)).body = true ∧
      pred k < program.predicates.length ∧ program.inSource (program.predicate (pred k)) = true
  /-- The typed values. -/
  typedCorr : ∀ v ∈ MLDSA44.hTyped, v ∈ V ∧ (σ).val v < program.values.length ∧
    program.IsSourceValue ((σ).val v) ∧ (program.value ((σ).val v)).typeSource = .node
  /-- The challenges keep their identifiers. -/
  chalId : ∀ j, (σ).chal j = j
  /-- `tr` (`66`) is held. -/
  readV : 66 ∈ V
  /-- The held pairs (native predicate, emulated predicate) of the data. -/
  held : List (ℕ × ℕ)
  /-- `pred` pairs each held native predicate with its emulated predicate. -/
  pred_held : ∀ p ∈ held, pred p.1 = p.2

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaEmbed program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaEmbed.σ program

set_option hygiene false in
local notation "hV" => MldsaEmbed.V program

/-- **An environment of the emulated program read as one of the native program** (through `σ`,
`RealizedProgram.pullEnv`). -/
abbrev pull (e : program.Env interp) : (nat).Env interp := (nat).pullEnv σ hV e

/-- **Domain `H`'s part holds** in the environment read as the native program's, where the emulated
source program holds. -/
theorem hSat {e : program.Env interp} (hs : program.SourceSatAt e) :
    MLDSA44.HSat (pull e) where
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
read as the native program's, is its renamed emulated value. -/
theorem reader_pull (e : program.Env interp) {v : ℕ} (hv : v ∈ hV) (i : ℕ) :
    (nat).reader (pull e) v i = RealizedProgram.castElt (program.reader e ((σ).val v) i) :=
  RealizedProgram.reader_pullEnv MldsaEmbed.embedding e hv i

variable (program) in
/-- **The renaming's inverse on the part**: the native value of `hV` an emulated value renames, from
the table of the renaming on the held values (`RealizedProgram.Renaming.invOn`). Irreducible: the
statements that read it compare its lookups, never its table. -/
@[irreducible] def eOf (v : ℕ) : Option ℕ :=
  ((σ).invOn hV).get? v

/-- An emulated value the inverse maps to `u` is `u`'s renamed value, with `u` held. -/
theorem eOf_spec {v u : ℕ} (h : eOf program v = some u) : u ∈ hV ∧ (σ).val u = v := by
  unfold eOf at h
  exact RealizedProgram.Renaming.invOn_spec h

end GordieHowe.MLDSA44.Emulated
