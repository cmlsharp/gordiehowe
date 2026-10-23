-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.Falcon512.Native.ROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Native.ROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `Falcon512.Native.ROMParams` with forked domains

The native Falcon-512 proof of possession at the ROM parameters as a multi-circuit IOP with forked domains on the
generic per-field domain proofs (`proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase, at the frontend's round-by-round knowledge soundness (`forkIop`, read at the
public key's statement values). Its compiled argument is spBCS's
(`GordieHowe/Applications/Falcon512/Native/ROMParams.lean`).

* **The transcript** (`forkTranscript`, `GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript`): the label, `32`-byte
  digests, the key writes, the branch names (each domain's field name), the phases' codecs and
  readers, and every domain's codecs and readers at its field's codec (`cod`) and size bounds
  (`numbers`).
* **The facts the setting is built from** (`forkTranscript_bounds`): the rounds of the term are at
  most `2357` (`forkFigures`, in the configuration file).
* **The loads** (`forkLoads`, `good_A_at`, `good_H_at`): every round's load within its domain's,
  each passing the Chernoff test `2^-2780`.
* **The round errors** (`forkError_le`): every round of the composite on its own is at most
  `errorMax / 2^140` (`GordieHowe.RealizedProgram.ProofSystem.fieldForkError_le`).
* **The queries and the leaves** (`forkFigures`, in the configuration file): at most `63 + 90`
  opened columns, trees of `3392` and `1694` leaves.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.ROMParams.Program (program)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/- Generated data: a domain index unified with a domain constant reads the generated program,
which raises maxRecDepth. -/
set_option maxRecDepth 8192

/-! ## The fields' codecs -/

/-- **A statement of every domain** from its statements at `H` and at `A`. -/
theorem domain_cases {P : Fin program.domains.length → Prop} (hH : P domainH) (hA : P domainA) :
    ∀ d, P d
  | ⟨0, _⟩ => hH
  | ⟨1, _⟩ => hA
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The codecs of the domains' fields**: `16`-byte `GF(2^128)` elements for `H`, `18`-byte
`F_q^9` elements for `A`, the C++ layouts and challenge readers. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interp (program.domainField d))
  | ⟨0, _⟩ => ⟨16, Codec.FieldBytes.gf2_128, CReader.gf2_128⟩
  | ⟨1, _⟩ => ⟨18, Codec.FieldBytes.falconNative, CReader.falconNative⟩
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `H`'s size bounds: `16`-byte elements, arrays of at most `1024`, reads of at
most `1250` (decided). -/
theorem fitsOkH : RealizedProgram.FitsOk (ready domainH) 16 1024 1250 := by decide +kernel

/-- Domain `A`'s size bounds: `18`-byte elements, arrays of at most `1024`, reads of at
most `2250` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 18 1024 2250 := by decide +kernel

/-- **The numbers of the domains** (`RealizedProgram.ForkNumbers`): the codecs `cod`, arrays of at most
`1024` elements, challenge reads of at most `1250` elements at `H` and `2250` at `A`. -/
def numbers : RealizedProgram.ForkNumbers ready where
  cod := cod
  Mx _ := 1024
  Lmax d := if d.1 = 0 then 1250 else 2250
  ok := domain_cases fitsOkH fitsOkA

variable (C : Compiled)

/-! ## The multi-circuit IOP with forked domains -/

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

/-- **`Falcon512.Native.ROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP PublicKey (program.Valuation interp → VarWitness)
    keyRel :=
  (proofSystem C.src).fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  (((proofSystem C.src).fieldBranches ready).soundIOPSound ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final).comap stmtOf

/-! ## The transcript -/

/-- **The branch names**: each domain's field name (`DomainProfile::field_name`): `GF(2^128)` for
`H`, `F_q^9` for `A`. -/
def branchName (d : Fin program.domains.length) : List Byte :=
  if d.1 = 0 then asciiBytes "GF(2^128)" else asciiBytes "F_q^9"

/-- **The C++ series–parallel transcript of `Falcon512.Native.ROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `32`-byte digests, the key writes (`falconKeyCodec`), every branch named by its
domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at `fieldBytes`) and readers
(`RealizedProgram.appReaders` at `samplerReaders`), every domain's at `numbers`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  (proofSystem C.src).fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label 32
    falconKeyCodec (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le)

/-! ## The facts the setting is built from -/

/-- **The facts the setting is built from**: the label, the digest length, the statement's
writes, the branch names and the figures of `numbers` (`RealizedProgram.ProofSystem.fieldForkTranscript_bounds`). -/
theorem forkTranscript_bounds : (forkTranscript C).Bounds :=
  (proofSystem C.src).fieldForkTranscript_bounds (forkLowering C) stmtOf numbers C.enforce
    (fun pk => by
      change (falconKeyWrites pk).length ≤ _
      rw [falconKeyWrites_length]
      norm_num)
    (Nat.le_of_ble_eq_true rfl) (by norm_num) (by norm_num)
    (fun a => by
      change (branchName a.1).length ≤ _
      unfold branchName
      split_ifs <;> decide)
    (by decide +kernel)

/-! ## The loads -/

/-- **Every round's load satisfies `good`** when every load within domain `A`'s bound
`⟨9 · 2250, 2⟩` and every load within domain `H`'s bound `⟨1250, 16⟩` (which also bounds the
phases' challenges) does (`RealizedProgram.ProofSystem.fieldForkLoads`). -/
theorem forkLoads {good : Load → Prop} (hA : ∀ L, L ≤ ⟨9 * 2250, 2⟩ → good L)
    (hH : ∀ L, L ≤ ⟨1250, 16⟩ → good L) :
    ∀ j, ((forkTranscript C).readers j).AllLoads good := by
  refine (proofSystem C.src).fieldForkLoads ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce)
    (domain_cases (fun L hL => hH L (hL.trans (by
        rw [numbers.forkLoad_fits, Load.le_iff]
        exact ⟨by decide +kernel, by decide +kernel⟩)))
      (fun L hL => hA L (hL.trans (by
        rw [numbers.forkLoad_fits, Load.le_iff]
        exact ⟨by decide +kernel, by decide +kernel⟩)))) ?_
  refine program.appReaders_allLoads samplerReaders (fun _ => chalLoadMax) chalLoad_le
    fun k => hH _ ?_
  have hk := RealizedProgram.length_chalList_le (ir := program) k
  rw [challenges_length] at hk
  simp only [chalLoadMax, Load.nsmul, Load.le_iff]
  omega

/-- **Domain `H`'s loads pass the Chernoff test `2^-2780`** (the first term is `2^-3584`). -/
theorem good_H_at {L : Load} (h : L ≤ ⟨1250, 16⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 2780) (32 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 2780 (N := 32 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `A`'s loads pass the Chernoff test `2^-2780`** (the first term is `2^-2787`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨9 * 2250, 2⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 2780) (32 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 2780 (N := 32 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-! ## The round errors -/

/-- **Domain `H`'s round charges are at most `errorMax / 2^140`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsH_le :
    program.FieldRoundsLe (ready domainH)
      ((errorMax : ℝ≥0) / 2 ^ 140) :=
  .of_num (ready domainH) (by convert gf2_128_card <;> rfl)
    (Tableau.gf128K282R2Commit_le.trans (div_two_pow_le (by norm_num)))
    (Tableau.gf128K282R2Test_le.trans (div_two_pow_le (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact Tableau.gf128K282R2Column_le.trans (div_two_pow_le (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Domain `A`'s round charges are at most `errorMax / 2^140`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsA_le :
    program.FieldRoundsLe (ready domainA)
      ((errorMax : ℝ≥0) / 2 ^ 140) :=
  .of_num (ready domainA) (by convert falconNativeField_card <;> rfl)
    (Ring.Native.Params.aNativeROMCommit_le.trans (div_two_pow_le (by norm_num)))
    (Ring.Native.Params.aNativeROMTest_le.trans (div_two_pow_le (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact Ring.Native.Params.aNativeROMColumn_le.trans (div_two_pow_le (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^140`**
(`RealizedProgram.ProofSystem.fieldForkError_le`): each domain's round charges (`roundsH_le`, `roundsA_le`) and the
phases' (`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop C).P (forkIop C).term) :
    (forkIopSound C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 140 :=
  (proofSystem C.src).fieldForkError_le ready stmtOf C.enforce source_rbr_knowledge_soundness
    sourceError_final
    (domain_cases roundsH_le roundsA_le) (fun _ => phaseError_le C _) c

/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^140`. -/
theorem maxRoundError_le : maxError (forkIopSound C).error ≤ (errorMax : ℝ≥0) / 2 ^ 140 :=
  maxError_le_iff.2 (forkError_le C)

end GordieHowe.Falcon512.Native.ROMParams
