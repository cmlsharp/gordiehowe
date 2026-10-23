-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.ProofSystem
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `MLDSA44.Native.QROMParams` with forked domains

The native ML-DSA-44 proof of possession at the QROM parameters as a multi-circuit IOP with forked domains on the
generic per-field domain proofs (`QROMParams.proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase, at the frontend's round-by-round knowledge soundness (`forkIop`, read at the
key's statement values). Its compiled argument is the compiler's with merges
(`GordieHowe/Applications/MLDSA44/Native/QROMParams.lean`).

* **The numbers of the domains** (`numbers`, `GordieHowe.RealizedProgram.ForkNumbers`): `32`-byte `F_q^11` elements
  for `A`, `32`-byte `GF(2^256)` elements for `H`, arrays of at most `1024` elements, challenge
  reads of at most `2400` and `1250` elements.
* **The transcript** (`forkTranscript`, `GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript`): the label, `48`-byte
  digests, the key-and-context writes, the branch names (each domain's field name,
  `DomainProfile::field_name`), the phases' codecs and readers, and every domain's codecs and
  readers at its field's codec and size bounds.
* **The facts the setting is built from** (`forkTranscript_bounds`): at most `2269` rounds
  (`forkFigures`, in the configuration file).
* **The loads** (`forkLoads`, `good_A_at`, `good_H_at`): every round's load within its domain's,
  each passing the Chernoff test `2^-990`.
* **The round errors** (`forkError_le`): every round of the composite on its own is at most
  `errorMax / 2^260` (`GordieHowe.RealizedProgram.ProofSystem.fieldForkError_le`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Native.QROMParams.Program (program)
open HashField (interp)
open scoped NNReal ENNReal

/- Generated data: a domain index `⟨0, h⟩` unified with `domainA` reads the generated program, which
raises `maxRecDepth`. -/
set_option maxRecDepth 8192

/-- **A statement of every domain** from its statements at `A` and at `H`. -/
theorem domain_cases {P : Fin program.domains.length → Prop} (hA : P domainA) (hH : P domainH) :
    ∀ d, P d
  | ⟨0, _⟩ => hA
  | ⟨1, _⟩ => hH
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-! ## The numbers of the domains -/

/-- **The codecs of the domains' fields**: `32`-byte `F_q^11` elements for `A`, `32`-byte
`GF(2^256)` elements for `H`, the C++ layouts and challenge readers. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interp (program.domainField d))
  | ⟨0, _⟩ => ⟨32, Codec.FieldBytes.mldsaNative11, CReader.mldsaNative11⟩
  | ⟨1, _⟩ => ⟨32, Codec.FieldBytes.gf2_256, CReader.gf2_256⟩
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `A`'s size bounds: `32`-byte elements, arrays of at most `1024`, reads of at most
`2400` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 32 1024 2400 := by decide +kernel

/-- Domain `H`'s size bounds: `32`-byte elements, arrays of at most `1024`, reads of at most
`1250` (decided). -/
theorem fitsOkH : RealizedProgram.FitsOk (ready domainH) 32 1024 1250 := by decide +kernel

/-- **The numbers of the domains** (`RealizedProgram.ForkNumbers`): the codecs `cod`, arrays of at most
`1024` elements, challenge reads of at most `2400` elements at `A` and `1250` at `H`. -/
def numbers : RealizedProgram.ForkNumbers ready where
  cod := cod
  Mx _ := 1024
  Lmax d := if d.1 = 0 then 2400 else 1250
  ok := domain_cases fitsOkA fitsOkH

variable (C : Compiled)

/-! ## The multi-circuit IOP with forked domains -/

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, (sourceError_final sampleEps)⟩

/-- **`MLDSA44.Native.QROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP KeyStmt
    (program.Valuation interp → ROMParams.VarWitness) keyRel :=
  (proofSystem C.src).fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  (((proofSystem C.src).fieldBranches ready).soundIOPSound ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    (sourceError_final sampleEps)).comap stmtOf

/-! ## The transcript -/

/-- **The branch names**: each domain's field name (`DomainProfile::field_name`,
`lib/gordiehowe/examples/shared/domain_profile.h`): `F_q^11` for `A`, `GF(2^256)` for `H`. -/
def branchName (d : Fin program.domains.length) : List Byte :=
  if d.1 = 0 then asciiBytes "F_q^11" else asciiBytes "GF(2^256)"

/-- **The C++ series–parallel transcript of `MLDSA44.Native.QROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `48`-byte digests (SHA-384), the key-and-context writes (`keyStmtCodec`), every
branch named by its domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at
`fieldBytes`) and readers (`RealizedProgram.appReaders` at `samplerReaders`), every domain's at
`numbers`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  (proofSystem C.src).fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label 48 keyStmtCodec (fun a => branchName a.1)
    (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le)

/-- **The facts the setting is built from**: the label, `48`-byte digests, the key-and-context
writes, branch names of at most `12` bytes, and the figures of `numbers`
(`RealizedProgram.ProofSystem.fieldForkTranscript_bounds`). -/
theorem forkTranscript_bounds : (forkTranscript C).Bounds :=
  (proofSystem C.src).fieldForkTranscript_bounds (forkLowering C) stmtOf numbers C.enforce
    (fun x => by
      change ((MLDSA44.PoP.StatementWrites.keyContext 0).pre x.1).length ≤ _
      rw [MLDSA44.PoP.StatementWrites.keyContext_pre_length]
      norm_num)
    (Nat.le_of_ble_eq_true rfl) (by norm_num) (by norm_num)
    (fun a => by
      change (branchName a.1).length ≤ _
      unfold branchName
      split_ifs <;> decide)
    (by decide +kernel)

/-! ## The loads -/

/-- **Domain `A`'s loads pass the Chernoff test `2^-990`** on `48 + fsExtraBytes`-byte streams:
`2400` draws of `F_q^11` and `144` column indices of `2` bytes (`passesChernoff_of_nat_at`; the
first term is `2^-2787.8`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨11 * 2400, 3⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 990) (48 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 990 (N := 48 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `H`'s loads pass the Chernoff test `2^-990`** on `48 + fsExtraBytes`-byte streams:
`1250` draws of `GF(2^256)` and `128` column indices of `2` bytes (the first term is
`2^-3583.8`). -/
theorem good_H_at {L : Load} (h : L ≤ ⟨1250, 32⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 990) (48 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 990 (N := 48 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Every round's load satisfies `good`** when every load within domain `A`'s bound
`⟨11 · 2400, 3⟩` and every load within domain `H`'s bound `⟨1250, 32⟩` (which also bounds the
phases' challenges) does (`RealizedProgram.ProofSystem.fieldForkLoads`, `ForkNumbers.forkLoad_fits`). -/
theorem forkLoads {good : Load → Prop} (hA : ∀ L, L ≤ ⟨11 * 2400, 3⟩ → good L)
    (hH : ∀ L, L ≤ ⟨1250, 32⟩ → good L) :
    ∀ j, ((forkTranscript C).readers j).AllLoads good := by
  refine (proofSystem C.src).fieldForkLoads ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce)
    (domain_cases (fun L hL => hA L (hL.trans (by
        rw [numbers.forkLoad_fits, Load.le_iff]
        exact ⟨by decide +kernel, by decide +kernel⟩)))
      (fun L hL => hH L (hL.trans (by
        rw [numbers.forkLoad_fits, Load.le_iff]
        exact ⟨by decide +kernel, by decide +kernel⟩)))) ?_
  refine program.appReaders_allLoads samplerReaders (fun _ => chalLoadMax) chalLoad_le
    fun k => hH _ ?_
  have hk := RealizedProgram.length_chalList_le (ir := program) k
  rw [challenges_length] at hk
  simp only [chalLoadMax, Load.nsmul, Load.le_iff]
  omega

/-! ## The round errors -/

/-- **Domain `A`'s round charges are at most `errorMax / 2^260`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsA_le :
    program.FieldRoundsLe (ready domainA) ((errorMax : ℝ≥0) / 2 ^ 260) :=
  .of_num (ready domainA) (by convert mldsaNativeField11_card <;> rfl)
    (AlgebraField.aCommit_le.trans (le_errorMax (by norm_num)))
    (AlgebraField.aTest_le.trans (le_errorMax (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact AlgebraField.aColumn_le.trans (le_errorMax (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Domain `H`'s round charges are at most `errorMax / 2^260`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsH_le :
    program.FieldRoundsLe (ready domainH) ((errorMax : ℝ≥0) / 2 ^ 260) :=
  .of_num (ready domainH) (by convert gf2_256_card <;> rfl)
    (Tableau.gf256K339R2Commit_le.trans (le_errorMax (by norm_num)))
    (Tableau.gf256K339R2Test_le.trans (le_errorMax (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact Tableau.gf256K339R2Column_le.trans (le_errorMax (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^140`**
(`RealizedProgram.ProofSystem.fieldForkError_le`): each domain's round charges (`roundsA_le`, `roundsH_le`) and the
phases' (`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop C).P (forkIop C).term) :
    (forkIopSound C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  (proofSystem C.src).fieldForkError_le ready stmtOf C.enforce source_rbr_knowledge_soundness
    (sourceError_final sampleEps)
    (domain_cases roundsA_le roundsH_le) (fun _ => phaseError_le C _) c

/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^140`. -/
theorem maxRoundError_le : maxError (forkIopSound C).error ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  maxError_le_iff.2 (forkError_le C)

end GordieHowe.MLDSA44.Native.QROMParams
