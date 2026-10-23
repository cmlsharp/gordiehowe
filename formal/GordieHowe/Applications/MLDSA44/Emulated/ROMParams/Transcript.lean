-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.FieldCharges
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `MLDSA44.Emulated.ROMParams` with forked domains

The emulated ML-DSA-44 proof of possession at the ROM parameters as a multi-circuit IOP with forked
domains on the generic per-field domain proofs (`proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase, at the frontend's round-by-round knowledge soundness (`forkIop`, read at the
key's statement values). Its compiled argument is the one spBCS gives
(`GordieHowe/Applications/MLDSA44/Emulated/ROMParams.lean`).

* **The transcript** (`forkTranscript`, `GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript`): the label, `32`-byte
  digests, the key-and-context writes, the branch names (each domain's field name,
  `DomainProfile::field_name`), the phases' codecs and readers, and every domain's codecs and
  readers at its field's codec (`cod`) and size bounds (`numbers`).
* **The facts the setting is built from** (`forkTranscript_bounds`): the rounds of the term are at
  most `2333` (`forkFigures`, in the configuration file).
* **The loads** (`forkLoads`, `good_A_at`, `good_H_at`): every round's load within its domain's,
  each passing the Chernoff test `2^-2780`.
* **The round errors** (`forkError_le`): every round of the composite on its own is at most
  `errorMax / 2^140` (`GordieHowe.RealizedProgram.ProofSystem.fieldForkError_le`).
* **The queries and the leaves** (`forkFigures`, in the configuration file): at most `96 + 63`
  opened columns, trees of `2560` and `3392` leaves.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open HashField (interp)
open scoped NNReal ENNReal

/- Generated data: a domain index `⟨0, h⟩` unified with `domainA` reads the generated program, which
raises `maxRecDepth`. -/
set_option maxRecDepth 8192

/-! ## The fields' codecs -/

/-- **A statement of every domain** from its statements at `A` and at `H`. -/
theorem domain_cases {P : Fin program.domains.length → Prop} (hA : P domainA) (hH : P domainH) :
    ∀ d, P d
  | ⟨0, _⟩ => hA
  | ⟨1, _⟩ => hH
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The codecs of the domains' fields**: `16`-byte Goldilocks² elements for `A`, `16`-byte
`GF(2^128)` elements for `H`, the C++ layouts and challenge readers. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interp (program.domainField d))
  | ⟨0, _⟩ => ⟨16, Codec.FieldBytes.goldilocksExt2, CReader.goldilocksExt2⟩
  | ⟨1, _⟩ => ⟨16, Codec.FieldBytes.gf2_128, CReader.gf2_128⟩
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `A`'s size bounds: `16`-byte elements, arrays of at most `1024`, reads of at
most `2400` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 16 1024 2400 := by decide +kernel

/-- Domain `H`'s size bounds: `16`-byte elements, arrays of at most `1024`, reads of at
most `1250` (decided). -/
theorem fitsOkH : RealizedProgram.FitsOk (ready domainH) 16 1024 1250 := by decide +kernel

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
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, (sourceError_final Native.ROMParams.sampleEps)⟩

/-- **`MLDSA44.Emulated.ROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP KeyStmt
    (program.Valuation interp → Native.ROMParams.VarWitness) keyRel :=
  (proofSystem C.src).fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  (((proofSystem C.src).fieldBranches ready).soundIOPSound ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    (sourceError_final Native.ROMParams.sampleEps)).comap stmtOf

/-! ## The transcript -/

/-- **The branch names**: each domain's field name (`DomainProfile::field_name`,
`lib/gordiehowe/examples/shared/domain_profile.h`): `Goldilocks^2` for `A`, `GF(2^128)` for `H`. -/
def branchName (d : Fin program.domains.length) : List Byte :=
  if d.1 = 0 then asciiBytes "Goldilocks^2" else asciiBytes "GF(2^128)"

/-- **The C++ series–parallel transcript of `MLDSA44.Emulated.ROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `32`-byte digests (SHA-256), the key-and-context writes (`keyStmtCodec`), every
branch named by its domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at
`fieldBytes`) and readers (`RealizedProgram.appReaders` at `samplerReaders`), every domain's at `numbers`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  (proofSystem C.src).fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label 32
    keyStmtCodec (fun a => branchName a.1) (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le)

/-! ## The facts the setting is built from -/

/-- **The facts the setting is built from**: the label, the digest length, the statement's
writes, the branch names and the figures of `numbers` (`RealizedProgram.ProofSystem.fieldForkTranscript_bounds`). -/
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

/-- **Every round's load satisfies `good`** when every load within domain `A`'s bound
`⟨2 · 2400, 8⟩` and every load within domain `H`'s bound `⟨1250, 16⟩` (which also bounds the
phases' challenges) does (`RealizedProgram.ProofSystem.fieldForkLoads`). -/
theorem forkLoads {good : Load → Prop} (hA : ∀ L, L ≤ ⟨2 * 2400, 8⟩ → good L)
    (hH : ∀ L, L ≤ ⟨1250, 16⟩ → good L) :
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

/-- **Domain `A`'s loads pass the Chernoff test `2^-2780`** on `32 + fsExtraBytes`-byte streams
(`passesChernoff_of_nat_at`; the first term is `2^-2787.8`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨2 * 2400, 8⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 2780) (32 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 2780 (N := 32 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `H`'s loads pass the Chernoff test `2^-2780`** on `32 + fsExtraBytes`-byte streams
(the first term is `2^-3583.8`). -/
theorem good_H_at {L : Load} (h : L ≤ ⟨1250, 16⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 2780) (32 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 2780 (N := 32 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-! ## The round errors -/

/-- **Domain `A`'s round charges are at most `errorMax / 2^140`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsA_le :
    program.FieldRoundsLe (ready domainA)
      ((errorMax : ℝ≥0) / 2 ^ 140) :=
  .of_num (ready domainA) (by convert goldilocksExt2_card <;> rfl)
    (Tableau.gold2K512R2Commit_le.trans (div_two_pow_le (by norm_num)))
    (Tableau.gold2K512R2Test_le.trans (div_two_pow_le (by norm_num)))
    (by
        rw [if_neg (by rw [np0]; norm_num)]
        exact Tableau.gold2K512R2Column_le.trans (div_two_pow_le (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
        rw [if_neg (by rw [np1]; norm_num)]
        exact Tableau.gf128K282R2Column_le.trans (div_two_pow_le (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^140`**
(`RealizedProgram.ProofSystem.fieldForkError_le`): each domain's round charges (`roundsA_le`, `roundsH_le`) and the
phases' (`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop C).P (forkIop C).term) :
    (forkIopSound C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 140 :=
  (proofSystem C.src).fieldForkError_le ready stmtOf C.enforce source_rbr_knowledge_soundness
    (sourceError_final Native.ROMParams.sampleEps)
    (domain_cases roundsA_le roundsH_le) (fun _ => phaseError_le C _) c

/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^140`. -/
theorem maxRoundError_le : maxError (forkIopSound C).error ≤ (errorMax : ℝ≥0) / 2 ^ 140 :=
  maxError_le_iff.2 (forkError_le C)

end GordieHowe.MLDSA44.Emulated.ROMParams
