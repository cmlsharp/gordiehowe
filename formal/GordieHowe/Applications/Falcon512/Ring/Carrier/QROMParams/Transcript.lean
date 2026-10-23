-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `Falcon512.Ring.Carrier.QROMParams` with forked domains

The Falcon ring carrier at the QROM parameters as a multi-circuit IOP with forked domains on the generic per-field
domain proofs (`proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`): domain `A` over Goldilocks⁴, forked with its
batch stage (`magnitudes.s2`) and its GKR (`c.A`) as branches and the tree and Ligero as the join
(the C++ `nb + 1 = 2` branches, `lib/gordiehowe/compiler/compiled_domain.h`), with the proof system's
application phase, at the frontend's round-by-round knowledge soundness (`forkIop`, the ring
statement read and checked, `comapWith`). Its compiled argument is the compiler's with merges
(`GordieHowe/Applications/Falcon512/Ring/Carrier/QROMParams.lean`).

* **The transcript** (`forkTranscript`): the label, `48`-byte digests, the ring statement's writes,
  the branch name, the phase's codecs and readers, and the domain's codecs and readers at its
  field's codec (`cod`) and size bounds (`numbers`), as `GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript` builds them.
* **The facts the setting is built from** (`forkTranscript_bounds`): the rounds of the term are at
  most `955` (`forkFigures`, in the configuration file).
* **The loads** (`forkLoads`, `good_A_at`, `good_phase_at`): every round's load within domain `A`'s
  or the phase's, each passing the Chernoff test `2^-3700`.
* **The round errors** (`forkError_le`): every round within `errorMax / 2^260`.
* **The queries and the leaves** (`forkFigures`, in the configuration file): at most `201` opened
  columns, a tree of `3072` leaves.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open Native (Signer CoreWit scheme)
open scoped NNReal ENNReal

/- Generated data: a domain index unified with a domain constant reads the generated program,
which raises maxRecDepth. -/
set_option maxRecDepth 8192

/-! ## The field's codec -/

/-- **A statement of every domain** from its statement at `A`. -/
theorem domain_cases {P : Fin program.domains.length → Prop} (hA : P domainA) : ∀ d, P d
  | ⟨0, _⟩ => hA
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- **The codec of the domain's field**: `32`-byte Goldilocks⁴ elements, the C++ layout and
challenge reader. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interpQROM (program.domainField d))
  | ⟨0, _⟩ => ⟨32, Codec.FieldBytes.goldilocksExt4, CReader.goldilocksExt4⟩
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `A`'s size bounds: `32`-byte elements, arrays of at most `1024`, reads of at most
`600` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 32 1024 600 := by decide +kernel

/-- **The numbers of the domain** (`RealizedProgram.ForkNumbers`): the codec `cod`, arrays of at most
`1024` elements, challenge reads of at most `600` elements. -/
def numbers : RealizedProgram.ForkNumbers ready where
  cod := cod
  Mx _ := 1024
  Lmax _ := 600
  ok := domain_cases fitsOkA

variable {G : Signer 32} (C : Compiled)

/-! ## The multi-circuit IOP with forked domains -/

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

variable (G) in
/-- **`Falcon512.Ring.Carrier.QROMParams` as a multi-circuit IOP with forked domains at the ring
statement**: the generic per-field domain proofs (`RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase at the frontend's round-by-round knowledge soundness (`source_rbr_knowledge_soundness`), the statement
read as its program statement and checked (`RealizedProgram.ProofSystem.IOP.comapWith stmtOf ringOk`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP (Ring.RStmt G)
    (program.Valuation interpQROM → CoreWit) ringStmtRel :=
  (proofSystem C.src).fieldIopWith ready (forkLowering C) Ring.stmtOf Ring.ringOk

variable (G) in
/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comapWith`). -/
noncomputable abbrev forkIopSound : (forkIop G C).Sound :=
  (((proofSystem C.src).fieldBranches ready).soundIOPSound ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness sourceError_final).comapWith Ring.stmtOf Ring.ringOk

variable (G) in
/-! ## The transcript -/

/-- **The branch name**: the domain's field name (`DomainProfile::field_name`, `Goldilocks^4`). -/
def branchName : List Byte := asciiBytes "Goldilocks^4"

variable (G) in
/-- **The C++ series–parallel transcript of `Falcon512.Ring.Carrier.QROMParams`**
(`RealizedProgram.ProofSystem.fieldForkTranscriptWith`): the label, `48`-byte digests (SHA-384), the ring statement's
writes (`Native.stmtCodecN` at `64` keys), the branch name, the phase's codecs and
readers, and the domain's commit, branch, join and column codecs and readers at `numbers`. No point
is granted extra stream bytes. -/
def forkTranscript : ProofSystemTranscript (forkIop G C) :=
  (proofSystem C.src).fieldForkTranscriptWith ready (forkLowering C) Ring.stmtOf numbers.cod
    (numbers.fits C.enforce)
    Ring.ringOk label 48 (Native.stmtCodecN G 64) (fun _ => branchName)
    (program.appWrites fieldBytes msgB_le)
    (program.appReaders samplerReaders (fun _ => chalLoadMax) chalLoad_le)

/-! ## The facts the setting is built from -/

variable (G) in
/-- **The facts the setting is built from**: the label, the digest length, the ring statement's
writes, the branch name and the figures of `numbers` (`RealizedProgram.ProofSystem.fieldForkTranscriptWith_bounds`). -/
theorem forkTranscript_bounds : (forkTranscript G C).Bounds :=
  (proofSystem C.src).fieldForkTranscriptWith_bounds (forkLowering C) Ring.stmtOf numbers C.enforce
    Ring.ringOk (fun x => (Native.length_ser_stmtCodecN_le x).trans (by norm_num))
    (Nat.le_of_ble_eq_true rfl) (by norm_num) (by norm_num)
    (fun _ => (by decide : branchName.length ≤ 2 ^ 10))
    (by decide +kernel)

/-! ## The loads -/

variable (G) in
/-- **Every round's load satisfies `good`** when every load within domain `A`'s bound
`⟨4 · 600, 8⟩` and every load within the phase's `⟨2 · 6, 16⟩` does: the commit rounds', the
branches' and the join part's are within domain `A`'s load (`ForkNumbers.forkLoad_fits`). -/
theorem forkLoads {good : Load → Prop} (hA : ∀ L, L ≤ ⟨4 * 600, 8⟩ → good L)
    (hP : ∀ L, L ≤ ⟨2 * 6, 16⟩ → good L) :
    ∀ j, ((forkTranscript G C).readers j).AllLoads good := by
  have hgood : ∀ d L, L ≤ RealizedProgram.forkLoad (proofSystem C.src).src (ready d) (numbers.cod d).rd
      (numbers.fits C.enforce d).Lmax → good L :=
    domain_cases (fun L hL => hA L (hL.trans (by
      rw [numbers.forkLoad_fits, Load.le_iff]
      exact ⟨by decide +kernel, by decide +kernel⟩)))
  have happ : (forkTranscript G C).appReaders.AllLoads good := by
    refine program.appReaders_allLoads samplerReaders (fun _ => chalLoadMax) chalLoad_le
      fun k => hP _ ?_
    have hk := RealizedProgram.length_chalList_le (ir := program) k
    rw [challenges_length] at hk
    simp only [chalLoadMax, Load.nsmul, Load.le_iff]
    omega
  exact (proofSystem C.src).fieldForkLoadsWith ready (forkLowering C) Ring.stmtOf numbers.cod (numbers.fits C.enforce) hgood happ

/-- **Domain `A`'s loads pass the Chernoff test `2^-3700`** on `48 + fsExtraBytes`-byte streams
(`passesChernoff_of_nat_at`; the first term is `2^-3708.0`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨4 * 600, 8⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 3700) (48 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 3700 (N := 48 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **The phase's loads pass the Chernoff test `2^-3700`** (the first term is `2^-4617.8`). -/
theorem good_phase_at {L : Load} (h : L ≤ ⟨2 * 6, 16⟩) :
    PassesChernoff (65 / 64) ((1 / 2) ^ 3700) (48 + fsExtraBytes) L :=
  (passesChernoff_of_nat_at 3700 (N := 48 + fsExtraBytes) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-! ## The round errors -/

/-- **Domain `A`'s round charges are at most `errorMax / 2^260`**
(`FieldRoundsLe.of_num`): the tableau's commit, test and column bounds, the batches', GKR's and
the combinations' numerators over the field's size (decided). -/
theorem roundsA_le :
    program.FieldRoundsLe (ready domainA) ((errorMax : ℝ≥0) / 2 ^ 260) :=
  .of_num (ready domainA) (by convert goldilocksExt4_card <;> rfl)
    (Tableau.gold4K512Commit_le.trans (le_errorMax (by norm_num)))
    (Tableau.gold4K512Test_le.trans (le_errorMax (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact Tableau.gold4K512Column_le.trans (le_errorMax (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

variable (G) in
/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^260`**
(`RealizedProgram.ProofSystem.fieldForkErrorWith_le`): the domain's round charges (`roundsA_le`) and the phase's
(`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop G C).P (forkIop G C).term) :
    (forkIopSound G C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  (proofSystem C.src).fieldForkErrorWith_le ready Ring.stmtOf C.enforce source_rbr_knowledge_soundness sourceError_final
    (domain_cases roundsA_le) (fun _ => phaseError_le C _) c

variable (G) in
/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^260`. -/
theorem maxRoundError_le : maxError (forkIopSound G C).error ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  maxError_le_iff.2 (forkError_le G C)

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
