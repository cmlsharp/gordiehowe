-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.Transcript.GrantedLoads
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `Falcon512.Ring.Native.QROMParams` with forked domains

The native Falcon ring at the QROM parameters as a multi-circuit IOP with forked domains on the generic per-field
domain proofs (`proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`): domain `A` forked into its batch's branch and
GKR's, with the proof system's application phase, at the frontend's round-by-round knowledge soundness
(`forkIop`, the ring statement read and checked, `GordieHowe.RealizedProgram.ProofSystem.IOP.comapWith`). Its compiled argument is
the compiler's with merges (`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams.lean`).

* **The transcript** (`forkTranscript`): the label, `32`-byte digests, the ring statement's writes,
  the branch name, the phase's codecs and readers, and the domain's codecs and readers at its
  field's codec (`cod`) and size bounds (`numbers`) (`GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscriptWith`).
* **The facts the setting is built from** (`forkTranscript_bounds`): the rounds of the term are at
  most `1038` (`forkFigures`, in the configuration file).
* **The loads** (`forkLoadsGranted`, `good_A_at`, `good_phase_at`, `good_stage_at`): every round's
  load passing the Chernoff test `2^-4260` at its own stream length, the inner combination at its
  grant.
* **The round errors** (`forkError_le`): every round within `errorMax / 2^260`
  (`GordieHowe.RealizedProgram.ProofSystem.fieldForkErrorWith_le`).
* **The queries and the leaves** (`forkFigures`, in the configuration file): at most `127` opened
  columns, a tree of `3258` leaves.
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
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

/-- **The codec of the domain's field**: `35`-byte `F_q^20` elements, the C++ layout and challenge
reader. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interpQROM (program.domainField d))
  | ⟨0, _⟩ => ⟨35, Codec.FieldBytes.falconNative20, CReader.falconNative20⟩
  | ⟨_ + 1, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `A`'s size bounds: `35`-byte elements, arrays of at most `1024`, reads of at most
`1250` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 35 1024 1250 := by decide +kernel

/-- **The numbers of the domain** (`RealizedProgram.ForkNumbers`): the codec `cod`, arrays of at most
`1024` elements, challenge reads of at most `1250` elements. -/
def numbers : RealizedProgram.ForkNumbers ready where
  cod := cod
  Mx _ := 1024
  Lmax _ := 1250
  ok := domain_cases fitsOkA
  grants _ := { stage := fun i => if i = 0 then aGrants.stage else 0, linear := aGrants.linear }

/-- Domain `A`'s reads other than the inner combination have at most `200` elements at `c.A`'s
`14` layers. -/
theorem restNumbersA :
    RealizedProgram.ForkRestNumbers (ready domainA) (program.padBound _) (program.circL _) 200 := by
  decide +kernel

/-- Domain `A`'s inner combination combines `1138` claims. -/
theorem claimCountA : program.claimCount (d := (domainA : ℕ)) (Pk := (ready domainA).Pk) = 1138 := by
  decide +kernel

variable {G : Signer 32} (C : Compiled)

/-- Domain `A`'s reads other than the inner combination (`restNumbersA`). -/
theorem restA : RealizedProgram.ForkRestSizesLe (proofSystem C.src).src (ready domainA) 200 :=
  RealizedProgram.forkRestSizesLe_ofOk C.enforce restNumbersA

/-! ## The multi-circuit IOP with forked domains -/

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

variable (G) in
/-- **`Falcon512.Ring.Native.QROMParams` as a multi-circuit IOP with forked domains at the ring
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

/-- **The branch name**: the domain's field name (`DomainProfile::field_name`, `F_q^20`). -/
def branchName : List Byte := asciiBytes "F_q^20"

variable (G) in
/-- **The C++ series–parallel transcript of `Falcon512.Ring.Native.QROMParams`**
(`RealizedProgram.ProofSystem.fieldForkTranscriptWith`): the label, `48`-byte digests (SHA-384), the ring statement's
writes, the branch name, the phase's codecs (`RealizedProgram.appWrites` at `fieldBytes`) and readers
(`RealizedProgram.appReaders` at `samplerReaders`), the domain's at `numbers`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop G C) :=
  (proofSystem C.src).fieldForkTranscriptWith ready (forkLowering C) Ring.stmtOf numbers.cod
    (numbers.fits C.enforce)
    Ring.ringOk Native.label 48 (Native.stmtCodecN G 64)
    (fun _ => branchName) (program.appWrites fieldBytes msgB_le)
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

/-- Domain `A`'s reads other than the inner combination are within `⟨20 · 200, 2⟩`: `200` draws of
`F_q^20` and `127` column indices of `2` bytes. -/
theorem forkRestLoadA_le :
    RealizedProgram.forkLoad (proofSystem C.src).src (ready domainA) (cod domainA).rd 200 ≤ ⟨20 * 200, 2⟩ := by
  have hN : (program.fieldFork (proofSystem C.src).src (ready domainA)).join.N = 3258 := rfl
  have ht : (program.fieldFork (proofSystem C.src).src (ready domainA)).join.cp.t = 127 := rfl
  refine RealizedProgram.forkLoad_le (proofSystem C.src).src (ready domainA) _ ?_ ?_ ?_
  · show Load.nsmul 200 CReader.falconNative20.load ≤ ⟨20 * 200, 2⟩
    rw [CReader.falconNative20_load]
    simp only [Load.nsmul, Load.le_iff]
    omega
  · rw [ht]
    norm_num
  · rw [← Rejection.lt_pow_iff_byteLen_le, hN]
    norm_num

/-- The Chernoff test `2^-4260` at a round's own stream length, `48 + fsExtraBytes` plus its
grant. -/
abbrev GoodAtE (g : ℕ) (L : Load) : Prop :=
  PassesChernoff (65 / 64) ((1 / 2) ^ 4260) (48 + fsExtraBytes + g) L

/-- Larger grants keep the test. -/
theorem goodAtE_mono (g : ℕ) (L : Load) (h : GoodAtE 0 L) : GoodAtE g L :=
  h.anti (by norm_num) (by omega)

/-- **Domain `A`'s rounds other than the inner combination pass `2^-4260`** on the default stream
(the first term is `2^-4264`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨20 * 200, 2⟩) : GoodAtE 0 L :=
  (passesChernoff_of_nat_at 4260 (N := 48 + fsExtraBytes + 0) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **The phase's loads pass `2^-4260`** (the first term is `2^-4620`). -/
theorem good_phase_at {L : Load} (h : L ≤ ⟨2 * 22, 4⟩) : GoodAtE 0 L :=
  (passesChernoff_of_nat_at 4260 (N := 48 + fsExtraBytes + 0) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `A`'s inner combination passes `2^-4260`** on its stream with the granted `161560`
bytes (the first term is `2^-6168`). -/
theorem good_stage_at : GoodAtE 161560 ⟨20 * 1138, 2⟩ :=
  passesChernoff_of_nat_at 4260 (N := 48 + fsExtraBytes + 161560) (by norm_num) (by decide +kernel)
    (by decide +kernel)

variable (G) in
/-- **Every round's load passes the Chernoff test `2^-4260` at its own stream length**
(`RealizedProgram.ProofSystem.fieldForkLoadsGrantedWith`): every round within domain `A`'s rest load (`good_A_at`) or
the phase's (`good_phase_at`) on the default stream, the inner combination of `1138` claims on its
stream with its grant of `161560` bytes (`good_stage_at`). -/
theorem forkLoadsGranted : ∀ j, ((forkTranscript G C).readers j).AllGranted GoodAtE := by
  refine (proofSystem C.src).fieldForkLoadsGrantedWith ready (forkLowering C) Ring.stmtOf numbers.cod
    (numbers.fits C.enforce) goodAtE_mono (Lr := fun _ => 200) (domain_cases (restA C))
    (domain_cases (fun L hL => good_A_at (hL.trans (forkRestLoadA_le C)))) (domain_cases ?_) ?_
  · intro n hn
    have hg : ((CReader.pi n (cod domainA).rd).extend
        ((numbers.fits C.enforce domainA).grants.stage 0)).grant = 161560 := by
      have h0 : CReader.falconNative20.grant = 0 := rfl
      have hs : (numbers.fits C.enforce domainA).grants.stage 0 = 161560 := rfl
      show ((CReader.pi _ CReader.falconNative20).extend _).grant = _
      rw [CReader.extend_grant, CReader.pi_grant, h0, Nat.mul_zero, Nat.zero_add, hs]
    have key : ∀ g, g = 161560 → n ≤ 1138 →
        GoodAtE g (Load.nsmul n CReader.falconNative20.load) := by
      rintro _ rfl hn'
      refine good_stage_at.of_le (by norm_num) ?_
      rw [CReader.falconNative20_load]
      simp only [Load.nsmul, Load.le_iff]
      omega
    exact key _ hg (claimCountA ▸ hn)
  · refine SpecReaders.AllGranted.of_allLoads goodAtE_mono
      (program.appReaders_allLoads samplerReaders (fun _ => chalLoadMax) chalLoad_le
        fun k => good_phase_at ?_)
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
  .of_num (ready domainA) (by convert falconNativeField20_card <;> rfl)
    (Tableau.fq20K271Commit_le.trans (le_errorMax (by norm_num)))
    (Tableau.fq20K271Test_le.trans (le_errorMax (by norm_num)))
    (by
        rw [if_neg (by decide +kernel)]
        exact Tableau.fq20K271Column_le.trans (le_errorMax (by norm_num)))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

variable (G) in
/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^260`**
(`RealizedProgram.ProofSystem.fieldForkErrorWith_le`): the domain's round charges (`roundsA_le`) and the phase's
(`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop G C).P (forkIop G C).term) :
    (forkIopSound G C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  (proofSystem C.src).fieldForkErrorWith_le ready Ring.stmtOf C.enforce source_rbr_knowledge_soundness
    sourceError_final
    (domain_cases roundsA_le) (fun _ => phaseError_le C _) c

variable (G) in
/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^260`. -/
theorem maxRoundError_le : maxError (forkIopSound G C).error ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  maxError_le_iff.2 (forkError_le G C)

end GordieHowe.Falcon512.Ring.Native.QROMParams
