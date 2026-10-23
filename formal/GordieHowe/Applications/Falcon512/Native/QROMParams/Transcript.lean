-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.Falcon512.Native.QROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Native.QROMParams.RoundErrors
public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.Transcript.GrantedLoads
public import GordieHowe.ProofSystem.Program.ForkJoinComap

@[expose] public section

/-!
# GordieHowe: the transcript of `Falcon512.Native.QROMParams` with forked domains

The native Falcon-512 proof of possession at the QROM parameters as a multi-circuit IOP with forked domains on the
generic per-field domain proofs (`proofSystem`, `GordieHowe.RealizedProgram.ProofSystem.fieldBranches`) with the proof system's
application phase, at the frontend's round-by-round knowledge soundness (`forkIop`, read at the
public key's statement values). Its compiled argument is spBCS's
(`GordieHowe/Applications/Falcon512/Native/QROMParams.lean`).

* **The transcript** (`forkTranscript`, `GordieHowe.RealizedProgram.ProofSystem.fieldForkTranscript`): the label, `48`-byte
  digests, the key writes, the branch names (each domain's field name), the phases' codecs and
  readers, and every domain's codecs and readers at its field's codec (`cod`) and size bounds
  (`numbers`).
* **The facts the setting is built from** (`forkTranscript_bounds`): the rounds of the term are at
  most `2315` (`forkFigures`, in the configuration file).
* **The loads** (`forkLoads`, `good_A_at`, `good_H_at`): every round's load within its domain's,
  each passing the Chernoff test `2^-1870` at its own stream length, domain `A`'s
  first combination on its stream granted `377160` bytes.
* **The round errors** (`forkError_le`): every round of the composite on its own is at most
  `errorMax / 2^140` (`GordieHowe.RealizedProgram.ProofSystem.fieldForkError_le`).
* **The queries and the leaves** (`forkFigures`, in the configuration file): at most `128 + 127`
  opened columns, trees of `4069` and `3258` leaves.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.QROMParams.Program (program)
open ROMParams (VarWitness rel stmtOf keyOf_stmtOf proj extractor)
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

/-- **The codecs of the domains' fields**: `16`-byte `GF(2^256)` elements for `H`, `18`-byte
`F_q^20` elements for `A`, the C++ layouts and challenge readers. -/
def cod : ∀ d : Fin program.domains.length,
    RealizedProgram.FieldCodec (interp (program.domainField d))
  | ⟨0, _⟩ => ⟨32, Codec.FieldBytes.gf2_256, CReader.gf2_256⟩
  | ⟨1, _⟩ => ⟨35, Codec.FieldBytes.falconNative20, CReader.falconNative20⟩
  | ⟨_ + 2, h⟩ => absurd h (by rw [domains_length]; omega)

/-- Domain `H`'s size bounds: `32`-byte elements, arrays of at most `1024`, reads of at most
`1250` (decided). -/
theorem fitsOkH : RealizedProgram.FitsOk (ready domainH) 32 1024 1250 := by decide +kernel

/-- Domain `A`'s size bounds: `35`-byte elements, arrays of at most `1024`, reads of at most
`2950` (decided). -/
theorem fitsOkA : RealizedProgram.FitsOk (ready domainA) 35 1024 2950 := by decide +kernel

/-- **The numbers of the domains** (`RealizedProgram.ForkNumbers`): the codecs `cod`, arrays of at most
`1024` elements, challenge reads of at most `1250` elements at `H` and `2950` at `A`, the first
combination of `A` granted `377160` bytes. -/
def numbers : RealizedProgram.ForkNumbers ready where
  cod := cod
  Mx _ := 1024
  Lmax d := if d.1 = 0 then 1250 else 2950
  ok := domain_cases fitsOkH fitsOkA
  grants d := if d.1 = 1 then { stage := fun i => if i = 0 then 377160 else 0 } else {}

variable (C : Compiled)

/-! ## The multi-circuit IOP with forked domains -/

/-- The lowering of the soundness theorem on the generic per-field domain proofs
(`RealizedProgram.ProofSystem.lowering`). -/
abbrev forkLowering :=
  (proofSystem C.src).lowering C.enforce ⟨_, source_rbr_knowledge_soundness, sourceError_final⟩

/-- **`Falcon512.Native.QROMParams` as a multi-circuit IOP with forked domains at the key**: the generic
per-field domain proofs (`RealizedProgram.ProofSystem.fieldIop`) with the proof system's application phase at the
frontend's round-by-round knowledge soundness (`QROMParams.source_rbr_knowledge_soundness`), the statement read as the key's
statement values (`stmtOf`). -/
abbrev forkIop : RealizedProgram.ProofSystem.IOP PublicKey (program.Valuation interp → VarWitness)
    keyRel :=
  (proofSystem C.src).fieldIop ready (forkLowering C) stmtOf

/-- The soundness data of `forkIop` (`RealizedProgram.ProofSystem.FieldBranches.soundIOPSound`, `RealizedProgram.ProofSystem.IOP.Sound.comap`). -/
noncomputable abbrev forkIopSound : (forkIop C).Sound :=
  (((proofSystem C.src).fieldBranches ready).soundIOPSound ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final).comap stmtOf

/-! ## The transcript -/

/-- **The branch names**: each domain's field name (`DomainProfile::field_name`): `GF(2^256)` for
`H`, `F_q^20` for `A`. -/
def branchName (d : Fin program.domains.length) : List Byte :=
  if d.1 = 0 then asciiBytes "GF(2^256)" else asciiBytes "F_q^20"

/-- **The C++ series–parallel transcript of `Falcon512.Native.QROMParams`** (`RealizedProgram.ProofSystem.fieldForkTranscript`): the
label `label`, `48`-byte digests, the key writes (`falconKeyCodec`), every branch named by its
domain's field (`branchName`), the phases' codecs (`RealizedProgram.appWrites` at `fieldBytes`) and readers
(`RealizedProgram.appReaders` at `samplerReaders`), every domain's at `numbers`. -/
abbrev forkTranscript : ProofSystemTranscript (forkIop C) :=
  (proofSystem C.src).fieldForkTranscript ready (forkLowering C) stmtOf numbers.cod
    (numbers.fits C.enforce) label 48
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

/-- Domain `A`'s challenge reads other than the first combination's have at most `200` elements. -/
theorem restNumbersA : RealizedProgram.ForkRestNumbers (ready domainA) (program.padBound _) (program.circL _) 200 := by
  decide +kernel

/-- Domain `H`'s first combination reads `claimCount ≤ 1250` elements. -/
theorem claimCountH_le : program.claimCount (d := (domainH : ℕ)) (Pk := (ready domainH).Pk) ≤ 1250 := by
  decide +kernel

/-- Domain `A`'s first combination reads `2675` elements. -/
theorem claimCountA : program.claimCount (d := (domainA : ℕ)) (Pk := (ready domainA).Pk) = 2675 := by
  decide +kernel

/-- **The bounds of the reads other than the first combination's**: `1250` for `H`, `200` for
`A`. -/
def restLmax : Fin program.domains.length → ℕ
  | ⟨0, _⟩ => 1250
  | ⟨1, _⟩ => 200
  | ⟨_ + 2, _⟩ => 0

/-- **The reads other than the first combination's are within `restLmax`**: `H`'s from its load
sizes, `A`'s from `restNumbersA` at `c.A`'s shape. -/
theorem restSizes : ∀ d, RealizedProgram.ForkRestSizesLe (proofSystem C.src).src (ready d) (restLmax d) :=
  domain_cases (numbers.fits C.enforce domainH).loads.rest
    (RealizedProgram.forkRestSizesLe_ofOk C.enforce restNumbersA)

/-- Domain `H`'s reads are within `⟨1250, 32⟩`: `1250` draws of `GF(2^256)` and `128` column
indices of `2` bytes. -/
theorem forkLoadH_le :
    RealizedProgram.forkLoad (proofSystem C.src).src (ready domainH) (cod domainH).rd 1250 ≤ ⟨1250, 32⟩ := by
  have hN : (program.fieldFork (proofSystem C.src).src (ready domainH)).join.N = 4069 := rfl
  have ht : (program.fieldFork (proofSystem C.src).src (ready domainH)).join.cp.t = 128 := rfl
  refine RealizedProgram.forkLoad_le (proofSystem C.src).src (ready domainH) _ ?_ ?_ ?_
  · show Load.nsmul 1250 CReader.gf2_256.load ≤ ⟨1250, 32⟩
    rw [CReader.gf2_256_load]
    simp only [Load.nsmul, Load.le_iff]
    omega
  · rw [ht]
    norm_num
  · rw [← Rejection.lt_pow_iff_byteLen_le, hN]
    norm_num

/-- Domain `A`'s reads other than the first combination's are within `⟨20 · 200, 2⟩`: `200` draws
of `F_q^20` and `127` column indices of `2` bytes. -/
theorem forkLoadA_le :
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

/-- The Chernoff test `2^-1870` at a round's own stream length, `48 + fsExtraBytes` plus its
grant. -/
abbrev GoodAtE (g : ℕ) (L : Load) : Prop :=
  PassesChernoff (65 / 64) ((1 / 2) ^ 1870) (48 + fsExtraBytes + g) L

/-- Larger grants keep the test. -/
theorem goodAtE_mono (g : ℕ) (L : Load) (h : GoodAtE 0 L) : GoodAtE g L :=
  h.anti (by norm_num) (by omega)

/-- **Domain `H`'s loads and the phases' pass `2^-1870`** on the default stream (the first term is
`2^-1879`). -/
theorem good_H_at {L : Load} (h : L ≤ ⟨1250, 32⟩) : GoodAtE 0 L :=
  (passesChernoff_of_nat_at 1870 (N := 48 + fsExtraBytes + 0) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `A`'s rounds other than the first combination pass `2^-1870`** on the default stream
(the first term is `2^-4264`). -/
theorem good_A_at {L : Load} (h : L ≤ ⟨20 * 200, 2⟩) : GoodAtE 0 L :=
  (passesChernoff_of_nat_at 1870 (N := 48 + fsExtraBytes + 0) (by norm_num) (by decide +kernel)
    (by decide +kernel)).of_le (by norm_num) h

/-- **Domain `A`'s first combination passes `2^-1870`** on its stream with the granted `377160`
bytes (the first term is `2^-8200`). -/
theorem good_stage_at : GoodAtE 377160 ⟨20 * 2675, 2⟩ :=
  passesChernoff_of_nat_at 1870 (N := 48 + fsExtraBytes + 377160) (by norm_num) (by decide +kernel)
    (by decide +kernel)

/-- **Every round's load passes the Chernoff test `2^-1870` at its own stream length**
(`RealizedProgram.ProofSystem.fieldForkLoadsGranted`): the reads other than the first combinations' within `H`'s load
(`good_H_at`) or `A`'s (`good_A_at`), `H`'s first combination within its load, `A`'s on its stream
with its grant (`good_stage_at`), the phases' on the default stream. -/
theorem forkLoadsGranted : ∀ j, ((forkTranscript C).readers j).AllGranted GoodAtE := by
  refine (proofSystem C.src).fieldForkLoadsGranted ready (forkLowering C) stmtOf numbers.cod (numbers.fits C.enforce)
    goodAtE_mono (restSizes C)
    (domain_cases (fun L hL => good_H_at (hL.trans (forkLoadH_le C)))
      (fun L hL => good_A_at (hL.trans (forkLoadA_le C))))
    (domain_cases (fun n hn => goodAtE_mono _ _ (good_H_at (((RealizedProgram.nsmul_le_forkLoad
        (src := (proofSystem C.src).src) (R := ready domainH) (cod domainH).rd
        (hn.trans claimCountH_le))).trans (forkLoadH_le C))))
      ?_) ?_
  · intro n hn
    have h0 : CReader.falconNative20.grant = 0 := rfl
    show GoodAtE ((CReader.pi _ CReader.falconNative20).extend 377160).grant
      (CReader.falconNative20.load.nsmul _)
    rw [CReader.extend_grant, CReader.pi_grant, h0, Nat.mul_zero, Nat.zero_add,
      CReader.falconNative20_load]
    rw [claimCountA] at hn
    refine good_stage_at.of_le (by norm_num) ?_
    simp only [Load.nsmul, Load.le_iff]
    omega
  · refine SpecReaders.AllGranted.of_allLoads goodAtE_mono
      (program.appReaders_allLoads samplerReaders (fun _ => chalLoadMax) chalLoad_le
        fun k => good_H_at ?_)
    have hk := RealizedProgram.length_chalList_le (ir := program) k
    rw [challenges_length] at hk
    simp only [chalLoadMax, Load.nsmul, Load.le_iff]
    omega

/-! ## The round errors -/

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

/-- **Every round of the series–parallel composite, on its own, is at most `errorMax / 2^260`**
(`RealizedProgram.ProofSystem.fieldForkError_le`): each domain's round charges (`roundsH_le`, `roundsA_le`) and the
phases' (`phaseError_le`). -/
theorem forkError_le (c : ChIdx (forkIop C).P (forkIop C).term) :
    (forkIopSound C).error c ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  (proofSystem C.src).fieldForkError_le ready stmtOf C.enforce source_rbr_knowledge_soundness
    sourceError_final
    (domain_cases roundsH_le roundsA_le) (fun _ => phaseError_le C _) c

/-- **The largest round error of the series–parallel composite** is at most `errorMax / 2^260`. -/
theorem maxRoundError_le : maxError (forkIopSound C).error ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  maxError_le_iff.2 (forkError_le C)

end GordieHowe.Falcon512.Native.QROMParams
