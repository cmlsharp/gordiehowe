-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Tableaux
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Facts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Ring.Native.QROMParams` under spBCS

The native ML-DSA-44 ring at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`) at the converted base messages' length `34`
(`GordieHowe.MLDSA44.Ring.convertedMsg`: `0 ‖ 0 ‖ m` for a `32`-byte ring message): the record
`configuration` (the IOP with forked domains `ringIop 34`, its transcript `ringTranscript 34`,
`48`-byte Fiat–Shamir salts, the ring relation `GordieHowe.MLDSA44.Ring.ringRel64 34` with the
witness read at the statement's program statement (`ringWit`), the honest prover, the honest
strategy `honestStrategy 34`, and the figures), its facts `configurationFacts`, and the instances
of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeQROM` and
`GordieHowe.Configuration.AdaptiveCompleteness`. The extractor is `ringKeyExtractor`. The ring
signatures at every message length are in
`GordieHowe/Applications/MLDSA44/Ring/Native/QROMParams/RingScheme.lean`.

The configuration is `GordieHowe.Configuration.ofCertifiedWith` at the generated certified data
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFrontWith`).

The figures: at most `2273` rounds, every round's load within `2^-990`, trees of at most `4069`
leaves, `273` queried leaves, `8099` verifier queries, round errors at most `13358901 / 2^260`,
`4549` digests per input, the query caps `2^100` (QROM) and `2^64` (ROM), `8005` positions and
`48`-byte digests.

* **The honest relation** (`ringHonestRel msgLen relH`): statements that pass the check and whose
  program statement is the strategy's; `mem_ringHonestRel`: an honest input's statement is an
  honest statement.

Circuit enforcement and honest-input acceptance are established by the generated certificates.
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Ring.Native.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.QROMParams (interp ProofSystems certified figures_eq figures
  conditions)
open scoped NNReal ENNReal

/- Generated data: the figures' checks read the generated program. -/
set_option maxRecDepth 8192

/-! ## The frontend -/


/-- **The source program's execution of `MLDSA44.Ring.Native.QROMParams`** at ready data of its honest strategy. -/
noncomputable def sourceExec {msgLen : ℕ} (R : certified.Ready) :
    program.SourceExecution interp (Native.relH (msgLen := msgLen) program RealizedProgram.fq11
      RealizedProgram.gf256) :=
  let E := Native.sourceExecution program RealizedProgram.fq11 RealizedProgram.gf256
    conditions.model.registered conditions.model.lawful
    R.facts.committed R.facts.boundNoCopy R.roles
    R.oneNodes conditions.model.bitNodes
      (Generated.MLDSA44.Ring.Native.QROMParams.conditions.noFieldForm rfl)
  let val := fun y : RingIn msgLen => roleVal program RealizedProgram.fq11 RealizedProgram.gf256 y
        Generated.MLDSA44.Ring.Native.QROMParams.SourceRoles.classifier
  E.withValues val R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x y _ c => RealizedProgram.agreeOnSourceVals_execEnv_of_values x _ _ (E.late y c) c
      fun _v hs _j hc => (role_coordinates y hs hc R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => RealizedProgram.packFreeAt_of_noGamma R.roles.noGamma _)

/-- **The execution has no completeness event.** -/
theorem sourceExec_δ {msgLen : ℕ} (R : certified.Ready) :
    ∑ k, (sourceExec (msgLen := msgLen) R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Native.sourceExecution_δ]
  simp

/-- **The ring statement's writes have at most `2^20` bytes** at message representatives of at
most `2^19` bytes (`length_ser_stmtCodecN_le`). -/
theorem stmtCodec_ser_le {msgLen : ℕ} (hmsg : msgLen ≤ 2 ^ 19) (x : RStmt msgLen) :
    ((stmtCodecN msgLen 64).ser x).length ≤ 2 ^ 20 :=
  (length_ser_stmtCodecN_le x).trans (by omega)

/-- The label has at most `2^10` bytes. -/
theorem labelNative_le : labelNative.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `MLDSA44.Ring.Native.QROMParams`** at `msgLen`-byte message representatives
(`Configuration.FrontendWith`): the ring statements (`RStmt msgLen`, `stmtCodecN msgLen 64`) read
as their program statements (`Native.stmtOf`) and checked (`ringOk`), the ring relation
(`ringRel64`) at the ring witness (`ringWit`), the honest inputs (`RingIn msgLen` at their ring
statements) with the execution `sourceExec`, and the label `labelNative`. -/
noncomputable def frontend (msgLen : ℕ) :
    Configuration.FrontendWith certified source (RStmt msgLen) (GordieHowe.Ring.RingWit (scheme msgLen))
      (RingIn msgLen) where
  codec := stmtCodecN msgLen 64
  stmtOf := Native.stmtOf (program := program) (I := interp)
  rel' := ringRel64 msgLen
  g := ringWit
  relH := Native.relH (msgLen := msgLen) program RealizedProgram.fq11 RealizedProgram.gf256
  exec := sourceExec
  keyStmtOf y := y.x
  label := labelNative
  ok := ringOk

/-- **The facts of `frontend`** at message representatives of at most `2^19` bytes: the ring
statement's writes (`stmtCodec_ser_le`), the label (`labelNative_le`), the witness map
(`ringStmtRel_sound`), the execution (`sourceExec_δ`) and the honest inputs' statements
(`RingIn.ringOk_x`). -/
theorem frontendFacts {msgLen : ℕ} (hmsg : msgLen ≤ 2 ^ 19) : (frontend msgLen).Facts :=
  ⟨stmtCodec_ser_le hmsg, labelNative_le, fun x f h => ringStmtRel_sound x f h.1 h,
    sourceExec_δ, fun y => ⟨y.ringOk_x, rfl⟩⟩

instantiate_config GordieHowe.MLDSA44.Ring.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedHonest] (msgLen : ℕ) => certified source (frontend msgLen).toFrontend

instantiate_config GordieHowe.MLDSA44.Ring.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedFrontWith]
  renaming forkIop → ringIop, forkIopSound → ringIopSound, forkTranscript → ringTranscript
  folding [ringStmtRel] (msgLen : ℕ) => certified source (frontend msgLen)

/-- **The honest strategy's completeness errors are `0`.** -/
theorem honestStrategy_delta {msgLen : ℕ} : ∑ k, (honestStrategy msgLen).δ k = 0 :=
  sourceExec_δ (msgLen := msgLen) completionReady

/-- **An honest input's statement is an honest statement**: it passes the check and its program
statement is the input's. -/
theorem mem_ringHonestRel {msgLen : ℕ} (y : RingIn msgLen) :
    (y.x, y) ∈ ringHonestRel msgLen (Native.relH (msgLen := msgLen) program RealizedProgram.fq11 RealizedProgram.gf256) :=
  ⟨y.ringOk_x, rfl⟩

variable (msgLen : ℕ) (C : ProofSystems)

variable {msgLen} in
/-- **The facts the setting is built from with `48`-byte salts** at message representatives of at
most `2^19` bytes (`Configuration.mergeBoundsWith`). -/
theorem ringMergeBounds (hmsg : msgLen ≤ 2 ^ 19) : (ringTranscript msgLen C).MergeBounds 48 :=
  Configuration.mergeBoundsWith certified source (frontendFacts hmsg) (by norm_num) C

/-- **The figures of `ringIop`** (`RealizedProgram.ProgramFigures.Check.figuresWith`, the generated figures): at
most `2273` rounds, trees of at most `4069` leaves, `273` queried leaves, `8099` verifier queries, `4549`
digests per input and `8005` positions. -/
theorem ringFigures : (ringIop msgLen C).Figures 2273 4069 273 8099 4549 8005 :=
  by simpa only [figures_eq, show certified.figures = figures from rfl] using
    certified.figuresOk.figuresWith (B := C) (Lw := ringLowering C) ringOk

variable {msgLen} in
/-- **The proof format `max 4069 273`**: every tree has at most `4069` leaves and every query phase
opens at most `273` positions (`ringFigures`). -/
theorem ringProofFormat (hmsg : msgLen ≤ 2 ^ 19) :
    (ringTranscript msgLen C).ProofFormat 48 (ringMergeBounds C hmsg) (max 4069 273) :=
  ProofSystemTranscript.formatBounds (ringMergeBounds C hmsg)
    (fun d => ((ringFigures msgLen C).leaves_le d).trans (le_max_left _ _))
    fun ch => ((ringFigures msgLen C).queries_le ch).trans (le_max_right _ _)

/-- The converted base messages' length `2 + 32` is within the setting's `2^19` bytes. -/
theorem msgLen_le : 2 + 32 ≤ 2 ^ 19 := by norm_num

/-! ## The configuration -/

/-- **`MLDSA44.Ring.Native.QROMParams` as a configuration under spBCS** at `34`-byte message representatives
(module docstring, `Configuration.ofCertifiedWith`): `48`-byte salts and the query cap `2 ^ 100`. -/
noncomputable def configuration : Configuration :=
  .ofCertifiedWith certified source (frontend (2 + 32)) 48 (2 ^ 100)

/-- **The facts of `configuration`** (`Configuration.ofCertifiedWith_facts`): the frontend's
(`frontendFacts` at `msgLen_le`) and the generated loads' check
(`GordieHowe.RuntimeInputs.FiguresFacts.loads`). -/
theorem configurationFacts : configuration.Facts :=
  Configuration.ofCertifiedWith_facts certified source (frontendFacts msgLen_le) (by norm_num) _
    (conditions.fullFacts.figures.loads rfl)

instantiate_config GordieHowe.MLDSA44.Ring.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  folding [ringStmtRel] configuration configurationFacts at proofSystem

end GordieHowe.MLDSA44.Ring.Native.QROMParams
