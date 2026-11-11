-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Ring.Native.QROMParams.SourceRoleSemantics
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHoweCerts.Generated.Falcon512.Ring.Native.QROMParams.Certified
public import GordieHoweCerts.Applications.Falcon512.Ring.Native.QROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Ring.Native.QROMParams` under spBCS

The native Falcon ring at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`), at every signer `G`: the record `mergeConfig G` (the IOP with
forked domains `forkIop G`, its transcript `forkTranscript G`, `48`-byte Fiat–Shamir salts, the ring
signature relation `FalconRing.ringRel64 G` with the witness read at the statement's program
statement and the signature encoded with the statement's salt, the honest prover, the honest strategy
`honestStrategy G`, and the figures), its facts `mergeFacts G` (with granted points: `GrantedFacts`), and the instances of the
templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeQROM` and `GordieHowe.Configuration.AdaptiveCompleteness`, each abstracted over `G`. The extractor is
`extractor`.

The configuration is `GordieHowe.Configuration.ofCertifiedWith` at the generated certified data
(`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFrontWith`).

The figures: at most `1038` rounds, every round's load within `2^-4260`, a tree of at most
`3258` leaves, `127` queried leaves, `3730` verifier queries
(`2 · 1038 + 3 + 127 · 13`), round errors at most `12734825 / 2^260`, `1042` digests per input
(`max 2 (1038 · 1) + 3 + 1`), the quantum query cap `2^100` and the classical query cap `2^64`, `3258` positions and
`48`-byte digests.

Domain `A`'s Ligero tableau (`RealizedProgram.Export.Plan.LigeroShapesValid`):
`(rate, t, block_enc) = (12, 127, 3799)` and `k = 271`, so `w = k − t = 144`; the `80 + 100 = 180`
subfield masks of its tree `F_q <4 F_q^4 <5 F_q^20` take two prefix rows (`⌈180 / w⌉`,
`tree_zk.h`'s `prefix_padded`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the native Falcon rings'
execution of the source program (`GordieHowe.Falcon512.Ring.sourceExecution`: the honest values of a ring statement and
a witness of the ring relation), with no completeness event (`δ = 0`), on the pairs of the ring
relation (`GordieHowe.Falcon512.Ring.RingIn`), at their statements; the realization's facts come from the
checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHoweCerts/Applications/Falcon512/Ring/Native/QROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.Configuration
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Generated.Falcon512.Ring.Native.QROMParams (interp certified)
open Generated.Falcon512.Ring.Native.QROMParams (conditions)
open Native (CoreWit scheme)
open Ring (RingIn relH)
open scoped NNReal ENNReal

/-! ## The frontend -/

/-- **The source program's execution of `Falcon512.Ring.Native.QROMParams`** at ready data of its honest strategy. -/
noncomputable def sourceExec {G : Signer 32} (R : certified.Ready) :
    program.SourceExecution interp (relH G program interp) :=
  let E := Ring.sourceExecution program interp _ conditions.model.registered conditions.model.lawful
    R.facts.committed R.facts.boundNoCopy R.roles
    R.oneNodes conditions.model.bitNodes
      (Generated.Falcon512.Ring.Native.QROMParams.conditions.noFieldForm rfl)
  let val := fun y : Ring.RingIn G =>
    (⟨Ring.specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      y.normIn.nA, y.normIn.nSq, y.normIn.nCc, y.normIn.nNd,
      y.normIn.nNc, y.normIn.nD, y.normIn.nDc, nativeQuotN y.normIn⟩ : Native.SourceValues (interp 0).K).valuation
        (program := program) Generated.Falcon512.Ring.Native.QROMParams.SourceRoles.classifier
  E.withValues val
    R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x y _ c => RealizedProgram.agreeOnSourceVals_execEnv_of_values x _ _ (E.late y c) c
      fun _v hs _j hc => (role_source_coordinates y hs hc R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => RealizedProgram.packFreeAt_of_noGamma R.roles.noGamma _)

/-- **The execution has no completeness event.** -/
theorem sourceExec_δ {G : Signer 32} (R : certified.Ready) :
    ∑ k, (sourceExec (G := G) R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Ring.sourceExecution_δ (I := interp)]
  simp

/-- **The ring statement's writes have at most `2^20` bytes** (`Native.length_ser_stmtCodecN_le`). -/
theorem stmtCodec_ser_le {G : Signer 32} (x : Ring.RStmt G) :
    ((Native.stmtCodecN G 64).ser x).length ≤ 2 ^ 20 :=
  (Native.length_ser_stmtCodecN_le x).trans (by norm_num)

/-- The label has at most `2^10` bytes. -/
theorem label_le : Native.label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `Falcon512.Ring.Native.QROMParams`** at the signer `G` (`Configuration.FrontendWith`): the ring
statements (`Ring.RStmt G`, `Native.stmtCodecN G 64`) read as their program statements
(`Ring.stmtOf`) and checked (`Ring.ringOk`), the ring relation (`Ring.ringRel64 G`) at the
extracted signature with the statement's salt, the honest inputs (`RingIn G` at their ring
statements) with the execution `sourceExec`, and the label `Native.label`. -/
noncomputable def frontend (G : Signer 32) :
    Configuration.FrontendWith certified source (Ring.RStmt G) (RingWit (scheme G)) (RingIn G) where
  codec := Native.stmtCodecN G 64
  stmtOf := Ring.stmtOf
  rel := Ring.ringRel64 G
  witnessMap x w := (w (Ring.stmtOf x)).withSalt (G := G) x.pub
  relH := relH G program interp
  exec := sourceExec
  stmtOfHonest y := y.x
  label := Native.label
  ok := Ring.ringOk

/-- **The facts of `frontend`**: the ring statement's writes (`stmtCodec_ser_le`), the label
(`label_le`), the witness map (`mem_ringRel64`), the execution (`sourceExec_δ`) and the honest
inputs' statements (`RingIn.ringOk_x`). -/
theorem frontendFacts (G : Signer 32) : (frontend G).Facts :=
  ⟨stmtCodec_ser_le, label_le, fun _ _ h => mem_ringRel64 h, sourceExec_δ,
    fun y => ⟨y.ringOk_x, rfl⟩⟩

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedHonest] (G : Signer 32) =>
    certified source (frontend G).toFrontend

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedFrontWith] folding [ringStmtRel]
  {G : Signer 32} => certified source (frontend G)

/-! ## The configuration -/

/-- **`Falcon512.Ring.Native.QROMParams` as a configuration under spBCS** at the signer `G` (module docstring,
`Configuration.ofCertifiedWith`): the QROM parameter set `ParamSet.qrom` (`48`-byte salts and the quantum query cap `2 ^ 100`). -/
noncomputable def configuration (G : Signer 32) : Configuration :=
  .ofCertifiedWith certified source (frontend G) .qrom

/-- **The facts of `configuration G`** (`Configuration.ofCertifiedWith_grantedFacts`): the frontend's
(`frontendFacts`). -/
theorem configurationFacts (G : Signer 32) : (configuration G).GrantedFacts :=
  Configuration.ofCertifiedWith_grantedFacts certified source (frontendFacts G) (Nat.le_of_ble_eq_true rfl)

instantiate_config GordieHowe.Falcon512.Ring.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  folding [ringStmtRel] {G : Signer 32} => (configuration G) (configurationFacts G) at proofSystem

end GordieHowe.Falcon512.Ring.Native.QROMParams
