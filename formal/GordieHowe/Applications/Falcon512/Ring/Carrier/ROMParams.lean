-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.SourceRoleSemantics
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Certified
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Ring.Carrier.ROMParams` under spBCS

The Falcon ring carrier at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`), at every signer `G`: the record `mergeConfig G` (the IOP with
forked domains `forkIop G`, its transcript `forkTranscript G`, `32`-byte Fiat–Shamir salts, the ring
signature relation `FalconRing.ringRel64 G` with the witness read at the statement's program
statement and the signature encoded with the statement's salt, the honest prover, the honest strategy
`honestStrategy G`, and the figures), its facts `mergeFacts G`, and the instances of the
templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM` and `GordieHowe.Configuration.AdaptiveCompleteness`, each abstracted over `G`. The extractor is
`ringKeyExtractor`.

The configuration is `GordieHowe.Configuration.ofCertifiedWith` at the generated certified data
(`GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFrontWith`).

The figures: at most `955` rounds, every round's load within `2^-4160`, a tree of at most `2560`
leaves, `96` queried leaves, `3160` verifier queries (`2 · 955 + 2 + 96 · 13`), round errors at most
`43660620 / 2^140`, `958` digests per input (`max 2 (955 · 1) + 2 + 1`), the query caps `2^40` (QROM) and
`2^64` (ROM), `2560` positions and `32`-byte digests.

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the carriers' execution
of the source program (`GordieHowe.Falcon512.Ring.carrierSourceExecution`: the honest values of a ring statement and a
witness of the ring relation), with no completeness event (`δ = 0`), on the pairs of the ring
relation (`GordieHowe.Falcon512.Ring.RingIn`), at their statements; the realization's facts come from the
checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring GordieHowe.Configuration
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.ROMParams (interp certified conditions)
open Native (Signer CoreWit scheme)
open Ring (RingIn relH)
open scoped NNReal ENNReal

/-! ## The frontend -/

/-- **The source program's execution through checked source roles** of `Falcon512.Ring.Carrier.ROMParams` at ready data of its honest strategy. -/
noncomputable def sourceExec {G : Signer 32} (R : certified.Ready) :
    program.SourceExecution interp (relH G program interp) :=
  let E := Ring.carrierSourceExecution program interp _ conditions.model.registered conditions.model.lawful
    R.facts.committed R.facts.boundNoCopy R.roles
    R.oneNodes conditions.model.bitNodes
      (Generated.Falcon512.Ring.Carrier.ROMParams.conditions.noFieldForm rfl)
  let val := fun y : Ring.RingIn G =>
    (⟨Ring.specK program y, y.w.idx, y.normIn.nS2, y.normIn.nS1,
      Carrier.quot y.normIn, Carrier.mag1 y.normIn, Carrier.mag2 y.normIn,
      Carrier.squares y.normIn⟩ : Carrier.SourceValues (interp 0).K).valuation
        (program := program) Generated.Falcon512.Ring.Carrier.ROMParams.SourceRoles.classifier
  E.withValues val
    R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x y _ c => RealizedProgram.agreeOnSourceVals_execEnv_of_values x _ _ (E.late y c) c
      fun _v hs _j hc => (role_source_coordinates y hs hc R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => RealizedProgram.packFreeAt_of_noGamma R.roles.noGamma _)

/-- **The execution has no completeness event.** -/
theorem sourceExec_δ {G : Signer 32} (R : certified.Ready) :
    ∑ k, (sourceExec (G := G) R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Ring.carrierSourceExecution_δ (I := interp)]
  simp

/-- **The ring statement's writes have at most `2^20` bytes** (`Native.length_ser_stmtCodecN_le`). -/
theorem stmtCodec_ser_le {G : Signer 32} (x : Ring.RStmt G) :
    ((Native.stmtCodecN G 64).ser x).length ≤ 2 ^ 20 :=
  (Native.length_ser_stmtCodecN_le x).trans (by norm_num)

/-- The label has at most `2^10` bytes. -/
theorem label_le : label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `Falcon512.Ring.Carrier.ROMParams`** at the signer `G` (`Configuration.FrontendWith`): the ring
statements (`Ring.RStmt G`, `Native.stmtCodecN G 64`) read as their program statements
(`Ring.stmtOf`) and checked (`Ring.ringOk`), the ring relation (`Ring.ringRel64 G`) at the
extracted signature with the statement's salt, the honest inputs (`RingIn G` at their ring
statements) with the execution `sourceExec`, and the label `label`. -/
noncomputable def frontend (G : Signer 32) :
    Configuration.FrontendWith certified source (Ring.RStmt G) (RingWit (scheme G)) (RingIn G) where
  codec := Native.stmtCodecN G 64
  stmtOf := Ring.stmtOf
  rel' := Ring.ringRel64 G
  g x w := (w (Ring.stmtOf x)).withSalt (G := G) x.pub
  relH := relH G program interp
  exec := sourceExec
  keyStmtOf y := y.x
  label := label
  ok := Ring.ringOk

/-- **The facts of `frontend`**: the ring statement's writes (`stmtCodec_ser_le`), the label
(`label_le`), the witness map (`mem_ringRel64`), the execution (`sourceExec_δ`) and the honest
inputs' statements (`RingIn.ringOk_x`). -/
theorem frontendFacts (G : Signer 32) : (frontend G).Facts :=
  ⟨stmtCodec_ser_le, label_le, fun _ _ h => mem_ringRel64 h, sourceExec_δ,
    fun y => ⟨y.ringOk_x, rfl⟩⟩

instantiate_config GordieHowe.Falcon512.Ring.Carrier.ROMParams
  from [GordieHowe.Configuration.CertifiedHonest] (G : Signer 32) =>
    certified source (frontend G).toFrontend

instantiate_config GordieHowe.Falcon512.Ring.Carrier.ROMParams
  from [GordieHowe.Configuration.CertifiedFrontWith] folding [ringStmtRel]
  {G : Signer 32} => certified source (frontend G)

/-! ## The configuration -/

/-- **`Falcon512.Ring.Carrier.ROMParams` as a configuration under spBCS** at the signer `G` (module docstring,
`Configuration.ofCertifiedWith`): `32`-byte salts and the query cap `2 ^ 40`. -/
noncomputable def configuration (G : Signer 32) : Configuration :=
  .ofCertifiedWith certified source (frontend G) 32 (2 ^ 40)

/-- **The facts of `configuration G`** (`Configuration.ofCertifiedWith_facts`): the frontend's
(`frontendFacts`) and the generated loads' check (`GordieHowe.RuntimeInputs.FiguresFacts.loads`). -/
theorem configurationFacts (G : Signer 32) : (configuration G).Facts :=
  Configuration.ofCertifiedWith_facts certified source (frontendFacts G) (by norm_num) _
    (conditions.fullFacts.figures.loads rfl)

instantiate_config GordieHowe.Falcon512.Ring.Carrier.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness]
  renaming keyExtractor → ringKeyExtractor
  folding [ringStmtRel] {G : Signer 32} => (configuration G) (configurationFacts G) at proofSystem

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
