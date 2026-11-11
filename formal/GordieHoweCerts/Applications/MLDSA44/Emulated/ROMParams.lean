-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Facts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Emulated.ROMParams` under spBCS

The emulated ML-DSA-44 proof of possession at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `32`-byte Fiat–Shamir salts, the ML-DSA-44
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM`,
`GordieHowe.Configuration.AdaptiveCompleteness` and `GordieHowe.Configuration.PaperRelation`.

The configuration is `GordieHowe.Configuration.ofCertified` at the generated certified data
(`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFront`).

The figures: at most `2333` rounds, every round's load within `2^-2780`, trees of at most `3392`
leaves, `159` queried leaves, `6737` verifier queries (`2 · 2333 + 4 + 159 · 13`), round errors at
most `63455233 / 2^140`, `4669` digests per input (`2 · 2333 + 2 + 1`), the quantum query cap `2^40` and the classical query cap `2^64`, `5952` positions (`2560 + 3392`) and `32`-byte digests.

The realization step's derivations (`RealizedProgram.Derivable`) are checked at the declared
statement bounds (`RealizedProgram.declaredRanges`): `key.a`, value `56`, below `q = 8380417`, and
`key.t1`, value `57`, below `2^10`, which every key's statement satisfies (`stmtBounded_stmtOf`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`GordieHowe.MLDSA44.Emulated.sourceExecution`), with no completeness event (`δ = 0`), on the honest
inputs `GordieHowe.MLDSA44.HonestInput` (a valid ML-DSA-44 honest input with a message of at most `32`
bytes, at its key); the realization's facts and the honest roles come from the generated
checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHoweCerts/Applications/MLDSA44/Emulated/ROMParams/Certified.lean`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open Generated.MLDSA44.Emulated.ROMParams (interp certified conditions)
open MLDSA44 (HonestInput)
open scoped NNReal ENNReal

/-! ## The frontend -/

/-- **The honest relation of `MLDSA44.Emulated.ROMParams`**: the statement is the input's key's. -/
abbrev relH : Set (program.Valuation interp × HonestInput) :=
  Emulated.relH program RealizedProgram.gold2 RealizedProgram.gf128

/-- **The source program's execution of `MLDSA44.Emulated.ROMParams`** at ready data of its honest strategy. -/
noncomputable def sourceExec (R : certified.Ready) :
    program.SourceExecution interp relH :=
  Emulated.sourceExecution program RealizedProgram.gold2 RealizedProgram.gf128 R.facts.committed
    R.facts.boundNoCopy R.roles R.oneNodes
    conditions.model.bitNodes (conditions.noFieldForm rfl)

/-- The execution has no completeness event. -/
theorem sourceExec_δ (R : certified.Ready) : ∑ k, (sourceExec R).δ k = 0 := by
  rw [sourceExec, Emulated.sourceExecution_δ]
  simp

/-- **The statement's writes have at most `2^20` bytes.** -/
theorem stmtCodec_ser_le (x : KeyStmt) : (keyStmtCodec.ser x).length ≤ 2 ^ 20 := by
  change ((MLDSA44.PoP.StatementWrites.keyContext 0).pre x.1).length ≤ _
  rw [MLDSA44.PoP.StatementWrites.keyContext_pre_length]
  norm_num

/-- The label has at most `2^10` bytes. -/
theorem label_le : label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `MLDSA44.Emulated.ROMParams`** (`Configuration.Frontend`): the statements `KeyStmt` with the codec
`keyStmtCodec`, read as their statement values (`stmtOf`), the relation `keyWitRel`, the honest
inputs `HonestInput` at `relH` with the execution `sourceExec`, and the label `label`. -/
noncomputable def frontend :
    Configuration.Frontend certified source KeyStmt MLDSA44.VarWitness HonestInput where
  codec := keyStmtCodec
  stmtOf := stmtOf
  rel := keyWitRel
  witnessMap s w := w (stmtOf s)
  relH := relH
  exec := sourceExec
  stmtOfHonest := keyStmtOf
  label := label

/-- **The facts of `frontend`**: the statement's writes (`stmtCodec_ser_le`), the label
(`label_le`), the witness map, the execution (`sourceExec_δ`) and the honest inputs' statements. -/
theorem frontendFacts : frontend.Facts :=
  ⟨stmtCodec_ser_le, label_le, (fun _ _ h => mem_keyWitRel h), sourceExec_δ,
    fun y => stmtOf_eq (keyStmtOf y)⟩

instantiate_config GordieHowe.MLDSA44.Emulated.ROMParams
  from [GordieHowe.Configuration.CertifiedHonest, GordieHowe.Configuration.CertifiedFront]
  folding [keyRel] certified source frontend

/-! ## The configuration -/

/-- **`MLDSA44.Emulated.ROMParams` as a configuration under spBCS** (module docstring,
`Configuration.ofCertified`): the ROM parameter set `ParamSet.rom` (`32`-byte salts and the quantum query cap `2 ^ 40`). -/
noncomputable def configuration : Configuration :=
  .ofCertified certified source frontend .rom

/-- **The facts of `configuration`** (`Configuration.ofCertified_facts`): the frontend's
(`frontendFacts`) and the generated loads' check (`GordieHowe.RuntimeInputs.FiguresFacts.loads`). -/
theorem configurationFacts : configuration.Facts :=
  Configuration.ofCertified_facts certified source frontendFacts (Nat.le_of_ble_eq_true rfl)
    (conditions.fullFacts.figures.loads rfl)

/-- **The honest inputs of the paper's relation** (`Configuration.HonestOf` at `keyWitRel`, the
paper's relation `MLDSA44.PoP.relUpTo 32` at the key): every pair has the honest input
`MLDSA44.HonestInput.ofRel` at its statement; no pair of the relation is excluded. -/
def honestOfRel : configuration.HonestOf where
  rel := keyWitRel
  rel_subset _ h := h
  honestOf x w hp := MLDSA44.HonestInput.ofRel x.1 w hp
  stmtOfHonest_honestOf _ _ _ := rfl

instantiate_config GordieHowe.MLDSA44.Emulated.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] folding [keyRel] configuration configurationFacts
    honestOfRel at proofSystem

/-! ## The printed instances

The instances the paper prints at the ROM parameters (`tab:eval-params`, `app:formal`) are headlines:
the model-free statements, the ROM statements, the source program's round-by-round knowledge
soundness and the largest round error. The other instances restate their templates at this
configuration and are not tagged. -/

attribute [headline]
  completeness
  completeness_honest
  completeness_of_rel
  honest_input_of_rel
  unconditional_witness_indistinguishability
  completeness_adaptive_rom
  knowledge_soundness_rom_at
  soundness_rom_at
  everlasting_zero_knowledge_rom
  everlasting_zero_knowledge_honest_rom
  weak_online_simulation_extractability_rom
  weak_online_simulation_extractability_rom_at_figures
  source_rbr_knowledge_soundness
  maxRoundError_le

end GordieHowe.MLDSA44.Emulated.ROMParams
