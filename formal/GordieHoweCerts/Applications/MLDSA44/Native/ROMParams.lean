-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.Facts
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.SourceRoleSemantics
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Native.ROMParams` under spBCS

The native ML-DSA-44 proof of possession at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `32`-byte Fiat–Shamir salts, the ML-DSA-44
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM`,
`GordieHowe.Configuration.AdaptiveCompleteness` and `GordieHowe.Configuration.PaperRelation`.

The configuration is `GordieHowe.Configuration.ofCertified` at the generated certified data
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFront`).

The IOP with forked domains (`forkIop`): the generic per-field domain proofs with the proof
system's application phase, at the frontend's round-by-round knowledge soundness, read at the key's
statement values. Its transcript (`forkTranscript`): the label, the digests, the key-and-context
writes, the branch names, the phases' and the domains' codecs and readers, all but the label and
the statement's writes the generated module's
(`RuntimeInputs.numbers`).

The figures are the program's (`GordieHowe.Generated.MLDSA44.Native.ROMParams.figures`), checked once
in the generated modules (`GordieHowe.ProgramData.FiguresOk`); the quantum query cap is `2^40` and the classical query cap `2^64`.

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`GordieHowe.MLDSA44.Native.sourceExecution`), with no completeness event (`δ = 0`), on the honest
inputs `HonestIn` (a valid ML-DSA-44 honest input with a message of at most `32` bytes, at its
key); the realization's facts and the honest roles come from the generated checks
(`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHoweCerts/Applications/MLDSA44/Native/ROMParams/Certified.lean`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Native.ROMParams.Program (program)
open Generated.MLDSA44.Native.ROMParams (interp certified conditions)
open scoped NNReal ENNReal

/-! ## The frontend -/

open RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The source program's execution of `MLDSA44.Native.ROMParams`** at ready data of its honest
strategy (`MLDSA44.Native.sourceExecution` at the ready data's committed facts and honest roles, the
interpretation's bit nodes and the absence of field-form `mod_q`s,
`GordieHowe.ProgramConditions.noFieldForm`). -/
noncomputable def sourceExec (R : certified.Ready) :
    program.SourceExecution interp (relH program RealizedProgram.fq6 RealizedProgram.gf128) :=
  let E := Native.sourceExecution program RealizedProgram.fq6 RealizedProgram.gf128 R.facts.committed
    R.facts.boundNoCopy R.roles R.oneNodes conditions.model.bitNodes (conditions.noFieldForm rfl)
  let val := fun i : MLDSA44.HonestInput =>
    Native.sourceVal (program := program)
      ({
  z := fun j => if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat
      (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz j h) : Int) : RealizedProgram.fq6.K) else 0
  hint := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq6 i).h (fm j h) else 0
  challenge := fun j => if h : j < 512 then
    (nativeA RealizedProgram.fq6 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0
  w := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq6 i).w (fm j h) else 0
  w1 := fun j => if h : j < 6144 then MLDSA44.NativeAlgebraCircuit.outputBits (nativeA RealizedProgram.fq6 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0
  nonpositive := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq6 i).np (fm j h) else 0
  offset := fun j => if h : j < 1024 then ((offN i (fm j h) : Nat) : RealizedProgram.fq6.K) else 0
  slack := fun j => if h : j < 1024 then ((slN i (fm j h) : Nat) : RealizedProgram.fq6.K) else 0
} : AlgebraSourceValues RealizedProgram.fq6.K)
      (⟨(honestData (K := RealizedProgram.gf128.K) i.y).buf,
  (fun j => ((flagNat i.L j : Nat) : RealizedProgram.gf128.K)),
  packWord (honestData (K := RealizedProgram.gf128.K) i.y).w1,
  packWord (honestData (K := RealizedProgram.gf128.K) i.y).mu,
  (fun p t j => if hp : p < 10 then if ht : t < 24 then
    stateWords HField.packing
      (iterRounds ((honestData (K := RealizedProgram.gf128.K) i.y).states ⟨p, hp⟩) (t + 1)) j
    else 0 else 0)⟩ : HashSourceValues RealizedProgram.gf128.K)
      ({
  selected := jF RealizedProgram.gf128 i
  threshold := packWord (FH := RealizedProgram.gf128) (lowF RealizedProgram.gf128 i)
  readValue := fun n => if h : n < 39 then ((honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).read ⟨n, h⟩).value else 0
  readOrigin := fun n => if h : n < 234 then
    ((honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin ⟨n % 6, by omega⟩ else 0
  encoded := fun n => if h : n < 256 then (honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).cEnc ⟨n, h⟩ else 0
  finalOrigin := fun n => if h : n < 256 then (honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).finalOrigin ⟨n, h⟩ else 0
  unit := fun n => if h : n < 39 then
    MemoryShuffle.unit (samM program RealizedProgram.fq6 RealizedProgram.gf128).Θ ((honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).signs ⟨n, h⟩) else 0
  origin := fun n => if h : n < 39 then
    (samM program RealizedProgram.fq6 RealizedProgram.gf128).originOf ((honestMemW program RealizedProgram.fq6 RealizedProgram.gf128 i).read ⟨n, h⟩).origin else 0
} : SelectionSourceValues RealizedProgram.gf128.K)
      Generated.MLDSA44.Native.ROMParams.SourceRoles.classifier
  E.withValues val R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x y _ c => agreeOnSourceVals_execEnv_of_values x _ _ (E.late y c) c
      fun _v hs _j hc => by
        change (Native.sourceExecution program RealizedProgram.fq6 RealizedProgram.gf128 R.facts.committed
          R.facts.boundNoCopy R.roles R.oneNodes conditions.model.bitNodes
          (conditions.noFieldForm rfl)).val y _v _j = _
        rw [Native.sourceExecution_val]
        exact (SourceRoleSemantics.role_source_coordinates y hs hc
          R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => packFreeAt_of_noGamma R.roles.noGamma _)

/-- The execution has no completeness event. -/
theorem sourceExec_δ (R) : ∑ k, (sourceExec R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Native.sourceExecution_δ]
  simp

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

/-- **The statement's writes have at most `2^20` bytes**: the key-and-context writes
(`MLDSA44.PoP.StatementWrites.keyContext_pre_length`). -/
theorem keyStmtCodec_ser_le (x : KeyStmt) : (keyStmtCodec.ser x).length ≤ 2 ^ 20 := by
  change ((MLDSA44.PoP.StatementWrites.keyContext 0).pre x.1).length ≤ _
  rw [MLDSA44.PoP.StatementWrites.keyContext_pre_length]
  norm_num

/-- The label has at most `2^10` bytes. -/
theorem label_le : label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `MLDSA44.Native.ROMParams`** (`Configuration.Frontend`): the key-and-context
statements (`KeyStmt`, `keyStmtCodec`) read as the key's statement values (`stmtOf`), the paper's
relation at the key (`keyWitRel`) with the witness read at those values, the honest inputs
(`MLDSA44.HonestInput`, at `relH` and their key, `keyStmtOf`) with the execution `sourceExec`,
and the label. -/
noncomputable def frontend :
    Configuration.Frontend certified source KeyStmt MLDSA44.VarWitness MLDSA44.HonestInput where
  codec := keyStmtCodec
  stmtOf := stmtOf
  rel := keyWitRel
  witnessMap s w := w (stmtOf s)
  relH := relH program RealizedProgram.fq6 RealizedProgram.gf128
  exec := sourceExec
  stmtOfHonest := keyStmtOf
  label := label

/-- **The facts of `frontend`**: the statement's writes (`keyStmtCodec_ser_le`), the label
(`label_le`), the witness map (`mem_keyWitRel`), the execution (`sourceExec_δ`) and the honest
inputs' statements (`stmtOf_eq`). -/
theorem frontendFacts : frontend.Facts :=
  ⟨keyStmtCodec_ser_le, label_le, fun _ _ h => mem_keyWitRel h, sourceExec_δ,
    fun y => stmtOf_eq (keyStmtOf y)⟩

instantiate_config GordieHowe.MLDSA44.Native.ROMParams
  from [GordieHowe.Configuration.CertifiedHonest, GordieHowe.Configuration.CertifiedFront]
  folding [keyRel] certified source frontend

/-! ## The configuration -/

/-- **`MLDSA44.Native.ROMParams` as a configuration under spBCS** (module docstring,
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

instantiate_config GordieHowe.MLDSA44.Native.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] folding [keyRel] configuration configurationFacts
    honestOfRel at proofSystem

end GordieHowe.MLDSA44.Native.ROMParams
