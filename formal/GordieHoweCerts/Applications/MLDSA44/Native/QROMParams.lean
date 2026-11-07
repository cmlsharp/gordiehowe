-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Facts
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.SourceRoleSemantics
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHoweCerts.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Native.QROMParams` under spBCS

The native ML-DSA-44 proof of possession at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `48`-byte Fiat–Shamir salts, the ML-DSA-44
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `Query` and `GordieHowe.Configuration.AdaptiveCompleteness`.

The configuration is `GordieHowe.Configuration.ofCertified` at the generated certified data
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFront`).

The figures: at most `2269` rounds, every round's load within `2^-990`, trees of at most `4069`
leaves, `272` queried leaves, `8078` verifier queries (`2 · 2269 + 4 + 272 · 13`), round errors at
most `13358901 / 2^260`, `4541` digests per input (`2 · 2269 + 2 + 1`), the query caps `2^100`
(QROM) and `2^64` (ROM), `7568` positions (`3499 + 4069`) and `48`-byte digests.

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`GordieHowe.MLDSA44.Native.sourceExecution`, at the facts of the program at the QROM parameters), with no completeness
event (`δ = 0`), on the honest inputs `GordieHowe.MLDSA44.HonestInput` (a valid ML-DSA-44 honest input
with a message of at most `32` bytes, at its key); the realization's facts come from the checks
(`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHoweCerts/Applications/MLDSA44/Native/QROMParams/Certified.lean`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Native.QROMParams.Program (program)
open Generated.MLDSA44.Native.QROMParams (interp certified conditions)
open RealizedProgram (fq11)
open MLDSA44 (HonestInput)
open scoped NNReal ENNReal

/-! ## The frontend -/

open RealizedProgram GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

/-- **The source program's execution of `MLDSA44.Native.QROMParams`** at ready data of its honest strategy. -/
noncomputable def sourceExec (R : certified.Ready) :
    program.SourceExecution interp (Native.relH program fq11 RealizedProgram.gf256) :=
  let E := Native.sourceExecution program RealizedProgram.fq11 RealizedProgram.gf256 R.facts.committed
    R.facts.boundNoCopy R.roles R.oneNodes conditions.model.bitNodes (conditions.noFieldForm rfl)
  let val := fun i : MLDSA44.HonestInput =>
    Native.sourceVal (program := program)
      ({
  z := fun j => if h : j < 1024 then
    ((MLDSA44.NativeAlgebraCircuit.flat
      (MLDSA44.NativeAlgebraCircuit.Honest.zCentered i.y.z) (fmz j h) : Int) : RealizedProgram.fq11.K) else 0
  hint := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq11 i).h (fm j h) else 0
  challenge := fun j => if h : j < 512 then
    (nativeA RealizedProgram.fq11 i).cA ⟨j / 2, by change j / 2 < 256; omega⟩ ⟨j % 2, by omega⟩ else 0
  w := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq11 i).w (fm j h) else 0
  w1 := fun j => if h : j < 6144 then MLDSA44.NativeAlgebraCircuit.outputBits (nativeA RealizedProgram.fq11 i).w1A
    ⟨j / 6, by change j / 6 < 4 * 256; omega⟩ ⟨j % 6, by change j % 6 < 6; omega⟩ else 0
  nonpositive := fun j => if h : j < 1024 then MLDSA44.NativeAlgebraCircuit.flat (nativeA RealizedProgram.fq11 i).np (fm j h) else 0
  offset := fun j => if h : j < 1024 then ((offN i (fm j h) : Nat) : RealizedProgram.fq11.K) else 0
  slack := fun j => if h : j < 1024 then ((slN i (fm j h) : Nat) : RealizedProgram.fq11.K) else 0
} : AlgebraSourceValues RealizedProgram.fq11.K)
      (⟨(honestData (K := RealizedProgram.gf256.K) i.y).buf,
  (fun j => ((flagNat i.L j : Nat) : RealizedProgram.gf256.K)),
  packWord (honestData (K := RealizedProgram.gf256.K) i.y).w1,
  packWord (honestData (K := RealizedProgram.gf256.K) i.y).mu,
  (fun p t j => if hp : p < 10 then if ht : t < 24 then
    stateWords HField.packing
      (iterRounds ((honestData (K := RealizedProgram.gf256.K) i.y).states ⟨p, hp⟩) (t + 1)) j
    else 0 else 0)⟩ : HashSourceValues RealizedProgram.gf256.K)
      ({
  selected := jF RealizedProgram.gf256 i
  threshold := packWord (FH := RealizedProgram.gf256) (lowF RealizedProgram.gf256 i)
  readValue := fun n => if h : n < 39 then ((honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).read ⟨n, h⟩).value else 0
  readOrigin := fun n => if h : n < 234 then
    ((honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).read ⟨n / 6, by change n / 6 < 39; omega⟩).origin ⟨n % 6, by omega⟩ else 0
  encoded := fun n => if h : n < 256 then (honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).cEnc ⟨n, h⟩ else 0
  finalOrigin := fun n => if h : n < 256 then (honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).finalOrigin ⟨n, h⟩ else 0
  unit := fun n => if h : n < 39 then
    MemoryShuffle.unit (samM program RealizedProgram.fq11 RealizedProgram.gf256).Θ ((honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).signs ⟨n, h⟩) else 0
  origin := fun n => if h : n < 39 then
    (samM program RealizedProgram.fq11 RealizedProgram.gf256).originOf ((honestMemW program RealizedProgram.fq11 RealizedProgram.gf256 i).read ⟨n, h⟩).origin else 0
} : SelectionSourceValues RealizedProgram.gf256.K)
      Generated.MLDSA44.Native.QROMParams.SourceRoles.classifier
  E.withValues val R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x y _ c => agreeOnSourceVals_execEnv_of_values x _ _ (E.late y c) c
      fun _v hs _j hc => by
        change (Native.sourceExecution program RealizedProgram.fq11 RealizedProgram.gf256 R.facts.committed
          R.facts.boundNoCopy R.roles R.oneNodes conditions.model.bitNodes
          (conditions.noFieldForm rfl)).val y _v _j = _
        rw [Native.sourceExecution_val]
        exact (SourceRoleSemantics.role_source_coordinates y hs hc
          R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => packFreeAt_of_noGamma R.roles.noGamma _)

/-- The execution has no completeness event. -/
theorem sourceExec_δ (R : certified.Ready) : ∑ k, (sourceExec R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Native.sourceExecution_δ]
  simp

/-- **The statement's writes have at most `2^20` bytes.** -/
theorem stmtCodec_ser_le (x : KeyStmt) : (keyStmtCodec.ser x).length ≤ 2 ^ 20 := by
  change ((MLDSA44.PoP.StatementWrites.keyContext 0).pre x.1).length ≤ _
  rw [MLDSA44.PoP.StatementWrites.keyContext_pre_length]
  norm_num

/-- The label has at most `2^10` bytes. -/
theorem label_le : label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `MLDSA44.Native.QROMParams`** (`Configuration.Frontend`): the statements `KeyStmt` with the codec
`keyStmtCodec`, read as their statement values (`stmtOf`), the headline relation `keyWitRel`, the honest
inputs `MLDSA44.HonestInput` at `Native.relH program fq11 RealizedProgram.gf256` with the execution `sourceExec`, and the label `label`. -/
noncomputable def frontend :
    Configuration.Frontend certified source KeyStmt MLDSA44.VarWitness MLDSA44.HonestInput where
  codec := keyStmtCodec
  stmtOf := stmtOf
  rel' := keyWitRel
  g s w := w (stmtOf s)
  relH := Native.relH program fq11 RealizedProgram.gf256
  exec := sourceExec
  keyStmtOf := keyStmtOf
  label := label

/-- **The facts of `frontend`**: the statement's writes (`stmtCodec_ser_le`), the label
(`label_le`), the witness map, the execution (`sourceExec_δ`) and the honest inputs' statements. -/
theorem frontendFacts : frontend.Facts :=
  ⟨stmtCodec_ser_le, label_le, (fun _ _ h => mem_keyWitRel h), sourceExec_δ,
    fun y => stmtOf_eq (keyStmtOf y)⟩

instantiate_config GordieHowe.MLDSA44.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedHonest, GordieHowe.Configuration.CertifiedFront]
  folding [keyRel] certified source frontend

/-! ## The configuration -/

/-- **`MLDSA44.Native.QROMParams` as a configuration under spBCS** (module docstring,
`Configuration.ofCertified`): `48`-byte salts and the query cap `2 ^ 100`. -/
noncomputable def configuration : Configuration :=
  .ofCertified certified source frontend 48 (2 ^ 100)

/-- **The facts of `configuration`** (`Configuration.ofCertified_facts`): the frontend's
(`frontendFacts`) and the generated loads' check (`GordieHowe.RuntimeInputs.FiguresFacts.loads`). -/
theorem configurationFacts : configuration.Facts :=
  Configuration.ofCertified_facts certified source frontendFacts (by norm_num) _
    (conditions.fullFacts.figures.loads rfl)

/-- **The honest inputs of the paper's relation** (`Configuration.HonestOf` at `keyWitRel`, the
paper's relation `MLDSA44.PoP.relUpTo 32` at the key): every pair has the honest input
`MLDSA44.HonestInput.ofRel` at its statement; no pair of the relation is excluded. -/
def honestOfRel : configuration.HonestOf where
  rel := keyWitRel
  rel_subset _ h := h
  honestOf p hp := MLDSA44.HonestInput.ofRel p.1.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.MLDSA44.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] folding [keyRel] configuration configurationFacts
    honestOfRel at proofSystem

end GordieHowe.MLDSA44.Native.QROMParams
