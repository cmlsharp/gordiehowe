-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.QROMParams.GadgetFacts
public import GordieHowe.Applications.Falcon512.Native.QROMParams.SourceRoleSemantics
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Certified
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Relations
public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting
public import GordieHowe.ProofSystem.Program.ForkJoinComap
public import GordieHowe.Applications.Configuration.Certified
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Native.QROMParams` under spBCS

The native Falcon-512 proof of possession at the QROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `48`-byte Fiat–Shamir salts, the Falcon-512
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts` (with granted points: `GrantedFacts`), and the instances of the templates of the
families `Common`, `Query` and `GordieHowe.Configuration.AdaptiveCompleteness`.

The configuration is `GordieHowe.Configuration.ofCertified` at the generated certified data
(`GordieHowe.Generated.Falcon512.Native.QROMParams.certified`), the source program's soundness (`source`) and the
frontend (`frontend`): its IOP, transcript, honest strategy and honest relation are the instances
of the generic templates (`GordieHowe.Configuration.CertifiedSource`,
`GordieHowe.Configuration.CertifiedHonest`, `GordieHowe.Configuration.CertifiedFront`).

The figures: at most `2315` rounds, every round's load within `2^-1870` at its own stream length,
trees of at most `4069` leaves, `255` queried leaves, `7951` verifier queries
(`2 · 2315 + 6 + 255 · 13`), round errors at most `13358901 / 2^260`, `4635` digests per input
(`2 · 2315 + 4 + 1`), the query caps `2^100` (QROM) and `2^64` (ROM), `7327` positions
(`4069 + 3258`) and `48`-byte digests.

The realization step's derivations (`RealizedProgram.Derivable`) include the MAC `mac.equal` with
its H predicate `mac.H`, its tail `mac` in the grouped form (four groups of eight chunks, two
base-`64` quotient digits per group, Boolean residues, the final one-digit quotient `mac.final.q`),
and `signature.equation` in the field form (its field equation a row of the program,
`RealizedProgram.DerivationsValid.fieldRows`).

Domain `A`'s Ligero tableau (`RealizedProgram.Export.Plan.LigeroShapesValid`):
`(rate, t, block_enc) = (12, 127, 3799)` and `k = 271`, so `w = k − t = 144`; the `80 + 100 = 180`
subfield masks of its tree `F_q <4 F_q^4 <5 F_q^20` take two prefix rows (`⌈180 / w⌉`,
`tree_zk.h`'s `prefix_padded`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`sourceExecution`), with no completeness event (`δ = 0`), on the honest inputs
`HonestIn` (a valid Falcon-512 honest input with a message of at most `32` bytes, at its key);
the realization's facts come from the checks (`completionReady`).

No statement has a compiler-trust hypothesis: the configuration's definitions are generic over the
program's proof systems (`ProofSystems`), and its statements are instantiated at `proofSystem`,
whose sources enforce the circuits' entries and accept the honest inputs by the certificates
(`GordieHowe/Applications/Falcon512/Native/QROMParams/Certified.lean`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.Falcon512.Native.QROMParams.Program (program)
open Generated.Falcon512.Native.QROMParams (interp certified conditions)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/-! ## The frontend -/

/-- **The source program's execution of `Falcon512.Native.QROMParams`** at ready data of its honest strategy. -/
noncomputable def sourceExec (R : certified.Ready) :
    program.SourceExecution interp (Native.relH program RealizedProgram.gf256 RealizedProgram.fq20) :=
  let E := Native.sourceExecution program RealizedProgram.gf256 RealizedProgram.fq20 _
    conditions.wellFormed conditions.model.registered conditions.model.lawful R.facts.committed
    R.facts.boundNoCopy R.roles R.oneNodes conditions.model.bitNodes
  let s : HonestIn → Native.SourceValues (interp 0).K
      (interp (RealizedProgram.SelectShape.field program selShape)).K := fun i =>
    { hash :=
        { nonce := fun j => if h : j < 320 then
            hBlock RealizedProgram.gf256 i.y ⟨j / 8, by omega⟩ ⟨j % 8, by omega⟩ else 0
          message := fun j => if h : j < 768 then
            hBlock RealizedProgram.gf256 i.y ⟨40 + j / 8, by omega⟩ ⟨j % 8, by omega⟩ else 0
          flags := fun j => if j < 40 + i.L then 1 else 0
          state := fun j => RealizedProgram.stateWords HField.packing
            (hStarts RealizedProgram.gf256 i.y 1) j
          rounds := fun p t j => RealizedProgram.stateWords HField.packing
            (GordieHowe.KeccakTrace.iterRounds (hStarts RealizedProgram.gf256 i.y p) (t + 1)) j }
      rawSamples := fun j => PackedClaim.pack (HField.packing (FH := RealizedProgram.gf256)) fun b =>
        decide (Bits.constBit (K := RealizedProgram.gf256.K)
          (if h : j < 512 then i.y.samples ⟨j, h⟩ else 0) b = 1)
      counts := fun j => if h : j < 717 then
        (hRoute program RealizedProgram.gf256 RealizedProgram.fq20 i.y ⟨j, h⟩).count_enc else 0
      full := fun j => if h : j < 205 then
        (hRoute program RealizedProgram.gf256 RealizedProgram.fq20 i.y ⟨512 + j, by omega⟩).full else 0
      crossing := Native.hNat program i.y 594
      s2 := Native.hNat program i.y 595
      s1 := Native.hNat program i.y 596
      magnitudes := Native.hNat program i.y 597
      squareDigits := Native.hNat program i.y 598
      columnCarries := Native.hNat program i.y 599
      batchDigits := Native.hNat program i.y 600
      batchCarries := Native.hNat program i.y 601
      finalDigits := Native.hNat program i.y 602
      finalCarries := Native.hNat program i.y 603 }
  E.withValues
    (fun i => (s i).valuation (program := program)
      Generated.Falcon512.Native.QROMParams.SourceRoles.classifier)
    R.facts.committed.sourceValid R.facts.committed.srcNoMessage
    (fun x i _ c => RealizedProgram.agreeOnSourceVals_execEnv_of_values x _ _ (E.late i c) c
      fun _v hs _j hc => (role_source_coordinates
        (⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
          fun _ => rfl, fun _ => rfl, fun slot j hslot => by
            interval_cases slot <;> rfl⟩ : Native.HonestSourceValues program RealizedProgram.gf256
              RealizedProgram.fq20 i (s i)) hs hc R.facts.committed.srcNoPadCopy).symm)
    (fun _ _ _ _ _ => RealizedProgram.packFreeAt_of_noGamma R.roles.noGamma _)

/-- The execution has no completeness event. -/
theorem sourceExec_δ (R : certified.Ready) : ∑ k, (sourceExec R).δ k = 0 := by
  rw [sourceExec, RealizedProgram.SourceExecution.withValues_δ, Native.sourceExecution_δ]
  simp

/-- **The statement's writes have at most `2^20` bytes.** -/
theorem stmtCodec_ser_le (pk : PublicKey) : (falconKeyCodec.ser pk).length ≤ 2 ^ 20 := by
  change (falconKeyWrites pk).length ≤ _
  rw [falconKeyWrites_length]
  norm_num

/-- The label has at most `2^10` bytes. -/
theorem label_le : label.length ≤ 2 ^ 10 :=
  Nat.le_of_ble_eq_true rfl

/-- **The frontend of `Falcon512.Native.QROMParams`** (`Configuration.Frontend`): the statements `PublicKey` with the codec
`falconKeyCodec`, read as their statement values (`stmtOf`), the headline relation `keyWitRel`, the honest
inputs `Native.HonestIn` at `Native.relH program RealizedProgram.gf256 RealizedProgram.fq20` with the execution `sourceExec`, and the label `label`. -/
noncomputable def frontend :
    Configuration.Frontend certified source PublicKey VarWitness Native.HonestIn where
  codec := falconKeyCodec
  stmtOf := stmtOf
  rel' := keyWitRel
  g s w := w (stmtOf s)
  relH := Native.relH program RealizedProgram.gf256 RealizedProgram.fq20
  exec := sourceExec
  keyStmtOf y := y.y.pk
  label := label

/-- **The facts of `frontend`**: the statement's writes (`stmtCodec_ser_le`), the label
(`label_le`), the witness map, the execution (`sourceExec_δ`) and the honest inputs' statements. -/
theorem frontendFacts : frontend.Facts :=
  ⟨stmtCodec_ser_le, label_le, (fun _ _ h => mem_keyWitRel h), sourceExec_δ,
    fun _ => rfl⟩

instantiate_config GordieHowe.Falcon512.Native.QROMParams
  from [GordieHowe.Configuration.CertifiedHonest, GordieHowe.Configuration.CertifiedFront]
  folding [keyRel] certified source frontend

/-! ## The configuration -/

/-- **`Falcon512.Native.QROMParams` as a configuration under spBCS** (module docstring,
`Configuration.ofCertified`): `48`-byte salts and the query cap `2 ^ 100`. -/
noncomputable def configuration : Configuration :=
  .ofCertified certified source frontend 48 (2 ^ 100)

/-- **The facts of `configuration`** (`Configuration.ofCertified_grantedFacts`): the frontend's
(`frontendFacts`). -/
theorem configurationFacts : configuration.GrantedFacts :=
  Configuration.ofCertified_grantedFacts certified source frontendFacts (by norm_num) _

/-- **The honest inputs of the supported pairs of the paper's relation**
(`Configuration.HonestOf` at `Falcon512.Native.keySupportedRel`: the pairs of `keyWitRel` whose
`HashToPoint` succeeds within the H circuit's `717` samples, `Falcon512.PoP.relSupported`): every
such pair has the honest input `HonestIn.ofRel` at its key. -/
def honestOfRel : configuration.HonestOf where
  rel := Native.keySupportedRel
  rel_subset _ h := h.1
  honestOf p hp := HonestIn.ofRel p.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.Falcon512.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] folding [keyRel] configuration
    configurationFacts honestOfRel at proofSystem

end GordieHowe.Falcon512.Native.QROMParams
