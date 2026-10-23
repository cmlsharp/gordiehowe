-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.QROMParams.HonestFacts
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Completion
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Transcript
public import GordieHowe.Applications.Configuration
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

The figures: at most `2315` rounds, every round's load within `2^-1870` at its own stream length,
trees of at most `4069` leaves, `255` queried leaves, `7951` verifier queries
(`2 · 2315 + 6 + 255 · 13`), round errors at most `errorMax / 2^260`, `4635` digests per input
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

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the honest
prover).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.Falcon512.Native.QROMParams.Program (program)
open ROMParams (HonestIn relH sourceExecution oneNodes VarWitness stmtOf)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/-! ## The honest strategy -/

set_option maxRecDepth 8192 in
/-- No late value is a source value (decided). -/
theorem facts_noSourceLate : ∀ v < program.values.length, program.IsLate v →
    ¬ program.IsSourceValue v := by
  decide +kernel

/-- **The ready data of the honest strategy of `Falcon512.Native.QROMParams`** (`RealizedProgram.CompletionReady`): the nodes
containing `1` (`oneNodes (FH := gf256) (FA := fq20)`), the program's validity, the interpretation's registry, integer
readings and MAC model, and the checks (`GordieHowe.Generated.Falcon512.Native.QROMParams.Completion.completionOk`). -/
def completionReady : program.CompletionReady interp Honest.PN
    Generated.Falcon512.Native.QROMParams.Cert.gens Generated.Falcon512.Native.QROMParams.Cert.cderivs where
  nodes := Generated.Falcon512.Native.QROMParams.Honest.nodes
  oneNodes := oneNodes (FH := RealizedProgram.gf256) (FA := RealizedProgram.fq20)
  wf := Generated.Falcon512.Native.QROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
  tables := Generated.Falcon512.Native.QROMParams.Realize.derivable.tables
  macsRealizable := Generated.Falcon512.Native.QROMParams.Realize.derivable.eventsOk
  sourceValid := Locality.sourceValid
  ok := Generated.Falcon512.Native.QROMParams.Completion.completionOk

set_option maxRecDepth 8192 in
/-- **The `kpriv` source values whose type no node states have checked types** (decided). -/
theorem kprivTyped : program.KprivTyped := by
  decide +kernel

/-- **The honest strategy of `Falcon512.Native.QROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the
execution `sourceExecution`): the honest valuation `honestVal` read off by `execOf`, the generated late
values, no completeness event. -/
noncomputable def honestStrategy : program.HonestStrategy interp (ROMParams.relH program RealizedProgram.gf256 RealizedProgram.fq20) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (ROMParams.sourceExecution program RealizedProgram.gf256 RealizedProgram.fq20 _ Generated.Falcon512.Native.QROMParams.Valid.wellFormed interpModel.registered
      interpModel.lawful completionReady.facts.committed completionReady.facts.boundNoCopy facts_noSourceLate kprivTyped (RealizedProgram.boundOneMem_of_natTypedIn
        (L := [(0, "bit"), (0, "GF(2^16)"), (1, "GF(p^1)")]) (oneNodes (FH := RealizedProgram.gf256) (FA := RealizedProgram.fq20))
        (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, honestStrategy.δ k ≤ honestBound := by
  simp [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, ROMParams.sourceExecution, honestBound]

/-! ## The facts of the figures -/

variable (C : Compiled)

/-- **The facts the spBCS setting is built from**: the transcript's (`forkTranscript_bounds`)
and `48`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript C).MergeBounds 48 :=
  ⟨forkTranscript_bounds C, by norm_num⟩

set_option maxRecDepth 8192 in
/-- **The figures of `forkIop`** (`RealizedProgram.ProofSystem.fieldIop_figures`, decided): at most `2315` rounds,
trees of at most `4069` leaves, `255` queried leaves, `7951` verifier queries, `4635` digests
per input and `7327` positions. -/
theorem forkFigures : (forkIop C).Figures 2315 4069 255 7951 4635 7327 :=
  (proofSystem C.src).fieldIop_figures (forkLowering C) stmtOf C.enforce (by decide +kernel)

/-! ## The configuration -/

/-- **`Falcon512.Native.QROMParams` as a configuration under spBCS** (module docstring). The
honest prover at a strategy `H`: the proof system's phased honest prover and every forked domain's honest
prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`, `RealizedProgram.ProofSystem.fieldHonestDomains`,
`RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the key's statement values
(`RealizedProgram.ProofSystem.IOP.Honest.comap`); its completeness error is the strategy's summed completeness errors
(`err`). -/
noncomputable def configuration : Configuration where
  Compiled := Compiled
  Stmt := PublicKey
  Wit := program.Valuation interp → VarWitness
  rel := keyRel
  iop := forkIop
  sound := forkIopSound
  T := forkTranscript
  kS := 48
  Wit' := VarWitness
  rel' := keyWitRel
  g s w := w (stmtOf s)
  TA C := (proofSystem C.src).CircuitsAccept
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel := keyHonestRel
  sim C := (proofSystem C.src).fieldIopSimData (forkLowering C) stmtOf
  honest C TA _ _ H := (proofSystem C.src).fieldIopHonest (forkLowering C) stmtOf TA H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := ROMParams.HonestIn
  relH := ROMParams.relH program RealizedProgram.gf256 RealizedProgram.fq20
  strategy := honestStrategy
  keyStmtOf y := y.y.pk
  inh := inferInstance
  rounds := 2315
  chernoff := 1870
  N := 4069
  nq := 255
  kq := 7951
  errorMax := errorMax
  errorExp := 260
  D := 4635
  qQ := 2 ^ 100
  qR := 2 ^ 64
  pos := 7327
  k := 48

/-- **The facts of `configuration`**: the figures' bounds (`transcriptMergeBounds`, `forkLoadsGranted`,
every round at its own stream length, `QROMParams.maxRoundError_le`), the end-to-end theorem at the
configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2e`, at the witness
map `mem_keyWitRel` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`). -/
theorem configurationFacts : configuration.GrantedFacts where
  hb := transcriptMergeBounds
  knowledge C _ hkq := ((proofSystem C.src).fieldBranches ready).e2e_knowledge ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq
  e2e C TA _ _ H _ hkq hf := ((proofSystem C.src).fieldBranches ready).e2e ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 48 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq hf TA ((proofSystem C.src).fieldHonestDomains ready)
    ((proofSystem C.src).fieldForkHonestDomains ready TA) H.toHonestCore
    H.complete
  rounds_le C := (forkFigures C).rounds_le
  loadsGranted := forkLoadsGranted
  leaves_le C := (forkFigures C).leaves_le
  queries_le C := (forkFigures C).queries_le
  kq_ge C := (forkFigures C).kq_ge
  kq_le := show 7951 ≤ 2 ^ 16 by norm_num
  error_le := maxRoundError_le
  digests_le C := (forkFigures C).digests_le
  pos_eq C := (forkFigures C).pos_eq
  k_eq _ := rfl
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem _ := rfl

/-- **The honest inputs of the supported pairs of the paper's relation**
(`Configuration.HonestOf` at `ROMParams.keySupportedRel`: the pairs of `keyWitRel` whose
`HashToPoint` succeeds within the H circuit's `639` samples, `Falcon512.PoP.relSupported`): every
such pair has the honest input `ROMParams.HonestIn.ofRel` at its key. -/
def honestOfRel : configuration.HonestOf where
  rel := ROMParams.keySupportedRel
  rel_subset _ h := h.1
  honestOf p hp := ROMParams.HonestIn.ofRel p.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.Falcon512.Native.QROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeQROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] configuration
    configurationFacts honestOfRel

end GordieHowe.Falcon512.Native.QROMParams
