-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestFacts
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Completion
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Transcript
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `Falcon512.Native.ROMParams` under spBCS

The native Falcon-512 proof of possession at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `32`-byte Fiat–Shamir salts, the Falcon-512
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM` and `GordieHowe.Configuration.AdaptiveCompleteness`.

The figures: at most `2357` rounds, every round's load within `2^-2780`, trees of at most `3392`
leaves, `153` queried leaves, `6711` verifier queries (`2 · 2357 + 8 + 153 · 13`), round errors at
most `errorMax / 2^140`, `4721` digests per input (`2 · 2357 + 6 + 1`), the query caps `2^40`
(QROM) and `2^64` (ROM), `5086` positions (`3392 + 1694`) and `32`-byte digests.

The realization step's derivations (`RealizedProgram.Derivable`) include the MAC `mac.equal` with
its H predicate `mac.H`, its tail `mac` in the grouped form (four groups of sixteen chunks, two
base-`64` quotient digits per group, Boolean residues, the final one-digit quotient `mac.final.q`),
and `signature.equation` in the field form (its field equation a row of the program,
`RealizedProgram.DerivationsValid.fieldRows`).

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`sourceExecution`), with no completeness event (`δ = 0`), on the honest inputs
`HonestIn` (a valid Falcon-512 honest input with a message of at most `32` bytes, at its key);
the realization's facts come from the checks (`completionReady`).

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the honest
prover).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.Falcon512.Native.ROMParams.Program (program)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/-! ## The honest strategy -/

set_option maxRecDepth 8192 in
/-- No late value is a source value (decided). -/
theorem facts_noSourceLate : ∀ v < program.values.length, program.IsLate v →
    ¬ program.IsSourceValue v := by
  decide +kernel

/-- **The ready data of the honest strategy of `Falcon512.Native.ROMParams`** (`RealizedProgram.CompletionReady`): the nodes
containing `1` (`oneNodes (FH := gf128) (FA := fq9)`), the program's validity, the interpretation's registry, integer
readings and MAC model, and the checks (`GordieHowe.Generated.Falcon512.Native.ROMParams.Completion.completionOk`). -/
def completionReady : program.CompletionReady interp Honest.PN
    Generated.Falcon512.Native.ROMParams.Cert.gens Generated.Falcon512.Native.ROMParams.Cert.cderivs where
  nodes := Generated.Falcon512.Native.ROMParams.Honest.nodes
  oneNodes := oneNodes (FH := RealizedProgram.gf128) (FA := RealizedProgram.fq9)
  wf := Generated.Falcon512.Native.ROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
  tables := Generated.Falcon512.Native.ROMParams.Realize.derivable.tables
  macsRealizable := Generated.Falcon512.Native.ROMParams.Realize.derivable.eventsOk
  sourceValid := Locality.sourceValid
  ok := Generated.Falcon512.Native.ROMParams.Completion.completionOk

set_option maxRecDepth 8192 in
/-- **The `kpriv` source values whose type no node states have checked types** (decided). -/
theorem kprivTyped : program.KprivTyped := by
  decide +kernel

/-- **The honest strategy of `Falcon512.Native.ROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the
execution `sourceExecution`): the honest valuation `honestVal` read off by `execOf`, the generated late
values, no completeness event. -/
noncomputable def honestStrategy : program.HonestStrategy interp (relH program RealizedProgram.gf128 RealizedProgram.fq9) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (sourceExecution program RealizedProgram.gf128 RealizedProgram.fq9 _ Generated.Falcon512.Native.ROMParams.Valid.wellFormed interpModel.registered
      interpModel.lawful completionReady.facts.committed completionReady.facts.boundNoCopy facts_noSourceLate kprivTyped (RealizedProgram.boundOneMem_of_natTypedIn
        (L := [(0, "bit"), (0, "GF(2^16)"), (1, "GF(p^1)")]) (oneNodes (FH := RealizedProgram.gf128) (FA := RealizedProgram.fq9))
        (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, honestStrategy.δ k ≤ honestBound := by
  simp [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, sourceExecution, honestBound]

/-! ## The facts of the figures -/

variable (C : Compiled)

/-- **The facts the spBCS setting is built from**: the transcript's (`forkTranscript_bounds`)
and `32`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript C).MergeBounds 32 :=
  ⟨forkTranscript_bounds C, by norm_num⟩

set_option maxRecDepth 8192 in
/-- **The figures of `forkIop`** (`RealizedProgram.ProofSystem.fieldIop_figures`, decided): at most `2357` rounds,
trees of at most `3392` leaves, `153` queried leaves, `6711` verifier queries, `4721` digests
per input and `5086` positions. -/
theorem forkFigures : (forkIop C).Figures 2357 3392 153 6711 4721 5086 :=
  (proofSystem C.src).fieldIop_figures (forkLowering C) stmtOf C.enforce (by decide +kernel)

/-! ## The configuration -/

/-- **`Falcon512.Native.ROMParams` as a configuration under spBCS** (module docstring).
The honest prover at a strategy `H`: the proof system's phased honest prover and every forked domain's honest
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
  kS := 32
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
  HonestIn := HonestIn
  relH := relH program RealizedProgram.gf128 RealizedProgram.fq9
  strategy := honestStrategy
  keyStmtOf y := y.y.pk
  inh := inferInstance
  rounds := 2357
  chernoff := 2780
  N := 3392
  nq := 153
  kq := 6711
  errorMax := errorMax
  errorExp := 140
  D := 4721
  qQ := 2 ^ 40
  qR := 2 ^ 64
  pos := 5086
  k := 32

/-- **The facts of `configuration`**: the figures' bounds (`transcriptMergeBounds`, `forkFigures`,
`forkLoads` at `good_A_at` and `good_H_at`, `maxRoundError_le`), the end-to-end theorem at the
configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2e`, at the witness
map `mem_keyWitRel` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`). -/
theorem configurationFacts : configuration.Facts where
  hb := transcriptMergeBounds
  knowledge C _ hkq := ((proofSystem C.src).fieldBranches ready).e2e_knowledge ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 32 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq
  e2e C TA _ _ H _ hkq hf := ((proofSystem C.src).fieldBranches ready).e2e ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    sourceError_final stmtOf (forkTranscript C) 32 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq hf TA ((proofSystem C.src).fieldHonestDomains ready)
    ((proofSystem C.src).fieldForkHonestDomains ready TA) H.toHonestCore
    H.complete
  rounds_le C := (forkFigures C).rounds_le
  loads C := forkLoads C (fun _ h => good_A_at h) fun _ h => good_H_at h
  leaves_le C := (forkFigures C).leaves_le
  queries_le C := (forkFigures C).queries_le
  kq_ge C := (forkFigures C).kq_ge
  kq_le := show 6711 ≤ 2 ^ 16 by norm_num
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

instantiate_config GordieHowe.Falcon512.Native.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] configuration
    configurationFacts honestOfRel

end GordieHowe.Falcon512.Native.ROMParams
