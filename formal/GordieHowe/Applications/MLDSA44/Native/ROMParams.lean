-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HonestFacts
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Completion
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Transcript
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd

@[expose] public section

/-!
# GordieHowe: the statements of `MLDSA44.Native.ROMParams` under spBCS

The native ML-DSA-44 proof of possession at the ROM parameters as a configuration under spBCS
(`GordieHowe/Applications/Configuration.lean`): the record `configuration` (the IOP with forked domains
`forkIop`, its transcript `forkTranscript`, `32`-byte Fiat–Shamir salts, the ML-DSA-44
proof-of-possession relation at the key `keyWitRel` with the witness read at the key's statement
values, the honest prover, the honest strategy `honestStrategy`, and the figures), its facts
`configurationFacts`, and the instances of the templates of the families `Common`, `GordieHowe.Configuration.ZeroKnowledgeROM` and `GordieHowe.Configuration.AdaptiveCompleteness`.

The figures: at most `2269` rounds, every round's load within `2^-2800`, trees of at most `3392`
leaves, `137` queried leaves, `6323` verifier queries (`2 · 2269 + 4 + 137 · 13`), round errors at
most `errorMax / 2^140`, `4541` digests per input (`2 · 2269 + 2 + 1`), the query caps `2^40`
(QROM) and `2^64` (ROM), `6155` positions (`2763 + 3392`) and `32`-byte digests.

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` at the execution of the
source program (`GordieHowe.MLDSA44.Native.ROMParams.sourceExecution`), with no completeness event (`δ = 0`), on the honest
inputs `HonestIn` (a valid ML-DSA-44 honest input with a message of at most `32` bytes, at its
key); the realization's facts come from the checks (`completionReady`).

All statements hold under the compiler trust (`CircuitsEnforce`, and `CircuitsAccept` for the honest
prover).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Configuration
open Generated.MLDSA44.Native.ROMParams.Program (program)
open HashField (interp)
open scoped NNReal ENNReal

/-! ## The honest strategy -/

set_option maxRecDepth 8192 in
/-- No late value is a source value (decided). -/
theorem facts_noSourceLate : ∀ v < program.values.length, program.IsLate v →
    ¬ program.IsSourceValue v := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Every value bound to its digits has the field or a node of `oneNodes` as its type (decided). -/
theorem facts_boundNatTyped : ∀ v < program.values.length, (program.value v).kind.isBound = true →
    program.natTypedInB [(0, "GF(p^1)"), (1, "bit"), (1, "GF(2^16)")] v = true := by
  decide +kernel

/-- **The ready data of the honest strategy of `MLDSA44.Native.ROMParams`** (`RealizedProgram.CompletionReady`): the nodes
containing `1` (`ROMParams.oneNodes`), the program's validity, the interpretation's registry, integer
readings and MAC model, and the checks (`GordieHowe.Generated.MLDSA44.Native.ROMParams.Completion.completionOk`). -/
def completionReady : program.CompletionReady interp (ROMParams.MldsaNativeHonest.PN (program := program))
    Generated.MLDSA44.Native.ROMParams.Cert.gens Generated.MLDSA44.Native.ROMParams.Cert.cderivs where
  nodes := Generated.MLDSA44.Native.ROMParams.Honest.nodes
  oneNodes := ROMParams.oneNodes
  wf := Generated.MLDSA44.Native.ROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
  tables := Generated.MLDSA44.Native.ROMParams.Realize.derivable.tables
  macsRealizable := Generated.MLDSA44.Native.ROMParams.Realize.derivable.eventsOk
  sourceValid := sourceValid
  ok := Generated.MLDSA44.Native.ROMParams.Completion.completionOk

set_option maxRecDepth 8192 in
/-- **The `kpriv` source values whose type no node states have checked types** (decided). -/
theorem kprivTyped : program.KprivTyped := by
  decide +kernel

/-- **The honest strategy of `MLDSA44.Native.ROMParams`** (`RealizedProgram.HonestStrategy.ofCompletionReady` at the execution
`ROMParams.sourceExecution`): the honest valuation `honestVal` read off by `execOf`, the
generated late values, no completeness event. -/
noncomputable def honestStrategy : program.HonestStrategy interp (relH program RealizedProgram.fq6 RealizedProgram.gf128) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (ROMParams.sourceExecution program RealizedProgram.fq6 RealizedProgram.gf128 completionReady.facts.committed completionReady.facts.boundNoCopy facts_noSourceLate kprivTyped
      (RealizedProgram.boundOneMem_of_natTypedIn ROMParams.oneNodes facts_boundNatTyped)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- The honest strategy's completeness errors are `0`. -/
theorem honestStrategy_delta : ∑ k, honestStrategy.δ k ≤ honestBound := by
  simp [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, ROMParams.sourceExecution, honestBound]

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

/-! ## The facts of the figures -/

variable (C : Compiled)

/-- **The facts the setting with merges is built from**: the transcript's (`forkTranscript_bounds`)
and `32`-byte salts. -/
theorem transcriptMergeBounds : (forkTranscript C).MergeBounds 32 :=
  ⟨forkTranscript_bounds C, by norm_num⟩

set_option maxRecDepth 8192 in
/-- **The figures of `forkIop`** (`RealizedProgram.ProofSystem.fieldIop_figures`, decided): at most `2269` rounds,
trees of at most `3392` leaves, `137` queried leaves, `6323` verifier queries, `4541` digests
per input and `6155` positions. -/
theorem forkFigures : (forkIop C).Figures 2269 3392 137 6323 4541 6155 :=
  (proofSystem C.src).fieldIop_figures (forkLowering C) stmtOf C.enforce (by decide +kernel)

/-! ## The configuration -/

/-- **`MLDSA44.Native.ROMParams` as a configuration under spBCS** (module docstring). The
honest prover at a strategy `H`: the proof system's phased honest prover and every forked domain's honest
prover on the generic per-field domain proofs (`RealizedProgram.ProofSystem.FieldBranches.honestAt`, `RealizedProgram.ProofSystem.fieldHonestDomains`,
`RealizedProgram.ProofSystem.fieldForkHonestDomains`) read through the key's statement values
(`RealizedProgram.ProofSystem.IOP.Honest.comap`); its completeness error is the strategy's summed completeness errors
(`err`). -/
noncomputable def configuration : Configuration where
  Compiled := Compiled
  Stmt := KeyStmt
  Wit := program.Valuation interp → ROMParams.VarWitness
  rel := keyRel
  iop := forkIop
  sound := forkIopSound
  T := forkTranscript
  kS := 32
  Wit' := ROMParams.VarWitness
  rel' := keyWitRel
  g s w := w (stmtOf s)
  TA C := (proofSystem C.src).CircuitsAccept
  Val := program.Valuation interp
  Strategy _ relH := program.HonestStrategy interp relH
  hrel := keyHonestRel
  sim C := (proofSystem C.src).fieldIopSimData (forkLowering C) stmtOf
  honest C TA _ _ H := (proofSystem C.src).fieldIopHonest (forkLowering C) stmtOf TA H.toHonestCore
  err H := ∑ k, H.δ k
  HonestIn := MLDSA44.HonestInput
  relH := relH program RealizedProgram.fq6 RealizedProgram.gf128
  strategy := honestStrategy
  keyStmtOf := keyStmtOf
  inh := inferInstance
  rounds := 2269
  chernoff := 2800
  N := 3392
  nq := 137
  kq := 6323
  errorMax := errorMax
  errorExp := 140
  D := 4541
  qQ := 2 ^ 40
  qR := 2 ^ 64
  pos := 6155
  k := 32

/-- **The facts of `configuration`**: the figures' bounds (`transcriptMergeBounds`, `forkFigures`,
`forkLoads` at `good_A_at` and `good_H_at`, `maxRoundError_le`), the end-to-end theorem at the
configuration's IOP (`RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `RealizedProgram.ProofSystem.FieldBranches.e2e`, at the witness
map `mem_keyWitRel` and the domains' generic honest provers) and the honest strategy's
(`honestStrategy_delta`). -/
theorem configurationFacts : configuration.Facts where
  hb := transcriptMergeBounds
  knowledge C _ hkq := ((proofSystem C.src).fieldBranches ready).e2e_knowledge ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    (sourceError_final sampleEps) stmtOf (forkTranscript C) 32 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq
  e2e C TA _ _ H _ hkq hf := ((proofSystem C.src).fieldBranches ready).e2e ((proofSystem C.src).fieldBranchesSound ready) C.enforce source_rbr_knowledge_soundness
    (sourceError_final sampleEps) stmtOf (forkTranscript C) 32 (transcriptMergeBounds C)
    (fun _ _ h => mem_keyWitRel h) hkq hf TA ((proofSystem C.src).fieldHonestDomains ready)
    ((proofSystem C.src).fieldForkHonestDomains ready TA) H.toHonestCore
    H.complete
  rounds_le C := (forkFigures C).rounds_le
  loads C := forkLoads C (fun _ h => good_A_at h) fun _ h => good_H_at h
  leaves_le C := (forkFigures C).leaves_le
  queries_le C := (forkFigures C).queries_le
  kq_ge C := (forkFigures C).kq_ge
  kq_le := show 6323 ≤ 2 ^ 16 by norm_num
  error_le := maxRoundError_le
  digests_le C := (forkFigures C).digests_le
  pos_eq C := (forkFigures C).pos_eq
  k_eq _ := rfl
  exact := nonpos_iff_eq_zero.1 honestStrategy_delta
  keyStmtOf_mem y := stmtOf_eq (keyStmtOf y)

/-- **The honest inputs of the paper's relation** (`Configuration.HonestOf` at `keyWitRel`, the
paper's relation `MLDSA44.PoP.relUpTo 32` at the key): every pair has the honest input
`MLDSA44.HonestInput.ofRel` at its statement; no pair of the relation is excluded. -/
def honestOfRel : configuration.HonestOf where
  rel := keyWitRel
  rel_subset _ h := h
  honestOf p hp := MLDSA44.HonestInput.ofRel p.1.1 p.2 hp
  keyStmtOf_honestOf _ _ := rfl

instantiate_config GordieHowe.MLDSA44.Native.ROMParams
  from [GordieHowe.Configuration.Common, GordieHowe.Configuration.ZeroKnowledgeROM,
    GordieHowe.Configuration.AdaptiveCompleteness,
    GordieHowe.Configuration.PaperRelation] configuration configurationFacts
    honestOfRel

end GordieHowe.MLDSA44.Native.ROMParams
