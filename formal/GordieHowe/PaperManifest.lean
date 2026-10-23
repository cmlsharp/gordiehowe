-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ReedSolomon.JohnsonAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import GordieHowe.Model.IOP.Causal
public import GordieHowe.Model.IOP.CausalSound
public import GordieHowe.Model.IOP.CausalComplete
public import GordieHowe.Model.IOP.CausalHVZK
public import GordieHowe.Model.IOP.Reduction
public import GordieHowe.Model.IOP.ReductionPrefix
public import GordieHowe.ProofSystem.Zerocheck.BitSumcheck
public import GordieHowe.ProofSystem.Zerocheck.BitSumcheckIP
public import GordieHowe.ProofSystem.Ligero.InterleavedAgreementList
public import GordieHowe.ProofSystem.Ligero.LongfellowOrder
public import GordieHowe.ProofSystem.Ligero.LongfellowOrder.V7
public import GordieHowe.ProofSystem.Ligero.UntestedMaskRow
public import GordieHowe.ProofSystem.Ligero.MaskTest.Paper
public import GordieHowe.Errata.AHIV22
public import GordieHowe.Errata.AHIV22UntestedMasks
public import GordieHowe.Errata.CHVY25
public import GordieHowe.Errata.CHVY25FamilyData
public import GordieHowe.ProofSystem.RingSwitching.TreePaper
public import GordieHowe.ProofSystem.RingSwitching.TowerPaper
public import GordieHowe.Foundations.Algebra.PackingTower
public import GordieHowe.Language.Realizations.PermutationEncoding
public import GordieHowe.ProofSystem.Program.Headlines
public import GordieHowe.ProofSystem.Program.ForkProofSystem
public import GordieHowe.ProofSystem.Program.FieldReadyGeneric
public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedLastProofQuery
public import GordieHowe.Model.QROM.Oracle
public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.SPBCS.Extraction.OnlineExtract
public import GordieHowe.SPBCS.Extraction.OnlineExtractROM
public import GordieHowe.SPBCS.Complete
public import GordieHowe.SPBCS.CompleteAdaptive
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.Knowledge
public import GordieHowe.SPBCS.KnowledgeTheorems
public import GordieHowe.SPBCS.Stability
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.SPBCS.ZeroKnowledgeROM
public import GordieHowe.SPBCS.WitnessIndist
public import GordieHowe.SPBCS.WitnessIndistAdaptive
public import GordieHowe.SPBCS.SimExtractJoint
public import GordieHowe.SPBCS.SimExtractROM
public import GordieHowe.SPBCS.SimExtractROMJoint
public import GordieHowe.SPBCS.SimExtractGame
public import GordieHowe.SPBCS.OracleTest
public import GordieHowe.SPBCS.Theorems
public import GordieHowe.SPBCS.Merkle.Compress
public import GordieHowe.Applications.Configuration
public import GordieHowe.ProofSystem.Program.EndToEnd
public import GordieHowe.Applications.Falcon512.Native.ROMParams
public import GordieHowe.Applications.Falcon512.Native.QROMParams
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams
public import GordieHowe.Model.IOP.SPIOP
public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.ROM.Interactive
public import GordieHowe.Model.ROM.InteractiveNIZKLastProofQuery
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Language.RealizedProgram.RealizationValid
public import GordieHowe.ProofSystem.Program.Errors
public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Assumptions
public import GordieHowe.ProofSystem.Program.FieldDomain
public import GordieHowe.ProofSystem.Program.FieldProofSystem
public import GordieHowe.ProofSystem.Zerocheck.AffineBatch
public import GordieHowe.ProofSystem.Zerocheck.MergedAffineBatchFused
public import GordieHowe.ProofSystem.Zerocheck.MergedAffineBatch
public import GordieHowe.ProofSystem.GKR.MaskedReduction
public import GordieHowe.ProofSystem.GKR.SourceCircuit
public import GordieHowe.Model.QROM.Purified
public import GordieHowe.Model.QROM.OutputLaw
public import GordieHowe.Model.QROM.OracleSimulation
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.Quantum.O2H.Basic
public import GordieHowe.Model.Quantum.O2H.Mixed
public import GordieHowe.Foundations.ReedSolomon.InterleavedProximity
public import GordieHowe.Foundations.ReedSolomon.BerlekampWelch
public import GordieHowe.Foundations.ReedSolomon.AffineProximity
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Transcript
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Transcript
public import GordieHowe.Applications.MLDSA44.Emulated.ZKFigures
public import GordieHowe.Model.QROM.QueryCount
public import GordieHowe.Model.QROM.CoherentBridgeCore
public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Language.Realizations.RealizeMacPaper

@[expose] public section

/-!
# The paper's machine-checked results and their Lean declarations

The paper prints the names of Lean declarations: the formalization table of
the appendix (`app:formal`) and notes beside its results. This file is the single source of
those names. `entries` pairs each result the paper calls machine-checked (its LaTeX label) with
its Lean declaration, and `appendixTable` gives the rows of the formalization table.

Each declaration is written as a name literal ``` ``GordieHowe.X ```, which elaborates only if `GordieHowe.X`
is a declaration of the environment, so renaming or deleting a declaration fails the build of
this file. The configuration instances of the generic per-configuration theorems are listed and
checked the same way.

`scripts/paper_manifest.py --paper-dir DIR` reads this file and writes the paper's names from it
into the paper's LaTeX source `DIR`: the table rows between the markers in
`sections/formal-appendix.tex`, and `generated/lean-names.tex`,
which defines the targets of `\leanref[style]{key}`. The script parses the literal syntax of
`entries` and `appendixTable` below, so keep each entry in the `{ key := …, label := …,
decl := … }` form, each row in the `{ statement := …, lean := … }` or `{ heading := … }` form,
and each string a literal or a `++` of literals.

In a table template, `{key}` prints the declaration of entry `key` without its leading `GordieHowe.`,
`{key:full}` prints the full name, and `{key:n}` prints its last `n` components.
-/

namespace GordieHowe.PaperManifest

open Lean (Name)

/-- **One machine-checked paper result**: the key by which the paper refers to it, the paper's
label and the Lean declaration. -/
structure Entry where
  /-- The key of the entry in `\leanref{key}` and in the table templates. -/
  key : String
  /-- The LaTeX label of the paper's result (or definition) whose counterpart `decl` is. -/
  label : String
  /-- The Lean declaration. -/
  decl : Name
  /-- The instances of `decl` in the configurations, when the paper states the result "in each
  configuration"; checked, not printed. -/
  instances : List Name := []

/-- **One row of the formalization table** (`app:formal`): the paper's statement column and the
Lean column, a template over entry keys, or a heading that opens a group of rows. -/
structure TableRow where
  /-- The heading of a group of rows, LaTeX; empty in a row of the table. -/
  heading : String := ""
  /-- The statement column, LaTeX. -/
  statement : String := ""
  /-- The Lean column, LaTeX, with `{key}`, `{key:full}` or `{key:n}` for an entry's name. -/
  lean : String := ""

/-- **The paper's machine-checked results**, one entry per printed or claimed counterpart. -/
def entries : List Entry := [
  -- Definitions.
  { key := "sp-term", label := "def:iop-schedule",
    decl := ``GordieHowe.IOP.SPTerm },
  { key := "causal-iop", label := "def:iop-schedule",
    decl := ``GordieHowe.IOP.SPIOP },
  { key := "causal-rbr-def", label := "def:rbr",
    decl := ``GordieHowe.IOP.CausalRBRKnowledgeSoundStmt },
  { key := "rbr-total", label := "lem:rbr-total",
    decl := ``GordieHowe.IOP.rbrKnowledgeSoundness_total_iff },
  { key := "red-prefix", label := "lem:red-prefix",
    decl := ``GordieHowe.IOP.Reduction.rbr_iff_prefixRBR },
  { key := "causal-hvzk-def", label := "def:hvzk",
    decl := ``GordieHowe.IOP.CausalHVZKStmt },
  { key := "causal-completeness-coins-def", label := "def:iop-complete",
    decl := ``GordieHowe.IOP.causalCompletenessCoins },
  { key := "source-prover", label := "def:o-honest",
    decl := ``GordieHowe.RealizedProgram.SourceProver },
  { key := "source-complete-def", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.SourceComplete },
  { key := "committed-reduction", label := "def:red",
    decl := ``GordieHowe.IOP.Reduction },
  { key := "red-rbr-def", label := "def:red-sec",
    decl := ``GordieHowe.IOP.Reduction.RBR },
  { key := "red-complete-def", label := "def:red-sec",
    decl := ``GordieHowe.IOP.Reduction.Complete },
  { key := "red-hvzk-def", label := "def:red-sec",
    decl := ``GordieHowe.IOP.Reduction.HVZK },
  { key := "plan-valid", label := "def:plan-valid",
    decl := ``GordieHowe.RealizedProgram.Valid },
  { key := "realizes", label := "def:plan",
    decl := ``GordieHowe.RealizedProgram.Derivable },
  { key := "adversary-qrom", label := "def:adversary",
    decl := ``GordieHowe.Quantum.QueryBoundedAdversary },
  { key := "adversary-rom", label := "def:adversary",
    decl := ``GordieHowe.ROM.QueryBoundedAdversary },
  { key := "zk-request", label := "def:narg-zk-post",
    decl := ``GordieHowe.QROM.ProofQuery },
  { key := "zk-after-last-request", label := "def:narg-zk-post",
    decl := ``GordieHowe.NARG.QROM.EverlastingZeroKnowledge },
  { key := "zk-after-last-request-rom", label := "def:narg-zk-post",
    decl := ``GordieHowe.NARG.ROM.EverlastingZeroKnowledge },
  { key := "merge-sse-def", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtractable },
  { key := "joint-sim-extraction-def", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtraction },
  { key := "merge-sse-rom-def", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtractableROM },
  { key := "merge-sse-conditions", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimExtracts },
  { key := "merge-sse-rom-conditions", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimExtractsROM },
  -- Series–parallel BCS: `thm:bcs-main`, its parts in the appendix, and the lemmas of their proofs.
  { key := "merkle-opening", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.MerkleOpening },
  { key := "per-leaf-opening", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.PerLeaf.opening },
  { key := "multiproof-opening", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.Multiproof.opening },
  { key := "multiproof-compress", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.Multiproof.compress_path },
  { key := "multiproof-decompress", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.Multiproof.check_decompress },
  { key := "multiproof-decompress-queries", label := "prot:generalized-bcs",
    decl := ``GordieHowe.SPBCS.Multiproof.trace_decompress_subset },
  { key := "merge-completeness-guarantees", label := "thm:bcs-main",
    decl := ``GordieHowe.SPBCS.completenessGuarantees },
  { key := "merge-zk-guarantees", label := "thm:bcs-main",
    decl := ``GordieHowe.SPBCS.privacyGuarantees },
  { key := "merge-knowledge-guarantees", label := "thm:bcs-main",
    decl := ``GordieHowe.SPBCS.knowledgeGuarantees },
  { key := "sim-extractability-joint", label := "thm:bcs-main",
    decl := ``GordieHowe.SPBCS.KnowledgeGuarantees.weak_online_simulation_extractability_qrom },
  { key := "merge-complete-fixed", label := "thm:bcs-complete",
    decl := ``GordieHowe.SPBCS.prob_not_accepts_prove_le },
  { key := "merge-complete-coins", label := "thm:bcs-complete",
    decl := ``GordieHowe.SPBCS.prob_not_accepts_prove_coins_le },
  { key := "merge-complete-adaptive-qrom", label := "thm:bcs-complete",
    decl := ``GordieHowe.SPBCS.complete_qrom },
  { key := "merge-complete-adaptive-rom", label := "thm:bcs-complete",
    decl := ``GordieHowe.SPBCS.complete_rom },
  { key := "merge-knowledge-bound", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.knowledgeBound },
  { key := "qverifier-online-extracts", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.QROM.onlineExtracts },
  { key := "merge-online-extracts-q", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.onlineExtracts_qrom },
  { key := "knowledge-guarantees-struct", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.KnowledgeGuarantees },
  { key := "knowledge-model-state", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.KnowledgeGuarantees.state_clause_qrom },
  { key := "merge-joint-bound", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.jointBound },
  { key := "rverifier-online-extracts", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.ROM.onlineExtracts },
  { key := "merge-online-extracts-r", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.onlineExtracts_rom },
  { key := "qverifier-soundness", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.QROM.soundness },
  { key := "merge-soundness-q", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.soundness_qrom },
  { key := "rverifier-soundness", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.ROM.soundness },
  { key := "merge-soundness-r", label := "thm:bcs-ks",
    decl := ``GordieHowe.SPBCS.soundness_rom },
  { key := "merge-zk-qrom", label := "thm:bcs-zk",
    decl := ``GordieHowe.SPBCS.everlastingZeroKnowledge_qrom },
  { key := "merge-zk-rom", label := "thm:bcs-zk",
    decl := ``GordieHowe.SPBCS.everlastingZeroKnowledge_rom },
  { key := "merge-wi-length", label := "thm:bcs-wi",
    decl := ``GordieHowe.SPBCS.unconditionallyWitnessIndistinguishable },
  { key := "merge-wi-advantage", label := "thm:bcs-wi",
    decl := ``GordieHowe.SPBCS.wiAdvantage_le },
  { key := "merge-sse-joint", label := "thm:bcs-se",
    decl := ``GordieHowe.SPBCS.weak_online_simulation_extractability_qrom },
  { key := "merge-sse-rom", label := "thm:bcs-se",
    decl := ``GordieHowe.SPBCS.weak_online_simulation_extractability_rom },
  { key := "joint-weak-sim-extraction", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtraction.unruhSimExtraction },
  { key := "merge-sse-fresh", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtractable.unruhSimExtraction_of_queryFreeTest },
  { key := "merge-cl06", label := "def:bcs-se",
    decl := ``GordieHowe.SPBCS.WeakOnlineSimulationExtractable.cl06Extraction },
  { key := "merge-oracle-test", label := "sec:bcs-thm",
    decl := ``GordieHowe.SPBCS.oracleTest_eq6_fails_eventually },
  { key := "merge-instab-union", label := "lem:sse-instability",
    decl := ``GordieHowe.SPBCS.instab_bad_union_le },
  { key := "merge-cond-instab", label := "lem:sse-instability",
    decl := ``GordieHowe.SPBCS.condInstab_bad_le },
  { key := "qrom-instab-collision", label := "lem:sse-instability",
    decl := ``GordieHowe.QROM.instab_digestCollision_le },
  { key := "merge-db-prob", label := "lem:sse-instability",
    decl := ``GordieHowe.SPBCS.dbProb_bad_union_le_of_queryCount },
  { key := "tp-query-count", label := "lem:sse-instability",
    decl := ``GordieHowe.Quantum.AdaptiveIAlg.tpQueryCount },
  { key := "merge-cover", label := "lem:sse-cover",
    decl := ``GordieHowe.SPBCS.cover_simExtGame },
  -- The proof system: composition, the subprotocols, ring switching and `thm:backend`.
  { key := "causal-rbr-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalRBRStmt.seq },
  { key := "causal-rbr-indep", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalRBRStmt.par },
  { key := "causal-completeness-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalComplete.seq },
  { key := "causal-completeness-indep", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalComplete.par },
  { key := "causal-hvzk-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalHVZK.seq },
  { key := "causal-hvzk-indep", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.CausalHVZK.par },
  { key := "red-rbr-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.RBR.seq },
  { key := "red-rbr-par", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.RBR.par },
  { key := "red-complete-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.Complete.seq },
  { key := "red-complete-par", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.Complete.par },
  { key := "red-hvzk-seq", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.HVZK.seq },
  { key := "red-hvzk-par", label := "lem:red-sp",
    decl := ``GordieHowe.IOP.Reduction.HVZK.par },
  { key := "logup-weighted", label := "lem:logup-point",
    decl := ``GordieHowe.Range.weightedArgument_prob_le },
  { key := "logup-weighted-complete", label := "lem:logup-point",
    decl := ``GordieHowe.Range.weightedArgument_complete },
  { key := "logup-committed", label := "lem:logup-point",
    decl := ``GordieHowe.Range.committedArgument_prob_le },
  { key := "logup-committed-complete", label := "lem:logup-point",
    decl := ``GordieHowe.Range.committedArgument_complete },
  { key := "logup-group", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.needlesIn_or_logupBad },
  { key := "lookup-holds", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.memHolds_of_lookup },
  { key := "phase-event-bound", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.eventBound_lowering },
  { key := "real-error", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.realError },
  { key := "phase-uniform", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.honestRun_uniform_of_respectsReads },
  { key := "phase-uniform-layout", label := "lem:phases",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.PhaseLayout.PadOrder.honestRun_uniform },
  { key := "honest-of-exec", label := "lem:core-red",
    decl := ``GordieHowe.RealizedProgram.HonestCore.ofCompletion },
  { key := "batch-merged-sound", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.fusedSound },
  { key := "batch-merged-honest", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.fusedHonest },
  { key := "batch-merged-error-sum", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.fusedError_sum },
  { key := "batch-merged-hvzk", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.fusedHvzk },
  { key := "batch-merged-error-first", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.fusedError_gammaRho },
  { key := "batch-merged-sep-sound", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.sound },
  { key := "batch-merged-sep-honest", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.honest },
  { key := "batch-merged-sep-hvzk", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.hvzk },
  { key := "batch-merged-sep-error-sum", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.error_sum },
  { key := "batch-merged-bits-sound", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.bitSumcheckSound },
  { key := "batch-merged-bits-hvzk", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.bitHvzk },
  { key := "batch-merged-bits-error-sum", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.bitError_sum },
  { key := "batch-sound", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.AffineBatch.sound },
  { key := "batch-honest", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.AffineBatch.honest },
  { key := "bit-sumcheck-sound", label := "lem:bit-sumcheck",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Sound.bitSumcheck },
  { key := "bit-sumcheck-rounds", label := "lem:bit-sumcheck",
    decl := ``GordieHowe.BitSumcheck.sound },
  { key := "bit-sumcheck-honest", label := "lem:bit-sumcheck",
    decl := ``GordieHowe.BitSumcheck.claims_honest },
  { key := "bit-sumcheck-hvzk", label := "lem:bit-sumcheck",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Honest.SimBijective.bitSumcheck },
  { key := "batch-bits-hvzk", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.AffineBatch.bitHvzk },
  { key := "batch-bits-sound", label := "lem:batch",
    decl := ``GordieHowe.BatchedZerocheck.AffineBatch.bitSumcheckSound },
  { key := "gkr-sound", label := "lem:gkr",
    decl := ``GordieHowe.GKR.LayeredCircuit.maskedSound },
  { key := "gkr-honest", label := "lem:gkr",
    decl := ``GordieHowe.GKR.LayeredCircuit.maskedHonest },
  { key := "gkr-hvzk", label := "lem:gkr",
    decl := ``GordieHowe.GKR.LayeredCircuit.hvzk },
  { key := "gkr-error-sum", label := "lem:gkr",
    decl := ``GordieHowe.GKR.LayeredCircuit.error_sum },
  { key := "stage-measure", label := "prot:bits",
    decl := ``GordieHowe.FieldProof.MaskedReduction.measure },
  { key := "squaring-chain-masks", label := "prot:bits",
    decl := ``GordieHowe.MaskScheme.squaringChainOver },
  { key := "stage-sound", label := "lem:bits-sound",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Sound.measure },
  { key := "stage-honest", label := "lem:bits-sound",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Honest.measure },
  { key := "squaring-chain-honest", label := "lem:bits-sound",
    decl := ``GordieHowe.MaskScheme.squaringChainOverHonest },
  { key := "squaring-chain-commits", label := "lem:bits-sound",
    decl := ``GordieHowe.MaskScheme.squaringChainOverHonest_commits },
  { key := "chain-mask-kit", label := "lem:bits-sound",
    decl := ``GordieHowe.MaskKit.chain },
  { key := "tree-reduces", label := "thm:tree",
    decl := ``GordieHowe.RingSwitching.Tree.reduces },
  { key := "tree-complete", label := "thm:tree",
    decl := ``GordieHowe.RingSwitching.Tree.complete },
  { key := "tree-hvzk", label := "thm:tree",
    decl := ``GordieHowe.RingSwitching.Tree.hvzk },
  { key := "tower-reduces", label := "cor:tower",
    decl := ``GordieHowe.RingSwitching.TowerSetup.reduces },
  { key := "tower-complete", label := "cor:tower",
    decl := ``GordieHowe.RingSwitching.TowerSetup.complete },
  { key := "tower-hvzk", label := "cor:tower",
    decl := ``GordieHowe.RingSwitching.TowerSetup.hvzk },
  { key := "backend-rbr", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.rbr_knowledge_soundness },
  { key := "backend-completeness", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.completeness },
  { key := "backend-hvzk", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.hvzk },
  { key := "fork-causal-rbr", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.causal_rbr_knowledge_soundness },
  { key := "fork-completeness", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness },
  { key := "fork-hvzk", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk },
  { key := "fork-completeness-coins", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.completeness_coins },
  { key := "fork-hvzk-coins", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.hvzk_coins },
  { key := "source-coin-complete", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.SourceComplete.coinComplete },
  { key := "honest-complete", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.HonestStrategy.complete },
  { key := "field-proof", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.fieldProof },
  { key := "field-sound", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.fieldSound },
  { key := "of-field-proofs", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.ofFieldProofs },
  { key := "field-forks", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.fieldBranches },
  { key := "packing-class", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.FieldInterp.Packing },
  { key := "packing-exists", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.FieldInterp.exists_packing_realizes },
  { key := "fieldok-mono", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.fieldOkB_mono },
  { key := "fieldok-generic", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.fieldOkB_generic },
  { key := "field-ready-generic", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.FieldReady.generic },
  { key := "tree-masking", label := "thm:backend",
    decl := ``GordieHowe.Ligero.MaskRow.TreeLayout.Masking },
  { key := "interp-model", label := "thm:backend",
    decl := ``GordieHowe.RealizedProgram.Interp.Model },
  { key := "circuits-enforce", label := "sec:formal-assumptions",
    decl := ``GordieHowe.RealizedProgram.CircuitsEnforce },
  { key := "circuits-accept", label := "sec:formal-assumptions",
    decl := ``GordieHowe.RealizedProgram.CircuitsAccept },
  -- Ligero: correlated agreement, the lemmas with and without the mask test, and Longfellow's order.
  { key := "johnson-line-certificate", label := "lem:mca-certificate",
    decl := ``GordieHowe.RSCode.lineCertificate_of_surplus },
  { key := "arklib-weighted-johnson", label := "lem:mca-certificate",
    decl := ``ReedSolomon.HiddenDerivative.exists_weighted_johnson_symbolic_certificate },
  { key := "johnson-line-closed", label := "lem:mca-instances",
    decl := ``GordieHowe.RSCode.lineCertificate_johnson },
  { key := "arklib-johnson-closed", label := "lem:mca-instances",
    decl := ``ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil },
  { key := "unique-decoding-line", label := "lem:mca-instances",
    decl := ``GordieHowe.RSCode.lineCertificate_uniqueDecoding },
  { key := "ligero-sound", label := "lem:ligero",
    decl := ``GordieHowe.Ligero.MaskTest.sound },
  { key := "ligero-complete", label := "lem:ligero",
    decl := ``GordieHowe.Ligero.MaskTest.complete },
  { key := "ligero-hvzk", label := "lem:ligero",
    decl := ``GordieHowe.Ligero.MaskTest.hvzk },
  { key := "untested-columns", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.selected_query_count },
  { key := "untested-bad-challenges", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.constraint_bad_count },
  { key := "untested-linear-columns", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.linear_query_count },
  { key := "untested-linear-bad", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.linear_bad_count },
  { key := "untested-quad-columns", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.quad_query_count },
  { key := "untested-quad-bad", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.quad_bad_count },
  { key := "untested-sound", label := "cor:untested-ligero",
    decl := ``GordieHowe.Ligero.UntestedMask.sound },
  { key := "untested-complete", label := "cor:untested-ligero",
    decl := ``GordieHowe.Ligero.UntestedMask.complete },
  { key := "untested-hvzk", label := "cor:untested-ligero",
    decl := ``GordieHowe.Ligero.UntestedMask.hvzk },
  { key := "untested-johnson-params", label := "lem:untested-masks",
    decl := ``GordieHowe.Ligero.UntestedMaskRow.Parameters.of_johnsonAgreement },
  { key := "ligero-lf-rbr", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.rbr_knowledge_soundness },
  { key := "ligero-lf-extractor", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.extractor },
  { key := "ligero-lf-state", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.stateFn },
  { key := "interleaved-list-le", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.InterleavedAgreementList.card_le },
  { key := "interleaved-list-le-one", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.InterleavedAgreementList.card_le_one },
  { key := "ligero-lf-data-list-le", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.card_dataList_le },
  { key := "ligero-lf-data-list-le-one", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.card_dataList_le_one },
  { key := "ligero-lf-data-list-proj", label := "lem:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.succ_mem_dataList },
  { key := "v7-hash-error", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.hash_error_le },
  { key := "v7-hash-joint", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.hashJoint_le },
  { key := "v7-hash-column", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.hashColumn_le },
  { key := "v7-sig-error", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.sig_error_le },
  { key := "v7-sig-joint", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.sigJoint_le },
  { key := "v7-sig-column", label := "app:ligero-lf-order",
    decl := ``GordieHowe.Ligero.LongfellowOrder.V7.sigColumn_le },
  -- Counterexamples to the published analyses of Ligero's tests, and the supplied step.
  { key := "ahiv22-b9-false-two", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.lemmaB9_false_two },
  { key := "ahiv22-b9-false-one", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.lemmaB9_false_one },
  { key := "ahiv22-appc-false-two", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.appCQuadratic_false_two },
  { key := "ahiv22-appc-false-one", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.appCQuadratic_false_one },
  { key := "ahiv22-lemma414", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.UntestedMasks.lemma414 },
  { key := "ahiv22-headline", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.AHIV22.UntestedMasks.Setup.acceptProb_le_of_not_satisfiable },
  { key := "chvy25-thm44-false", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.CHVY25.theorem44_false },
  { key := "chvy25-thm44-false-ncol", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.CHVY25.theorem44_false_ncol },
  { key := "chvy25-summed-false", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.CHVY25.Family.theorem44Summed_false_family },
  { key := "chvy25-summed-false-ncol", label := "app:ligero-errata",
    decl := ``GordieHowe.Errata.CHVY25.Family.theorem44Summed_false_family_ncol },
  -- `thm:e2e` for every realized program, with the proofs over each field, and its errors.
  { key := "e2e-generic", label := "thm:e2e",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e },
  { key := "e2e-generic-knowledge", label := "thm:e2e",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge },
  { key := "e2e-guarantees", label := "thm:e2e",
    decl := ``GordieHowe.SPBCS.ProofSystemTranscript.Guarantees },
  { key := "e2e-source", label := "thm:e2e",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_source },
  { key := "e2e-coins", label := "thm:e2e",
    decl := ``GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_coins },
  { key := "e2e-coin-guarantees", label := "thm:e2e",
    decl := ``GordieHowe.SPBCS.ProofSystemTranscript.CoinGuarantees },
  { key := "knowledge-error-eq", label := "thm:e2e",
    decl := ``GordieHowe.SPBCS.knowledgeError_eq },
  -- `thm:e2e` for the proofs of possession of ML-DSA-44 at the ROM parameters
  -- (`MLDSA44.Emulated.ROMParams`) and the QROM parameters (`MLDSA44.Emulated.QROMParams`),
  -- instances of `e2e`; the templates are also checked for Falcon-512's
  -- (`Falcon512.Native.ROMParams`, `Falcon512.Native.QROMParams`, the companion paper).
  { key := "mldsa-source-rbr-rom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.ROMParams.source_rbr_knowledge_soundness },
  { key := "mldsa-source-rbr-qrom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.QROMParams.source_rbr_knowledge_soundness },
  { key := "mldsa-honest-rom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.ROMParams.honestStrategy },
  { key := "mldsa-honest-qrom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.QROMParams.honestStrategy },
  { key := "mldsa-max-error-rom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.ROMParams.maxRoundError_le },
  { key := "mldsa-max-error-qrom", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.Emulated.QROMParams.maxRoundError_le },
  { key := "cfg-completeness-adaptive-qrom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.AdaptiveCompleteness.completeness_adaptive_qrom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.completeness_adaptive_qrom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.completeness_adaptive_qrom,
      ``GordieHowe.Falcon512.Native.ROMParams.completeness_adaptive_qrom,
      ``GordieHowe.Falcon512.Native.QROMParams.completeness_adaptive_qrom] },
  { key := "cfg-completeness-adaptive-rom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.AdaptiveCompleteness.completeness_adaptive_rom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.completeness_adaptive_rom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.completeness_adaptive_rom,
      ``GordieHowe.Falcon512.Native.ROMParams.completeness_adaptive_rom,
      ``GordieHowe.Falcon512.Native.QROMParams.completeness_adaptive_rom] },
  { key := "cfg-completeness", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.completeness,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.completeness,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.completeness,
      ``GordieHowe.Falcon512.Native.ROMParams.completeness,
      ``GordieHowe.Falcon512.Native.QROMParams.completeness] },
  { key := "cfg-completeness-of-rel", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.PaperRelation.completeness_of_rel,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.completeness_of_rel,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.completeness_of_rel,
      ``GordieHowe.Falcon512.Native.ROMParams.completeness_of_rel,
      ``GordieHowe.Falcon512.Native.QROMParams.completeness_of_rel] },
  { key := "cfg-honest-input-of-rel", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.PaperRelation.honest_input_of_rel,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.honest_input_of_rel,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.honest_input_of_rel,
      ``GordieHowe.Falcon512.Native.ROMParams.honest_input_of_rel,
      ``GordieHowe.Falcon512.Native.QROMParams.honest_input_of_rel] },
  { key := "mldsa-valid-of-witness", label := "thm:e2e",
    decl := ``GordieHowe.MLDSA44.PoP.HonestInput.valid_ofWitness },
  { key := "cfg-completeness-honest", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.completeness_honest,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.completeness_honest,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.completeness_honest,
      ``GordieHowe.Falcon512.Native.ROMParams.completeness_honest,
      ``GordieHowe.Falcon512.Native.QROMParams.completeness_honest] },
  { key := "cfg-knowledge-soundness", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.knowledge_soundness_qrom_at,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.knowledge_soundness_qrom_at,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.knowledge_soundness_qrom_at,
      ``GordieHowe.Falcon512.Native.ROMParams.knowledge_soundness_qrom_at,
      ``GordieHowe.Falcon512.Native.QROMParams.knowledge_soundness_qrom_at] },
  { key := "cfg-soundness", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.soundness_qrom_at,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.soundness_qrom_at,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.soundness_qrom_at,
      ``GordieHowe.Falcon512.Native.ROMParams.soundness_qrom_at,
      ``GordieHowe.Falcon512.Native.QROMParams.soundness_qrom_at] },
  { key := "cfg-knowledge-soundness-rom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.knowledge_soundness_rom_at,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.knowledge_soundness_rom_at,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.knowledge_soundness_rom_at,
      ``GordieHowe.Falcon512.Native.ROMParams.knowledge_soundness_rom_at,
      ``GordieHowe.Falcon512.Native.QROMParams.knowledge_soundness_rom_at] },
  { key := "cfg-soundness-rom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.soundness_rom_at,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.soundness_rom_at,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.soundness_rom_at,
      ``GordieHowe.Falcon512.Native.ROMParams.soundness_rom_at,
      ``GordieHowe.Falcon512.Native.QROMParams.soundness_rom_at] },
  { key := "cfg-zero-knowledge", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.everlasting_zero_knowledge_qrom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.everlasting_zero_knowledge_qrom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.everlasting_zero_knowledge_qrom,
      ``GordieHowe.Falcon512.Native.ROMParams.everlasting_zero_knowledge_qrom,
      ``GordieHowe.Falcon512.Native.QROMParams.everlasting_zero_knowledge_qrom] },
  { key := "cfg-zero-knowledge-rom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.everlasting_zero_knowledge_rom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.everlasting_zero_knowledge_rom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.everlasting_zero_knowledge_rom,
      ``GordieHowe.Falcon512.Native.ROMParams.everlasting_zero_knowledge_rom,
      ``GordieHowe.Falcon512.Native.QROMParams.everlasting_zero_knowledge_rom] },
  { key := "cfg-zero-knowledge-honest", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.everlasting_zero_knowledge_honest_qrom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.everlasting_zero_knowledge_honest_qrom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.everlasting_zero_knowledge_honest_qrom,
      ``GordieHowe.Falcon512.Native.ROMParams.everlasting_zero_knowledge_honest_qrom,
      ``GordieHowe.Falcon512.Native.QROMParams.everlasting_zero_knowledge_honest_qrom] },
  { key := "cfg-wi", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.unconditional_witness_indistinguishability,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.unconditional_witness_indistinguishability,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.unconditional_witness_indistinguishability,
      ``GordieHowe.Falcon512.Native.ROMParams.unconditional_witness_indistinguishability,
      ``GordieHowe.Falcon512.Native.QROMParams.unconditional_witness_indistinguishability] },
  { key := "cfg-sse-online", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.weak_online_simulation_extractability_qrom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.weak_online_simulation_extractability_qrom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.weak_online_simulation_extractability_qrom,
      ``GordieHowe.Falcon512.Native.ROMParams.weak_online_simulation_extractability_qrom,
      ``GordieHowe.Falcon512.Native.QROMParams.weak_online_simulation_extractability_qrom] },
  { key := "cfg-sse", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.unruh_simulation_extractability_qrom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.unruh_simulation_extractability_qrom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.unruh_simulation_extractability_qrom,
      ``GordieHowe.Falcon512.Native.ROMParams.unruh_simulation_extractability_qrom,
      ``GordieHowe.Falcon512.Native.QROMParams.unruh_simulation_extractability_qrom] },
  -- `tab:eval-params`, the zero-knowledge column: the bit security of everlasting zero knowledge
  -- for the proofs of possession of ML-DSA-44 (and of Falcon-512, the companion paper's).
  { key := "mldsa-zk-bits-rom", label := "tab:eval-params",
    decl := ``GordieHowe.MLDSA44.Emulated.ROMParams.zero_knowledge_bits_rom,
    instances := [``GordieHowe.Falcon512.Native.ROMParams.zero_knowledge_bits_rom] },
  { key := "mldsa-zk-bits-qrom", label := "tab:eval-params",
    decl := ``GordieHowe.MLDSA44.Emulated.QROMParams.zero_knowledge_bits_qrom,
    instances := [``GordieHowe.Falcon512.Native.QROMParams.zero_knowledge_bits_qrom] },
  { key := "cfg-sse-rom", label := "thm:e2e",
    decl := ``GordieHowe.Configuration.Common.weak_online_simulation_extractability_rom,
    instances := [
      ``GordieHowe.MLDSA44.Emulated.ROMParams.weak_online_simulation_extractability_rom,
      ``GordieHowe.MLDSA44.Emulated.QROMParams.weak_online_simulation_extractability_rom,
      ``GordieHowe.Falcon512.Native.ROMParams.weak_online_simulation_extractability_rom,
      ``GordieHowe.Falcon512.Native.QROMParams.weak_online_simulation_extractability_rom] },
  -- Definitions and lemmas of the background, the relation language, the compiler, the proof
  -- system and the appendices, in the paper's order.
  { key := "rel-trace", label := "def:frob-trace",
    decl := ``GordieHowe.RelativePacking.relTrace },
  { key := "stage-basis", label := "def:dual-basis",
    decl := ``GordieHowe.PackingStage.StageBasis },
  { key := "stage-pack", label := "def:pack",
    decl := ``GordieHowe.PackingStage.StageBasis.pack },
  { key := "stage-unpack", label := "def:pack",
    decl := ``GordieHowe.PackingStage.StageBasis.coord },
  { key := "unpack-tower", label := "lem:unpack-tower",
    decl := ``GordieHowe.PackingStage.unpack_tower },
  { key := "stage-twist", label := "def:twist",
    decl := ``GordieHowe.PackingStage.StageBasis.form },
  { key := "rs-code", label := "def:rs",
    decl := ``GordieHowe.RSCode },
  { key := "arklib-unique-decoding", label := "def:unique-decoding",
    decl := ``Code.uniqueDecodingRadius },
  { key := "arklib-unique-decoding-rs", label := "def:unique-decoding",
    decl := ``ReedSolomon.uniqueDecodingRadius_RS_eq },
  { key := "johnson-exception-closed", label := "lem:mca-instances",
    decl := ``ReedSolomon.HiddenDerivative.johnsonExceptionCount_lt_closed },
  { key := "line-certificate", label := "def:mca",
    decl := ``GordieHowe.RSCode.LineCertificate },
  { key := "iop", label := "def:iop",
    decl := ``GordieHowe.IOP.IOP },
  { key := "sp-before", label := "def:sp-order",
    decl := ``GordieHowe.IOP.SPTerm.Leaf.Before },
  { key := "claim-conj", label := "def:claims",
    decl := ``GordieHowe.IOP.relConj },
  { key := "out-holds", label := "def:claims",
    decl := ``GordieHowe.FieldProof.MaskedReduction.OutHolds },
  { key := "rows-hold", label := "def:claims",
    decl := ``GordieHowe.RowsHold },
  { key := "red-seq", label := "def:red-comp",
    decl := ``GordieHowe.IOP.Reduction.seq },
  { key := "red-par", label := "def:red-comp",
    decl := ``GordieHowe.IOP.Reduction.par },
  { key := "index-map", label := "def:o-tensor",
    decl := ``GordieHowe.RealizedProgram.IndexMap },
  { key := "ir-value", label := "def:o-vars",
    decl := ``GordieHowe.RealizedProgram.Value },
  { key := "ir-expr", label := "def:o-expr",
    decl := ``GordieHowe.RealizedProgram.Expr },
  { key := "eval-int", label := "def:o-int-expr",
    decl := ``GordieHowe.RealizedProgram.evalIntWith },
  { key := "holds-with", label := "def:o-preds",
    decl := ``GordieHowe.RealizedProgram.HoldsWith },
  { key := "ir-program", label := "def:o-programs",
    decl := ``GordieHowe.RealizedProgram },
  { key := "challenge-order", label := "def:o-phases",
    decl := ``GordieHowe.RealizedProgram.ChallengeOrder },
  { key := "is-late", label := "def:o-late",
    decl := ``GordieHowe.RealizedProgram.IsLate },
  { key := "statement-in", label := "def:o-semantics",
    decl := ``GordieHowe.RealizedProgram.StatementIn },
  { key := "source-accepting", label := "def:o-semantics",
    decl := ``GordieHowe.RealizedProgram.SourceAcceptingAt },
  { key := "source-exec-env", label := "def:o-semantics",
    decl := ``GordieHowe.RealizedProgram.SourceProver.execEnvAt },
  { key := "expr-ivl", label := "def:interval",
    decl := ``GordieHowe.RealizedProgram.Expr.ivl },
  { key := "mod-one-digit", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_oneDigit },
  { key := "mod-digits", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_digits },
  { key := "mod-committed", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_committed },
  { key := "mod-grouped", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_grouped },
  { key := "mod-integer", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_fieldEq },
  { key := "mod-field", label := "lem:core-mod",
    decl := ``GordieHowe.RealizedProgram.holdsWith_mod_of_field },
  { key := "grouped-mod", label := "def:mod-parts",
    decl := ``GordieHowe.RealizedProgram.GroupedMod },
  { key := "conv-matrix", label := "def:macconv",
    decl := ``GordieHowe.Conv.matrix },
  { key := "conv-max", label := "def:macconv",
    decl := ``GordieHowe.Conv.convMax },
  { key := "mac-realization", label := "def:mac-record",
    decl := ``GordieHowe.RealizedProgram.MacRealization },
  { key := "mac-cross-hosted", label := "lem:core-mac",
    decl := ``GordieHowe.RealizedProgram.crossHolds_or_macBad_of },
  { key := "mac-cross-unhosted", label := "lem:core-mac",
    decl := ``GordieHowe.RealizedProgram.crossHolds_or_macBad_twoTail_of },
  { key := "mac-binding-prob", label := "lem:core-mac",
    decl := ``GordieHowe.MAC.probUniform_bindingEvent_le },
  { key := "mac-binding", label := "lem:poly-mac",
    decl := ``GordieHowe.MAC.binding },
  { key := "logup-outside", label := "lem:logup",
    decl := ``GordieHowe.Range.committedBadPoly_ne_zero_of_outside },
  { key := "logup-histogram", label := "lem:logup",
    decl := ``GordieHowe.Range.committedBadPoly_rowHistogram },
  { key := "twist-identity", label := "lem:twist",
    decl := ``GordieHowe.PackingStage.StageBasis.linear_identity },
  { key := "packing-tree", label := "def:packing-tree",
    decl := ``GordieHowe.RingSwitching.Tree },
  { key := "realized-program", label := "def:plan",
    decl := ``GordieHowe.RealizedProgram },
  { key := "tree-spec", label := "def:o-admissible",
    decl := ``GordieHowe.TreeSpec },
  { key := "subfield-test", label := "lem:subfield-test",
    decl := ``GordieHowe.Ligero.SubfieldTest.card_filter_mem_le_of_agrees },
  { key := "ligero-commit-error", label := "def:ligero-errors",
    decl := ``GordieHowe.Ligero.AgreementThreshold.Threshold.commitError },
  { key := "ligero-mask-test-error", label := "def:ligero-errors",
    decl := ``GordieHowe.Ligero.MaskTest.error },
  { key := "ligero-untested-error", label := "def:ligero-errors",
    decl := ``GordieHowe.Ligero.UntestedMask.error },
  { key := "wi-def", label := "def:narg-wi",
    decl := ``GordieHowe.SPBCS.WitnessIndistinguishableOfLength },
  { key := "combine-sound", label := "lem:combine",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Sound.combine },
  { key := "combine-honest", label := "lem:combine",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Honest.combine },
  { key := "expr-deg", label := "def:o-degree",
    decl := ``GordieHowe.RealizedProgram.exprDeg },
  { key := "rbr-knowledge-soundness", label := "def:o-guarantees",
    decl := ``GordieHowe.IOP.rbrKnowledgeSoundness },
  { key := "source-extractor", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.sourceExtractor },
  { key := "rbr-paper-of-source", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.rbr_paper_of_source },
  { key := "rbr-source-of-paper", label := "def:o-guarantees",
    decl := ``GordieHowe.RealizedProgram.rbr_source_of_paper },
  { key := "source-spec", label := "def:o-ip",
    decl := ``GordieHowe.RealizedProgram.sourceSpec },
  { key := "source-verifier", label := "def:o-ip",
    decl := ``GordieHowe.RealizedProgram.sourceVerifier },
  { key := "perm-check", label := "lem:o-multiset",
    decl := ``GordieHowe.PermutationEvent.multiset_eq_or_badAt },
  { key := "perm-check-bound", label := "lem:o-multiset",
    decl := ``GordieHowe.ChallengeEvent.probUniform_badAt_le },
  { key := "mset-encoding", label := "lem:o-multiset",
    decl := ``GordieHowe.PermutationEvent.probUniform_prodPoly_eq_le },
  { key := "mset-challenge", label := "lem:o-multiset",
    decl := ``GordieHowe.PermutationEvent.probUniform_mset_le_of_prodPoly_ne },
  { key := "mset-joint", label := "lem:o-multiset",
    decl := ``GordieHowe.PermutationEvent.probUniform_mset_joint_le },
  { key := "cells-sound", label := "lem:cells-sound",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Sound.measure },
  { key := "cells-honest", label := "lem:cells-sound",
    decl := ``GordieHowe.FieldProof.MaskedReduction.Honest.measure },
  { key := "subfield-mask-kit", label := "lem:cells-sound",
    decl := ``GordieHowe.MaskKit.subfield },
  { key := "agreement-list", label := "def:list",
    decl := ``GordieHowe.PolynomialAgreementList.candidates },
  { key := "johnson-agreement", label := "def:johnson-agreement",
    decl := ``GordieHowe.Ligero.MaskedConstraintList.johnsonAgreement },
  { key := "tableau-commitment", label := "def:tableau",
    decl := ``GordieHowe.Ligero.Tableau.Commitment },
  { key := "tableau-parameters", label := "def:tableau",
    decl := ``GordieHowe.Ligero.Tableau.Parameters },
  { key := "tableau-honest", label := "def:tableau",
    decl := ``GordieHowe.Ligero.HVZK.commitOf },
  { key := "mask-split-vanishing", label := "lem:mask-split",
    decl := ``GordieHowe.Ligero.MaskPieces.exists_splitting_vanishing },
  { key := "mask-split-kernel", label := "lem:mask-split",
    decl := ``GordieHowe.Ligero.MaskPieces.exists_kernel_eval },
  { key := "mask-split-three", label := "lem:mask-split",
    decl := ``GordieHowe.Ligero.MaskPieces.covers_three },
  { key := "mask-split-two", label := "lem:mask-split",
    decl := ``GordieHowe.Ligero.MaskPieces.not_covers_fin_two },
  { key := "batched-relation", label := "def:batched-relation",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch },
  { key := "batched-holds", label := "def:batched-relation",
    decl := ``GordieHowe.BatchedZerocheck.MergedAffineBatch.Holds },
  { key := "skip-points", label := "def:skip-domain",
    decl := ``GordieHowe.Sumcheck.FieldSkip.SkipPoints },
  { key := "mle", label := "def:mle",
    decl := ``GordieHowe.GKR.ClaimEvaluation.mle },
  { key := "eq-poly", label := "def:mle",
    decl := ``GordieHowe.EqPolynomial.eqPoly },
  { key := "skip-poly", label := "def:skip-poly",
    decl := ``GordieHowe.Sumcheck.FieldSkip.zeroPoly },
  { key := "layered-circuit", label := "def:layered-circuit",
    decl := ``GordieHowe.GKR.LayeredCircuit },
  { key := "layered-circuit-sat", label := "def:layered-circuit",
    decl := ``GordieHowe.GKR.LayeredCircuit.Satisfied },
  { key := "narg-prover", label := "def:narg",
    decl := ``GordieHowe.NARG.Prover },
  { key := "narg-verifier-qrom", label := "def:narg",
    decl := ``GordieHowe.NARG.QROM.Verifier },
  { key := "narg-verifier-rom", label := "def:narg",
    decl := ``GordieHowe.NARG.ROM.Verifier },
  { key := "narg-complete-qrom", label := "def:narg-complete",
    decl := ``GordieHowe.NARG.QROM.Complete },
  { key := "narg-complete-rom", label := "def:narg-complete",
    decl := ``GordieHowe.NARG.ROM.Complete },
  { key := "narg-ks-qrom", label := "def:narg-ks",
    decl := ``GordieHowe.NARG.QROM.Adversary.OnlineExtracts },
  { key := "narg-ks-rom", label := "def:narg-ks",
    decl := ``GordieHowe.NARG.ROM.Adversary.OnlineExtracts },
  { key := "narg-sound-qrom", label := "def:narg-sound",
    decl := ``GordieHowe.NARG.QROM.Adversary.acceptsFalse },
  { key := "narg-sound-rom", label := "def:narg-sound",
    decl := ``GordieHowe.NARG.ROM.Adversary.acceptsFalse },
  { key := "narg-zk-qrom", label := "def:narg-zk",
    decl := ``GordieHowe.NARG.QROM.ZeroKnowledge },
  { key := "narg-zk-rom", label := "def:narg-zk",
    decl := ``GordieHowe.NARG.ROM.ZeroKnowledge },
  { key := "bcs-kq", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.kqOf },
  { key := "bcs-sim-queries", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.simQueries },
  { key := "bcs-nj", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.Merges.nJ },
  { key := "bcs-overrun", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.Base.overrun },
  { key := "bcs-key-collision", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.keyCollision },
  { key := "bcs-leaf-bound", label := "def:bcs-quantities",
    decl := ``GordieHowe.SPBCS.leafBound },
  { key := "pad-coherent", label := "lem:pad-purify",
    decl := ``GordieHowe.Quantum.Alg.toQueryAlgCoh },
  { key := "query-count", label := "lem:pad-purify",
    decl := ``GordieHowe.QROM.QueryCount },
  { key := "lifting-count", label := "lem:pad-purify",
    decl := ``GordieHowe.QROM.Lifting.measured_le_of_queryCount },
  { key := "o2h-count", label := "lem:pad-purify",
    decl := ``GordieHowe.Quantum.O2HSetting.o2h_fresh_secret_of_count },
  { key := "ks-sound-qrom", label := "lem:ks-sound",
    decl := ``GordieHowe.NARG.QROM.Verifier.acceptsFalse_le_of_outcomeDistLE },
  { key := "ks-sound-rom", label := "lem:ks-sound",
    decl := ``GordieHowe.NARG.ROM.Adversary.acceptsFalse_le },
  { key := "block-oracle", label := "lem:block-oracle",
    decl := ``GordieHowe.SPBCS.QROM.extractionOutputState_eq },
  { key := "sim-ext-game", label := "def:bcs-base-game",
    decl := ``GordieHowe.SPBCS.simExtGame },
  -- Results from the literature that the formalization proves.
  { key := "sz", label := "lem:sz",
    decl := ``MvPolynomial.schwartz_zippel_totalDegree },
  { key := "johnson-bound", label := "lem:johnson",
    decl := ``GordieHowe.PolynomialAgreementList.card_candidates_le },
  { key := "arklib-mca-affine", label := "thm:mca-affine",
    decl := ``ReedSolomon.exists_affine_exceptionalSet_full_agreement_of_exactLine },
  { key := "zhandry-l3", label := "sec:formal-results",
    decl := ``GordieHowe.QROM.stO_eq },
  { key := "zhandry-l4", label := "sec:formal-results",
    decl := ``GordieHowe.QROM.simLaw_out },
  { key := "zhandry-l4-state", label := "sec:formal-results",
    decl := ``GordieHowe.QROM.reduce_simState },
  { key := "zhandry-l5", label := "sec:formal-results",
    decl := ``GordieHowe.QROM.oracle_sim_sets },
  { key := "cms19-lifting", label := "sec:formal-results",
    decl := ``GordieHowe.QROM.Lifting.basic_lifting },
  { key := "o2h-pure", label := "sec:formal-results",
    decl := ``GordieHowe.Quantum.O2HSetting.o2h },
  { key := "o2h-mixed", label := "sec:formal-results",
    decl := ``GordieHowe.Quantum.O2HSetting.o2h_mixed },
  { key := "interleaved-proximity", label := "sec:formal-results",
    decl := ``GordieHowe.InterleavedProximity.card_close_mul_le },
  { key := "berlekamp-welch", label := "sec:formal-results",
    decl := ``GordieHowe.RSCode.BerlekampWelch.decode_eq_some_iff },
  { key := "affine-proximity", label := "sec:formal-results",
    decl := ``GordieHowe.RSCode.affineProximity }
]
/-- **The rows of the formalization table** (`app:formal`), in order: a heading opens each group. -/
def appendixTable : List TableRow := [
  { heading := "Background (\\cref{sec:prelims,app:background-proofs})" },
  { statement := "\\Cref{lem:poly-mac}",
    lean := "{mac-binding}, {mac-binding-prob}" },
  { statement := "\\Cref{lem:logup}, with the denominators cleared",
    lean := "{logup-outside}, {logup-histogram}" },
  { statement := "\\Cref{def:frob-trace}",
    lean := "{rel-trace}" },
  { statement := "\\Cref{def:dual-basis}",
    lean := "{stage-basis}" },
  { statement := "\\Cref{def:pack}",
    lean := "{stage-pack}, {stage-unpack}" },
  { statement := "\\Cref{lem:unpack-tower}, with the basis as independence and membership in " ++
      "\\(T\\)",
    lean := "{unpack-tower}" },
  { statement := "\\Cref{def:twist}",
    lean := "{stage-twist}" },
  { statement := "\\Cref{lem:twist}",
    lean := "{twist-identity}" },
  { statement := "\\Cref{def:rs}, as the code's parameters with a unique-decoding radius",
    lean := "{rs-code}" },
  { statement := "\\Cref{def:unique-decoding}",
    lean := "ArkLib's {arklib-unique-decoding:full}, with {arklib-unique-decoding-rs:full}" },
  { statement := "\\Cref{def:mca}",
    lean := "{line-certificate}" },
  { statement := "\\Cref{lem:mca-instances}",
    lean := "part~(1): {johnson-line-closed}, with ArkLib's closed form " ++
      "{johnson-exception-closed:full}; part~(2): {unique-decoding-line}" },
  { statement := "\\Cref{lem:mca-certificate}",
    lean := "{johnson-line-certificate}" },
  { statement := "\\Cref{def:iop}, the verifier of a public-coin IOP with challenge-determined " ++
      "queries",
    lean := "{iop}" },
  { statement := "\\Cref{def:sp-order}",
    lean := "{sp-before}" },
  { statement := "\\Cref{def:iop-schedule}",
    lean := "{sp-term}, {causal-iop}" },
  { statement := "\\Cref{def:iop-complete}",
    lean := "{causal-completeness-coins-def}" },
  { statement := "\\Cref{def:rbr}",
    lean := "{causal-rbr-def}" },
  { statement := "\\Cref{lem:rbr-total}",
    lean := "{rbr-total}" },
  { statement := "\\Cref{def:hvzk}",
    lean := "{causal-hvzk-def}" },
  { statement := "\\Cref{def:red,def:red-sec}",
    lean := "{committed-reduction}, {red-rbr-def}, {red-complete-def}, {red-hvzk-def}" },
  { statement := "\\Cref{def:claims}(1), (2) and~(4)",
    lean := "{rows-hold} (the projection onto the elements of the oracle input in one field), {out-holds} " ++
      "(claims at a value map), {claim-conj}" },
  { statement := "\\Cref{def:red-comp}",
    lean := "{red-seq}, {red-par}" },
  { statement := "\\Cref{lem:red-sp}",
    lean := "{red-rbr-seq}, {red-rbr-par}, {red-complete-seq}, {red-complete-par}, " ++
      "{red-hvzk-seq}, {red-hvzk-par}" },
  { statement := "\\Cref{lem:red-sp}, for public-coin IOPs with input and output claims and no " ++
      "pass-through part",
    lean := "{causal-rbr-seq}, {causal-rbr-indep}, {causal-completeness-seq}, " ++
      "{causal-completeness-indep}, {causal-hvzk-seq}, {causal-hvzk-indep}" },
  { statement := "\\Cref{lem:red-prefix}",
    lean := "{red-prefix}" },
  { statement := "\\Cref{lem:combine}, composed in series after a reduction",
    lean := "{combine-sound}, {combine-honest}" },
  { heading := "The relation language (\\cref{sec:o-language,app:language})" },
  { statement := "\\Cref{def:o-tensor}",
    lean := "{index-map}" },
  { statement := "\\Cref{def:o-vars}",
    lean := "{ir-value}" },
  { statement := "\\Cref{def:o-expr}",
    lean := "{ir-expr}" },
  { statement := "\\Cref{def:o-int-expr}",
    lean := "{eval-int}" },
  { statement := "\\Cref{def:o-preds}, with \\(\\pshare(x, y)\\) stating that every entry of " ++
      "\\(y\\) is below \\(2^w\\) and that, if every entry of \\(x\\) is below \\(2^w\\), " ++
      "\\(x\\) and \\(y\\) represent equal naturals. When \\(x\\) holds bits, this is " ++
      "\\(\\pshare(x, y)\\)",
    lean := "{holds-with}" },
  { statement := "\\Cref{def:o-programs}, with the honest prover's randomized functions " ++
      "supplied",
    lean := "{ir-program:1}" },
  { statement := "\\Cref{def:o-phases}",
    lean := "{challenge-order}" },
  { statement := "\\Cref{def:o-late}",
    lean := "{is-late}" },
  { statement := "\\Cref{def:o-semantics}, with the honest prover's randomized functions " ++
      "supplied, with statements that pass the program's membership checks and with no " ++
      "type-set condition on their values",
    lean := "{statement-in}, {source-accepting}, {source-exec-env}" },
  { statement := "\\Cref{def:o-honest} and \\cref{def:o-guarantees}(1), with the honest " ++
      "prover's randomized functions supplied, with acceptance including the field equations " ++
      "of the field-form congruences",
    lean := "{source-prover}, {source-complete-def}" },
  { statement := "\\Cref{def:o-guarantees}(2)",
    lean := "{rbr-knowledge-soundness} at {source-verifier} and {source-extractor}; for the " ++
      "paper's \\(\\Pi_{\\Prog_0}\\), {rbr-paper-of-source}, {rbr-source-of-paper}" },
  { statement := "\\Cref{def:o-degree}, in one challenge",
    lean := "{expr-deg}" },
  { statement := "\\Cref{def:o-ip}, with the pads of the late values in the first message",
    lean := "{source-spec}, {source-verifier}" },
  { statement := "\\Cref{lem:o-multiset}(1), for records of arity~1",
    lean := "{perm-check}, with the bound {perm-check-bound}" },
  { statement := "\\Cref{lem:o-multiset}(2)",
    lean := "{mset-encoding}, {mset-challenge}, {mset-joint}" },
  { heading := "The compiler (\\cref{sec:compiler})" },
  { statement := "\\Cref{def:interval}, with one interval for all entries of an expression, " ++
      "for linear maps among the library's operators, and without \\(\\kpub\\) coefficients",
    lean := "{expr-ivl}" },
  { statement := "\\Cref{lem:core-mod}(1), (3) and~(4), from the equation in \\(\\K\\) to the " ++
      "predicate",
    lean := "part~(1), for a quotient computed from \\(e\\) and \\(e'\\): {mod-one-digit}; for " ++
      "a quotient committed as digits: {mod-digits}, {mod-committed}, {mod-grouped}; part~(3): " ++
      "{mod-integer}; part~(4): {mod-field}" },
  { statement := "\\Cref{def:mod-parts}, for the accumulators of a MAC",
    lean := "{grouped-mod}" },
  { statement := "\\Cref{def:macconv}",
    lean := "{conv-matrix}, {conv-max}" },
  { statement := "\\Cref{def:mac-record}",
    lean := "{mac-realization}" },
  { statement := "\\Cref{lem:core-mac}, part~(1) at the MACs of a realized program, with " ++
      "\\(\\pshare(x, y)\\) stating that every entry of \\(y\\) is below \\(2^w\\) and that, " ++
      "if every entry of \\(x\\) is below \\(2^w\\), \\(x\\) and \\(y\\) represent equal " ++
      "naturals",
    lean := "part~(1): {mac-cross-hosted}, {mac-cross-unhosted}; part~(2): {mac-binding-prob}" },
  { statement := "\\Cref{def:packing-tree}",
    lean := "{packing-tree}" },
  { statement := "\\Cref{def:plan}",
    lean := "{realized-program:1}" },
  { statement := "\\Cref{def:plan}, the condition that the realized program realizes its source " ++
      "program, checked from the certificates",
    lean := "{realizes}" },
  { statement := "\\Cref{def:plan-valid}, with further well-formedness conditions",
    lean := "{plan-valid}" },
  { heading := "The proof system (\\cref{sec:proof-system,app:pack-tree,app:batched-general," ++
      "app:gkr})" },
  { statement := "\\Cref{thm:backend}(1)",
    lean := "{fork-completeness-coins}, {fork-hvzk-coins}, from {source-coin-complete}; " ++
      "for a deterministic honest prover, at every value of the pads, {fork-completeness}, " ++
      "{fork-hvzk}; {honest-complete}" },
  { statement := "\\Cref{thm:backend}(2)",
    lean := "{fork-causal-rbr}" },
  { statement := "\\Cref{thm:backend}, for every finite field with an admissible packing tree " ++
      "(\\cref{def:packing-tree}), with tableaus with " ++
      "or without the mask test",
    lean := "{field-forks}, from {field-proof}, {field-sound} and {of-field-proofs}; the class " ++
      "{packing-class}, with every finite field in it by {packing-exists}; the exported " ++
      "checks {fieldok-mono}, {fieldok-generic}, {field-ready-generic}; the masking of each " ++
      "tableau, with its round errors, {tree-masking}; under the hypothesis {interp-model} " ++
      "that Lean's fields follow their specifications, the MAC fields have polynomial bases and " ++
      "the functions computed from the statement have their stated ranges, proved for each " ++
      "configuration" },
  { statement := "\\Cref{sec:formal-assumptions}, the assumptions on the compiled GKR circuits",
    lean := "{circuits-enforce}, {circuits-accept}" },
  { statement := "\\Cref{lem:logup-point}",
    lean := "parts (1) and (2): {logup-weighted}, {logup-weighted-complete}; part (3): " ++
      "{logup-committed}, {logup-committed-complete}" },
  { statement := "\\Cref{lem:phases}(1), as the bound on the events of the realization step in " ++
      "the proof of \\cref{thm:backend}",
    lean := "{phase-event-bound}, with the errors {real-error}; each group's LogUp identity, " ++
      "for a range table and by \\cref{lem:logup-point}(3) for any other table, {logup-group}; " ++
      "each direct lookup \\(\\pin(e, e')\\) from its groups' identities, for \\(e'\\) a range, " ++
      "a table, or an expression whose coordinates are the table's rows, {lookup-holds}" },
  { statement := "\\Cref{lem:core-red}(2)",
    lean := "{honest-of-exec}" },
  { statement := "\\Cref{lem:phases}(3)",
    lean := "{phase-uniform}, from {phase-uniform-layout}" },
  { statement := "\\Cref{lem:batch}",
    lean := "{batch-merged-sound}, {batch-merged-honest}, {batch-merged-hvzk}, with the errors " ++
      "{batch-merged-error-first}, {batch-merged-error-sum}; without merging, {batch-sound}, " ++
      "{batch-honest}; in the proof system, with the merging challenge and the zerocheck point " ++
      "as separate verifier messages of errors \\((\\nQ - 1)/|\\K|\\) and " ++
      "\\(\\nrv/|\\K|\\), {batch-merged-sep-sound}, {batch-merged-sep-honest}, " ++
      "{batch-merged-sep-hvzk}, with the errors {batch-merged-sep-error-sum}" },
  { statement := "\\Cref{lem:batch}, for operands that are bits",
    lean := "{batch-merged-bits-sound}, {batch-merged-bits-hvzk}, with the errors " ++
      "{batch-merged-bits-error-sum}; without merging, {batch-bits-sound}, {batch-bits-hvzk}" },
  { statement := "\\Cref{lem:bit-sumcheck}",
    lean := "{bit-sumcheck-sound}, from {bit-sumcheck-rounds}; {bit-sumcheck-honest}; {bit-sumcheck-hvzk}" },
  { statement := "\\Cref{lem:gkr}",
    lean := "{gkr-sound}, {gkr-honest}, {gkr-hvzk}, with the errors {gkr-error-sum}" },
  { statement := "\\Cref{lem:subfield-test}, for one row, as a count of samples",
    lean := "{subfield-test}" },
  { statement := "\\Cref{def:o-admissible}",
    lean := "{tree-spec}" },
  { statement := "\\Cref{lem:cells-sound}, composed in series after a reduction",
    lean := "{cells-sound}, {cells-honest}; the honest masks {subfield-mask-kit}" },
  { statement := "\\Cref{prot:bits}, the measurement after the combination",
    lean := "{stage-measure}, with {squaring-chain-masks}" },
  { statement := "\\Cref{lem:bits-sound}, composed in series after a reduction",
    lean := "{stage-sound}, {stage-honest}; the honest masks {squaring-chain-honest}, on all " ++
      "data with the product constraints by {squaring-chain-commits}; as a kit of a packing " ++
      "tree, {chain-mask-kit}" },
  { statement := "\\Cref{thm:tree}",
    lean := "{tree-reduces}, {tree-complete}, {tree-hvzk}" },
  { statement := "\\Cref{cor:tower}(1), with the soundness error equal to the bound",
    lean := "{tower-reduces}" },
  { statement := "\\Cref{cor:tower}(2)",
    lean := "{tower-complete}" },
  { statement := "\\Cref{cor:tower}(3)",
    lean := "{tower-hvzk}" },
  { statement := "\\Cref{def:batched-relation}",
    lean := "{batched-relation}, {batched-holds}" },
  { statement := "\\Cref{def:skip-domain}",
    lean := "{skip-points}" },
  { statement := "\\Cref{def:mle}",
    lean := "{mle}, {eq-poly}" },
  { statement := "\\Cref{def:skip-poly}",
    lean := "{skip-poly}" },
  { statement := "\\Cref{def:layered-circuit}",
    lean := "{layered-circuit}, {layered-circuit-sat}" },
  { heading := "Ligero (\\cref{sec:pack-ligero,app:ligero-general})" },
  { statement := "\\Cref{def:ligero-errors}",
    lean := "{ligero-commit-error}, {ligero-mask-test-error}, {ligero-untested-error}" },
  { statement := "\\Cref{lem:ligero}(1)",
    lean := "{ligero-sound}" },
  { statement := "\\Cref{lem:ligero}(2)",
    lean := "{ligero-complete}" },
  { statement := "\\Cref{lem:ligero}(3)",
    lean := "{ligero-hvzk}" },
  { statement := "\\Cref{def:list}, as \\(\\List_d(u, a + 1)\\)",
    lean := "{agreement-list}" },
  { statement := "\\Cref{def:johnson-agreement}",
    lean := "{johnson-agreement}" },
  { statement := "\\Cref{def:tableau}",
    lean := "{tableau-parameters}, {tableau-commitment}, {tableau-honest}" },
  { statement := "\\Cref{lem:mask-split}",
    lean := "part~(1): {mask-split-vanishing}; part~(2): {mask-split-kernel}; part~(3): " ++
      "{mask-split-three}, {mask-split-two}" },
  { statement := "\\Cref{lem:untested-masks}",
    lean := "the linear test: {untested-linear-columns}, {untested-linear-bad}; the quadratic " ++
      "test: {untested-quad-columns}, {untested-quad-bad}; for the test that the verifier " ++
      "selects, {untested-columns}, {untested-bad-challenges}; its last sentence: " ++
      "{untested-johnson-params}" },
  { statement := "\\Cref{cor:untested-ligero}, part~(1) of \\cref{lem:ligero}",
    lean := "{untested-sound}" },
  { statement := "\\Cref{cor:untested-ligero}, part~(2) of \\cref{lem:ligero}",
    lean := "{untested-complete}" },
  { statement := "\\Cref{cor:untested-ligero}, part~(3) of \\cref{lem:ligero}",
    lean := "{untested-hvzk}" },
  { statement := "\\Cref{lem:ligero-lf-order}, in the round-by-round form of Chiesa, Manohar " ++
      "and Spooner, equivalent to \\cref{def:rbr} by \\cref{lem:rbr-total}",
    lean := "{ligero-lf-rbr}, with the extractor {ligero-lf-extractor} and the state " ++
      "function {ligero-lf-state}; part~(1): {ligero-lf-data-list-le}, " ++
      "{ligero-lf-data-list-le-one}, from {interleaved-list-le}, {interleaved-list-le-one}; " ++
      "the state function's list, over the data rows and the low-degree mask row, projects " ++
      "onto the list of part~(1) by {ligero-lf-data-list-proj}" },
  { statement := "\\Cref{app:ligero-lf-order}, the round errors at \\LF version~7's parameters",
    lean := "{v7-hash-joint}, {v7-hash-column}, {v7-hash-error} (hash tableau); " ++
      "{v7-sig-joint}, {v7-sig-column}, {v7-sig-error} (signature tableau)" },
  { heading := "Counterexamples to the published analyses (\\cref{app:ligero-errata})" },
  { statement := "Ames et al.'s Lemma~B.9 fails, at \\(t = 1\\) and \\(t = 2\\)",
    lean := "{ahiv22-b9-false-one}, {ahiv22-b9-false-two}" },
  { statement := "The quadratic term of Ames et al.'s Appendix~C fails, at \\(t = 1\\) and \\(t " ++
      "= 2\\)",
    lean := "{ahiv22-appc-false-one}, {ahiv22-appc-false-two}" },
  { statement := "Ames et al.'s Lemma~4.14 holds with arbitrary mask rows and an arbitrary " ++
      "blinding row, also with the field term \\((e + 1)/|\\F|^{\\sigma}\\)",
    lean := "{ahiv22-lemma414}, from {ahiv22-headline}" },
  { statement := "Cascudo et al.'s Theorem~4.4 fails, at code length \\(n\\) and at \\LF's " ++
      "encoded length \\(n + 2k - 1\\)",
    lean := "{chvy25-thm44-false}, {chvy25-thm44-false-ncol}" },
  { statement := "The sum of Cascudo et al.'s Theorems~4.3 and~4.4 fails for every \\(k\\) from " ++
      "\\(13\\) to \\(30\\), at both code lengths",
    lean := "{chvy25-summed-false}, {chvy25-summed-false-ncol}" },
  { statement := "\\Cref{sec:pack-ligero-errata}, the repaired bound, is " ++
      "\\cref{lem:untested-masks}",
    lean := "{untested-columns}, {untested-bad-challenges}" },
  { heading := "Series--parallel BCS (\\cref{sec:bcs})" },
  { statement := "\\Cref{def:adversary}",
    lean := "{adversary-qrom}, {adversary-rom}" },
  { statement := "\\Cref{def:narg-zk-post}, in the QROM for finite statement, witness and " ++
      "proof sets, to which the configurations map theirs",
    lean := "{zk-after-last-request}, {zk-after-last-request-rom}, with " ++
      "the proof queries {zk-request}" },
  { statement := "\\Cref{def:narg-wi}, for the arguments of \\spBCS{}",
    lean := "{wi-def}" },
  { statement := "\\Cref{def:bcs-se}, for the arguments of \\spBCS{}, at the database extractor " ++
      "and \\(\\errsim = 0\\)",
    lean := "{merge-sse-def}, with its two conditions in {merge-sse-conditions}; " ++
      "{merge-sse-rom-def}, with its two conditions in {merge-sse-rom-conditions}" },
  { statement := "\\Cref{thm:bcs-main}",
    lean := "{merge-complete-adaptive-qrom}, {merge-complete-adaptive-rom} (part~(1)), " ++
      "{merge-zk-guarantees} (parts~(3) " ++
      "and~(4)), {merge-knowledge-guarantees} (parts~(2) and~(5)), for every Merkle opening " ++
      "format ({merkle-opening}), among them the authentication paths ({per-leaf-opening})" },
  { statement := "\\Cref{thm:bcs-main}, with the authentication paths of each tree compressed " ++
      "into one multiproof",
    lean := "the declarations for \\cref{thm:bcs-main} at the multiproof format " ++
      "({multiproof-opening}), which the configurations use. The honest multiproof is the " ++
      "compression of the honest authentication paths ({multiproof-compress}). An accepted " ++
      "multiproof yields accepted authentication paths ({multiproof-decompress}) whose queries " ++
      "are among its own ({multiproof-decompress-queries})" },
  { statement := "\\Cref{def:narg}",
    lean := "{narg-prover}; {narg-verifier-qrom}, {narg-verifier-rom}" },
  { statement := "\\Cref{def:narg-complete}",
    lean := "{narg-complete-qrom}, {narg-complete-rom}" },
  { statement := "\\Cref{def:narg-ks}, in the QROM with a classical auxiliary input of the adversary, " ++
      "the trace distance bounded at each value of it and averaged",
    lean := "{narg-ks-qrom}, {narg-ks-rom}" },
  { statement := "\\Cref{def:narg-sound}",
    lean := "{narg-sound-qrom}, {narg-sound-rom}" },
  { statement := "\\Cref{lem:ks-sound}",
    lean := "{ks-sound-qrom}, {ks-sound-rom}" },
  { statement := "\\Cref{def:narg-zk}, in the QROM for finite statement, witness and proof " ++
      "sets, to which the configurations map theirs",
    lean := "{narg-zk-qrom}, {narg-zk-rom}" },
  { statement := "\\Cref{def:bcs-quantities}",
    lean := "{bcs-kq}, {bcs-sim-queries}, {bcs-nj}, {bcs-overrun}, {bcs-key-collision}, " ++
      "{bcs-leaf-bound}" },
  { statement := "\\Cref{thm:bcs-complete}(1)",
    lean := "{merge-complete-fixed}" },
  { statement := "\\Cref{thm:bcs-complete}(2)",
    lean := "{merge-complete-adaptive-qrom}, {merge-complete-adaptive-rom}" ++
      ", {merge-complete-coins} (a fixed statement)" },
  { statement := "\\Cref{thm:bcs-zk}(1)",
    lean := "{merge-zk-qrom}" },
  { statement := "\\Cref{thm:bcs-zk}(2)",
    lean := "{merge-zk-rom}" },
  { statement := "\\Cref{thm:bcs-wi}",
    lean := "{merge-wi-length}, from {merge-wi-advantage}" },
  { statement := "\\Cref{lem:pad-purify}, in a per-execution-path form: at most \\(T\\) " ++
      "queries other than dummy queries on each execution path, with \\cite[Lem.~5.9]{EPRINT:ChiManSpo19} and " ++
      "\\cite[Thm.~3]{EPRINT:AmbHamUnr18} proved for this form",
    lean := "{pad-coherent} with {query-count}; {lifting-count}, {o2h-count}" },
  { statement := "\\Cref{lem:block-oracle}, for the algorithm of the proof of " ++
      "\\cref{thm:bcs-ks}, at each value of its output and verdict",
    lean := "{block-oracle}" },
  { statement := "\\Cref{lem:sse-instability}",
    lean := "{merge-instab-union}, from {merge-cond-instab} and {qrom-instab-collision}; " ++
      "with step~6 of the proof of \\cref{thm:bcs-se}, {merge-db-prob} (at the " ++
      "per-execution-path query count {tp-query-count})" },
  { statement := "\\Cref{thm:bcs-ks}(1)",
    lean := "{merge-online-extracts-q}, from {merge-knowledge-bound} and " ++
      "{qverifier-online-extracts}; the clause on the joint state in the field " ++
      "{knowledge-model-state:1} of {knowledge-guarantees-struct}, which " ++
      "{merge-knowledge-guarantees} proves" },
  { statement := "\\Cref{thm:bcs-ks}(2)",
    lean := "{merge-online-extracts-r}, from {merge-joint-bound} and " ++
      "{rverifier-online-extracts}" },
  { statement := "\\Cref{thm:bcs-main}(2), soundness",
    lean := "{merge-soundness-q}, from {qverifier-soundness}; " ++
      "{merge-soundness-r}, from {rverifier-soundness}" },
  { statement := "\\Cref{thm:bcs-se}(1)",
    lean := "{merge-sse-joint}" },
  { statement := "\\Cref{thm:bcs-se}(2)",
    lean := "{merge-sse-rom}" },
  { statement := "\\Cref{def:bcs-base-game}",
    lean := "{sim-ext-game}" },
  { statement := "\\Cref{lem:sse-cover}",
    lean := "{merge-cover}" },
  { statement := "\\Cref{def:bcs-se} implies Unruh's Definition~14, inequality~(6), at error " ++
      "\\(\\errsim + \\errse\\), for tests that are events of the adversary's measured " ++
      "output (\\cref{sec:prelims-sse}), for the extractor of \\cref{thm:bcs-se}, " ++
      "at \\(\\errsim = 0\\)",
    lean := "{joint-weak-sim-extraction}, {merge-sse-fresh}" },
  { statement := "\\Cref{def:bcs-se} gives Chase and Lysyanskaya's extraction property in the " ++
      "QROM (\\cref{sec:bcs-thm}), for the arguments of \\spBCS{} at the database extractor " ++
      "and \\(\\errsim = 0\\)",
    lean := "{merge-cl06}" },
  { statement := "\\Cref{sec:bcs-thm}: for the database extractor and tests that query the " ++
      "oracle, inequality~(6) of Unruh's Definition~14 fails along families of " ++
      "complete instances",
    lean := "{merge-oracle-test}" },
  { heading := "End to end (\\cref{sec:sec-main})" },
  { statement := "\\Cref{thm:e2e}",
    lean := "{e2e-source}, from \\cref{def:o-guarantees}(1) at every \\(\\errc\\), with the " ++
      "guarantees {e2e-coin-guarantees}; for any honest prover, {e2e-coins}; for a " ++
      "deterministic honest prover, {e2e-generic}, with the guarantees {e2e-guarantees}; " ++
      "part~(2) alone, " ++
      "{e2e-generic-knowledge}; the error of part~(2) in the QROM, {knowledge-error-eq}" },
  { heading := "End to end, for the proofs of possession of ML-DSA-44 (\\cref{sec:sec-main})" },
  { statement := "\\Cref{thm:e2e}, its hypotheses on \\(\\Prog_0\\): round-by-round knowledge " ++
      "soundness, and completeness with \\(\\errc = 0\\)",
    lean := "{mldsa-source-rbr-rom}, {mldsa-source-rbr-qrom}; the honest strategies " ++
      "{mldsa-honest-rom}, {mldsa-honest-qrom}" },
  { statement := "\\Cref{thm:e2e}, the largest round error \\(\\errk\\)",
    lean := "{mldsa-max-error-rom}, {mldsa-max-error-qrom}" },
  { statement := "\\Cref{thm:e2e}(1), with numerical upper bounds on \\(\\errov\\) and " ++
      "\\(\\errkey\\)",
    lean := "{cfg-completeness-adaptive-qrom}, " ++
      "{cfg-completeness-adaptive-rom}; for a fixed statement, " ++
      "{cfg-completeness}, and on the honest inputs, {cfg-completeness-honest}; at every pair " ++
      "of the relation, {cfg-completeness-of-rel}, at the honest input of the pair " ++
      "({cfg-honest-input-of-rel}), valid with no pair excluded ({mldsa-valid-of-witness})" },
  { statement := "\\Cref{thm:e2e}(2), at every \\(t\\), with numerical upper bounds on " ++
      "\\(\\errk\\) and \\(c'\\) and, in the QROM, on \\(2\\sqrt{k_q/2^{8(b+e)}}\\), and on " ++
      "\\(k_q\\), with statements the encoded keys at which each call of RejNTTPoly in ExpandA " ++
      "finishes within \\(1008\\) bytes of SHAKE128 output; at any other key no signature verifies",
    lean := "{cfg-knowledge-soundness}, {cfg-soundness}; " ++
      "{cfg-knowledge-soundness-rom}, {cfg-soundness-rom}" },
  { statement := "\\Cref{thm:e2e}(3)",
    lean := "{cfg-zero-knowledge}, {cfg-zero-knowledge-rom}; on " ++
      "the honest inputs, {cfg-zero-knowledge-honest}, which every pair of the relation has " ++
      "at its statement ({cfg-honest-input-of-rel})" },
  { statement := "\\Cref{tab:eval-params}, the zero-knowledge column for ML-DSA-44: " ++
      "\\(\\errzk^{\\mathrm{C}}(t, Q) \\le Q t\\, 2^{-116.46}\\) at the ROM parameters and " ++
      "\\(\\errzk(t, Q) \\le Q t\\, 2^{-180.19}\\) at the QROM parameters, for every " ++
      "\\(t \\ge 1\\) and \\(Q \\le 2^{{}64}\\), with \\(\\errc = 0\\)",
    lean := "{mldsa-zk-bits-rom}, {mldsa-zk-bits-qrom}" },
  { statement := "\\Cref{thm:e2e}(4)",
    lean := "{cfg-wi}, on the honest inputs, which every pair of the relation has at its " ++
      "statement ({cfg-honest-input-of-rel})" },
  { statement := "\\Cref{thm:e2e}(5)",
    lean := "{cfg-sse-online}, {cfg-sse-rom}; in Unruh's weak fresh " ++
      "form, {cfg-sse}" },
  { heading := "Results from the literature (\\cref{sec:formal-results})" },
  { statement := "Schwartz--Zippel~\\cite{Sch79,Zip79} (\\cref{lem:sz})",
    lean := "Mathlib's {sz:full}" },
  { statement := "Dao, Kominers and Thaler's Theorem~5.12~\\cite{EPRINT:DaoKomTha26}, for lines " ++
      "(\\cref{lem:mca-instances}(1))",
    lean := "ArkLib's {arklib-johnson-closed}" },
  { statement := "The interpolation certificate of Dao, Kominers and Thaler~\\cite[Lem.~3.12 " ++
      "and App.~B]{EPRINT:DaoKomTha26}, at the parameters \\((m, B, H)\\) " ++
      "(\\cref{lem:mca-certificate})",
    lean := "ArkLib's {arklib-weighted-johnson}" },
  { statement := "Dao, Kominers and Thaler's Johnson bound~\\cite[App.~B.1]{EPRINT:DaoKomTha26} " ++
      "(\\cref{lem:johnson})",
    lean := "{johnson-bound}" },
  { statement := "Dao, Kominers and Thaler's Corollary~7.2~\\cite{EPRINT:DaoKomTha26} " ++
      "(\\cref{thm:mca-affine})",
    lean := "ArkLib's {arklib-mca-affine}" },
  { statement := "Zhandry's Lemma~3~\\cite{EPRINT:Zhandry18}",
    lean := "{zhandry-l3}" },
  { statement := "Zhandry's Lemma~4~\\cite{EPRINT:Zhandry18}",
    lean := "{zhandry-l4-state}; for the measured output, {zhandry-l4}" },
  { statement := "Zhandry's Lemma~5~\\cite{EPRINT:Zhandry18}",
    lean := "{zhandry-l5}" },
  { statement := "Chiesa, Manohar and Spooner's Lemma~5.7~\\cite{EPRINT:ChiManSpo19}, for " ++
      "properties that exclude the empty database",
    lean := "{cms19-lifting}" },
  { statement := "Chiesa, Manohar and Spooner's Theorem~8.6~\\cite{EPRINT:ChiManSpo19}",
    lean := "{qverifier-soundness}, {qverifier-online-extracts}" },
  { statement := "Ambainis, Hamburg and Unruh's one-way-to-hiding " ++
      "lemma~\\cite[Thm.~3]{EPRINT:AmbHamUnr18}, for pure and for mixed adversaries",
    lean := "{o2h-pure}, {o2h-mixed}" },
  { statement := "The interleaved proximity lemma of Ames et al.~\\cite[Lem.~4.2]{EPRINT:AHIV22}, " ++
      "jointly over its repetitions",
    lean := "{interleaved-proximity}" },
  { statement := "Berlekamp--Welch decoding",
    lean := "{berlekamp-welch}" },
  { statement := "Correlated agreement for affine spaces at unique " ++
      "decoding~\\cite[Thm.~1.6]{EPRINT:BCIKS20}",
    lean := "{affine-proximity}" }
]

end GordieHowe.PaperManifest
