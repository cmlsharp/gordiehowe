-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.TranscriptData
public import GordieHowe.ProofSystem.Program.ForkJoinMerge
public import GordieHowe.ProofSystem.Program.ForkJoinZK
public import GordieHowe.SPBCS.Setting
public import GordieHowe.SPBCS.Theorems
public import GordieHowe.SPBCS.KnowledgeTheorems

@[expose] public section

/-!
# The setting with merges of a configuration with forked domains

A configuration whose domains are forked circuit proofs is a multi-circuit IOP with forked domains
(`GordieHowe.RealizedProgram.ProofSystem.IOP`); its compiled argument with merges is spBCS's
(`GordieHowe/SPBCS/Setting.lean`) over the composite `GordieHowe.RealizedProgram.ProofSystem.IOP.toCausalIOP` and the merges of its
domains (`GordieHowe.RealizedProgram.ProofSystem.IOP.merges`: each domain merges its branches into its join part). This module is
generic in the IOP `C`.

- `SPBCS.ProofSystemTranscript.MergeBounds T kS`: the facts the setting is built from, `T.Bounds` and
  Fiat–Shamir salts of at most `2^10` bytes.
- `SPBCS.ProofSystemTranscript.setting T kS hb`: the setting with merges (`GordieHowe.SPBCS.Setting`) at
  `k`-byte digests, `2k`-byte Merkle salts, `kS`-byte Fiat–Shamir salts, `2^40`-byte inputs, writes
  of at most `2^20` bytes, the site layout `GordieHowe.RealizedProgram.ProofSystem.IOP.siteLayout`, oracle answers of
  `k + fsExtraBytes + g` bytes for the largest grant `g`, and the readers as samplers, each round
  reading at most its own stream length; `preimages`: the preimage samplers of its samplers.
- Its sizes: the overrun (`GordieHowe.SPBCS.ProofSystemTranscript.overrun_le_at_granted`, in
  `GordieHowe/Applications/Configuration.lean`: each round's Chernoff certificate), the positions
  (`card_pos`), the format bounds of its query phases (`formatBounds`), and the
  verifier's queries on accepting runs (`length_queries_le`).
- The statements at the setting, from the guarantees of spBCS
  (`GordieHowe.SPBCS.knowledgeGuarantees`, `GordieHowe.SPBCS.privacyGuarantees`, and completeness at fixed coins,
  `GordieHowe.SPBCS.prob_not_accepts_prove_le` and its adaptive forms): knowledge soundness and soundness in the QROM and the ROM,
  completeness, the four zero-knowledge forms, simulation-sound extractability and its form for
  tests that query the oracle.
-/

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal

variable {Stmt W : Type} {rel : Set (Stmt × W)}

namespace ProofSystemTranscript

variable {C : RealizedProgram.ProofSystem.IOP Stmt W rel}

/-- **The facts a setting with merges is built from**: the facts of a series–parallel setting
(`Bounds`) and Fiat–Shamir salts of at most `2^10` bytes. -/
structure MergeBounds (T : ProofSystemTranscript C) (kS : ℕ) : Prop extends T.Bounds where
  /-- The Fiat–Shamir salt has at most `2^10` bytes. -/
  kS_le : kS ≤ 2 ^ 10

variable {T : ProofSystemTranscript C}

/-- The final digests of one chain input have at most `2^18` bytes. -/
theorem nJ_mul_le (hb : T.Bounds) : C.merges.nJ * T.k ≤ 2 ^ 8 * 2 ^ 10 := by
  rw [C.nJ_merges]
  exact Nat.mul_le_mul (Finset.sup_le fun d _ => hb.nb_le d) hb.k_le

variable (T) in
/-- **The setting with merges of a configuration** (module docstring). -/
def setting (kS : ℕ) (hb : T.MergeBounds kS) :
    Setting C.toCausalIOP C.merges T.k where
  k := T.k
  kN := 2 * T.k
  kS := kS
  L := 2 ^ 40
  e := Configurations.fsExtraBytes + T.maxGrant
  kMin_le_k := le_rfl
  label := T.label
  stmt := T.stmt
  layout := C.siteLayout
  write := C.writeOf (k := T.k) (SpecWrites.appendN C.m T.commitWrites ++ T.appWrites)
    T.branchWrites T.joinWrites
  leaf := C.leafOf T.leaf
  leaf_fit := C.leafOf_fit hb.leaf_le
  nd := C.m
  one_le_nd := NeZero.one_le
  nTrees_le := C.nTrees_le_m
  B := 2 ^ 20
  write_B_le := C.writeOf_B_le (roots_le hb.toBounds)
  fits x o := by
    have h2 := C.length_label_le hb.nb_le o
    have key : ∀ a d g f : ℕ, a ≤ 2 ^ 10 + (9 + kS) + 2 ^ 20 → d ≤ C.m + 2 ^ 8 + 3 →
        g ≤ Configurations.maxRounds * 2 ^ 20 → f ≤ 2 ^ 8 * 2 ^ 10 → a + d + g + f ≤ 2 ^ 40 := by
      have := hb.kS_le
      have := hb.m_le
      simp only [Configurations.maxRounds]
      omega
    exact key _ _ _ _ (length_saltedCodec_le hb.toBounds x) h2 (rounds_mul_le hb.toBounds)
      (nJ_mul_le hb.toBounds)
  sampler := C.samplersOf T.readers T.k (Configurations.fsExtraBytes + T.maxGrant) T.stream

variable (T) in
/-- **The preimage samplers of the setting's samplers** (`RealizedProgram.ProofSystem.IOP.preimagesOf`), from which
the zero-knowledge simulator draws each round's stream at its simulated challenge. -/
def preimages (kS : ℕ) (hb : T.MergeBounds kS) :
    (T.setting kS hb).model.Preimages := fun c =>
  C.preimagesOf T.readers T.k (Configurations.fsExtraBytes + T.maxGrant) T.stream c.leaf.label c.idx

/-! ### The sizes of the setting -/

/-- **The positions of the setting with merges** are the leaves of the domains' trees. -/
theorem card_pos {kS : ℕ} (hb : T.MergeBounds kS) :
    Fintype.card (T.setting kS hb).model.Pos = ∑ d, (C.oracle d).nLeaves := by
  rw [Fintype.card_congr (SPBCS.Pos.equivSigma _), Fintype.card_sigma]
  simp only [Fintype.card_congr Position.equivSigma, Fintype.card_sigma, Fintype.card_fin]
  change ∑ q : C.term.Leaf, ∑ i, ∑ t : Fin ((C.comp q.label).nTrees i), (C.comp q.label).nLeaves i t = _
  simp only [C.sum_nLeaves_comp]
  rw [Fintype.sum_eq_single C.preLeafT fun q hq => if_neg (C.label_ne_pre hq)]
  rfl

/-- **The format bounds of the query phases of the setting with merges**: at most `nq` queried
leaves and trees of at most `N` leaves (`Setting.formatBounds`). -/
theorem formatBounds {kS : ℕ} (hb : T.MergeBounds kS) {N nq : ℕ}
    (hN : ∀ d, (C.oracle d).nLeaves ≤ N) (hq : ∀ ch, (C.queryList ch).length ≤ nq) :
    (T.setting kS hb).model.FormatBounds (T.setting kS hb).queries nq N :=
  (T.setting kS hb).formatBounds hq fun p i τ => C.nLeaves_comp_le hN p.label i τ

/-- **The query budget of the verifier with merges** of the setting: two per round, one per
branch, and `1 + log₂ (2N)` per queried leaf. -/
theorem kqOf_merges (N nq : ℕ) :
    SPBCS.kqOf C.merges C.rounds nq N =
      2 * ∑ q : C.shape.term.Leaf, C.rounds q.label + ∑ d, C.shape.nb d +
        nq * (1 + Nat.log 2 (2 * N)) := by
  rw [SPBCS.kqOf, SPTerm.size_eq_sum, C.card_site]

/-- **The verifier's queries on accepting runs of the setting with merges**: two per round, one
per branch, and `1 + log₂ (2N)` per queried leaf, for trees of at most `N` leaves and at most `nq`
queried leaves (`SPBCS.queries_length_le_of_formatBounds`). -/
theorem length_queries_le {kS : ℕ} (hb : T.MergeBounds kS) {N nq : ℕ}
    (hN : ∀ d, (C.oracle d).nLeaves ≤ N) (hq : ∀ ch, (C.queryList ch).length ≤ nq) (x : Stmt)
    (h : Query T.k (2 * T.k) kS (2 ^ 40) → Out T.k (Configurations.fsExtraBytes + T.maxGrant))
    (π : (T.setting kS hb).model.NIProof)
    (hv : (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x)) :
    ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤
      2 * ∑ q : C.shape.term.Leaf, C.rounds q.label + ∑ d, C.shape.nb d +
        nq * (1 + Nat.log 2 (2 * N)) :=
  (kqOf_merges (C := C) N nq) ▸
    SPBCS.queries_length_le_of_formatBounds (formatBounds hb hN hq) hv

/-! ### The statements at the setting -/

section Statements

variable (T) (kS : ℕ) (hb : T.MergeBounds kS)

/-- **The verifier with merges of the setting in the QROM** with `kq` queries, as a
`NARG.QROM.Verifier` (`SPBCS.toQVerifier`). -/
noncomputable abbrev verifier (kq : ℕ) :=
  (T.setting kS hb).model.toQVerifier (T.setting kS hb).queries kq

/-- **The verifier with merges of the setting in the ROM** with `kq` queries, as a
`NARG.ROM.Verifier` (`SPBCS.toRVerifier`). -/
noncomputable abbrev verifierROM (kq : ℕ) :=
  (T.setting kS hb).model.toRVerifier (T.setting kS hb).queries kq

/-- **The proof format of the zero-knowledge games at the setting** with the proof bound `pB`:
every query phase opens at most `pB` positions and every tree has at most `pB` leaves
(`FormatBounds` at `pB`). -/
abbrev ProofFormat (pB : ℕ) : Prop :=
  (T.setting kS hb).model.FormatBounds (T.setting kS hb).queries pB pB

/-- **The honest prover of the setting** at the causal honest prover `honest` with coins in `R`:
`SPBCS.niProver`, with uniform coins, Merkle salts and salt, its proofs in the format
`pB` (`hf`). -/
noncomputable abbrev prover {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' R : Type} [Fintype R] [Nonempty R]
    (honest : I' → R → CausalProver C.P C.term Stmt) :=
  (T.setting kS hb).model.niProver (T.setting kS hb).layout honest (T.setting kS hb).encoder hf

/-- **The simulator of the setting** at the simulator data `SD`: `SPBCS.niSimulator` at the
simulator `RealizedProgram.ProofSystem.IOP.simulator SD`, its proofs in the format `pB` (`hf`).

Running time: that of `SPBCS.niSimulator` at the setting (its Running time paragraph). This running
time is argued here, not proved in Lean. -/
abbrev simulator {pB : ℕ} (hf : T.ProofFormat kS hb pB) (SD : C.SimData) :=
  (T.setting kS hb).model.niSimulator (T.setting kS hb).layout
    (T.setting kS hb).viewEncoder.toViewRead pB
    (ViewEncoder.formatBounds _ (T.setting kS hb).encoder (T.setting kS hb).viewEncoder hf) id
    (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb)

variable {T kS hb}

/-- **Knowledge soundness at the setting with merges: online extractability** (DFMS22
Definition 3.1, p. 10, with `εsim = 0` and a quantum auxiliary output;
`SPBCS.onlineExtracts_toQVerifier`, the `knowledge` clause of
`SPBCS.knowledgeGuarantees` at the budget `kq`, at the soundness of the multi-circuit IOP
with forked domains, `RealizedProgram.ProofSystem.IOP.Sound.causal_rbr`) against `t`-query adversaries without proof queries of
`def:adversary` (`Quantum.QueryBoundedAdversary`) with an auxiliary output in `Z`, for the relation
`rel'` at the extractor mapped by `g` (`hg`), with the verifier's query budget `kq` (`hkq`). The
final digests of a domain's branches add `C.merges.nJ` digests (`RealizedProgram.ProofSystem.IOP.nJ_merges`). -/
theorem knowledge [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {Zo : Type} {t : ℕ} (𝒢 : (T.setting kS hb).QROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof × Zo) t) :
    𝒢.OnlineExtracts (T.verifier kS hb kq) NARG.QROM.compressedSim rel'
      (NARG.QROM.compressedExt ((T.setting kS hb).model.dbExtractBits (C.extractor.mapWit g))) 0
      (knowledgeError T.k (Configurations.fsExtraBytes + T.maxGrant) kq (t + kq) (digests (C := C))
        C.merges.nJ (maxError Sd.error)) :=
  SPBCS.onlineExtracts_toQVerifier (Sd.causal_rbr.mapWit hg) hkq 𝒢

open Classical in
/-- **Soundness at the setting with merges** (`SPBCS.soundness_toQVerifier`, the `soundness`
clause of `SPBCS.knowledgeGuarantees` at the budget `kq`): every `t`-query adversary without proof
queries outputs a statement without a witness of `rel'` and a proof the verifier accepts with
probability at most the knowledge error of `knowledge`. -/
theorem soundness [Inhabited W] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {t : ℕ} (𝒜 : (T.setting kS hb).QROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof) t) :
    𝒜.acceptsFalse (T.verifier kS hb kq) rel' ≤
      knowledgeError T.k (Configurations.fsExtraBytes + T.maxGrant) kq (t + kq) (digests (C := C))
        C.merges.nJ (maxError Sd.error) :=
  SPBCS.soundness_toQVerifier (E := C.extractor.mapWit g) (Sd.causal_rbr.mapWit hg) hkq 𝒜

/-- **Knowledge soundness at the setting with merges in the ROM: online extractability against the
lazily sampled oracle** (`SPBCS.onlineExtracts_toRVerifier`, the `knowledgeROM` clause of
`SPBCS.knowledgeGuarantees` at the budget `kq`) against classical `t`-query adversaries without
proof queries (`ROM.QueryBoundedAdversary`) with an auxiliary output in `Z`. -/
theorem knowledgeROM [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {Zo : Type} {t : ℕ} (𝒢 : (T.setting kS hb).ROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof × Zo) t) :
    𝒢.OnlineExtracts (T.verifierROM kS hb kq) NARG.ROM.OracleSampler.lazy.law rel' ((T.setting kS hb).model.dbExtract (C.extractor.mapWit g)) 0
      (knowledgeErrorROM T.k (t + kq) (digests (C := C)) C.merges.nJ (maxError Sd.error)) :=
  SPBCS.onlineExtracts_toRVerifier (Sd.causal_rbr.mapWit hg) hkq 𝒢

open Classical in
/-- **Soundness at the setting with merges in the ROM** (`SPBCS.soundness_toRVerifier`, the
`soundnessROM` clause of `SPBCS.knowledgeGuarantees` at the budget `kq`): every classical `t`-query
adversary without proof queries outputs a statement without a witness of `rel'` and a proof the
verifier accepts with probability at most `knowledgeErrorROM`. -/
theorem soundnessROM [Inhabited W] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {t : ℕ} (𝒜 : (T.setting kS hb).ROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof) t) :
    𝒜.acceptsFalse (T.verifierROM kS hb kq) rel' ≤
      knowledgeErrorROM T.k (t + kq) (digests (C := C)) C.merges.nJ (maxError Sd.error) :=
  SPBCS.soundness_toRVerifier (E := C.extractor.mapWit g) (Sd.causal_rbr.mapWit hg) hkq 𝒜

variable (T kS hb) in
open Classical in
/-- **Everlasting zero knowledge at the setting with merges against query-bounded adversaries** (`NARG.QROM.EverlastingZeroKnowledge` at every finite statement and
honest-input types): the prover of `Hc` (`prover`, `SPBCS.niProver`)
against the simulator of `RealizedProgram.ProofSystem.IOP.simulator SD` (`simulator`, `SPBCS.niSimulator`),
with error `ε`. -/
def ZeroKnowledge {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (X' W' : Type) [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → Stmt)
    (fw : W' → I'),
    NARG.QROM.EverlastingZeroKnowledge (fun x w => (fx x, fw w) ∈ relI) queryEncoding
      ((T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc)).comap fx fw)
      ((T.simulator kS hb hf SD).comap fx) ε

variable (T kS hb) in
open Classical in
/-- **Query-counted zero knowledge at the setting with merges against query-bounded adversaries**
(`NARG.QROM.ZeroKnowledge`, every query counted, at every finite statement and
honest-input types): the prover of `Hc` (`prover`, `SPBCS.niProver`)
against the simulator of `RealizedProgram.ProofSystem.IOP.simulator SD` (`simulator`, `SPBCS.niSimulator`),
with error `ε`. -/
def ZeroKnowledgeQuery {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (X' W' : Type) [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → Stmt)
    (fw : W' → I'),
    NARG.QROM.ZeroKnowledge (fun x w => (fx x, fw w) ∈ relI) queryEncoding
      ((T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc)).comap fx fw)
      ((T.simulator kS hb hf SD).comap fx) ε

variable (T kS hb) in
open Classical in
/-- **Everlasting zero knowledge in the ROM at the setting with merges against query-bounded
classical adversaries** (`GordieHowe.ROM.EverlastingZeroKnowledge`):
the compiled prover of `Hc` against the compiled simulator of
`RealizedProgram.ProofSystem.IOP.simulator SD`, with error `ε`. -/
def ZeroKnowledgeROM {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  NARG.ROM.EverlastingZeroKnowledge (fun x w => (x, w) ∈ relI)
    (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc)) (T.simulator kS hb hf SD) ε

variable (T kS hb) in
open Classical in
/-- **Query-counted zero knowledge in the ROM at the setting with merges**
(`GordieHowe.ROM.ZeroKnowledge`, all queries counted, no oracle read after the output):
the compiled prover of `Hc` against the compiled simulator of
`RealizedProgram.ProofSystem.IOP.simulator SD`, with error `ε`. -/
def ZeroKnowledgeROMQuery {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI)
    (ε : ℕ → ℕ → ℝ) : Prop :=
  NARG.ROM.ZeroKnowledge (fun x w => (x, w) ∈ relI)
    (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc)) (T.simulator kS hb hf SD) ε

variable (T kS hb) in
open Classical in
/-- **Simulation-sound extractability at the setting with merges in the QROM**
(`SPBCS.SimulationSoundExtractableFresh`) with the counted simulator of
`RealizedProgram.ProofSystem.IOP.simulator SD`, the extractor `E` of `rel'` and the verifier's query budget `kq`, with
error `ε`. -/
def SimExtractable [DecidableEq Stmt] {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) {W' : Type}
    (rel' : Set (Stmt × W')) (E : CausalExtractor C.P C.term Stmt W') (kq : ℕ)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  (T.setting kS hb).model.SimulationSoundExtractableFresh pB
    (T.setting kS hb).queries rel' E kq ((T.simulator kS hb hf SD).encode queryEncoding) ε

open Classical in
/-- **Simulation-sound extractability at the setting with merges in the QROM**
(`SPBCS.simulation_sound_extractability`, the `simExtractability` clause of
`SPBCS.knowledgeGuarantees` at the budget `kq`) against query-bounded adversaries, with the
counted simulator of `RealizedProgram.ProofSystem.IOP.simulator SD` and the database extractor at the extractor mapped
by `g`, at the verifier's query budget `kq` (`hkq`), with `q = 2 |Pos| + t.size n + Σ_d nb d`
simulator queries per proof query (`RealizedProgram.ProofSystem.IOP.card_site`: one site per branch). -/
theorem simExtractability [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) :
    T.SimExtractable kS hb hf Hc rel' (C.extractor.mapWit g) kq
      ((T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
        (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
          ∑ d, C.shape.nb d)) := by
  have hk : 0 < (T.setting kS hb).k := hb.k_pos
  have h := SPBCS.simulation_sound_extractability (M := (T.setting kS hb).model)
    (B := pB) (T.setting kS hb).queries hkq (Sd.causal_rbr.mapWit hg)
    ((T.setting kS hb).model.niJointSimulatorProg (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder.toViewRead pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
    (SPBCS.simAssignsAtKeys_niJointSimulatorProg hk (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
  unfold SimExtractable
  rw [(T.setting kS hb).model.encode_niSimulator (T.setting kS hb).layout (T.setting kS hb).encoder
    (T.setting kS hb).viewEncoder hf, ← C.card_site]
  exact h

variable (T kS hb) in
/-- **Weak online simulation extractability at the setting with merges in the ROM**
(`SPBCS.WeakOnlineSimulationExtractableROM`) with the classical simulator program of
`RealizedProgram.ProofSystem.IOP.simulator SD` (the program of `simulator`), making at most `q` queries per proof query, the
extractor `E` of `rel'` and the verifier's query budget `kq`, with error `ε`. -/
def SimExtractableROM [DecidableEq Stmt] {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) {W' : Type}
    (rel' : Set (Stmt × W')) (E : CausalExtractor C.P C.term Stmt W') (kq q : ℕ)
    (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  (T.setting kS hb).model.WeakOnlineSimulationExtractableROM pB
    (T.setting kS hb).queries rel' E kq
    (T.simulator kS hb hf SD).prog q ε

/-- **Weak online simulation extractability at the setting with merges in the ROM**
(`SPBCS.weak_online_simulation_extractability_rom`, the `simExtractabilityROM` clause of
`SPBCS.knowledgeGuarantees` at the budget `kq`) against query-bounded classical adversaries
with an auxiliary output, with the classical simulator program of `RealizedProgram.ProofSystem.IOP.simulator SD` and
the database extractor at the extractor mapped by `g`, at the verifier's query budget `kq`
(`hkq`), with `q = 2 |Pos| + t.size n + Σ_d nb d` simulator queries per proof query
(`RealizedProgram.ProofSystem.IOP.card_site`: one site per branch): oracle simulation error `0` and extraction error
`simExtractionErrorROM kq (maxError ε) q`. -/
theorem simExtractabilityROM [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) :
    T.SimExtractableROM kS hb hf Hc rel' (C.extractor.mapWit g) kq
      (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
        ∑ d, C.shape.nb d)
      ((T.setting kS hb).model.simExtractionErrorROM kq (maxError Sd.error)
        (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
          ∑ d, C.shape.nb d)) := by
  have hk : 0 < (T.setting kS hb).k := hb.k_pos
  have h := SPBCS.weak_online_simulation_extractability_rom (M := (T.setting kS hb).model)
    (B := pB) (Qs := (T.setting kS hb).queries)
    (Sim := ((T.setting kS hb).model.niSimulatorTotal (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder.toViewRead pB id
      (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb)).prog)
    (fun _ _ => (T.setting kS hb).model.assignsAtKeys_jointProg (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder.toViewRead pB hk _ _ _ _ _ _ _)
    (fun _ _ G => (T.setting kS hb).model.length_trace_jointProg_le (h := G)
      (T.setting kS hb).layout (T.setting kS hb).viewEncoder.toViewRead pB _ _ _ _ _ _ _)
    (Sd.causal_rbr.mapWit hg) hkq
  unfold SimExtractableROM
  rw [simulator, (T.setting kS hb).model.niSimulator_eq, ← C.card_site]
  exact h

variable (T kS hb) in
open Classical in
/-- **Simulation-sound extractability for tests that query the oracle, at the setting with merges
in the QROM** (`SPBCS.SimulationSoundExtractableSimOracle`), with the counted simulator of
`RealizedProgram.ProofSystem.IOP.simulator SD`, the causal extractor `E` of `rel'` (from which the targeted extractor
is built) and the verifier's query budget `kq`, with error `ε`. -/
def SimExtractableSimOracle [DecidableEq Stmt] {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI)
    {W' : Type} (rel' : Set (Stmt × W')) (E : CausalExtractor C.P C.term Stmt W') (kq : ℕ)
    (ε : ℕ → ℕ → ℕ → ℝ≥0∞) : Prop :=
  (T.setting kS hb).model.SimulationSoundExtractableSimOracle pB
    (T.setting kS hb).queries rel' E kq ((T.simulator kS hb hf SD).encode queryEncoding) ε

open Classical in
/-- **Simulation-sound extractability for tests that query the oracle, at the setting with merges in
the QROM** (`SPBCS.simulation_sound_extractability_sim_oracle`, the
`simExtractabilitySimOracle` clause of `SPBCS.knowledgeGuarantees` at the budget `kq`) against
query-bounded adversaries, with the counted simulator of `RealizedProgram.ProofSystem.IOP.simulator SD` and the targeted
extractor at the extractor mapped by `g`, at the verifier's query budget `kq` (`hkq`), with
`q = 2 |Pos| + t.size n + Σ_d nb d` simulator queries per proof query (`RealizedProgram.ProofSystem.IOP.card_site`: one site
per branch) and the swap error at the test's queries. -/
theorem simExtractabilitySimOracle [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type}
    {rel' : Set (Stmt × W')} {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel')
    {kq : ℕ}
    (hkq : ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
      ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq)
    {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) :
    T.SimExtractableSimOracle kS hb hf Hc rel' (C.extractor.mapWit g) kq
      fun tq tTest Q => (T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
          (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
            ∑ d, C.shape.nb d) (tq + tTest) Q +
        (T.setting kS hb).model.swapError tTest := by
  have hk : 0 < (T.setting kS hb).k := hb.k_pos
  have h := SPBCS.simulation_sound_extractability_sim_oracle
    (M := (T.setting kS hb).model) (B := pB) (T.setting kS hb).queries hkq
    (Sd.causal_rbr.mapWit hg)
    ((T.setting kS hb).model.niJointSimulatorProg (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder.toViewRead pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
    (SPBCS.simAssignsAtKeys_niJointSimulatorProg hk (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
  unfold SimExtractableSimOracle
  rw [(T.setting kS hb).model.encode_niSimulator (T.setting kS hb).layout (T.setting kS hb).encoder
    (T.setting kS hb).viewEncoder hf, ← C.card_site]
  exact h

end Statements

end ProofSystemTranscript

end GordieHowe.SPBCS
