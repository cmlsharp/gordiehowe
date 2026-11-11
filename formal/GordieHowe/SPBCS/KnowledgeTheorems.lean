-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Headline
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.SimExtractUnruh
public import GordieHowe.SPBCS.SimExtractJoint
public import GordieHowe.SPBCS.SimOracle
public import GordieHowe.SPBCS.SimExtractROMJoint
public import GordieHowe.SPBCS.SimProg

@[expose] public section

/-!
# Knowledge soundness and weak online simulation extractability of spBCS with nested merges

The guarantees of `thm:bcs-main` for the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`) on any
series–parallel term with merges, with the paper's errors and `n_J = Mg.nJ`, for every Merkle
opening format `M.opening` (`GordieHowe/SPBCS/Merkle/Opening.lean`): the authentication paths of paper
`prot:generalized-bcs` (`PerLeaf.opening`) and the compressed multiproofs of the configurations
(`Multiproof.opening`), at the same errors.

## Knowledge soundness and weak online simulation extractability

`KnowledgeGuarantees` bundles knowledge soundness (paper `thm:bcs-ks`) and soundness
(`thm:bcs-main`(2)) in the QROM and the ROM, weak online simulation extractability (`thm:bcs-se`,
joint form) in the QROM and the ROM, and three forms of Unruh's weak simulation-sound
extractability (Unruh 2017 Definition 14, p. 21, eq. (6), `d = 1`, `p = 1`) in the QROM: for
residual-state tests that make no oracle queries (with fresh extraction, and with Unruh's
Extract), and for tests that query the oracle, with the test answered by the simulated oracle at
the extra error `swapError`. They hold at the verifier's query bound `M.kq NQ N`
(`def:bcs-quantities`'s `k_q`), with the database extractor `dbExtract` and the simulator `niSimulator` of the zero-knowledge
argument (`GordieHowe/SPBCS/SimProg.lean`) run through `queryEncoding`, which makes at
most `q_S = 2 |Pos| + t.size n + |Site|` queries. `knowledgeGuarantees` proves them from causal
round-by-round knowledge soundness.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

/-! ### Knowledge soundness and weak online simulation extractability -/

section Knowledge

variable [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P X k kN kS L e)
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq X]

/-- **The queries of one run of the spBCS simulator**, the paper's `q_S`
(`def:bcs-quantities`): `2 |Pos| + t.size n + |Site|`. -/
abbrev simQueries : ℕ := 2 * Fintype.card M.Pos + t.size n + Fintype.card Mg.Site

/-- **The verifier's query bound** `k_q = 2 nmsg + n_B + q_IOP (1 + ⌊log₂ 2N⌋)`
(`def:bcs-quantities`, `kqOf`) for query phases opening at most `NQ` positions and trees of at most
`N` leaves. -/
def kq (_ : SPBCS Mg P X k kN kS L e) (NQ N : ℕ) : ℕ := kqOf Mg n NQ N

/-- **The knowledge error in the QROM** at the verifier's query bound `M.kq NQ N`, the largest
challenge error `maxError ε` and `t` adversary queries (`thm:bcs-main`(2), `errks(t)`):
`knowledgeError k e kq (t + kq) c nJ (maxError ε)` with `c = M.senc.digestsPerInput`, which is
`2√(kq/2^(8(k+e))) + 6(t + kq)²(maxError ε + (max(2, c) + nJ + 1)(t + kq)/2^(8k))`. -/
noncomputable def ksError (NQ N : ℕ) (ε : ChIdx P t → ℝ≥0) (t' : ℕ) : ℝ≥0∞ :=
  knowledgeError k e (M.kq NQ N) (t' + M.kq NQ N) M.senc.digestsPerInput Mg.nJ (maxError ε)

/-- **The knowledge error in the ROM** at the verifier's query bound `M.kq NQ N` and `t`
adversary queries (`thm:bcs-main`(2), `errks^C(t)`): `knowledgeErrorROM k (t + kq) c nJ
(maxError ε)`, which is `(t + kq)(maxError ε + (max(2, c) + nJ + 1)(t + kq)/2^(8k))`. -/
noncomputable def ksErrorROM (NQ N : ℕ) (ε : ChIdx P t → ℝ≥0) (t' : ℕ) : ℝ≥0∞ :=
  knowledgeErrorROM k (t' + M.kq NQ N) M.senc.digestsPerInput Mg.nJ (maxError ε)

/-- **The extraction error of weak online simulation extractability in the QROM** at the
verifier's query bound `M.kq NQ N` and the simulator's `q_S` queries per proof query
(`thm:bcs-main`(5), `errse(t, Q)`): `simExtractionError kq (maxError ε) q_S`, a function of the
adversary's queries `t` and proof queries `Q`. -/
noncomputable def seError (NQ N : ℕ) (ε : ChIdx P t → ℝ≥0) : ℕ → ℕ → ℝ≥0∞ :=
  M.simExtractionError (M.kq NQ N) (maxError ε) M.simQueries

/-- **The extraction error of weak online simulation extractability in the ROM** at the
verifier's query bound `M.kq NQ N` (`thm:bcs-main`(5), `errse^C(t, Q)`):
`simExtractionErrorROM kq (maxError ε) q_S`. -/
noncomputable def seErrorROM (NQ N : ℕ) (ε : ChIdx P t → ℝ≥0) : ℕ → ℕ → ℝ≥0∞ :=
  M.simExtractionErrorROM (M.kq NQ N) (maxError ε) M.simQueries

/-- **The error of simulation-sound extractability for tests that query the oracle** at a test
with `tTest` queries answered by the simulated oracle: the extraction error `seError` at the
adversary's and the test's queries together, plus the swap term `swapError tTest`. -/
noncomputable def seErrorSimOracle (NQ N : ℕ) (ε : ChIdx P t → ℝ≥0) (tq tTest Q : ℕ) : ℝ≥0∞ :=
  M.seError NQ N ε (tq + tTest) Q + M.swapError tTest

/-- **Knowledge soundness and weak online simulation extractability of the spBCS compiler**
(module docstring) at the encoders `E₀`, the view laws `VE` of the query phases `Qs`, the format
bounds `hb` (every query phase opens at most `NQ` positions and every tree has at most `N` leaves,
so the verifier makes at most `M.kq NQ N` queries), the site layout `Λ`, the joint simulator `Sim`
on public statements `pub x`, the preimage samplers `T`, and the causal extractor `Ext` with
challenge errors `ε`. The simulator `VE.niSimulator` gives proofs in the format `B` of the
format bounds `hB` (`knowledgeGuarantees_max` takes `B = max NQ N`, `FormatBounds.max`). Every
adversary class is the paper's `def:adversary`:
`Quantum.QueryBoundedAdversary` in the QROM and `ROM.QueryBoundedAdversary` in the ROM, without
proof queries for knowledge soundness and soundness.

* `knowledge` (`thm:bcs-ks`(1), `def:narg-ks`): online extractability with the database extractor
  `dbExtractBits`, at `ksError`;
* `state_clause_qrom`: the clause on the joint state: at every auxiliary input and every value
  of the output and the verdict, the state of the adversary's register after measuring only its
  output in the extraction run is its state in the model's run;
* `soundness` (`thm:bcs-main`(2), the QROM): a statement without a witness with an accepted proof,
  at the same error;
* `knowledgeROM`, `soundnessROM` (`thm:bcs-ks`(2), `thm:bcs-main`(2) in the ROM): online
  extractability against the lazily sampled oracle and soundness against classical adversaries, at
  `ksErrorROM`;
* `weak_online_simulation_extractability_qrom` (`thm:bcs-se`(1), joint form): weak online simulation
  extractability in the QROM against query-bounded adversaries, with the simulator `niSimulator`
  run through `queryEncoding` and the database extractor `dbExtract`: the extraction run leaves the
  adversary's output, the challenger's registers, the verdict and the adversary's unmeasured
  (quantum) workspace in the model's simulated run's state, and wins without
  extraction with probability at most `seError`;
* `simExtractability` (`thm:bcs-se`(1)): weak simulation-sound extractability in the QROM
  against query-bounded adversaries for query-free tests that are classical predicates of the
  measured workspace, with the same simulator, at `seError`;
* `simExtractabilityQueryFree` (`thm:bcs-se`(1) through the implication from `def:bcs-se` to Unruh's
  Definition 14 in the paper's Section 6.1.2): for every adversary of the game (whose steps need
  not be channels, a larger class than `def:adversary`) and every query-free test of its residual
  state, Unruh's Prove with the test against the fresh extraction event of the adversary followed
  by the test;
* `simExtractabilityUnruh` (`thm:bcs-se`(1) through the same implication): for every query-bounded
  adversary and every query-free test, Unruh's Prove with the test against Unruh's Extract with the
  test;
* `simExtractabilitySimOracle`: for every query-bounded adversary and every test of its
  residual state with at most `tTest` queries to the final oracle, Prove with the test against the
  targeted extractor `E_T` with the test run after extraction on the simulated oracle, at
  `seErrorSimOracle`;
* `simExtractabilityROM` (`thm:bcs-se`(2)): weak online simulation extractability in the ROM
  (`def:bcs-se`, `WeakOnlineSimulationExtractableROM`) against query-bounded classical
  adversaries with an auxiliary output, with the program of the simulator `niSimulator` on
  uniform coins and the database extractor `dbExtract` on the table of the lazily sampled
  execution: oracle simulation error `0`, and extraction error `seErrorROM`, which is
  `errks^C(t + Q q_S)`. -/
structure KnowledgeGuarantees (E₀ : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    (Qs : ∀ x, M.IOPQueries V x) (VE : M.ViewEncoder E₀ Qs) {B : ℕ} (hB : M.FormatBounds Qs B B)
    {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) (Λ : SiteLayout Mg) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) {Wit : Type} (rel : Set (X × Wit))
    (Ext : CausalExtractor P t X Wit) (ε : ChIdx P t → ℝ≥0) : Prop where
  /-- Knowledge soundness in the QROM: online extractability. -/
  knowledge : ∀ (Z : Type) (t' : ℕ) (𝒢 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof × Z) t'),
    𝒢.OnlineExtracts (M.qVerifier Qs NQ N) NARG.QROM.compressedSim rel
      (NARG.QROM.compressedExt (M.dbExtractBits Ext)) 0 (M.ksError NQ N ε t')
  /-- The state clause of knowledge soundness in the QROM against the model's run. -/
  state_clause_qrom : ∀ (Z : Type) (t' : ℕ) (𝒢 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof × Z) t')
    (a : 𝒢.Aux) (vo : NARG.VerifiedOutput (Claim X M.NIProof × Z)),
    (M.qVerifier Qs NQ N).extractionOutputState Prod.fst NARG.QROM.compressedSim (𝒢.run a) (𝒢.run a).defaultOut vo =
      (M.qVerifier Qs NQ N).realOutputState Prod.fst (𝒢.modelRun a) vo
  /-- Soundness in the QROM. -/
  soundness : ∀ (t' : ℕ) (𝒜 : NARG.QROM.Adversary (queryBits k kN kS L) k e (Claim X M.NIProof) t'),
    𝒜.acceptsFalse (M.qVerifier Qs NQ N) rel ≤ M.ksError NQ N ε t'
  /-- Knowledge soundness in the ROM: online extractability against the lazily sampled oracle. -/
  knowledgeROM : ∀ (Z : Type) (t' : ℕ) (𝒢 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof × Z) t'),
    𝒢.OnlineExtracts (M.rVerifier Qs NQ N) NARG.ROM.OracleSampler.lazy.law rel (M.dbExtract Ext) 0
      (M.ksErrorROM NQ N ε t')
  /-- Soundness in the ROM. -/
  soundnessROM : ∀ (t' : ℕ) (𝒜 : NARG.ROM.Adversary (Query k kN kS L) (Out k e) (Claim X M.NIProof) t'),
    𝒜.acceptsFalse (M.rVerifier Qs NQ N) rel ≤ M.ksErrorROM NQ N ε t'
  /-- Weak online simulation extractability in the QROM: the joint form. -/
  weak_online_simulation_extractability_qrom : M.WeakOnlineSimulationExtractable B Qs rel
    Ext (M.kq NQ N) ((VE.niSimulator Λ hB pub Sim T).encode queryEncoding) (M.seError NQ N ε)
  /-- Simulation-sound extractability in the QROM. -/
  simExtractability : M.SimulationSoundExtractableFresh B Qs rel Ext (M.kq NQ N)
    ((VE.niSimulator Λ hB pub Sim T).encode queryEncoding) (M.seError NQ N ε)
  /-- Simulation-sound extractability in the QROM for query-free tests, with Unruh's Prove. -/
  simExtractabilityQueryFree : M.SimulationSoundExtractableQueryFree B Qs rel Ext
    (M.kq NQ N) ((VE.niSimulator Λ hB pub Sim T).encode queryEncoding) (M.seError NQ N ε)
  /-- Simulation-sound extractability in the QROM for query-free tests, in Unruh's form. -/
  simExtractabilityUnruh : M.SimulationSoundExtractableQueryFreeUnruh B Qs rel Ext
    (M.kq NQ N) ((VE.niSimulator Λ hB pub Sim T).encode queryEncoding) (M.seError NQ N ε)
  /-- Simulation-sound extractability in the QROM for tests that query the oracle, with the test
  answered by the simulated oracle after extraction. -/
  simExtractabilitySimOracle : M.SimulationSoundExtractableSimOracle B Qs rel Ext
    (M.kq NQ N) ((VE.niSimulator Λ hB pub Sim T).encode queryEncoding)
    (M.seErrorSimOracle NQ N ε)
  /-- Weak online simulation extractability in the ROM. -/
  simExtractabilityROM : M.WeakOnlineSimulationExtractableROM B Qs rel Ext (M.kq NQ N)
    (VE.niSimulator Λ hB pub Sim T).prog M.simQueries (M.seErrorROM NQ N ε)

variable {M}

omit [DecidableEq X] in
/-- **The counted spBCS simulator assigns only at the keys of its chain inputs.** -/
theorem simAssignsAtKeys_niJointSimulatorProg (hk : 0 < k) (Λ : SiteLayout Mg)
    {E₀ : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x}
    (VE : M.ViewEncoder E₀ Qs) (B : ℕ) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    M.SimAssignsAtKeys B (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) id :=
  simAssignsAtKeys_of_mapQuery (M.niSimulatorTotal Λ VE.toViewRead B pub Sim T).prog (fun _ _ => rfl)
    fun _ _ => M.assignsAtKeys_jointProg Λ VE.toViewRead B hk _ _ _ _ _ _ _

/-- **Knowledge soundness and weak online simulation extractability of the spBCS compiler**
(`KnowledgeGuarantees`) when the composite is causally round-by-round knowledge sound at the
causal extractor `Ext` with errors `ε` (`hrbr`, at some state function `St`), digests have at
least one byte (`hk`), and the query phases open at most `NQ` positions and the trees have at
most `N` leaves (`hb`), which bound the verifier's queries by `M.kq NQ N`, and `B` bounds both the
opened positions and the leaves per tree (`hB`), the proof format of the simulator. -/
@[headline]
theorem knowledgeGuarantees (hk : 0 < k) {E₀ : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E₀ Qs) {B : ℕ}
    (hB : M.FormatBounds Qs B B) {NQ N : ℕ} (hb : M.FormatBounds Qs NQ N) (Λ : SiteLayout Mg)
    {Pub : Type} (pub : X → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
    {Wit : Type} {rel : Set (X × Wit)} {Ext : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V Ext St ε) :
    M.KnowledgeGuarantees E₀ Qs VE hB hb Λ pub Sim T rel Ext ε where
  knowledge _ _ 𝒢 := onlineExtracts_qrom hrbr hb 𝒢
  state_clause_qrom _ _ 𝒢 a vo := (QROM.extractionOutputState_eq _ Prod.fst (𝒢.run a) _ vo).trans
    (𝒢.realOutputState_eq_model _ a vo)
  soundness _ 𝒜 := soundness_qrom hrbr hb 𝒜
  knowledgeROM _ _ 𝒢 := onlineExtracts_rom hrbr hb 𝒢
  soundnessROM _ 𝒜 := soundness_rom hrbr hb 𝒜
  weak_online_simulation_extractability_qrom := by
    rw [M.encode_niSimulator Λ E₀ VE hB]
    exact weak_online_simulation_extractability_qrom (B := B) Qs hb.queriesAtMost hrbr
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T)
      (simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T)
  simExtractability := by
    rw [M.encode_niSimulator Λ E₀ VE hB]
    exact simulation_sound_extractability (B := B) Qs hb.queriesAtMost hrbr
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T)
      (simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T)
  simExtractabilityQueryFree := by
    rw [M.encode_niSimulator Λ E₀ VE hB]
    exact simulation_sound_extractability_query_free (B := B) Qs hb.queriesAtMost hrbr
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T)
      (simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T)
  simExtractabilityUnruh := by
    rw [M.encode_niSimulator Λ E₀ VE hB]
    exact simulation_sound_extractability_query_free_unruh (B := B) Qs hb.queriesAtMost hrbr
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T)
      (simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T)
  simExtractabilitySimOracle := by
    rw [M.encode_niSimulator Λ E₀ VE hB]
    exact simulation_sound_extractability_sim_oracle (B := B) Qs hb.queriesAtMost hrbr
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T)
      (simAssignsAtKeys_niJointSimulatorProg hk Λ VE B pub Sim T)
  simExtractabilityROM := by
    rw [ViewEncoder.niSimulator, M.niSimulator_eq]
    exact weak_online_simulation_extractability_rom (B := B) (Qs := Qs)
      (fun _ _ => M.assignsAtKeys_jointProg Λ VE.toViewRead B hk _ _ _ _ _ _ _)
      (fun _ _ G => M.length_trace_jointProg_le (h := G) Λ VE.toViewRead B _ _ _ _ _ _ _)
      hrbr hb.queriesAtMost

/-- **`knowledgeGuarantees` with one format bound**: the simulator's proof format is
`max NQ N`, whose format bounds follow from `hb` (`FormatBounds.max`). -/
theorem knowledgeGuarantees_max (hk : 0 < k) {E₀ : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E₀ Qs) {NQ N : ℕ}
    (hb : M.FormatBounds Qs NQ N) (Λ : SiteLayout Mg)
    {Pub : Type} (pub : X → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
    {Wit : Type} {rel : Set (X × Wit)} {Ext : CausalExtractor P t X Wit} {St : CausalStateFn P t X}
    {ε : ChIdx P t → ℝ≥0} (hrbr : CausalRBRKnowledgeSound rel V Ext St ε) :
    M.KnowledgeGuarantees E₀ Qs VE hb.max hb Λ pub Sim T rel Ext ε :=
  knowledgeGuarantees hk VE hb.max hb Λ pub Sim T hrbr

end Knowledge

end

end GordieHowe.SPBCS
