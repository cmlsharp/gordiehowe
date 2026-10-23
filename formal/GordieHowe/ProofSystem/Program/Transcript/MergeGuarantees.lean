-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.MergeSetting

@[expose] public section

/-!
# The guarantees of the setting with merges of a multi-circuit IOP with forked domains

The guarantees of spBCS (paper `thm:bcs-main`) at the setting with merges of a
multi-circuit IOP with forked domains (`GordieHowe.SPBCS.ProofSystemTranscript.setting`), bundled in the form the
end-to-end theorem (paper `thm:e2e`) states them:

* `GordieHowe.SPBCS.ProofSystemTranscript.QueryBudget`: the verifier with merges makes at most `kq` queries on every
  accepting run;
* `GordieHowe.SPBCS.ProofSystemTranscript.KnowledgeGuarantees` (paper `thm:e2e`(2)): knowledge soundness and
  soundness in the QROM and the ROM at the verifier with budget `kq`, with the largest round error
  of the IOP's soundness data as `errk`;
* `GordieHowe.SPBCS.ProofSystemTranscript.Guarantees` (paper `thm:e2e`(1)–(5)): these, completeness at error
  `errc` (`GordieHowe.SPBCS.CompletenessGuarantees`), everlasting zero knowledge at HVZK error `errc`
  (`GordieHowe.SPBCS.PrivacyGuarantees`), unconditional witness indistinguishability, and weak online
  simulation extractability in the QROM and the ROM;
* `GordieHowe.SPBCS.ProofSystemTranscript.CoinGuarantees` (paper `thm:e2e`(1)–(5) for an honest prover with coins):
  the same, with completeness, everlasting zero knowledge and witness indistinguishability at the honest
  prover whose coins are drawn (`GordieHowe.RealizedProgram.ProofSystem.IOP.coinHonest`); parts (5) of both are
  `GordieHowe.SPBCS.ProofSystemTranscript.SimGuarantees`, which read the honest prover only through its simulator;
* `GordieHowe.SPBCS.ProofSystemTranscript.knowledgeGuarantees`, `GordieHowe.SPBCS.ProofSystemTranscript.guarantees`,
  `GordieHowe.SPBCS.ProofSystemTranscript.coinGuarantees`: they hold for every soundness data and every honest prover
  whose completeness events have together probability at most `errc`
  (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.ErrorBound`; over the coins, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.CoinErrorBound`).
-/

namespace GordieHowe.ROM

open GordieHowe.IOP
open scoped ENNReal

variable {B : Type} [Fintype B] [Nonempty B]

/-- **A one-point first coordinate**: the uniform probability on `Unit × B` is that on `B` at the
point `()`. -/
theorem probUniform_unit_prod (p : Unit × B → Prop) :
    Pr[z ← (Unit × B) : p z] = Pr[y ← B : p ((), y)] := by
  rw [probUniform_prod_eq_sum, Fintype.sum_unique, Fintype.card_unit, Nat.cast_one, inv_one,
    one_mul]
  try rfl

omit [Fintype B] [Nonempty B] in
/-- **A one-point average**: the uniform average over `Unit` is the value at `()`. -/
theorem sum_unit_inv_card_mul (f : Unit → ℝ≥0∞) :
    ∑ r, (Fintype.card Unit : ℝ≥0∞)⁻¹ * f r = f () := by
  rw [Fintype.sum_unique, Fintype.card_unit, Nat.cast_one, inv_one, one_mul]

end GordieHowe.ROM

namespace GordieHowe.SPBCS

open GordieHowe.QROM
open scoped NNReal ENNReal

/-- **The knowledge error in the paper's form** (`thm:bcs-main`(2)): an answer has `k + e` bytes
(`Out.card_eq_two_pow`), so the oracle-simulation term is `2 √(kq / 2^(8(k + e)))`. -/
theorem knowledgeError_eq (k e kq t c cP : ℕ) (κ : ℝ≥0) :
    knowledgeError k e kq t c cP κ = 2 * esqrt (kq / 2 ^ (8 * (k + e))) +
      6 * (t : ℝ≥0∞) ^ 2 * ((κ : ℝ≥0∞) + (((max 2 c + cP + 1) * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) := by
  rw [knowledgeError, Out.card_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal

variable {Stmt W : Type} {rel : Set (Stmt × W)}

namespace ProofSystemTranscript

variable {C : RealizedProgram.ProofSystem.IOP Stmt W rel} {T : ProofSystemTranscript C} {kS : ℕ}

variable (T kS) (hb : T.MergeBounds kS)

/-- **A query budget of the verifier with merges**: on every accepting run at the setting with
merges, the verifier makes at most `kq` queries (paper `def:bcs-quantities`, `k_q`). -/
def QueryBudget (kq : ℕ) : Prop :=
  ∀ x h π, (T.setting kS hb).model.Accepts h x π ((T.setting kS hb).queries x) →
    ((T.setting kS hb).model.queries x π h ((T.setting kS hb).queries x)).length ≤ kq

/-- **Knowledge soundness and soundness at the setting with merges** (paper `thm:e2e`(2),
`thm:bcs-main`(2)), at the verifier with merges with query budget `kq` (`hkq`), for the relation
`rel'` and the IOP's extractor with its witness read by `g`, with the largest round error
`maxError Sd.error` of the soundness data `Sd` as `errk`:

* in the QROM, online extractability (DFMS22 Definition 3.1, p. 10, with simulation error `0`)
  against `t`-query adversaries without proof queries with an auxiliary output, and soundness, with error
  `knowledgeError k e kq (t + kq) c n_J errk`: `2 √(kq/2^(8(k + e))) + 6 (t + kq)² (errk +
  c' (t + kq)/2^(8k))` with `c' = max 2 c + n_J + 1` (`knowledgeError_eq`), at `k`-byte digests,
  `k + e`-byte streams, `c = digests` and `n_J = C.merges.nJ`;
* in the ROM, the same against classical adversaries with error
  `knowledgeErrorROM k (t + kq) c n_J errk`: `(t + kq) (errk + c' (t + kq)/2^(8k))`. -/
structure KnowledgeGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} (rel' : Set (Stmt × W'))
    (g : Stmt → W → W') {kq : ℕ} (hkq : T.QueryBudget kS hb kq) : Prop where
  /-- Knowledge soundness in the QROM: online extractability. -/
  knowledge : ∀ {Zo : Type} {t : ℕ} (𝒢 : (T.setting kS hb).QROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof × Zo) t),
    𝒢.OnlineExtracts (T.verifier kS hb kq) NARG.QROM.compressedSim rel'
      (NARG.QROM.compressedExt ((T.setting kS hb).model.dbExtractBits (C.extractor.mapWit g))) 0
      (knowledgeError T.k (Configurations.fsExtraBytes + T.maxGrant) kq (t + kq) (digests (C := C))
        C.merges.nJ (maxError Sd.error))
  /-- Soundness in the QROM. -/
  soundness : ∀ {t : ℕ} (𝒜 : (T.setting kS hb).QROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof) t),
    𝒜.acceptsFalse (T.verifier kS hb kq) rel' ≤
      knowledgeError T.k (Configurations.fsExtraBytes + T.maxGrant) kq (t + kq) (digests (C := C))
        C.merges.nJ (maxError Sd.error)
  /-- Knowledge soundness in the ROM: online extractability against the lazily sampled
  oracle. -/
  knowledgeROM : ∀ {Zo : Type} {t : ℕ} (𝒢 : (T.setting kS hb).ROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof × Zo) t),
    𝒢.OnlineExtracts (T.verifierROM kS hb kq) NARG.ROM.OracleSampler.lazy.law rel' ((T.setting kS hb).model.dbExtract (C.extractor.mapWit g)) 0
      (knowledgeErrorROM T.k (t + kq) (digests (C := C)) C.merges.nJ (maxError Sd.error))
  /-- Soundness in the ROM. -/
  soundnessROM : ∀ {t : ℕ} (𝒜 : (T.setting kS hb).ROMAdversary (Claim Stmt (T.setting kS hb).model.NIProof) t),
    𝒜.acceptsFalse (T.verifierROM kS hb kq) rel' ≤
      knowledgeErrorROM T.k (t + kq) (digests (C := C)) C.merges.nJ (maxError Sd.error)

open Classical in
/-- **The simulation-extraction guarantees of the end-to-end theorem at the setting with merges**
(paper `thm:e2e`(5), `thm:bcs-se`), at the verifier with query budget `kq` (`hkq`), the soundness
data `Sd`, the relation `rel'` with the extractor's witness read by `g`, and the simulator of the
honest prover `Hc` (`RealizedProgram.ProofSystem.IOP.simulator SD`): weak online simulation extractability in the joint
form of `def:bcs-se`, in the QROM (`SPBCS.WeakOnlineSimulationExtractable`) and in the ROM
(`SPBCS.WeakOnlineSimulationExtractableROM`, with the classical simulator program and oracle
simulation error `0`), and simulation-sound extractability (Unruh 2017 Definition 14, p. 21, weak
variant) for residual-state tests that make no oracle queries and for tests answered by the
simulated oracle after extraction, with `2 |Pos| + t.size n + Σ_d nb d` simulator queries per
proof query. They read the honest prover only through its simulator. -/
structure SimGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} (rel' : Set (Stmt × W'))
    (g : Stmt → W → W') {kq : ℕ} (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB)
    {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) : Prop where
  /-- Part (5): weak online simulation extractability in the QROM, the joint form of
  `def:bcs-se`. -/
  simOnlineExtractability : (T.setting kS hb).model.WeakOnlineSimulationExtractable pB
    (T.setting kS hb).queries rel' (C.extractor.mapWit g) kq hkq
    ((T.simulator kS hb hf SD).encode queryEncoding)
    ((T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
      (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
        ∑ d, C.shape.nb d))
  /-- Part (5): weak online simulation extractability in the ROM, the joint form of
  `def:bcs-se`. -/
  simOnlineExtractabilityROM : T.SimExtractableROM kS hb hf Hc rel' (C.extractor.mapWit g) kq
    (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
      ∑ d, C.shape.nb d)
    ((T.setting kS hb).model.simExtractionErrorROM kq (maxError Sd.error)
      (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
        ∑ d, C.shape.nb d))
  /-- Part (5) in Unruh's weak fresh form, for query-free tests. -/
  simExtractability : T.SimExtractable kS hb hf Hc rel' (C.extractor.mapWit g) kq
    ((T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
      (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
        ∑ d, C.shape.nb d))
  /-- Part (5) for tests that query the oracle, answered by the simulated oracle after
  extraction. -/
  simExtractabilitySimOracle : T.SimExtractableSimOracle kS hb hf Hc rel' (C.extractor.mapWit g) kq
    fun tq tTest Q => (T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
        (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
          ∑ d, C.shape.nb d) (tq + tTest) Q +
      (T.setting kS hb).model.swapError tTest


open Classical in
/-- **The guarantees of the end-to-end theorem at the setting with merges** (paper `thm:e2e`,
`thm:bcs-main`), at the verifier with query budget `kq` (`hkq`), the soundness data `Sd`, the
relation `rel'` with the extractor's witness read by `g`, and the honest prover `Hc` with
completeness and HVZK error `errc`:

1. completeness (`SPBCS.CompletenessGuarantees`) at every value `c` of the honest prover's
   coins (the honest prover at `c`, with the one-point coin space `Unit`), for a fixed statement and
   at a drawn witness, at `errc + errov + errkey`; and completeness of the honest prover with
   uniform coins, Merkle salts and salt (`prover`) against adversaries choosing
   the statement after their queries (`NARG.ROM.Complete`, `NARG.QROM.Complete`), at
   `errc + errov + errkey` plus `t/2^(8 kS)` (ROM) or `2t/2^(4 kS)` (QROM);
2. knowledge soundness and soundness in the QROM and the ROM (`KnowledgeGuarantees`);
3. everlasting zero knowledge in the QROM and the ROM, and the query-counted and
   sampler forms (`SPBCS.PrivacyGuarantees` at HVZK error `errc`, the compiled simulator of the
   simulator `RealizedProgram.ProofSystem.IOP.simulator SD` of the honest prover's simulator data);
4. unconditional adaptive multi-theorem witness indistinguishability at
   `Q · wiError errc (choiceCount ℓ)`;
5. weak online simulation extractability and simulation-sound extractability
   (`SimGuarantees`). -/
structure Guarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} (rel' : Set (Stmt × W'))
    (g : Stmt → W → W') {kq : ℕ} (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB)
    {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) (errc : ℝ≥0) : Prop
    extends T.SimGuarantees kS hb Sd rel' g hkq hf Hc where
  /-- Part (1): completeness, at every value `c` of the honest prover's coins. -/
  completeness : ∀ c : Hc.Coins, (T.setting kS hb).model.CompletenessGuarantees
    (T.setting kS hb).encoder (T.setting kS hb).queries
    (fun y (_ : Unit) => RealizedProgram.ProofSystem.IOP.honest Hc y c) relI errc
  /-- Part (1): completeness in the ROM against adversaries choosing the statement, at uniform
  coins, Merkle salts and salt. -/
  completeROM : NARG.ROM.Complete (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc))
    (T.verifierROM kS hb kq) (fun x π => Claim.mk x π.val) (fun x y => (x, y) ∈ relI) fun t =>
      (errc : ℝ≥0∞) + (T.setting kS hb).model.overrun +
        SPBCS.keyCollision (∑ q : C.shape.term.Leaf, C.rounds q.label) T.k + t / 2 ^ (8 * kS)
  /-- Part (1): completeness in the QROM against adversaries choosing the statement, at uniform
  coins, Merkle salts and salt. -/
  completeQROM : NARG.QROM.Complete queryEncoding
    (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc))
    (T.verifier kS hb kq) (fun x π => Claim.mk x π.val) (fun x y => (x, y) ∈ relI) fun t =>
      (errc : ℝ≥0∞) + (T.setting kS hb).model.overrun +
        SPBCS.keyCollision (∑ q : C.shape.term.Leaf, C.rounds q.label) T.k + 2 * t / 2 ^ (4 * kS)
  /-- Part (2): knowledge soundness and soundness. -/
  knowledge : T.KnowledgeGuarantees kS hb Sd rel' g hkq
  /-- Part (3): everlasting zero knowledge. -/
  zeroKnowledge : (T.setting kS hb).model.PrivacyGuarantees (T.setting kS hb).encoder
    (T.setting kS hb).queries (T.setting kS hb).viewEncoder hf (T.setting kS hb).layout
    (RealizedProgram.ProofSystem.IOP.honest Hc) id (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb) relI errc
  /-- Part (4): unconditional witness indistinguishability. -/
  witnessIndist : ∀ (eX : SPBCS.BitEncoding Stmt) (eW : SPBCS.BitEncoding I') (Q ℓ : ℕ),
    (T.setting kS hb).model.WitnessIndistinguishableOfLength
      (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.honest Hc)) eX eW relI Q ℓ
      (Q * (T.setting kS hb).model.wiError errc (SPBCS.choiceCount ℓ))

open Classical in
/-- **The guarantees of the end-to-end theorem at the setting with merges for an honest prover
with coins** (paper `thm:e2e`, `thm:bcs-main`, with the honest prover's coins drawn as in
`def:iop-complete` and `def:hvzk`): as `Guarantees`, for honest inputs `J` related to statements by
`relJ` and read with uniform coins `ω` as the honest prover's inputs `inp y ω`, with parts (1), (3)
and (4) at the honest prover with coins:

1. completeness at every value `c` of the honest prover's coins, over uniform coins `ω`
   (`SPBCS.CompletenessGuarantees` at the honest prover `RealizedProgram.ProofSystem.IOP.honest Hc (inp y ω) c`
   with the coin space `Ω`), and completeness of the honest prover with uniform coins `ω`, honest
   coins, Merkle salts and salt against adversaries choosing the statement (`NARG.ROM.Complete`,
   `NARG.QROM.Complete`);
3. everlasting zero knowledge (`SPBCS.PrivacyGuarantees` at the honest prover with coins
   `RealizedProgram.ProofSystem.IOP.coinHonest Hc inp` and HVZK error `errc`);
4. unconditional adaptive multi-theorem witness indistinguishability at
   `Q · wiError errc (choiceCount ℓ)`, on `relJ`;

and parts (2) and (5) as in `Guarantees`. -/
structure CoinGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} (rel' : Set (Stmt × W'))
    (g : Stmt → W → W') {kq : ℕ} (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB)
    {I' : Type} {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) {J Ω : Type} [Fintype Ω]
    [Nonempty Ω] (relJ : Set (Stmt × J)) (inp : J → Ω → I') (errc : ℝ≥0) : Prop
    extends T.SimGuarantees kS hb Sd rel' g hkq hf Hc where
  /-- Part (1): completeness, at every value `c` of the honest prover's coins, over the coins `ω`. -/
  completeness : ∀ c : Hc.Coins, (T.setting kS hb).model.CompletenessGuarantees
    (T.setting kS hb).encoder (T.setting kS hb).queries
    (fun y (ω : Ω) => RealizedProgram.ProofSystem.IOP.honest Hc (inp y ω) c) relJ errc
  /-- Part (1): completeness in the ROM against adversaries choosing the statement, at uniform
  coins `ω`, honest coins, Merkle salts and salt. -/
  completeROM : NARG.ROM.Complete
    (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.coinHonest Hc inp))
    (T.verifierROM kS hb kq) (fun x π => Claim.mk x π.val) (fun x y => (x, y) ∈ relJ) fun t =>
      (errc : ℝ≥0∞) + (T.setting kS hb).model.overrun +
        SPBCS.keyCollision (∑ q : C.shape.term.Leaf, C.rounds q.label) T.k + t / 2 ^ (8 * kS)
  /-- Part (1): completeness in the QROM against adversaries choosing the statement, at uniform
  coins `ω`, honest coins, Merkle salts and salt. -/
  completeQROM : NARG.QROM.Complete queryEncoding
    (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.coinHonest Hc inp))
    (T.verifier kS hb kq) (fun x π => Claim.mk x π.val) (fun x y => (x, y) ∈ relJ) fun t =>
      (errc : ℝ≥0∞) + (T.setting kS hb).model.overrun +
        SPBCS.keyCollision (∑ q : C.shape.term.Leaf, C.rounds q.label) T.k + 2 * t / 2 ^ (4 * kS)
  /-- Part (2): knowledge soundness and soundness. -/
  knowledge : T.KnowledgeGuarantees kS hb Sd rel' g hkq
  /-- Part (3): everlasting zero knowledge. -/
  zeroKnowledge : (T.setting kS hb).model.PrivacyGuarantees (T.setting kS hb).encoder
    (T.setting kS hb).queries (T.setting kS hb).viewEncoder hf (T.setting kS hb).layout
    (RealizedProgram.ProofSystem.IOP.coinHonest Hc inp) id (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb) relJ errc
  /-- Part (4): unconditional witness indistinguishability. -/
  witnessIndist : ∀ (eX : SPBCS.BitEncoding Stmt) (eW : SPBCS.BitEncoding J) (Q ℓ : ℕ),
    (T.setting kS hb).model.WitnessIndistinguishableOfLength
      (T.prover kS hb hf (RealizedProgram.ProofSystem.IOP.coinHonest Hc inp)) eX eW relJ Q ℓ
      (Q * (T.setting kS hb).model.wiError errc (SPBCS.choiceCount ℓ))

variable {T kS hb}

/-- **Knowledge soundness and soundness at the setting with merges** (`KnowledgeGuarantees`) for
the soundness data `Sd` of the IOP, the relation `rel'` into which the witness map `g` sends the
IOP's relation (`hg`), and the query budget `kq` (`hkq`): `ProofSystemTranscript.knowledge`,
`soundness`, `knowledgeROM`, `soundnessROM`. -/
theorem knowledgeGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : T.QueryBudget kS hb kq) : T.KnowledgeGuarantees kS hb Sd rel' g hkq where
  knowledge 𝒢 := ProofSystemTranscript.knowledge Sd hg hkq 𝒢
  soundness 𝒜 := ProofSystemTranscript.soundness Sd hg hkq 𝒜
  knowledgeROM 𝒢 := ProofSystemTranscript.knowledgeROM Sd hg hkq 𝒢
  soundnessROM 𝒜 := ProofSystemTranscript.soundnessROM Sd hg hkq 𝒜

open Classical in
/-- **Weak online simulation extractability at the setting with merges in the QROM, joint form**
(`SPBCS.weak_online_simulation_extractability_qrom`, paper `def:bcs-se`, `thm:bcs-se`(1)) with the
simulator of the setting (`simulator`) run through `queryEncoding` and the database extractor at the IOP's extractor
mapped by `g`, at the verifier's query budget `kq` (`hkq`), with `q = 2 |Pos| + t.size n + Σ_d nb d`
simulator queries per proof query (`RealizedProgram.ProofSystem.IOP.card_site`). -/
theorem simOnlineExtractability [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type}
    {rel' : Set (Stmt × W')} {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel')
    {kq : ℕ} (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type}
    {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) :
    (T.setting kS hb).model.WeakOnlineSimulationExtractable pB
      (T.setting kS hb).queries rel' (C.extractor.mapWit g) kq hkq
      ((T.simulator kS hb hf SD).encode queryEncoding)
      ((T.setting kS hb).model.simExtractionError kq (maxError Sd.error)
        (2 * Fintype.card (T.setting kS hb).model.Pos + C.shape.term.size C.rounds +
          ∑ d, C.shape.nb d)) := by
  have hk : 0 < (T.setting kS hb).k := hb.k_pos
  have h := SPBCS.weak_online_simulation_extractability_qrom (M := (T.setting kS hb).model)
    (B := pB) (T.setting kS hb).queries hkq (Sd.causal_rbr.mapWit hg)
    ((T.setting kS hb).model.niJointSimulatorProg (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder.toViewRead pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
    (SPBCS.simAssignsAtKeys_niJointSimulatorProg hk (T.setting kS hb).layout
      (T.setting kS hb).viewEncoder pB id (RealizedProgram.ProofSystem.IOP.simulator SD)
      (T.preimages kS hb))
  rw [simulator, (T.setting kS hb).model.encode_niSimulator (T.setting kS hb).layout
    (T.setting kS hb).encoder (T.setting kS hb).viewEncoder hf, ← C.card_site]
  exact h

/-- **The simulation-extraction guarantees at the setting with merges** (`SimGuarantees`) for the
soundness data `Sd`, the witness map `g` into `rel'` (`hg`), the query budget `kq` (`hkq`) and the
simulator of every honest prover `Hc`: `simOnlineExtractability`, `simExtractabilityROM`,
`simExtractability`, `simExtractabilitySimOracle`. -/
theorem simGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type}
    {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) :
    T.SimGuarantees kS hb Sd rel' g hkq hf Hc where
  simOnlineExtractability := simOnlineExtractability Sd hg hkq hf Hc
  simOnlineExtractabilityROM := simExtractabilityROM Sd hg hkq hf Hc
  simExtractability := simExtractability Sd hg hkq hf Hc
  simExtractabilitySimOracle := simExtractabilitySimOracle Sd hg hkq hf Hc

/-- **The guarantees of the end-to-end theorem at the setting with merges** (`Guarantees`) for
the soundness data `Sd`, the witness map `g` into `rel'` (`hg`), the query budget `kq` (`hkq`) and
an honest prover `Hc` whose completeness events have together probability at most `errc` (`hE`):
the completeness guarantees at `RealizedProgram.ProofSystem.IOP.completeness_of_errorBound`, the knowledge
guarantees, the zero-knowledge guarantees at `RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound`, witness
indistinguishability, and simulation extractability (`simGuarantees`). -/
theorem guarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type}
    {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) {errc : ℝ≥0}
    (hE : Hc.app.ErrorBound fun _ => errc) :
    T.Guarantees kS hb Sd rel' g hkq hf Hc errc :=
  have hzk := (T.setting kS hb).model.privacyGuarantees (T.setting kS hb).viewEncoder hf
    (T.setting kS hb).layout id (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb)
    (RealizedProgram.ProofSystem.IOP.hvzk_of_errorBound Hc hE)
  { completeness := fun c => (T.setting kS hb).model.completenessGuarantees fun x y hy =>
      (ROM.probUniform_unit_prod _).trans_le (RealizedProgram.ProofSystem.IOP.completeness_of_errorBound Hc hE c x y hy)
    completeROM := by
      have h := (T.setting kS hb).model.complete_rom _ (T.setting kS hb).encoder
        (T.setting kS hb).queries (fun x y => (x, y) ∈ relI) (T.setting kS hb).layout
        (T.setting kS hb).viewEncoder hf
        (fun x y hy => ROM.probUniform_prod_le fun c =>
          RealizedProgram.ProofSystem.IOP.completeness_of_errorBound Hc hE c x y hy) kq
      simp only [SPTerm.size_eq_sum] at h
      exact h
    completeQROM := by
      have h := (T.setting kS hb).model.complete_qrom _ (T.setting kS hb).encoder
        (T.setting kS hb).queries (fun x y => (x, y) ∈ relI) (T.setting kS hb).layout
        (T.setting kS hb).viewEncoder hf
        (fun x y hy => ROM.probUniform_prod_le fun c =>
          RealizedProgram.ProofSystem.IOP.completeness_of_errorBound Hc hE c x y hy) kq
      simp only [SPTerm.size_eq_sum] at h
      exact h
    knowledge := knowledgeGuarantees Sd hg hkq
    zeroKnowledge := hzk
    witnessIndist := hzk.witnessIndist
    toSimGuarantees := simGuarantees Sd hg hkq hf Hc }

/-- **The guarantees of the end-to-end theorem at the setting with merges for an honest prover
with coins** (`CoinGuarantees`) for the soundness data `Sd`, the witness map `g` into `rel'`
(`hg`), the query budget `kq` (`hkq`) and an honest prover `Hc` whose completeness events have
together, over the coins `ω`, probability at most `errc` (`hE`): the completeness guarantees at
`RealizedProgram.ProofSystem.IOP.completeness_coins`, the knowledge guarantees, the zero-knowledge guarantees at
`RealizedProgram.ProofSystem.IOP.hvzk_coins`, witness indistinguishability, and simulation
extractability (`simGuarantees`). -/
theorem coinGuarantees [Inhabited W] [DecidableEq Stmt] (Sd : C.Sound) {W' : Type} {rel' : Set (Stmt × W')}
    {g : Stmt → W → W'} (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') {kq : ℕ}
    (hkq : T.QueryBudget kS hb kq) {pB : ℕ} (hf : T.ProofFormat kS hb pB) {I' : Type}
    {relI : Set (Stmt × I')} {SD : C.SimData} (Hc : C.Honest SD I' relI) {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (Stmt × J)} {inp : J → Ω → I'}
    {errc : ℝ≥0} (hE : Hc.app.CoinErrorBound relJ inp fun _ => errc) :
    T.CoinGuarantees kS hb Sd rel' g hkq hf Hc relJ inp errc :=
  have hzk := (T.setting kS hb).model.privacyGuarantees (T.setting kS hb).viewEncoder hf
    (T.setting kS hb).layout id (RealizedProgram.ProofSystem.IOP.simulator SD) (T.preimages kS hb)
    (RealizedProgram.ProofSystem.IOP.hvzk_coins Hc hE)
  { completeness := fun c => (T.setting kS hb).model.completenessGuarantees
      (RealizedProgram.ProofSystem.IOP.completeness_coins Hc hE c)
    completeROM := by
      have h := (T.setting kS hb).model.complete_rom _ (T.setting kS hb).encoder
        (T.setting kS hb).queries (fun x y => (x, y) ∈ relJ) (T.setting kS hb).layout
        (T.setting kS hb).viewEncoder hf
        (fun x y hy => RealizedProgram.ProofSystem.IOP.completeness_coinHonest Hc hE x y hy) kq
      simp only [SPTerm.size_eq_sum] at h
      exact h
    completeQROM := by
      have h := (T.setting kS hb).model.complete_qrom _ (T.setting kS hb).encoder
        (T.setting kS hb).queries (fun x y => (x, y) ∈ relJ) (T.setting kS hb).layout
        (T.setting kS hb).viewEncoder hf
        (fun x y hy => RealizedProgram.ProofSystem.IOP.completeness_coinHonest Hc hE x y hy) kq
      simp only [SPTerm.size_eq_sum] at h
      exact h
    knowledge := knowledgeGuarantees Sd hg hkq
    zeroKnowledge := hzk
    witnessIndist := hzk.witnessIndist
    toSimGuarantees := simGuarantees Sd hg hkq hf Hc }

end ProofSystemTranscript

end GordieHowe.SPBCS
