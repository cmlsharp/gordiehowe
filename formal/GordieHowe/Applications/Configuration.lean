-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Transcript.MergeGuarantees
public import GordieHowe.ProofSystem.Program.Transcript.GrantedLoads
public import GordieHowe.Applications.Configuration.Instantiate

@[expose] public section

/-!
# The configurations under spBCS, generically

A configuration with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP`) is compiled by spBCS
at its spBCS setting (`GordieHowe.SPBCS.ProofSystemTranscript.setting`). Its headline statements
are the statements of that setting (`GordieHowe/ProofSystem/Program/Transcript/MergeSetting.lean`,
`GordieHowe/ProofSystem/Program/Transcript/MergeCompletenessAdaptive.lean`) at the configuration's IOP, transcript, salt
length, relations, honest prover and figures, with the figures' side conditions discharged once.

This module states them once, generically:

* `GordieHowe.Configuration`: the data of a configuration (the compiled-circuit type, the IOP, its soundness
  data, its transcript, the Fiat–Shamir salt length, the headline relation and the witness map,
  the honest prover and its completeness error as type families, the fixed honest strategy, and the
  figures: rounds, Chernoff exponent, leaves, queried leaves, verifier queries, the largest round
  error, digests per input, query caps, positions and the digest length);
* `GordieHowe.Configuration.GrantedFacts`: the facts the generic proofs use, and `GordieHowe.Configuration.Facts`, the form
  of a configuration without granted points, which extends it. Among them are the guarantees of
  the end-to-end theorem at the configuration's IOP (`knowledge`, `e2e`), which a configuration
  proves as an instance of the proof system's end-to-end theorem
  (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e`, paper
  `thm:e2e`); every headline follows from them and the figures;
* the templates (`@[config_template]`, `GordieHowe/Applications/Configuration/Instantiate.lean`) in four families:
  `Common` (the setting, the extractor, the knowledge errors, the verifiers, the honest prover and
  the headlines every configuration has), `GordieHowe.Configuration.ZeroKnowledgeROM` (query-counted zero knowledge in the ROM, the
  ROM parameters' form), `Query` (query-counted zero knowledge in the QROM, the QROM parameters'
  form) and `GordieHowe.Configuration.AdaptiveCompleteness` (adaptive completeness).

A configuration instantiates them with `instantiate_config N from [families] R F`, where `R` is its
record and `F` its facts (`Facts` coerced to `GrantedFacts`); the instances' statements show the
configuration's own definitions and figures. A configuration whose record depends on data (the
ring configurations' signer) instantiates them under binders,
`instantiate_config N from [families] (x : X) => R x (F x)`.

The fact `GordieHowe.SPBCS.ProofSystemTranscript.overrun_le_at_granted` (the overrun when rounds are granted extra
stream bytes) is generic in the IOP and stated here, before the record.
-/

namespace GordieHowe.SPBCS.ProofSystemTranscript

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS GordieHowe.SPBCS GordieHowe.QROM

variable {Stmt W : Type} {rel : Set (Stmt × W)} {C : RealizedProgram.ProofSystem.IOP Stmt W rel}
  {T : ProofSystemTranscript C} {kS : ℕ}

/-- **The overrun of the spBCS setting at a Chernoff exponent `E` with granted points**: when
every round's load passes the test `2^-E` at `z = 65/64` on `k + fsExtraBytes` bytes plus its grant
(`SpecReaders.AllGranted`), the overrun is at most the round count over `2^E`. -/
theorem overrun_le_at_granted (hb : T.MergeBounds kS) (E : ℕ)
    (h : ∀ j, (T.readers j).AllGranted fun g L =>
      Configurations.PassesChernoff (65 / 64) ((1 / 2) ^ E) (T.k + Configurations.fsExtraBytes + g) L) :
    (T.setting kS hb).model.overrun ≤ (∑ q : C.shape.term.Leaf, C.rounds q.label : ℕ) / 2 ^ E := by
  have hc := card_chIdx_le (C := C)
  calc (T.setting kS hb).model.overrun
      = ∑ c : ChIdx C.P C.term, (C.samplersOf T.readers T.k (Configurations.fsExtraBytes + T.maxGrant) T.stream
          c.leaf.label c.idx).rejectionProb := rfl
    _ ≤ ∑ _c : ChIdx C.P C.term, ENNReal.ofReal ((1 / 2) ^ E) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hc' : Configurations.PassesChernoff (65 / 64) ((1 / 2) ^ E) (T.stream c.leaf.label c.idx)
            ((T.readers c.leaf.label) c.idx).load := h c.leaf.label c.idx
        unfold RealizedProgram.ProofSystem.IOP.samplersOf
        rw [SpecReaders.sampler_rejectionProb _ (T.stream_le c.leaf.label c.idx)]
        exact ((T.readers c.leaf.label c.idx).failProb_le (by norm_num) hc'.pow_lt _ _).trans
          (ENNReal.ofReal_le_ofReal hc'.bound_le)
    _ = Fintype.card (ChIdx C.P C.term) * ENNReal.ofReal ((1 / 2) ^ E) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
        rw [Configurations.nat_mul_ofReal_pow]
        exact ENNReal.div_le_div_right (by exact_mod_cast hc) _

end GordieHowe.SPBCS.ProofSystemTranscript

namespace GordieHowe.Configuration

open IOP IOP.ProtocolSpec IOP.SPTerm GordieHowe.SPBCS GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open scoped NNReal ENNReal

/-- **The data of a configuration under spBCS** (module docstring). Every field is
data; the facts the generic proofs use are `Configuration.GrantedFacts`. -/
structure _root_.GordieHowe.Configuration where
  /-- The compiled circuits, with the trust bundle that relates them to the program. -/
  Compiled : Type
  /-- The statements. -/
  Stmt : Type
  /-- The decision of equality of statements: the database extractor (`SPBCS.dbExtract`) reads
  the recorded inputs whose statement is the one it extracts at. -/
  [decEq : DecidableEq Stmt]
  /-- The witnesses of the IOP's relation. -/
  Wit : Type
  /-- The IOP's relation. -/
  rel : Set (Stmt × Wit)
  /-- The multi-circuit IOP with forked domains at the compiled circuits. -/
  iop : Compiled → RealizedProgram.ProofSystem.IOP Stmt Wit rel
  /-- Its soundness data. -/
  sound : ∀ C, (iop C).Sound
  /-- Its transcript: label, digests, codecs and challenge readers. -/
  T : ∀ C, ProofSystemTranscript (iop C)
  /-- The Fiat–Shamir salt length in bytes. -/
  kS : ℕ
  /-- The witnesses of the headline relation. -/
  Wit' : Type
  /-- The headline relation. -/
  rel' : Set (Stmt × Wit')
  /-- The map from the IOP's witnesses to the headline relation's, applied by the extractor. -/
  g : Stmt → Wit → Wit'
  /-- The trust type of the honest prover (the compiler's completeness) at the compiled circuits. -/
  TA : Compiled → Prop
  /-- The valuations the honest strategies are stated over. -/
  Val : Type
  /-- The honest strategies on honest inputs `Inp` related to valuations by `relH`. -/
  Strategy : (Inp : Type) → Set (Val × Inp) → Type
  /-- The honest relation at the statements, from the strategy's relation at the valuations. -/
  hrel : {Inp : Type} → Set (Val × Inp) → Set (Stmt × Inp)
  /-- The simulator data of the IOP: data apart from the honest prover and the soundness data. -/
  sim : ∀ C, (iop C).SimData
  /-- The honest prover of the IOP at a strategy, simulated by `sim`. -/
  honest : ∀ C, TA C → ∀ {Inp : Type} {relH : Set (Val × Inp)}, Strategy Inp relH →
    (iop C).Honest (sim C) Inp (hrel relH)
  /-- The completeness error of a strategy (the paper's `errc`): the summed probabilities of its
  completeness events. -/
  err : ∀ {Inp : Type} {relH : Set (Val × Inp)}, Strategy Inp relH → ℝ≥0
  /-- The honest inputs of the fixed honest strategy. -/
  HonestIn : Type
  /-- The relation of the fixed honest strategy at the valuations. -/
  relH : Set (Val × HonestIn)
  /-- The fixed honest strategy. -/
  strategy : Strategy HonestIn relH
  /-- The statement of an honest input of the fixed strategy. -/
  keyStmtOf : HonestIn → Stmt
  /-- A default witness of the IOP's relation (for the extractor's failure output). -/
  inh : Inhabited Wit
  /-- The bound on the rounds of the composite. -/
  rounds : ℕ
  /-- The Chernoff exponent of every round's load: each round's stream overruns with probability at
  most `2^-chernoff`. -/
  chernoff : ℕ
  /-- The bound on the leaves of every domain's tree. -/
  N : ℕ
  /-- The bound on the leaves the verifier queries. -/
  nq : ℕ
  /-- The bound on the verifier's queries on accepting runs. -/
  kq : ℕ
  /-- The numerator of the bound on the largest round error. -/
  errorMax : ℕ
  /-- The exponent of the denominator of the bound on the largest round error. -/
  errorExp : ℕ
  /-- The bound on the digests of one chain input with the final digests. -/
  D : ℕ
  /-- The query cap of the quantum headlines (`2^40` at the ROM parameters, `2^100` at the QROM
  parameters). -/
  qQ : ℕ
  /-- The query cap of the classical headlines. -/
  qR : ℕ
  /-- The positions: the leaves of all trees. -/
  pos : ℕ
  /-- The digest length in bytes. -/
  k : ℕ

attribute [instance] Configuration.decEq Configuration.inh

section

variable (R : Configuration)

/-- **The proof bound of the zero-knowledge games**: the larger of the tree bound `N` and the
query bound `nq`, at least the leaves of every tree and the opened leaves. -/
@[config_reduce]
abbrev proofBound : ℕ := max R.N R.nq

/-- **The facts of a configuration the generic proofs use**: the setting's facts, the guarantees
of the end-to-end theorem at the configuration's IOP, the figures' bounds and the honest prover's
facts, every round's load at its own stream length (`k + fsExtraBytes` plus its grant,
`SpecReaders.AllGranted`). A configuration without granted points states `Facts`, which this
extends. -/
structure GrantedFacts : Prop where
  /-- The facts every spBCS setting is built from. -/
  hb : ∀ C, (R.T C).MergeBounds R.kS
  /-- **The end-to-end theorem, knowledge soundness** (paper `thm:e2e`(2)) at every query budget
  of the spBCS verifier, for the headline relation at the extractor's witness read by `g`
  (an instance of `RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`). -/
  knowledge : ∀ C {kq : ℕ} (hkq : (R.T C).QueryBudget R.kS (hb C) kq),
    (R.T C).KnowledgeGuarantees R.kS (hb C) (R.sound C) R.rel' R.g hkq
  /-- **The end-to-end theorem** (paper `thm:e2e`) at every honest strategy, with the strategy's
  completeness error (an instance of `RealizedProgram.ProofSystem.FieldBranches.e2e`). -/
  e2e : ∀ C (TA : R.TA C) {Inp : Type} {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH)
    {kq : ℕ} (hkq : (R.T C).QueryBudget R.kS (hb C) kq) (hf : (R.T C).ProofFormat R.kS (hb C) R.proofBound),
    (R.T C).Guarantees R.kS (hb C) (R.sound C) R.rel' R.g hkq hf (R.honest C TA H) (R.err H)
  /-- The composite has at most `rounds` rounds. -/
  rounds_le : ∀ C, ∑ q : (R.iop C).shape.term.Leaf, (R.iop C).rounds q.label ≤ R.rounds
  /-- Every round's load passes the Chernoff test `2^-chernoff` on the round's own stream length,
  `k + fsExtraBytes` plus its grant. -/
  loadsGranted : ∀ C j, ((R.T C).readers j).AllGranted fun g L =>
    PassesChernoff (65 / 64) ((1 / 2) ^ R.chernoff) ((R.T C).k + fsExtraBytes + g) L
  /-- Every domain's tree has at most `N` leaves. -/
  leaves_le : ∀ C d, ((R.iop C).oracle d).nLeaves ≤ R.N
  /-- The verifier queries at most `nq` leaves. -/
  queries_le : ∀ C ch, ((R.iop C).queryList ch).length ≤ R.nq
  /-- `kq` bounds the count of `length_queries_le`: two per round, one per branch and
  `1 + log₂ (2N)` per queried leaf. -/
  kq_ge : ∀ C, 2 * R.rounds + ∑ d, (R.iop C).shape.nb d + R.nq * (1 + Nat.log 2 (2 * R.N)) ≤ R.kq
  /-- The verifier makes at most `2^16` queries. -/
  kq_le : R.kq ≤ 2 ^ 16
  /-- The largest round error is at most `errorMax / 2^errorExp`. -/
  error_le : ∀ C, maxError (R.sound C).error ≤ (R.errorMax : ℝ≥0) / 2 ^ R.errorExp
  /-- The digests of one chain input, the final digests and the seeding's are at most `D`. -/
  digests_le : ∀ C,
    max 2 (ProofSystemTranscript.digests (C := R.iop C)) + (R.iop C).merges.nJ + 1 ≤ R.D
  /-- The trees have `pos` leaves in all. -/
  pos_eq : ∀ C, ∑ d, ((R.iop C).oracle d).nLeaves = R.pos
  /-- The transcript's digests have `k` bytes. -/
  k_eq : ∀ C, (R.T C).k = R.k
  /-- The fixed honest strategy has no completeness error. -/
  exact : R.err R.strategy = 0
  /-- An honest input of the fixed strategy is honest at its statement. -/
  keyStmtOf_mem : ∀ y, (R.keyStmtOf y, y) ∈ R.hrel R.relH

/-- **The facts of a configuration without granted points**: `GrantedFacts` with every round's
load passing the Chernoff test on `k + fsExtraBytes` bytes (`loads`), which a grant keeps
(`PassesChernoff.anti`, `SpecReaders.AllGranted.of_allLoads`). -/
structure Facts : Prop extends R.GrantedFacts where
  /-- Every round's load passes the Chernoff test `2^-chernoff`. -/
  loads : ∀ C j, ((R.T C).readers j).AllLoads
    (PassesChernoff (65 / 64) ((1 / 2) ^ R.chernoff) ((R.T C).k + fsExtraBytes))
  loadsGranted := fun C j => SpecReaders.AllGranted.of_allLoads
    (fun _ _ h => h.anti (by norm_num) (Nat.le_add_right _ _)) (loads C j)

/-- The facts of a configuration without granted points are its facts. -/
instance {R : Configuration} : CoeOut R.Facts R.GrantedFacts :=
  ⟨Facts.toGrantedFacts⟩

end

namespace Common

variable (R : Configuration) (F : R.GrantedFacts)

/-! ## The setting, the extractor and the verifiers -/

/-- **The spBCS setting of the configuration** (`SPBCS.ProofSystemTranscript.setting` of its
transcript at `kS`-byte salts). -/
@[config_template]
abbrev setting (C : R.Compiled) :
    Setting (R.iop C).toCausalIOP (R.iop C).merges (R.T C).k :=
  (R.T C).setting R.kS (F.hb C)

/-- **The extractor of the statements**: the composite's extractor (`RealizedProgram.ProofSystem.IOP.extractor`), its
witness read by the witness map `g` (`CausalExtractor.mapWit`).

Running time: one run of the composite's extractor (the application phase's extraction from the
domains' commit phases) and one application of the witness map `g`, polynomial when `g` is (the
configurations' maps read the witness at the statement's values: one `ExpandA` and one `H(pk)` for
ML-DSA, the key's coefficients for Falcon). This running time is argued here, not proved in Lean. -/
@[config_template]
def keyExtractor (_F : R.GrantedFacts) (C : R.Compiled) :
    CausalExtractor (R.iop C).P (R.iop C).term R.Stmt R.Wit' :=
  (R.iop C).extractor.mapWit R.g

/-- **The extractor of the statements is the composite's**, its witness read by `g`. -/
theorem keyExtractor_eq (C : R.Compiled) :
    keyExtractor R F C = (R.iop C).extractor.mapWit R.g :=
  rfl

/-- **The decoding of the database extractor's queries**: the decoder of the chain inputs of the
setting (`SPBCS.MergeEncoding.decode` of the spBCS compiler's encoding), which the database
extractor applies to every transcript query of the database (`SPBCS.φ`) and to every input it
reads behind a final digest (`SPBCS.resolveSink`). It parses the label, the salt, the statement
writes by the transcript's statement codec, and the chain contents by the write codecs.

Running time: one pass over the input's bytes, with one parse of each write by its codec, the
statement codec's parse included (for ML-DSA-44, one decision of `ExpandAWithin`: `16 · 336`
SHAKE128 candidates). This running time is argued here, not proved in Lean. -/
@[config_template]
def queryDecoder (C : R.Compiled) :=
  ((R.T C).setting R.kS (F.hb C)).model.senc.decode

/-- **The quantum knowledge error at `t` queries**:
`2^9/2^(4k) + 6 t² (errorMax/2^errorExp + D t/2^(8k))`. -/
@[config_template]
noncomputable abbrev knowledgeErrorQROM (_F : R.GrantedFacts) (t : ℕ) : ℝ≥0∞ :=
  2 ^ 9 / 2 ^ (4 * R.k) + 6 * (t : ℝ≥0∞) ^ 2 *
    ((((R.errorMax : ℝ≥0) / 2 ^ R.errorExp : ℝ≥0) : ℝ≥0∞) + ((R.D * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * R.k))

/-- **The classical knowledge error at `t` queries** (the adversary's and the verifier's):
`t (errorMax/2^errorExp + D t/2^(8k))`. -/
@[config_template]
noncomputable abbrev knowledgeErrorROM (_F : R.GrantedFacts) (t : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) * ((((R.errorMax : ℝ≥0) / 2 ^ R.errorExp : ℝ≥0) : ℝ≥0∞) +
    ((R.D * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * R.k))

/-- **The verifier's queries on accepting runs**: at most `kq`, two per round, one per branch and
`1 + log₂ (2N)` per queried leaf (`SPBCS.ProofSystemTranscript.length_queries_le`). -/
@[config_template]
theorem verifierQueries_le (C : R.Compiled) (x : R.Stmt) (h) (π : (setting R F C).model.NIProof)
    (hv : (setting R F C).model.Accepts h x π ((setting R F C).queries x)) :
    ((setting R F C).model.queries x π h ((setting R F C).queries x)).length ≤ R.kq := by
  refine ((R.T C).length_queries_le (F.hb C) (F.leaves_le C) (F.queries_le C) x h π
    hv).trans (le_trans ?_ (F.kq_ge C))
  have := F.rounds_le C
  omega

/-- **The spBCS verifier in the QROM**, at its `kq` queries. -/
@[config_template]
noncomputable abbrev verifierQROM (C : R.Compiled) :=
  (R.T C).verifier R.kS (F.hb C) R.kq


/-- **The spBCS verifier in the ROM**, at `kq` queries. -/
@[config_template]
noncomputable abbrev verifierROM (C : R.Compiled) :=
  (R.T C).verifierROM R.kS (F.hb C) R.kq

/-- **The overrun of the spBCS setting**: at most `rounds / 2^chernoff`
(`SPBCS.ProofSystemTranscript.overrun_le_at_granted`, every round's load within `2^-chernoff` on
its own stream length). -/
@[config_template]
theorem overrun_le (C : R.Compiled) :
    (setting R F C).model.overrun ≤ (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff :=
  ((R.T C).overrun_le_at_granted (F.hb C) R.chernoff (F.loadsGranted C)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast F.rounds_le C) _)

/-- **The positions of the spBCS setting**: `pos`, the leaves of all trees
(`SPBCS.ProofSystemTranscript.card_pos`). -/
@[config_template]
theorem card_pos (C : R.Compiled) : Fintype.card (setting R F C).model.Pos = R.pos :=
  ((R.T C).card_pos (F.hb C)).trans (F.pos_eq C)

/-- **The quantum knowledge error is monotone in the query count.** -/
@[config_template]
theorem knowledgeErrorQROM_mono {t t' : ℕ} (h : t ≤ t') :
    knowledgeErrorQROM R F t ≤ knowledgeErrorQROM R F t' := by
  unfold knowledgeErrorQROM
  gcongr

/-- **The classical knowledge error is monotone in the query count.** -/
@[config_template]
theorem knowledgeErrorROM_mono {t t' : ℕ} (h : t ≤ t') :
    knowledgeErrorROM R F t ≤ knowledgeErrorROM R F t' := by
  unfold knowledgeErrorROM
  gcongr

/-! ## Knowledge soundness and soundness -/

/-- **Knowledge soundness of the configuration's argument at `t` quantum queries: online
extractability** (DFMS22 Definition 3.1, p. 10, with CMS19's compressed oracle as the oracle
simulator, `εsim = 0` and a quantum auxiliary output;
`SPBCS.ProofSystemTranscript.knowledge`, the `knowledge` clause of
`SPBCS.knowledgeGuarantees`) against every `t`-query adversary of `def:adversary` that makes no
proof queries (`Quantum.QueryBoundedAdversary`) whose output is a statement, a proof and a
classical value in `Z`: the state of the adversary's register after measuring only its output is
the same in the coherent extraction run as in the real run, and in the extraction run the spBCS
verifier accepts while the database extractor at `keyExtractor` returns no witness of the
headline relation with probability at most `forkKnowledgeErrorAt (t + kq)`. The compiled
circuits' `enforce`: trust base. -/
@[config_template headline]
theorem knowledge_soundness_qrom_at (C : R.Compiled) {Zo : Type} {t : ℕ}
    (𝒢 : (setting R F C).QROMAdversary (Claim R.Stmt (setting R F C).model.NIProof × Zo) t) :
    𝒢.OnlineExtracts (verifierQROM R F C) NARG.QROM.compressedSim R.rel'
      (NARG.QROM.compressedExt ((setting R F C).model.dbExtractBits (keyExtractor R F C))) 0
      (knowledgeErrorQROM R F (t + R.kq)) := by
  have h1 := (F.knowledge C (verifierQueries_le R F C)).knowledge 𝒢
  have h2 : _ ≤ knowledgeErrorQROM R F (t + R.kq) := (Configurations.knowledgeError_le (k := (R.T C).k)
    (e := fsExtraBytes + (R.T C).maxGrant) (t := t + R.kq) F.kq_le (F.digests_le C)
    (F.error_le C)).trans_eq (by rw [F.k_eq C])
  rw [keyExtractor_eq R F C]
  exact h1.mono le_rfl h2

/-- **Soundness of the configuration's argument at `t` quantum queries**
(`SPBCS.ProofSystemTranscript.soundness`, the `soundness` clause of
`SPBCS.knowledgeGuarantees`): every `t`-query adversary of `def:adversary` that makes no proof
queries outputs a statement without a witness of the headline relation and a proof the spBCS
verifier accepts with probability at most `forkKnowledgeErrorAt (t + kq)`. The compiled circuits'
`enforce`: trust base. -/
@[config_template headline]
theorem soundness_qrom_at (C : R.Compiled) {t : ℕ} (𝒜 : (setting R F C).QROMAdversary (Claim R.Stmt (setting R F C).model.NIProof) t) :
    𝒜.acceptsFalse (verifierQROM R F C) R.rel' ≤ knowledgeErrorQROM R F (t + R.kq) := by
  have h2 : _ ≤ knowledgeErrorQROM R F (t + R.kq) := (Configurations.knowledgeError_le (k := (R.T C).k)
    (e := fsExtraBytes + (R.T C).maxGrant) (t := t + R.kq) F.kq_le (F.digests_le C)
    (F.error_le C)).trans_eq (by rw [F.k_eq C])
  exact ((F.knowledge C (verifierQueries_le R F C)).soundness 𝒜).trans h2

/-- **Knowledge soundness of the configuration's argument in the classical random-oracle model at
`t` queries: online extractability against the lazily sampled oracle**
(`SPBCS.ProofSystemTranscript.knowledgeROM`, the `knowledgeROM` clause of
`SPBCS.knowledgeGuarantees`): for every classical `t`-query adversary that makes no proof queries
(`ROM.QueryBoundedAdversary`) with an auxiliary output in `Z`, the extraction run has the real
run's law of the output and the verdict, and in it the spBCS verifier accepts while the
database extractor at `keyExtractor`, reading the table of the adversary's and the verifier's
`kq` queries, returns no witness of the headline relation with probability at most
`forkKnowledgeErrorROMAt (t + kq)`. The compiled circuits' `enforce`: trust base. -/
@[config_template headline]
theorem knowledge_soundness_rom_at (C : R.Compiled) {Zo : Type} {t : ℕ}
    (𝒢 : (setting R F C).ROMAdversary (Claim R.Stmt (setting R F C).model.NIProof × Zo) t) :
    𝒢.OnlineExtracts (verifierROM R F C) NARG.ROM.OracleSampler.lazy.law R.rel'
      ((setting R F C).model.dbExtract (keyExtractor R F C)) 0
      (knowledgeErrorROM R F (t + R.kq)) := by
  have h1 := (F.knowledge C (verifierQueries_le R F C)).knowledgeROM 𝒢
  have h2 : _ ≤ knowledgeErrorROM R F (t + R.kq) := (Configurations.knowledgeErrorROM_le
    (k := (R.T C).k) (t := t + R.kq) (F.digests_le C) (F.error_le C)).trans_eq (by rw [F.k_eq C])
  rw [keyExtractor_eq R F C]
  exact h1.mono le_rfl h2

/-- **Soundness of the configuration's argument in the classical random-oracle model at `t`
queries** (`SPBCS.ProofSystemTranscript.soundnessROM`, the `soundnessROM` clause of
`SPBCS.knowledgeGuarantees`): every classical `t`-query adversary that makes no proof queries
outputs a statement without a witness of the headline relation and a proof the spBCS verifier accepts
with probability at most `forkKnowledgeErrorROMAt (t + kq)`. The compiled circuits' `enforce`:
trust base. -/
@[config_template headline]
theorem soundness_rom_at (C : R.Compiled) {t : ℕ} (𝒜 : (setting R F C).ROMAdversary (Claim R.Stmt (setting R F C).model.NIProof) t) :
    𝒜.acceptsFalse (verifierROM R F C) R.rel' ≤ knowledgeErrorROM R F (t + R.kq) := by
  have h2 : _ ≤ knowledgeErrorROM R F (t + R.kq) := (Configurations.knowledgeErrorROM_le
    (k := (R.T C).k) (t := t + R.kq) (F.digests_le C) (F.error_le C)).trans_eq (by rw [F.k_eq C])
  exact ((F.knowledge C (verifierQueries_le R F C)).soundnessROM 𝒜).trans h2

/-- **Knowledge soundness of the configuration's argument at the quantum query cap `qQ`** (online
extractability, DFMS22 Definition 3.1, p. 10, with CMS19's compressed oracle as the oracle
simulator and simulation error `0`): for every
adversary of `def:adversary` that makes no proof queries, with at most `qQ` queries and an
auxiliary output, the extraction run leaves the adversary's register in its real-run state at every
output and verdict, and in it the spBCS verifier accepts while the database extractor returns no witness with probability at
most `forkKnowledgeErrorAt (qQ + kq)` (`knowledge_soundness_qrom_at`, `knowledgeErrorQROM_mono`).
The compiled circuits' `enforce`: trust base. -/
@[config_template headline]
theorem knowledge_soundness_qrom (C : R.Compiled) {Zo : Type} {t : ℕ}
    (𝒢 : (setting R F C).QROMAdversary (Claim R.Stmt (setting R F C).model.NIProof × Zo) t) (ht : t ≤ R.qQ) :
    𝒢.OnlineExtracts (verifierQROM R F C) NARG.QROM.compressedSim R.rel'
      (NARG.QROM.compressedExt ((setting R F C).model.dbExtractBits (keyExtractor R F C))) 0
      (knowledgeErrorQROM R F (R.qQ + R.kq)) :=
  (knowledge_soundness_qrom_at R F C 𝒢).mono le_rfl
    (knowledgeErrorQROM_mono R F (Nat.add_le_add_right ht _))

/-- **Soundness of the configuration's argument at the quantum query cap `qQ`**: every
adversary of `def:adversary` that makes no proof queries, with at most `qQ` queries, outputs a statement without a
witness of the headline relation and an accepted proof with probability at most
`forkKnowledgeErrorAt (qQ + kq)` (`soundness_qrom_at`, `knowledgeErrorQROM_mono`). The compiled
circuits' `enforce`: trust base. -/
@[config_template headline]
theorem soundness_qrom (C : R.Compiled) {t : ℕ} (𝒜 : (setting R F C).QROMAdversary (Claim R.Stmt (setting R F C).model.NIProof) t)
    (ht : t ≤ R.qQ) :
    𝒜.acceptsFalse (verifierQROM R F C) R.rel' ≤ knowledgeErrorQROM R F (R.qQ + R.kq) :=
  (soundness_qrom_at R F C 𝒜).trans (knowledgeErrorQROM_mono R F (Nat.add_le_add_right ht _))

/-- **Knowledge soundness of the configuration's argument in the classical random-oracle model at
the classical query cap `qR`** (online extractability against the lazily sampled oracle): for every
classical adversary that makes no proof queries, with at most `qR` queries and an auxiliary output,
the extraction run has the real run's law of the output and the verdict, and in it the spBCS
verifier accepts while the database extractor returns no witness with probability at most
`forkKnowledgeErrorROMAt (qR + kq)` (`knowledge_soundness_rom_at`,
`knowledgeErrorROM_mono`). The compiled circuits' `enforce`: trust base. -/
@[config_template headline]
theorem knowledge_soundness_rom (C : R.Compiled) {Zo : Type} {t : ℕ}
    (𝒢 : (setting R F C).ROMAdversary (Claim R.Stmt (setting R F C).model.NIProof × Zo) t) (ht : t ≤ R.qR) :
    𝒢.OnlineExtracts (verifierROM R F C) NARG.ROM.OracleSampler.lazy.law R.rel'
      ((setting R F C).model.dbExtract (keyExtractor R F C)) 0
      (knowledgeErrorROM R F (R.qR + R.kq)) :=
  (knowledge_soundness_rom_at R F C 𝒢).mono le_rfl
    (knowledgeErrorROM_mono R F (Nat.add_le_add_right ht _))

/-- **Soundness of the configuration's argument in the classical random-oracle model at the
classical query cap `qR`**: every classical adversary that makes no proof queries, with at most
`qR` queries, outputs a statement without a witness of the headline relation and an accepted proof with
probability at most `forkKnowledgeErrorROMAt (qR + kq)` (`soundness_rom_at`,
`knowledgeErrorROM_mono`). The compiled circuits' `enforce`: trust base. -/
@[config_template headline]
theorem soundness_rom (C : R.Compiled) {t : ℕ} (𝒜 : (setting R F C).ROMAdversary (Claim R.Stmt (setting R F C).model.NIProof) t)
    (ht : t ≤ R.qR) :
    𝒜.acceptsFalse (verifierROM R F C) R.rel' ≤ knowledgeErrorROM R F (R.qR + R.kq) :=
  (soundness_rom_at R F C 𝒜).trans
    (knowledgeErrorROM_mono R F (Nat.add_le_add_right ht _))

/-! ## The honest prover -/

/-- **The proof format of the zero-knowledge games**: every query phase of the configuration's
setting opens at most `proofBound` positions and every tree has at most `proofBound` leaves, since
`proofBound` is the larger of the tree size `N` and the number `nq` of queried leaves. -/
@[config_template]
theorem proofFormat (C : R.Compiled) : (R.T C).ProofFormat R.kS (F.hb C) R.proofBound :=
  ProofSystemTranscript.formatBounds (F.hb C) (fun d => (F.leaves_le C d).trans (le_max_left _ _))
    fun ch => (F.queries_le C ch).trans (le_max_right _ _)

/-- **The honest prover of the configuration at a strategy**: the IOP's honest prover at the
strategy `H` (the proof system's phased honest prover and every forked domain's honest prover, read
at the statement). `TA`: trust base. -/
@[config_template]
abbrev honestProver (_F : R.GrantedFacts) (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    (R.iop C).Honest (R.sim C) Inp (R.hrel relH) :=
  R.honest C TA H

/-- **The honest prover of the configuration's argument** at the strategy `H`: the compiled proof
of the IOP's honest prover, with uniform coins, Merkle salts and salt, in the format `proofBound`
(`ProofSystemTranscript.prover`). It is the prover of every completeness, zero-knowledge and
witness-indistinguishability statement of the configuration. `TA`: trust base. -/
@[config_template]
noncomputable abbrev prover (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :=
  (R.T C).prover R.kS (F.hb C) (proofFormat R F C)
    (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C TA H))

/-- **The simulator of the configuration's argument**: the compiled simulator
(`ProofSystemTranscript.simulator`, `SPBCS.niSimulator`) of the IOP's simulator at the
configuration's simulator data (`Configuration.sim`), its proofs in the format `proofBound`. It
reads no honest prover, strategy or witness, and it is the simulator of every zero-knowledge and
simulation-extractability statement of the configuration, at every strategy.

Running time: that of `SPBCS.niSimulator` at the setting (its Running time paragraph). This running
time is argued here, not proved in Lean. -/
@[config_template]
abbrev simulator (C : R.Compiled) :=
  (R.T C).simulator R.kS (F.hb C) (proofFormat R F C) (R.sim C)

open Classical in
/-- **Completeness of the configuration's argument** (paper `thm:e2e`(1) at a fixed statement:
the `completeness` clause of `SPBCS.CompletenessGuarantees` at `GrantedFacts.e2e`): on an
honest input `y` at the statement `s`, at every value `c` of the honest prover's coins, Merkle salts
`ν` and salt `σ`, over a uniform oracle the spBCS verifier rejects the compiled honest proof
with probability at most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k)` (the strategy's
completeness error, the overrun and the key collisions). The compiled circuits' `enforce`, `TA`:
trust base. -/
@[config_template headline]
theorem completeness (C : R.Compiled) (TA : R.TA C) {Inp : Type} {relH : Set (R.Val × Inp)}
    (H : R.Strategy Inp relH) (c : (honestProver R F C TA H).Coins)
    {s : R.Stmt} {y : Inp} (hy : (s, y) ∈ R.hrel relH)
    (ν : (setting R F C).model.Pos → MerkleSalt (2 * (R.T C).k)) (σ : FiatShamirSalt R.kS) :
    Pr[h ← (Query (R.T C).k (2 * (R.T C).k) R.kS (2 ^ 40) →
          Out (R.T C).k (fsExtraBytes + (R.T C).maxGrant)) :
        ¬ (setting R F C).model.Accepts h s ((prover R F C TA H).toFn.prove h s y
          { salt := σ, coins := { iop := c, merkleSalts := ν } }).val ((setting R F C).queries s)] ≤
      (R.err H : ℝ≥0∞) + (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k := by
  have hp : ∀ h, ((prover R F C TA H).toFn.prove h s y
      { salt := σ, coins := { iop := c, merkleSalts := ν } }).val = SPBCS.prove
        (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C TA H) y c) s σ
        (setting R F C).encoder ν h ((setting R F C).queries s) := fun h =>
    (setting R F C).model.toFn_niProver (setting R F C).layout _ (setting R F C).encoder
      (setting R F C).viewEncoder (proofFormat R F C) h s y _
  refine le_of_eq_of_le (congrArg (probUniform _) (funext fun h => congrArg Not (congrArg
    (fun π => (setting R F C).model.Accepts h s π ((setting R F C).queries s)) (hp h)))) ?_
  have h := ((F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).completeness c).completeness s y ν σ hy
  rw [ROM.probUniform_unit_prod, SPTerm.size_eq_sum] at h
  refine h.trans (add_le_add (add_le_add le_rfl (overrun_le R F C)) ?_)
  rw [← F.k_eq C]
  exact SPBCS.keyCollision_mono (F.rounds_le C) _

open Classical in
/-- **Completeness of the configuration's argument at a drawn honest input** (the
`completenessOfSampler` form of `Common.completeness`, `WitnessSampler.prob_draw_le`): for a
witness sampler `D` whose honest input on the proof query `u` is outside the honest relation at the
statement `s` with probability at most `η` (`hD`), at every value `c` of the honest prover's coins,
Merkle salts `ν` and salt `σ`, over the sampler's coins and a uniform oracle the spBCS verifier
rejects the compiled honest proof at the drawn input with probability at most
`err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + η`. The compiled circuits' `enforce`, `TA`:
trust base. -/
@[config_template headline]
theorem completeness_of_sampler (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH)
    (c : (honestProver R F C TA H).Coins) {U : Type} (D : WitnessSampler U Inp)
    {s : R.Stmt} {u : U} {η : ℝ≥0} (hD : D.MissesAtMostAt (R.hrel relH) s u η)
    (ν : (setting R F C).model.Pos → MerkleSalt (2 * (R.T C).k)) (σ : FiatShamirSalt R.kS) :
    Pr[d ← D.Draw (Query (R.T C).k (2 * (R.T C).k) R.kS (2 ^ 40) →
          Out (R.T C).k (fsExtraBytes + (R.T C).maxGrant)) :
        ¬ (setting R F C).model.Accepts d.oracle s ((prover R F C TA H).toFn.prove d.oracle s
          (D.draw u d.coins) { salt := σ, coins := { iop := c, merkleSalts := ν } }).val
          ((setting R F C).queries s)] ≤
      (R.err H : ℝ≥0∞) + (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k + η :=
  D.prob_draw_le hD (fun y h => ¬ (setting R F C).model.Accepts h s ((prover R F C TA H).toFn.prove
      h s y { salt := σ, coins := { iop := c, merkleSalts := ν } }).val ((setting R F C).queries s))
    fun _ hy => completeness R F C TA H c hy ν σ

open Classical in
/-- **Zero knowledge of the configuration's argument** (paper `thm:e2e`(3) in the QROM: the
`zeroKnowledge` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): everlasting
zero knowledge for many adaptively chosen proofs (the distinguisher receives the whole oracle
after the last proof query) against query-bounded adversaries
(`NARG.QROM.EverlastingZeroKnowledge`) of the configuration's prover `prover` on the honest inputs,
against its simulator `simulator`, for statements and honest inputs read from any finite types, with error
`zkError (err H)`, the strategy's completeness error as the HVZK error. The compiled circuits'
`enforce`, `TA`: trust base. -/
@[config_template headline]
theorem everlasting_zero_knowledge_qrom (C : R.Compiled) (TA : R.TA C) {Inp : Type} {relH : Set (R.Val × Inp)}
    (H : R.Strategy Inp relH) {X' W' : Type} [Fintype X'] [DecidableEq X'] [Fintype W']
    [DecidableEq W'] (fx : X' → R.Stmt) (fw : W' → Inp) :
    NARG.QROM.EverlastingZeroKnowledge (fun x w => (fx x, fw w) ∈ R.hrel relH) queryEncoding
      ((prover R F C TA H).comap fx fw) ((simulator R F C).comap fx)
      ((setting R F C).model.zkError (R.err H)) :=
  (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledge X' W' fx fw

open Classical in
/-- **Zero knowledge of the configuration's argument at drawn honest inputs** (the
`zeroKnowledgeOfSampler` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): the zero
knowledge of `everlasting_zero_knowledge_qrom` when each proof query of `relU` is answered at an honest input drawn
by `D`, which misses the honest relation with probability at most `η` (`hD`): against every
query-bounded adversary (`SPBCS.ZeroKnowledgeOfSampler`), for statements and proof queries read
from any finite types, the counted honest prover drawing its input (`drawProver`) and the configuration's
counted simulator are at most `zkError (err H) t Q + Q · η` apart. The compiled
circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem everlasting_zero_knowledge_qrom_of_sampler (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) {U : Type}
    (D : WitnessSampler U Inp) {relU : Set (R.Stmt × U)} {η : ℝ≥0}
    (hD : D.MissesAtMost (R.hrel relH) relU η) :
    (setting R F C).model.ZeroKnowledgeOfSampler (setting R F C).layout
      (setting R F C).viewEncoder (proofFormat R F C)
      (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C TA H)) id
      (RealizedProgram.ProofSystem.IOP.simulator (R.sim C))
      ((R.T C).preimages R.kS (F.hb C)) D relU
      (fun t Q => (setting R F C).model.zkError (R.err H) t Q + Q * η) :=
  (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeOfSampler D relU η hD

/-- **Witness indistinguishability of the configuration's argument** (paper `thm:e2e`(4):
`ProofSystemTranscript.Guarantees.witnessIndist` at `GrantedFacts.e2e`): unconditional (against a
distinguisher given the whole random oracle), adaptive multi-theorem witness indistinguishability
(CY24 Definition 33.1.1, pp. 426-427, at unbounded queries, p. 430) of the compiled honest prover on
the honest inputs: for injective binary encodings `eX` of statements and `eW` of honest inputs,
against adversaries making `Q` proof queries, each a statement and two honest inputs of total
encoding length at most `ℓ` chosen as a function of the whole oracle and the earlier proofs, every
distinguisher of the oracle and the proofs has advantage at most `Q · wiError (err H) (choiceCount
ℓ)` (`SPBCS.WitnessIndistinguishableOfLength`), the strategy's completeness error as the HVZK
error. The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem unconditional_witness_indistinguishability (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH)
    (eX : SPBCS.BitEncoding R.Stmt) (eW : SPBCS.BitEncoding Inp) (Q ℓ : ℕ) :
    (setting R F C).model.WitnessIndistinguishableOfLength (prover R F C TA H) eX eW
      (R.hrel relH) Q ℓ
      (Q * (setting R F C).model.wiError (R.err H) (SPBCS.choiceCount ℓ)) :=
  (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).witnessIndist eX eW Q ℓ

open Classical in
/-- **Zero knowledge of the configuration's argument in the classical random-oracle model**
(paper `thm:e2e`(3) in the ROM: the `zeroKnowledgeROM` clause of `SPBCS.PrivacyGuarantees` at
`GrantedFacts.e2e`): everlasting zero knowledge for many adaptively chosen proofs (the
distinguisher receives the whole oracle after the last proof query) against query-bounded
classical adversaries (`NARG.ROM.EverlastingZeroKnowledge`), of the prover `prover` against
the compiled simulator, with error `zkErrorROM (err H)`. The compiled circuits' `enforce`, `TA`:
trust base. -/
@[config_template headline]
theorem everlasting_zero_knowledge_rom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    NARG.ROM.EverlastingZeroKnowledge (fun x w => (x, w) ∈ R.hrel relH) (prover R F C TA H)
      (simulator R F C) ((setting R F C).model.zkErrorROM (R.err H)) :=
  (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeROM

open Classical in
/-- **Weak online simulation extractability of the configuration's argument in the QROM** (paper
`thm:e2e`(5) in the QROM, the joint form of `def:bcs-se`:
`SPBCS.ProofSystemTranscript.SimGuarantees.simOnlineExtractability` at `GrantedFacts.e2e`) against
query-bounded adversaries, with the counted simulator of the configuration's simulator (`simulator`) and the
database extractor at `keyExtractor`, at the verifier's `kq` queries: in the extraction run the
joint state of the adversary's output and its auxiliary output is as in the simulated run, and an
accepted proof of a fresh statement from which the extractor obtains no witness of the headline
relation has probability at most `simExtractionError kq (max_c ε c) q t Q`
(`SPBCS.WeakOnlineSimulationExtractable`). The compiled circuits' `enforce`, `TA`: trust
base. -/
@[config_template headline]
theorem weak_online_simulation_extractability_qrom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    (setting R F C).model.WeakOnlineSimulationExtractable R.proofBound
      (setting R F C).queries R.rel' (keyExtractor R F C) R.kq (verifierQueries_le R F C)
      ((simulator R F C).encode queryEncoding)
      ((setting R F C).model.simExtractionError R.kq (maxError (R.sound C).error)
        (2 * Fintype.card (setting R F C).model.Pos +
          (R.iop C).shape.term.size (R.iop C).rounds + ∑ d, (R.iop C).shape.nb d)) := by
  rw [keyExtractor_eq R F C]
  exact (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).simOnlineExtractability

open Classical in
/-- **Simulation-sound extractability of the configuration's argument in the QROM** (paper
`thm:e2e`(5) in the QROM: `SPBCS.ProofSystemTranscript.SimGuarantees.simExtractability` at
`GrantedFacts.e2e`; Unruh 2017, Definition 14, p. 21, weak variant, for residual-state tests that
make no oracle queries, with straight-line extraction and freshness in both events) against
query-bounded adversaries, with the counted simulator of the configuration's simulator (`simulator`) and the
database extractor at `keyExtractor`, at the verifier's `kq` queries. The compiled circuits'
`enforce`, `TA`: trust base. -/
@[config_template headline]
theorem unruh_simulation_extractability_qrom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    (setting R F C).model.SimulationSoundExtractableFresh R.proofBound
      (setting R F C).queries R.rel' (keyExtractor R F C) R.kq
      ((simulator R F C).encode queryEncoding)
      ((setting R F C).model.simExtractionError R.kq (maxError (R.sound C).error)
        (2 * Fintype.card (setting R F C).model.Pos +
          (R.iop C).shape.term.size (R.iop C).rounds + ∑ d, (R.iop C).shape.nb d)) := by
  rw [keyExtractor_eq R F C]
  exact (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).simExtractability

/-- **Weak online simulation extractability of the configuration's argument in the classical
random-oracle model** (paper `thm:e2e`(5) in the ROM, the joint form of `def:bcs-se`:
`SPBCS.ProofSystemTranscript.SimGuarantees.simOnlineExtractabilityROM` at `GrantedFacts.e2e`)
against query-bounded classical adversaries with an auxiliary output, with the classical simulator
program of the configuration's simulator (`simulator`) on uniform coins and the database extractor at `keyExtractor`
on the table of the lazily sampled execution, at the verifier's `kq` queries: the extractor's
execution has the simulated execution's law of the claim, the auxiliary output, the statements
of the proof queries and the verdict (oracle simulation error `0`), and wins without extraction with
probability at most `simExtractionErrorROM kq (max_c ε c) q tq Q`. The compiled circuits'
`enforce`, `TA`: trust base. -/
@[config_template headline]
theorem weak_online_simulation_extractability_rom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    (setting R F C).model.WeakOnlineSimulationExtractableROM R.proofBound
      (setting R F C).queries R.rel' (keyExtractor R F C) R.kq (simulator R F C).prog
      (2 * Fintype.card (setting R F C).model.Pos +
        (R.iop C).shape.term.size (R.iop C).rounds + ∑ d, (R.iop C).shape.nb d)
      ((setting R F C).model.simExtractionErrorROM R.kq (maxError (R.sound C).error)
        (2 * Fintype.card (setting R F C).model.Pos +
          (R.iop C).shape.term.size (R.iop C).rounds + ∑ d, (R.iop C).shape.nb d)) := by
  rw [keyExtractor_eq R F C]
  exact (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).simOnlineExtractabilityROM

open Classical in
/-- **Simulation-sound extractability of the configuration's argument for tests that query the
oracle** (`SPBCS.ProofSystemTranscript.SimGuarantees.simExtractabilitySimOracle` at
`GrantedFacts.e2e`; Unruh
2017, Definition 14, p. 21, weak variant, eq. (6) with the test in Extract′ answered by the
simulated oracle after extraction) against query-bounded adversaries, with the counted simulator of
the configuration's simulator (`simulator`) and the targeted extractor at `keyExtractor`, at the verifier's
`kq` queries: for every adversary with at most `tq` queries and `Q` proof queries and every
residual-state test with at most `tTest` queries, Prove with the test is at most Extract′ with the
test plus `simExtractionError kq (max_c ε c) q (tq + tTest) Q + swapError tTest`. The compiled
circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem unruh_simulation_extractability_sim_oracle_qrom (C : R.Compiled) (TA : R.TA C)
    {Inp : Type} {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    (setting R F C).model.SimulationSoundExtractableSimOracle R.proofBound
      (setting R F C).queries R.rel' (keyExtractor R F C) R.kq
      ((simulator R F C).encode queryEncoding)
      fun tq tTest Q => (setting R F C).model.simExtractionError R.kq
          (maxError (R.sound C).error)
          (2 * Fintype.card (setting R F C).model.Pos +
            (R.iop C).shape.term.size (R.iop C).rounds + ∑ d, (R.iop C).shape.nb d) (tq + tTest) Q +
        (setting R F C).model.swapError tTest := by
  rw [keyExtractor_eq R F C]
  exact (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).simExtractabilitySimOracle

/-! ## The fixed honest strategy -/

open Classical in
/-- **Zero knowledge of the configuration's argument on its honest inputs** (`everlasting_zero_knowledge_qrom`
at the fixed honest strategy, whose completeness error is `0`): everlasting zero
knowledge for many adaptively chosen proofs (the distinguisher receives the whole oracle after the
last proof query) against query-bounded adversaries of the compiled honest prover on the
valid honest inputs at their statements, at the configuration's compiled simulator, with error
`zkError 0`. The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem everlasting_zero_knowledge_honest_qrom (C : R.Compiled) (TA : R.TA C) {X' W' : Type}
    [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → R.Stmt)
    (fw : W' → R.HonestIn) :
    NARG.QROM.EverlastingZeroKnowledge (fun x w => (fx x, fw w) ∈ R.hrel R.relH) queryEncoding
      ((prover R F C TA R.strategy).comap fx fw) ((simulator R F C).comap fx)
      ((setting R F C).model.zkError 0) := by
  have h := everlasting_zero_knowledge_qrom R F C TA R.strategy fx fw
  rwa [F.exact] at h

open Classical in
/-- **Completeness of the configuration's argument on its honest inputs** (`Common.completeness` at
the fixed honest strategy, whose completeness error is `0`): on a valid honest input `y` at its
statement, at every value of the honest prover's coins, Merkle salts and salt, over a uniform
oracle the spBCS verifier rejects the compiled honest proof with probability at most
`rounds/2^chernoff + C(rounds, 2)/2^(8k)`. The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem completeness_honest (C : R.Compiled) (TA : R.TA C)
    (c : (honestProver R F C TA R.strategy).Coins) (y : R.HonestIn)
    (ν : (setting R F C).model.Pos → MerkleSalt (2 * (R.T C).k)) (σ : FiatShamirSalt R.kS) :
    Pr[h ← (Query (R.T C).k (2 * (R.T C).k) R.kS (2 ^ 40) →
          Out (R.T C).k (fsExtraBytes + (R.T C).maxGrant)) :
        ¬ (setting R F C).model.Accepts h (R.keyStmtOf y) ((prover R F C TA R.strategy).toFn.prove h
          (R.keyStmtOf y) y { salt := σ, coins := { iop := c, merkleSalts := ν } }).val
          ((setting R F C).queries (R.keyStmtOf y))] ≤
      (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k := by
  have h := completeness R F C TA R.strategy c (F.keyStmtOf_mem y) ν σ
  rwa [F.exact, ENNReal.coe_zero, zero_add] at h

end Common

namespace ZeroKnowledgeROM

open Common

variable (R : Configuration) (F : R.GrantedFacts)

open Classical in
/-- **Query-counted zero knowledge of the configuration's argument in the classical random-oracle
model** (the `zeroKnowledgeROMQuery` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`):
adaptive multi-theorem statistical zero knowledge (Unruh 2017 Definition 6, p. 14, with classical
adversaries all of whose queries are counted, `NARG.ROM.ZeroKnowledge`) of the
compiled honest prover against the compiled simulator: every classical adversary with a budget of
`t` queries over all its steps, whose output does not read the final oracle, with `Q` proof
queries answered, has advantage at most
`Q t/2^(8 kS) + Q (Q - 1)/(2 · 2^(8 kS)) + Q · keyCollision rounds k
+ Q (4 · pos · t + 4 (pos² Q + pos))/2^(16 k) + Q (rounds/2^chernoff + err H)`
(`zkErrorROMQuery (err H)` at `pos` positions, `rounds` rounds, `2k`-byte Merkle salts and the
overrun bound `overrun_le`). The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem zero_knowledge_rom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    NARG.ROM.ZeroKnowledge (fun x w => (x, w) ∈ R.hrel relH) (prover R F C TA H)
      (simulator R F C)
      (fun t Q => Q * t / 2 ^ (8 * R.kS) + Q * (Q - 1) / (2 * 2 ^ (8 * R.kS)) +
        Q * (SPBCS.keyCollision R.rounds R.k).toReal +
        Q * ((4 * t * R.pos + 4 * (Q * R.pos ^ 2 + R.pos)) / 2 ^ (16 * R.k)) +
        Q * (R.rounds / 2 ^ R.chernoff + R.err H)) := by
  refine GordieHowe.ROM.ZeroKnowledge.mono
    (F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeROMQuery fun t Q => ?_
  have hkc : (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (R.T C).k).toReal ≤
      (SPBCS.keyCollision R.rounds R.k).toReal := by
    rw [← F.k_eq C, SPTerm.size_eq_sum]
    exact ENNReal.toReal_mono (SPBCS.keyCollision_ne_top _ _)
      (SPBCS.keyCollision_mono (F.rounds_le C) _)
  have hov : (setting R F C).model.overrun.toReal ≤ R.rounds / 2 ^ R.chernoff := by
    have h := ENNReal.toReal_mono (ENNReal.div_lt_top (by simp) (by simp)).ne
      (overrun_le R F C)
    rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
  have hU : (Fintype.card (setting R F C).model.Pos : ℝ) = R.pos := by
    exact_mod_cast card_pos R F C
  have hN : (2 : ℝ) ^ (8 * (setting R F C).kN) = 2 ^ (16 * R.k) := by
    change (2 : ℝ) ^ (8 * (2 * (R.T C).k)) = _
    rw [F.k_eq C]
    congr 1
    ring
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  rw [Base.zkErrorROMQuery, hU, hN]
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl le_rfl)
    (mul_le_mul_of_nonneg_left hkc hQ)) le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add hov le_rfl) hQ)

end ZeroKnowledgeROM

namespace ZeroKnowledgeQROM

open Common

variable (R : Configuration) (F : R.GrantedFacts)

open Classical in
/-- **Query-counted zero knowledge of the configuration's argument in the QROM** (the
`zeroKnowledgeQueryCounted` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): adaptive
multi-theorem statistical zero knowledge with every query counted (Unruh 2017 Definition 6, p. 14,
over the paper's `(t, Q)`-adversaries, `def:adversary`, `NARG.QROM.ZeroKnowledge`)
of the compiled honest prover against the compiled simulator, for all finite statement and witness
types: every adversary making at most `t` queries on every branch, over all its query slots and its
post phase, with `Q` proof queries answered, has advantage at most
`4 Q t/2^(4 kS) + Q (Q - 1)/2^(8 kS) + Q · keyCollision rounds k + Q (4 t √pos/2^(8 k)
+ 3 (pos + pos² Q + pos²)/2^(16 k)) + Q (rounds/2^chernoff + err H)` (`zkErrorQuery (err H)` at
`pos` positions, `rounds` rounds, `2k`-byte Merkle salts and the overrun bound
`overrun_le`). The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem zero_knowledge_qrom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) {X' W' : Type} [Fintype X']
    [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → R.Stmt) (fw : W' → Inp) :
    NARG.QROM.ZeroKnowledge (fun x w => (fx x, fw w) ∈ R.hrel relH) queryEncoding
      ((prover R F C TA H).comap fx fw) ((simulator R F C).comap fx)
      (fun t Q => 4 * Q * t / 2 ^ (4 * R.kS) + Q * (Q - 1) / 2 ^ (8 * R.kS) +
        Q * (SPBCS.keyCollision R.rounds R.k).toReal +
        Q * (4 * t * √R.pos / 2 ^ (8 * R.k) +
          3 * ((R.pos + Q * R.pos ^ 2 + R.pos ^ 2) / 2 ^ (16 * R.k))) +
        Q * (R.rounds / 2 ^ R.chernoff + R.err H)) := by
  refine GordieHowe.QROM.ZeroKnowledge.mono
    ((F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeQueryCounted X' W' fx fw)
    fun t Q => ?_
  have hkc : (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (R.T C).k).toReal ≤
      (SPBCS.keyCollision R.rounds R.k).toReal := by
    rw [← F.k_eq C, SPTerm.size_eq_sum]
    exact ENNReal.toReal_mono (SPBCS.keyCollision_ne_top _ _)
      (SPBCS.keyCollision_mono (F.rounds_le C) _)
  have hov : (setting R F C).model.overrun.toReal ≤ R.rounds / 2 ^ R.chernoff := by
    have h := ENNReal.toReal_mono (ENNReal.div_lt_top (by simp) (by simp)).ne
      (overrun_le R F C)
    rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
  have hU : (Fintype.card (setting R F C).model.Pos : ℝ) = R.pos := by
    exact_mod_cast card_pos R F C
  have h4 : (2 : ℝ) ^ (4 * (setting R F C).kN) = 2 ^ (8 * R.k) := by
    change (2 : ℝ) ^ (4 * (2 * (R.T C).k)) = _
    rw [F.k_eq C]
    congr 1
    ring
  have h8 : (2 : ℝ) ^ (8 * (setting R F C).kN) = 2 ^ (16 * R.k) := by
    change (2 : ℝ) ^ (8 * (2 * (R.T C).k)) = _
    rw [F.k_eq C]
    congr 1
    ring
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  rw [Base.zkErrorQuery, hU, h4, h8]
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl le_rfl)
    (mul_le_mul_of_nonneg_left hkc hQ)) le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add hov le_rfl) hQ)

end ZeroKnowledgeQROM

namespace AdaptiveCompleteness

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **Completeness of the configuration's argument in the ROM** (paper `thm:e2e`(1) in the ROM;
`def:narg-complete`, `NARG.ROM.Complete`; Unruh 2017 Definition 5, p. 14;
`ProofSystemTranscript.Guarantees.completeROM` at `GrantedFacts.e2e`): at every honest strategy
`H`, the honest prover `prover`, with uniform coins, Merkle salts and salt, is complete for the
spBCS verifier `verifierROM`: every classical `t`-query adversary that outputs a statement and an
honest input after its queries makes the honest proof of a valid pair rejected with probability at
most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + t/2^(8 kS)`. The compiled circuits'
`enforce`, `TA`: trust base. -/
@[config_template headline]
theorem completeness_adaptive_rom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    NARG.ROM.Complete (prover R F C TA H) (verifierROM R F C) (fun x π => SPBCS.Claim.mk x π.val)
      (fun x y => (x, y) ∈ R.hrel relH) fun t => (R.err H : ℝ≥0∞) +
        (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k + t / 2 ^ (8 * R.kS) :=
  fun t 𝒜 => ((F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).completeROM t 𝒜).trans <| by
    rw [← F.k_eq C]
    exact add_le_add (add_le_add (add_le_add le_rfl (overrun_le R F C))
      (SPBCS.keyCollision_mono (F.rounds_le C) _)) le_rfl

/-- **Completeness of the configuration's argument in the QROM** (paper `thm:e2e`(1) in the
QROM; `def:narg-complete`, `NARG.QROM.Complete`; Unruh 2017 Definition 5, p. 14;
`ProofSystemTranscript.Guarantees.completeQROM` at `GrantedFacts.e2e`): at every honest strategy
`H`, the honest prover `prover` run through `queryEncoding`, with uniform coins, Merkle salts and
salt, is complete for the
spBCS verifier `verifierQROM`: every `t`-query adversary of `def:adversary` that outputs a statement
and an honest input after its queries makes the honest proof of a valid pair rejected with
probability at most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + 2 t/2^(4 kS)`. The compiled
circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem completeness_adaptive_qrom (C : R.Compiled) (TA : R.TA C) {Inp : Type}
    {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH) :
    NARG.QROM.Complete queryEncoding (prover R F C TA H) (verifierQROM R F C)
      (fun x π => SPBCS.Claim.mk x π.val)
      (fun x y => (x, y) ∈ R.hrel relH) fun t => (R.err H : ℝ≥0∞) +
        (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k +
          2 * t / 2 ^ (4 * R.kS) :=
  fun t 𝒜 => ((F.e2e C TA H (verifierQueries_le R F C) (proofFormat R F C)).completeQROM t 𝒜).trans <| by
    rw [← F.k_eq C]
    exact add_le_add (add_le_add (add_le_add le_rfl (overrun_le R F C))
      (SPBCS.keyCollision_mono (F.rounds_le C) _)) le_rfl

/-- **Completeness of the configuration's argument in the ROM on its honest inputs**
(`completeness_adaptive_rom` at the fixed honest strategy, whose completeness error is `0`): the
honest prover is complete for the spBCS verifier at error
`rounds/2^chernoff + C(rounds, 2)/2^(8k) + t/2^(8 kS)` against classical `t`-query adversaries.
The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem completeness_adaptive_honest_rom (C : R.Compiled) (TA : R.TA C) :
    NARG.ROM.Complete (prover R F C TA R.strategy) (verifierROM R F C)
      (fun x π => SPBCS.Claim.mk x π.val)
      (fun x y => (x, y) ∈ R.hrel R.relH) fun t =>
        (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k + t / 2 ^ (8 * R.kS) :=
  fun t 𝒜 => (completeness_adaptive_rom R F C TA R.strategy t 𝒜).trans_eq <| by
    rw [F.exact, ENNReal.coe_zero, zero_add]

/-- **Completeness of the configuration's argument in the QROM on its honest inputs**
(`completeness_adaptive_qrom` at the fixed honest strategy, whose completeness error is `0`): the
honest prover is complete for the spBCS verifier at error
`rounds/2^chernoff + C(rounds, 2)/2^(8k) + 2 t/2^(4 kS)` against `t`-query adversaries of
`def:adversary`. The compiled circuits' `enforce`, `TA`: trust base. -/
@[config_template headline]
theorem completeness_adaptive_honest_qrom (C : R.Compiled) (TA : R.TA C) :
    NARG.QROM.Complete queryEncoding (prover R F C TA R.strategy) (verifierQROM R F C)
      (fun x π => SPBCS.Claim.mk x π.val)
      (fun x y => (x, y) ∈ R.hrel R.relH) fun t =>
        (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k +
          2 * t / 2 ^ (4 * R.kS) :=
  fun t 𝒜 => (completeness_adaptive_qrom R F C TA R.strategy t 𝒜).trans_eq <| by
    rw [F.exact, ENNReal.coe_zero, zero_add]

end AdaptiveCompleteness

/-- **The honest inputs of a relation's pairs**: a relation `rel` within the headline relation
`rel'` and, for each of its pairs, an honest input of the fixed strategy at the pair's statement.
It carries the paper's relation (or its restriction to the pairs the honest prover supports, named
at the configuration) to the honest inputs the completeness, zero-knowledge and
witness-indistinguishability statements quantify over. -/
structure HonestOf (R : Configuration) where
  /-- The relation. -/
  rel : Set (R.Stmt × R.Wit')
  /-- It lies within the headline relation. -/
  rel_subset : rel ⊆ R.rel'
  /-- The honest input of a pair. -/
  honestOf : (p : R.Stmt × R.Wit') → p ∈ rel → R.HonestIn
  /-- The honest input of a pair is at the pair's statement. -/
  keyStmtOf_honestOf : ∀ p (hp : p ∈ rel), R.keyStmtOf (honestOf p hp) = p.1

namespace PaperRelation

open Common

variable (R : Configuration) (F : R.GrantedFacts) (B : R.HonestOf)
include F

/-- **Every pair of the relation has an honest input at its statement**: the honest input
`B.honestOf p hp` of a pair `p` of `B.rel` is in the honest relation at `p`'s statement, so the
completeness, zero-knowledge and witness-indistinguishability statements of the configuration on
its honest inputs hold on the honest inputs of the relation's pairs, the honest prover run on
`B.honestOf p hp`. -/
@[config_template headline]
theorem honest_input_of_rel {p : R.Stmt × R.Wit'} (hp : p ∈ B.rel) :
    (p.1, B.honestOf p hp) ∈ R.hrel R.relH := by
  have h := F.keyStmtOf_mem (B.honestOf p hp)
  rwa [B.keyStmtOf_honestOf p hp] at h

open Classical in
/-- **Completeness of the configuration's argument on the relation's pairs**
(`Common.completeness_honest` at the honest input `B.honestOf p hp` of a pair `p` of `B.rel`, at
`p`'s statement): at every value of the honest prover's coins, Merkle salts and salt, over a
uniform oracle the spBCS verifier rejects the compiled honest proof of `p`'s statement with
probability at most `rounds/2^chernoff + C(rounds, 2)/2^(8k)`. The compiled circuits' `enforce`,
`TA`: trust base. -/
@[config_template headline]
theorem completeness_of_rel (C : R.Compiled) (TA : R.TA C)
    (c : (honestProver R F C TA R.strategy).Coins) {p : R.Stmt × R.Wit'} (hp : p ∈ B.rel)
    (ν : (setting R F C).model.Pos → MerkleSalt (2 * (R.T C).k)) (σ : FiatShamirSalt R.kS) :
    Pr[h ← (Query (R.T C).k (2 * (R.T C).k) R.kS (2 ^ 40) →
          Out (R.T C).k (fsExtraBytes + (R.T C).maxGrant)) :
        ¬ (setting R F C).model.Accepts h p.1 ((prover R F C TA R.strategy).toFn.prove h
          p.1 (B.honestOf p hp) { salt := σ, coins := { iop := c, merkleSalts := ν } }).val
          ((setting R F C).queries p.1)] ≤
      (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k := by
  have h := completeness_honest R F C TA c (B.honestOf p hp) ν σ
  rwa [B.keyStmtOf_honestOf p hp] at h

end PaperRelation

end GordieHowe.Configuration
