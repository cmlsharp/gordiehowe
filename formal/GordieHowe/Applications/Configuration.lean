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
`GordieHowe/SPBCS/CompleteAdaptive.lean`) at the configuration's IOP, transcript, salt
length, relations, honest prover and figures, with the figures' side conditions discharged once.

This module states them once, generically:

* `GordieHowe.Configuration`: the data of a configuration (the type of proof systems its code is generic over, the IOP, its soundness
  data, its transcript, the Fiat–Shamir salt length, the relation and the witness map,
  the honest prover and its completeness error as type families, the fixed honest strategy, and the
  figures: rounds, Chernoff exponent and point, leaves, queried leaves, verifier queries, the
  largest round error, digests per input, query caps, positions and the digest length);
* `GordieHowe.Configuration.GrantedFacts`: the facts the generic proofs use, and `GordieHowe.Configuration.Facts`, the form
  of a configuration without granted points, which extends it. Among them are the guarantees of
  the end-to-end theorem at the configuration's IOP (`knowledge`, `e2e`), which a configuration
  proves as an instance of the proof system's end-to-end theorem
  (`GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`, `GordieHowe.RealizedProgram.ProofSystem.FieldBranches.e2e`, paper
  `thm:e2e`); every headline follows from them and the figures;
* the templates (`@[config_template]`, `GordieHowe/Applications/Configuration/Instantiate.lean`) in five families:
  `Common` (the setting, the extractor, the knowledge errors, the verifiers, the honest prover and
  the headlines every configuration has), `GordieHowe.Configuration.ZeroKnowledgeROM` (query-counted zero knowledge in the ROM, the
  ROM parameters' form), `GordieHowe.Configuration.ZeroKnowledgeQROM` (query-counted zero knowledge
  in the QROM, the QROM parameters' form), `GordieHowe.Configuration.AdaptiveCompleteness` (adaptive
  completeness) and `GordieHowe.Configuration.PaperRelation` (the honest inputs and the completeness
  of the pairs of a relation within the configuration's relation, `GordieHowe.Configuration.HonestOf`).

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
every round's load passes the test `2^-E` at a point `z` on `k + fsExtraBytes` bytes plus its grant
(`SpecReaders.AllGranted`), the overrun is at most the round count over `2^E`. -/
theorem overrun_le_at_granted (hb : T.MergeBounds kS) (z : ℝ) (E : ℕ)
    (h : ∀ j, (T.readers j).AllGranted fun g L =>
      Configurations.PassesChernoff z ((1 / 2) ^ E) (T.k + Configurations.fsExtraBytes + g) L) :
    (T.setting kS hb).model.overrun ≤ (∑ q : C.shape.term.Leaf, C.rounds q.label : ℕ) / 2 ^ E := by
  have hc := card_chIdx_le (C := C)
  calc (T.setting kS hb).model.overrun
      = ∑ c : ChIdx C.P C.term, (C.samplersOf T.readers T.k (Configurations.fsExtraBytes + T.maxGrant) T.stream
          c.leaf.label c.idx).rejectionProb := rfl
    _ ≤ ∑ _c : ChIdx C.P C.term, ENNReal.ofReal ((1 / 2) ^ E) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hc' : Configurations.PassesChernoff z ((1 / 2) ^ E) (T.stream c.leaf.label c.idx)
            ((T.readers c.leaf.label) c.idx).load := h c.leaf.label c.idx
        unfold RealizedProgram.ProofSystem.IOP.samplersOf
        rw [SpecReaders.sampler_rejectionProb _ (stream_le hb.toBounds c.leaf.label c.idx)]
        exact ((T.readers c.leaf.label c.idx).failProb_le hc'.one_le hc'.pow_lt _ _).trans
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

/-- **The data of a configuration under spBCS**: the type of proof systems its code is generic
over, the IOP, its soundness data and transcript, the Fiat–Shamir salt length, the
relation and the witness map, the honest prover and its completeness error as type families, the
fixed honest strategy, and the figures. Every field is data; the facts the generic proofs use are
`Configuration.GrantedFacts`. -/
structure _root_.GordieHowe.Configuration.{u} where
  /-- The proof systems the configuration's code is generic over (the program's
  `RealizedProgram.ProofSystem`, a `Type 1`). Its definitions take one and read it at run time; its
  statements are instantiated at the configuration's proof system (`instantiate_config … at`). -/
  ProofSystem : Type u
  /-- The statements. -/
  Stmt : Type
  /-- The decision of equality of statements: the database extractor (`SPBCS.dbExtract`) reads
  the recorded inputs whose statement is the one it extracts at. -/
  [decEq : DecidableEq Stmt]
  /-- The witnesses of the IOP's relation. -/
  IopWit : Type
  /-- The IOP's relation. -/
  iopRel : Set (Stmt × IopWit)
  /-- The multi-circuit IOP with forked domains at a proof system. -/
  iop : ProofSystem → RealizedProgram.ProofSystem.IOP Stmt IopWit iopRel
  /-- Its soundness data. -/
  sound : ∀ C, (iop C).Sound
  /-- Its transcript: label, digests, codecs and challenge readers. -/
  T : ∀ C, ProofSystemTranscript (iop C)
  /-- The Fiat–Shamir salt length in bytes. -/
  kS : ℕ
  /-- The witnesses of the relation. -/
  Wit : Type
  /-- The relation the argument is about (the paper's relation in `thm:e2e`). -/
  rel : Set (Stmt × Wit)
  /-- The witness map from the IOP's witnesses to the relation's, applied by the extractor. -/
  witnessMap : Stmt → IopWit → Wit
  /-- The valuations the honest strategies are stated over. -/
  Val : Type
  /-- The honest strategies on honest inputs `Inp` related to valuations by `relH`. -/
  Strategy : (Inp : Type) → Set (Val × Inp) → Type
  /-- The honest relation at the statements, from the strategy's relation at the valuations. -/
  hrel : {Inp : Type} → Set (Val × Inp) → Set (Stmt × Inp)
  /-- The simulator data of the IOP: data apart from the honest prover and the soundness data. -/
  sim : ∀ C, (iop C).SimData
  /-- The honest prover of the IOP at a strategy, simulated by `sim`. -/
  honest : ∀ C {Inp : Type} {relH : Set (Val × Inp)}, Strategy Inp relH →
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
  stmtOfHonest : HonestIn → Stmt
  /-- A default witness of the IOP's relation (for the extractor's failure output). -/
  inh : Inhabited IopWit
  /-- The bound on the rounds of the composite. -/
  rounds : ℕ
  /-- The Chernoff exponent of every round's load: each round's stream overruns with probability at
  most `2^-chernoff`. -/
  chernoff : ℕ
  /-- The numerator of the point `zNum / zDen` at which every round's load passes the Chernoff
  test. -/
  zNum : ℕ
  /-- The denominator of that point. -/
  zDen : ℕ
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
  of the spBCS verifier, for the relation at the extractor's witness read by `witnessMap`
  (an instance of `RealizedProgram.ProofSystem.FieldBranches.e2e_knowledge`). -/
  knowledge : ∀ C {kq : ℕ} (hkq : (R.T C).QueryBudget R.kS (hb C) kq),
    (R.T C).KnowledgeGuarantees R.kS (hb C) (R.sound C) R.rel R.witnessMap hkq
  /-- **The end-to-end theorem** (paper `thm:e2e`) at every honest strategy, with the strategy's
  completeness error (an instance of `RealizedProgram.ProofSystem.FieldBranches.e2e`). -/
  e2e : ∀ C {Inp : Type} {relH : Set (R.Val × Inp)} (H : R.Strategy Inp relH)
    {kq : ℕ} (hkq : (R.T C).QueryBudget R.kS (hb C) kq) (hf : (R.T C).ProofFormat R.kS (hb C) R.proofBound),
    (R.T C).Guarantees R.kS (hb C) (R.sound C) R.rel R.witnessMap hkq hf (R.honest C H) (R.err H)
  /-- The composite has at most `rounds` rounds. -/
  rounds_le : ∀ C, ∑ q : (R.iop C).shape.term.Leaf, (R.iop C).rounds q.label ≤ R.rounds
  /-- Every round's load passes the Chernoff test `2^-chernoff` at the point `zNum / zDen` on the
  round's own stream length, `k + fsExtraBytes` plus its grant. -/
  loadsGranted : ∀ C j, ((R.T C).readers j).AllGranted fun g L =>
    PassesChernoff ((R.zNum : ℝ) / R.zDen) ((1 / 2) ^ R.chernoff) ((R.T C).k + fsExtraBytes + g) L
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
  stmtOfHonest_mem : ∀ y, (R.stmtOfHonest y, y) ∈ R.hrel R.relH

/-- **The facts of a configuration without granted points**: `GrantedFacts` with every round's
load passing the Chernoff test on `k + fsExtraBytes` bytes (`loads`), which a grant keeps
(`PassesChernoff.anti`, `SpecReaders.AllGranted.of_allLoads`). -/
structure Facts : Prop extends R.GrantedFacts where
  /-- Every round's load passes the Chernoff test `2^-chernoff` at the point `zNum / zDen`. -/
  loads : ∀ C j, ((R.T C).readers j).AllLoads
    (PassesChernoff ((R.zNum : ℝ) / R.zDen) ((1 / 2) ^ R.chernoff) ((R.T C).k + fsExtraBytes))
  loadsGranted := fun C j => SpecReaders.AllGranted.of_allLoads
    (fun _ _ h => h.anti (Nat.le_add_right _ _)) (loads C j)

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
abbrev setting (C : R.ProofSystem) :
    Setting (R.iop C).toCausalIOP (R.iop C).merges (R.T C).k :=
  (R.T C).setting R.kS (F.hb C)

/-- **The valuations of the configuration's program** (`Configuration.Val`): the values the honest
strategies are stated over. -/
@[config_template]
abbrev Valuation (_F : R.GrantedFacts) : Type :=
  R.Val

/-- **The honest strategies of the configuration** on honest inputs `Inp` related to valuations by
`relH` (`Configuration.Strategy`). -/
@[config_template]
abbrev HonestStrategy (_F : R.GrantedFacts) {Inp : Type} (relH : Set (Valuation R _F × Inp)) : Type :=
  R.Strategy Inp relH

/-- **The random oracle of the configuration's setting** (`SPBCS.Setting.Oracle`): the functions
from the setting's queries to its answers, the paper's `RO`. -/
@[config_template]
abbrev Oracle (C : R.ProofSystem) : Type :=
  (setting R F C).Oracle

/-- **The argument of the configuration**: the spBCS compiler data of its setting
(`SPBCS.Setting.model`), the paper's spBCS transformation of the IOP. -/
@[config_template]
abbrev argument (C : R.ProofSystem) :=
  (setting R F C).model

/-- **The query phase of the configuration's setting** (`SPBCS.Setting.queries`), decided by the
IOP's verifier through query locality. -/
@[config_template]
abbrev queries (C : R.ProofSystem) :=
  (setting R F C).queries

/-- **The proof bound of the zero-knowledge games** (`Configuration.proofBound`): the larger of the
tree bound `N` and the query bound `nq`. -/
@[config_template]
abbrev proofBound (_F : R.GrantedFacts) : ℕ :=
  R.proofBound

/-- **The extractor of the statements**: the composite's extractor (`RealizedProgram.ProofSystem.IOP.extractor`), its
witness read by the witness map `witnessMap` (`CausalExtractor.mapWit`).

Running time: one run of the composite's extractor (the application phase's extraction from the
domains' commit phases) and one application of the witness map `witnessMap`, polynomial when it is (the
configurations' maps read the witness at the statement's values: one `ExpandA` and one `H(pk)` for
ML-DSA, the key's coefficients for Falcon). This running time is argued here, not proved in Lean. -/
@[config_template]
def extractor (_F : R.GrantedFacts) (C : R.ProofSystem) :
    CausalExtractor (R.iop C).P (R.iop C).term R.Stmt R.Wit :=
  (R.iop C).extractor.mapWit R.witnessMap

/-- **The extractor of the statements is the composite's**, its witness read by `witnessMap`. -/
theorem extractor_eq (C : R.ProofSystem) :
    extractor R F C = (R.iop C).extractor.mapWit R.witnessMap :=
  rfl

/-- **The decoding of the database extractor's queries**: the decoder of the chain inputs of the
setting (`SPBCS.MergeEncoding.decode` of the spBCS compiler's encoding), which the database
extractor applies to every transcript query of the database (`SPBCS.candidate`) and to every input
it reads behind a final digest (`SPBCS.resolveSink`). It parses the label, the salt, the statement
writes by the transcript's statement codec, and the chain contents by the write codecs.

Running time: one pass over the input's bytes, with one parse of each write by its codec, the
statement codec's parse included (for ML-DSA-44, one decision of `ExpandAWithin`: `16 · 336`
SHAKE128 candidates). This running time is argued here, not proved in Lean. -/
@[config_template]
def queryDecoder (C : R.ProofSystem) :=
  ((R.T C).setting R.kS (F.hb C)).model.senc.decode

/-- **The quantum knowledge error at `t` queries**:
`2^9/2^(4k) + 6 t² (errorMax/2^errorExp + D t/2^(8k))`. At `t + kq` it bounds the paper's
`errks(t)` (`thm:e2e`(2)), the spBCS error `2 √(kq/2^(8(k + e))) + 6 (t + kq)² (errk + c' (t +
kq)/2^(8k))` (`SPBCS.knowledgeError_eq`), term by term (`Configurations.knowledgeError_le`): the
first term `2^9/2^(4k)` bounds `2 √(kq/2^(8(k + e)))` since `kq ≤ 2^16` (`GrantedFacts.kq_le`),
`errorMax/2^errorExp` bounds the largest round error `errk` (`GrantedFacts.error_le`), and `D`
bounds `c'` (`GrantedFacts.digests_le`). -/
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

/-- **The quantum extraction error against `t`-query adversaries** (paper `thm:e2e`(2), `errks(t)`):
the quantum knowledge error at the adversary's and the verifier's queries, `t + kq`. -/
@[config_template]
noncomputable abbrev extractionErrorQROM (t : ℕ) : ℝ≥0∞ :=
  knowledgeErrorQROM R F (t + R.kq)

/-- **The classical extraction error against `t`-query adversaries** (paper `thm:e2e`(2),
`errks^C(t)`): the classical knowledge error at the adversary's and the verifier's queries,
`t + kq`. -/
@[config_template]
noncomputable abbrev extractionErrorROM (t : ℕ) : ℝ≥0∞ :=
  knowledgeErrorROM R F (t + R.kq)

/-- **The bound on the overrun** (paper `errov`): `rounds / 2^chernoff` (`overrun_le`). -/
@[config_template]
noncomputable abbrev overrunBound (_F : R.GrantedFacts) : ℝ≥0∞ :=
  (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff

/-- **The bound on the key collisions** (paper `errkey`): `C(rounds, 2)/2^(8k)`
(`SPBCS.keyCollision` at `rounds` rounds and `k`-byte digests). -/
@[config_template]
noncomputable abbrev keyCollisionBound (_F : R.GrantedFacts) : ℝ≥0∞ :=
  SPBCS.keyCollision R.rounds R.k

/-- **The verifier's queries on accepting runs**: at most `kq`, two per round, one per branch and
`1 + log₂ (2N)` per queried leaf (`SPBCS.ProofSystemTranscript.length_queries_le`). -/
@[config_template]
theorem verifierQueries_le (C : R.ProofSystem) (x : R.Stmt) (h) (π : (argument R F C).NIProof)
    (hv : (argument R F C).Accepts h x π (queries R F C x)) :
    ((argument R F C).queries x π h (queries R F C x)).length ≤ R.kq := by
  refine ((R.T C).length_queries_le (F.hb C) (F.leaves_le C) (F.queries_le C) x h π
    hv).trans (le_trans ?_ (F.kq_ge C))
  have := F.rounds_le C
  omega

/-- **The spBCS verifier in the QROM**, at its `kq` queries. -/
@[config_template]
abbrev verifierQROM (C : R.ProofSystem) :=
  (R.T C).verifier R.kS (F.hb C) R.kq


/-- **The spBCS verifier in the ROM**, at `kq` queries. -/
@[config_template]
abbrev verifierROM (C : R.ProofSystem) :=
  (R.T C).verifierROM R.kS (F.hb C) R.kq

/-- **The knowledge adversaries in the QROM** (paper `def:narg-ks`): the `t`-query adversaries of
`def:adversary` against the configuration's setting that make no proof queries, whose output is a
claim (a statement and a proof) and an auxiliary output in `Zo`. -/
@[config_template]
abbrev KnowledgeAdversaryQROM (C : R.ProofSystem) (Zo : Type) (t : ℕ) :=
  (setting R F C).QROMAdversary (Claim R.Stmt (argument R F C).NIProof × Zo) t

/-- **The soundness adversaries in the QROM** (paper `def:narg-sound`): the `t`-query adversaries
of `def:adversary` against the configuration's setting that make no proof queries, whose output is
a claim. -/
@[config_template]
abbrev SoundnessAdversaryQROM (C : R.ProofSystem) (t : ℕ) :=
  (setting R F C).QROMAdversary (Claim R.Stmt (argument R F C).NIProof) t

/-- **The knowledge adversaries in the ROM** (paper `def:narg-ks`): the classical `t`-query
adversaries against the configuration's setting that make no proof queries, whose output is a
claim and an auxiliary output in `Zo`. -/
@[config_template]
abbrev KnowledgeAdversaryROM (C : R.ProofSystem) (Zo : Type) (t : ℕ) :=
  (setting R F C).ROMAdversary (Claim R.Stmt (argument R F C).NIProof × Zo) t

/-- **The soundness adversaries in the ROM** (paper `def:narg-sound`): the classical `t`-query
adversaries against the configuration's setting that make no proof queries, whose output is a
claim. -/
@[config_template]
abbrev SoundnessAdversaryROM (C : R.ProofSystem) (t : ℕ) :=
  (setting R F C).ROMAdversary (Claim R.Stmt (argument R F C).NIProof) t

/-- **The online extractor in the QROM**: the database extractor at `extractor` on the bits of
the compressed oracle's database (`SPBCS.dbExtractBits`, `NARG.QROM.compressedExt`), DFMS22's
online extractor.

Running time: one read of the compressed oracle's register slots into a database
(`NARG.QROM.compressedExt`, `slotsDB`), one pass over the slots, and one run of
`SPBCS.dbExtractBits` at `extractor` on it (its Running time paragraph). This running time is
argued here, not proved in Lean. -/
@[config_template]
abbrev extractorQROM (C : R.ProofSystem) :=
  NARG.QROM.compressedExt ((argument R F C).dbExtractBits (extractor R F C))

/-- **The online extractor in the ROM**: the database extractor at `extractor` on the table of
the lazily sampled oracle (`SPBCS.dbExtract`).

Running time: one run of `SPBCS.dbExtract` at `extractor` (its Running time paragraph). This
running time is argued here, not proved in Lean. -/
@[config_template]
abbrev extractorROM (C : R.ProofSystem) :=
  (argument R F C).dbExtract (extractor R F C)

/-- **The overrun of the spBCS setting**: at most `rounds / 2^chernoff`
(`SPBCS.ProofSystemTranscript.overrun_le_at_granted`, every round's load within `2^-chernoff` on
its own stream length). -/
@[config_template]
theorem overrun_le (C : R.ProofSystem) :
    (argument R F C).overrun ≤ overrunBound R F :=
  ((R.T C).overrun_le_at_granted (F.hb C) _ R.chernoff (F.loadsGranted C)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast F.rounds_le C) _)

/-- **The positions of the spBCS setting**: `pos`, the leaves of all trees
(`SPBCS.ProofSystemTranscript.card_pos`). -/
@[config_template]
theorem card_pos (C : R.ProofSystem) : Fintype.card (argument R F C).Pos = R.pos :=
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
verifier accepts while the database extractor at `extractor` returns no witness of the
relation with probability at most `extractionErrorQROM t`, the quantum knowledge error at
`t + kq` (paper `thm:e2e`(2), `errks(t)`). -/
@[config_template headline]
theorem knowledge_soundness_qrom_at (C : R.ProofSystem) {Zo : Type} {t : ℕ}
    (𝒢 : KnowledgeAdversaryQROM R F C Zo t) :
    𝒢.OnlineExtracts (verifierQROM R F C) NARG.QROM.compressedSim R.rel
      (extractorQROM R F C) 0 (extractionErrorQROM R F t) := by
  have h1 := (F.knowledge C (verifierQueries_le R F C)).knowledge 𝒢
  have h2 : _ ≤ knowledgeErrorQROM R F (t + R.kq) := (Configurations.knowledgeError_le (k := (R.T C).k)
    (e := fsExtraBytes + (R.T C).maxGrant) (t := t + R.kq) F.kq_le (F.digests_le C)
    (F.error_le C)).trans_eq (by rw [F.k_eq C])
  exact h1.mono le_rfl h2

/-- **Soundness of the configuration's argument at `t` quantum queries**
(`SPBCS.ProofSystemTranscript.soundness`, the `soundness` clause of
`SPBCS.knowledgeGuarantees`): every `t`-query adversary of `def:adversary` that makes no proof
queries outputs a statement without a witness of the relation and a proof the spBCS
verifier accepts with probability at most `extractionErrorQROM t` (paper `thm:e2e`(2), `errks(t)`). -/
@[config_template headline]
theorem soundness_qrom_at (C : R.ProofSystem) {t : ℕ} (𝒜 : SoundnessAdversaryQROM R F C t) :
    𝒜.acceptsFalse (verifierQROM R F C) R.rel ≤ extractionErrorQROM R F t := by
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
database extractor at `extractor`, reading the table of the adversary's and the verifier's
`kq` queries, returns no witness of the relation with probability at most
`extractionErrorROM t`, the classical knowledge error at `t + kq` (paper `thm:e2e`(2), `errks^C(t)`). -/
@[config_template headline]
theorem knowledge_soundness_rom_at (C : R.ProofSystem) {Zo : Type} {t : ℕ}
    (𝒢 : KnowledgeAdversaryROM R F C Zo t) :
    𝒢.OnlineExtracts (verifierROM R F C) NARG.ROM.OracleSampler.lazy.law R.rel
      (extractorROM R F C) 0 (extractionErrorROM R F t) := by
  have h1 := (F.knowledge C (verifierQueries_le R F C)).knowledgeROM 𝒢
  have h2 : _ ≤ knowledgeErrorROM R F (t + R.kq) := (Configurations.knowledgeErrorROM_le
    (k := (R.T C).k) (t := t + R.kq) (F.digests_le C) (F.error_le C)).trans_eq (by rw [F.k_eq C])
  exact h1.mono le_rfl h2

/-- **Soundness of the configuration's argument in the classical random-oracle model at `t`
queries** (`SPBCS.ProofSystemTranscript.soundnessROM`, the `soundnessROM` clause of
`SPBCS.knowledgeGuarantees`): every classical `t`-query adversary that makes no proof queries
outputs a statement without a witness of the relation and a proof the spBCS verifier accepts
with probability at most `extractionErrorROM t` (paper `thm:e2e`(2), `errks^C(t)`). -/
@[config_template headline]
theorem soundness_rom_at (C : R.ProofSystem) {t : ℕ} (𝒜 : SoundnessAdversaryROM R F C t) :
    𝒜.acceptsFalse (verifierROM R F C) R.rel ≤ extractionErrorROM R F t := by
  have h2 : _ ≤ knowledgeErrorROM R F (t + R.kq) := (Configurations.knowledgeErrorROM_le
    (k := (R.T C).k) (t := t + R.kq) (F.digests_le C) (F.error_le C)).trans_eq (by rw [F.k_eq C])
  exact ((F.knowledge C (verifierQueries_le R F C)).soundnessROM 𝒜).trans h2

/-- **Knowledge soundness of the configuration's argument at the quantum query cap `qQ`** (online
extractability, DFMS22 Definition 3.1, p. 10, with CMS19's compressed oracle as the oracle
simulator and simulation error `0`): for every
adversary of `def:adversary` that makes no proof queries, with at most `qQ` queries and an
auxiliary output, the extraction run leaves the adversary's register in its real-run state at every
output and verdict, and in it the spBCS verifier accepts while the database extractor returns no witness with probability at
most `extractionErrorQROM qQ` (`knowledge_soundness_qrom_at`, `knowledgeErrorQROM_mono`). -/
@[config_template]
theorem knowledge_soundness_qrom (C : R.ProofSystem) {Zo : Type} {t : ℕ}
    (𝒢 : KnowledgeAdversaryQROM R F C Zo t) (ht : t ≤ R.qQ) :
    𝒢.OnlineExtracts (verifierQROM R F C) NARG.QROM.compressedSim R.rel
      (extractorQROM R F C) 0 (extractionErrorQROM R F R.qQ) :=
  (knowledge_soundness_qrom_at R F C 𝒢).mono le_rfl
    (knowledgeErrorQROM_mono R F (Nat.add_le_add_right ht _))

/-- **Soundness of the configuration's argument at the quantum query cap `qQ`**: every
adversary of `def:adversary` that makes no proof queries, with at most `qQ` queries, outputs a statement without a
witness of the relation and an accepted proof with probability at most
`extractionErrorQROM qQ` (`soundness_qrom_at`, `knowledgeErrorQROM_mono`). -/
@[config_template]
theorem soundness_qrom (C : R.ProofSystem) {t : ℕ} (𝒜 : SoundnessAdversaryQROM R F C t)
    (ht : t ≤ R.qQ) :
    𝒜.acceptsFalse (verifierQROM R F C) R.rel ≤ extractionErrorQROM R F R.qQ :=
  (soundness_qrom_at R F C 𝒜).trans (knowledgeErrorQROM_mono R F (Nat.add_le_add_right ht _))

/-- **Knowledge soundness of the configuration's argument in the classical random-oracle model at
the classical query cap `qR`** (online extractability against the lazily sampled oracle): for every
classical adversary that makes no proof queries, with at most `qR` queries and an auxiliary output,
the extraction run has the real run's law of the output and the verdict, and in it the spBCS
verifier accepts while the database extractor returns no witness with probability at most
`extractionErrorROM qR` (`knowledge_soundness_rom_at`,
`knowledgeErrorROM_mono`). -/
@[config_template]
theorem knowledge_soundness_rom (C : R.ProofSystem) {Zo : Type} {t : ℕ}
    (𝒢 : KnowledgeAdversaryROM R F C Zo t) (ht : t ≤ R.qR) :
    𝒢.OnlineExtracts (verifierROM R F C) NARG.ROM.OracleSampler.lazy.law R.rel
      (extractorROM R F C) 0 (extractionErrorROM R F R.qR) :=
  (knowledge_soundness_rom_at R F C 𝒢).mono le_rfl
    (knowledgeErrorROM_mono R F (Nat.add_le_add_right ht _))

/-- **Soundness of the configuration's argument in the classical random-oracle model at the
classical query cap `qR`**: every classical adversary that makes no proof queries, with at most
`qR` queries, outputs a statement without a witness of the relation and an accepted proof with
probability at most `extractionErrorROM qR` (`soundness_rom_at`,
`knowledgeErrorROM_mono`). -/
@[config_template]
theorem soundness_rom (C : R.ProofSystem) {t : ℕ} (𝒜 : SoundnessAdversaryROM R F C t)
    (ht : t ≤ R.qR) :
    𝒜.acceptsFalse (verifierROM R F C) R.rel ≤ extractionErrorROM R F R.qR :=
  (soundness_rom_at R F C 𝒜).trans
    (knowledgeErrorROM_mono R F (Nat.add_le_add_right ht _))

/-! ## The honest prover -/

/-- **The proof format of the zero-knowledge games**: every query phase of the configuration's
setting opens at most `proofBound` positions and every tree has at most `proofBound` leaves, since
`proofBound` is the larger of the tree size `N` and the number `nq` of queried leaves. -/
@[config_template]
theorem proofFormat (C : R.ProofSystem) : (R.T C).ProofFormat R.kS (F.hb C) R.proofBound :=
  ProofSystemTranscript.formatBounds (F.hb C) (fun d => (F.leaves_le C d).trans (le_max_left _ _))
    fun ch => (F.queries_le C ch).trans (le_max_right _ _)

/-- **The honest prover of the configuration at a strategy**: the IOP's honest prover at the
strategy `H` (the proof system's phased honest prover and every forked domain's honest prover, read
at the statement). -/
@[config_template]
abbrev honestProver (_F : R.GrantedFacts) (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R _F × Inp)} (H : HonestStrategy R _F relH) :
    (R.iop C).Honest (R.sim C) Inp (R.hrel relH) :=
  R.honest C H

/-- **The honest prover of the configuration's argument** at the strategy `H`: the compiled proof
of the IOP's honest prover, with coins, Merkle salts and salt whose law is an argument of each
statement (`coinLaw`), in the format `proofBound` (`ProofSystemTranscript.prover`). It is the
prover of every completeness, zero-knowledge and witness-indistinguishability statement of the
configuration. -/
@[config_template]
noncomputable abbrev prover (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :=
  (R.T C).prover R.kS (F.hb C) (proofFormat R F C)
    (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C H))

/-- **The coin law of the configuration's honest prover** at the strategy `H`: uniform on the
prover's coins, the Fiat–Shamir salt, the IOP prover's coins and a Merkle salt per position
(`NARG.Prover.uniformLaw`). It is named so that the inferred `Fintype` and `Nonempty` instance
terms of `PMF.uniformOfFintype` stay out of the templates' headline statements, which read
`coinLaw`. -/
@[config_template]
noncomputable abbrev coinLaw (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :=
  (prover R F C H).uniformLaw

/-- **The simulator of the configuration's argument**: the compiled simulator
(`ProofSystemTranscript.simulator`, `SPBCS.niSimulator`) of the IOP's simulator at the
configuration's simulator data (`Configuration.sim`), its proofs in the format `proofBound`. It
reads no honest prover, strategy or witness, and it is the simulator of every zero-knowledge and
simulation-extractability statement of the configuration, at every strategy.

Running time: that of `SPBCS.niSimulator` at the setting (its Running time paragraph). This running
time is argued here, not proved in Lean. -/
@[config_template]
abbrev simulator (C : R.ProofSystem) :=
  (R.T C).simulator R.kS (F.hb C) (proofFormat R F C) (R.sim C)

/-- **The coins of the configuration's honest prover** at the strategy `H` (`prover`): a
Fiat–Shamir salt, the IOP prover's coins and a Merkle salt per position (`SPBCS.ProverCoins`). -/
@[config_template]
abbrev HonestCoins (C : R.ProofSystem) {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) : Type :=
  SaltedCoins (FiatShamirSalt R.kS) ((argument R F C).ProverCoins (honestProver R F C H).Coins)

/-- **The honest proof**: the proof of the configuration's honest prover at the strategy `H`
(`prover`) under the oracle `h`, at the statement `s`, the honest input `y` and the coins `r`. -/
@[config_template]
noncomputable abbrev honestProof (C : R.ProofSystem) {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (h : Oracle R F C) (s : R.Stmt) (y : Inp) (r : HonestCoins R F C H) :
    (argument R F C).NIProof :=
  ((prover R F C H).toFn.prove h s y r).val

/-- **The rejection event**: under the oracle `h`, the spBCS verifier rejects the proof `π` at the
statement `s` (its query phase `queries`). -/
@[config_template]
abbrev Rejects (C : R.ProofSystem) (h : Oracle R F C) (s : R.Stmt) (π : (argument R F C).NIProof) :
    Prop :=
  ¬ (argument R F C).Accepts h s π (queries R F C s)

/-- **The completeness error of a strategy at the configuration's figures** (paper
`errc + errov + errkey`): the strategy's completeness error `err H`, the overrun bound and the
key-collision bound. -/
@[config_template]
noncomputable abbrev completenessError {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) : ℝ≥0∞ :=
  (R.err H : ℝ≥0∞) + overrunBound R F + keyCollisionBound R F

/-- **Completeness of the configuration's argument** (paper `thm:e2e`(1) at a fixed statement:
the `completeness` clause of `SPBCS.CompletenessGuarantees` at `GrantedFacts.e2e`): on an
honest input `y` at the statement `s`, at every value `r` of the honest prover's coins
(`HonestCoins`: the salt, the IOP prover's coins and the Merkle salts), over a uniform oracle the spBCS verifier rejects the compiled honest proof
with probability at most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k)` (the strategy's
completeness error, the overrun and the key collisions). -/
@[config_template headline]
theorem completeness (C : R.ProofSystem) {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (r : HonestCoins R F C H)
    {s : R.Stmt} {y : Inp} (hy : (s, y) ∈ R.hrel relH) :
    Pr[h ← Oracle R F C : Rejects R F C h s (honestProof R F C H h s y r)] ≤
      completenessError R F H := by
  rcases r with ⟨σ, c, ν⟩
  have hp : ∀ h, ((prover R F C H).toFn.prove h s y
      { salt := σ, coins := { iop := c, merkleSalts := ν } }).val = SPBCS.prove
        (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C H) y c) s σ
        (setting R F C).encoder ν h ((setting R F C).queries s) := fun h =>
    (setting R F C).model.toFn_niProver (setting R F C).layout _ (setting R F C).encoder
      (setting R F C).viewEncoder (proofFormat R F C) h s y _
  refine le_of_eq_of_le (congrArg (probUniform _) (funext fun h => congrArg Not (congrArg
    (fun π => (setting R F C).model.Accepts h s π ((setting R F C).queries s)) (hp h)))) ?_
  have h := ((F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).completeness c).completeness s y ν σ hy
  rw [ROM.probUniform_unit_prod, SPBCS.completenessError, SPBCS.keyCollisionBound,
    SPTerm.size_eq_sum] at h
  refine h.trans (add_le_add (add_le_add le_rfl (overrun_le R F C)) ?_)
  show _ ≤ SPBCS.keyCollision R.rounds R.k
  rw [← F.k_eq C]
  exact SPBCS.keyCollision_mono (F.rounds_le C) _

/-- **Completeness of the configuration's argument at a drawn honest input** (the
`completenessOfSampler` form of `Common.completeness`, `WitnessSampler.prob_draw_le`): for a
witness sampler `D` whose honest input on the proof query `u` is outside the honest relation at the
statement `s` with probability at most `η` (`hD`), at every value `r` of the honest prover's coins
(`HonestCoins`), over the sampler's coins and a uniform oracle the spBCS verifier
rejects the compiled honest proof at the drawn input with probability at most
`err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + η`. -/
@[config_template]
theorem completeness_of_sampler (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH)
    (r : HonestCoins R F C H) {U : Type} (D : WitnessSampler U Inp)
    {s : R.Stmt} {u : U} {η : ℝ≥0} (hD : D.MissesAtMostAt (R.hrel relH) s u η) :
    Pr[d ← D.Draw (Oracle R F C) : Rejects R F C d.oracle s (honestProof R F C H d.oracle s
        (D.draw u d.coins) r)] ≤
      completenessError R F H + η :=
  D.prob_draw_le hD (fun y h => Rejects R F C h s (honestProof R F C H h s y r))
    fun _ hy => completeness R F C H r hy

/-- **Zero knowledge of the configuration's argument** (paper `thm:e2e`(3) in the QROM: the
`zeroKnowledge` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): everlasting
zero knowledge for many adaptively chosen proofs (the distinguisher receives the whole oracle
after the last proof query) against query-bounded adversaries
(`NARG.QROM.EverlastingZeroKnowledge`) of the configuration's prover `prover` on the honest inputs,
against its simulator `simulator`, for statements and honest inputs read from any finite types, with error
`zkError (err H)`, the strategy's completeness error as the HVZK error. -/
@[config_template headline]
theorem everlasting_zero_knowledge_qrom (C : R.ProofSystem) {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) {X' W' : Type} [Fintype X'] [DecidableEq X'] [Fintype W']
    [DecidableEq W'] (fx : X' → R.Stmt) (fw : W' → Inp) :
    NARG.QROM.EverlastingZeroKnowledgeOn (Prod.map fx fw ⁻¹' R.hrel relH) queryEncoding
      ((prover R F C H).comap fx fw) (coinLaw R F C H) ((simulator R F C).comap fx)
      ((argument R F C).zkError (R.err H)) := by
  classical
  exact .of_everlastingZeroKnowledge
    ((F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledge X' W' fx fw)

/-- **Zero knowledge of the configuration's argument at drawn honest inputs** (the
`zeroKnowledgeOfSampler` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): the zero
knowledge of `everlasting_zero_knowledge_qrom` when each proof query of `relU` is answered at an honest input drawn
by `D`, which misses the honest relation with probability at most `η` (`hD`): against every
query-bounded adversary (`SPBCS.ZeroKnowledgeOfSampler`), for statements and proof queries read
from any finite types, the counted honest prover drawing its input (`drawProver`) and the configuration's
counted simulator are at most `zkError (err H) t Q + Q · η` apart. -/
@[config_template]
theorem everlasting_zero_knowledge_qrom_of_sampler (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) {U : Type}
    (D : WitnessSampler U Inp) {relU : Set (R.Stmt × U)} {η : ℝ≥0}
    (hD : D.MissesAtMost (R.hrel relH) relU η) :
    (argument R F C).ZeroKnowledgeOfSampler (setting R F C).layout
      (setting R F C).viewEncoder (proofFormat R F C)
      (RealizedProgram.ProofSystem.IOP.honest (honestProver R F C H)) id
      (RealizedProgram.ProofSystem.IOP.simulator (R.sim C))
      ((R.T C).preimages R.kS (F.hb C)) D relU
      (fun t Q => (argument R F C).zkError (R.err H) t Q + Q * η) :=
  (F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeOfSampler D relU η hD

/-- **Witness indistinguishability of the configuration's argument** (paper `thm:e2e`(4):
`ProofSystemTranscript.Guarantees.witnessIndist` at `GrantedFacts.e2e`): unconditional (against a
distinguisher given the whole random oracle), adaptive multi-theorem witness indistinguishability
(CY24 Definition 33.1.1, pp. 426-427, at unbounded queries, p. 430) of the compiled honest prover on
the honest inputs: for injective binary encodings `eX` of statements and `eW` of honest inputs,
against adversaries making `Q` proof queries, each a statement and two honest inputs of total
encoding length at most `ℓ` chosen as a function of the whole oracle and the earlier proofs, every
distinguisher of the oracle and the proofs has advantage at most `Q · wiError (err H) (choiceCount
ℓ)` (`SPBCS.WitnessIndistinguishableOfLength`), the strategy's completeness error as the HVZK
error. -/
@[config_template headline]
theorem unconditional_witness_indistinguishability (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH)
    (eX : SPBCS.BitEncoding R.Stmt) (eW : SPBCS.BitEncoding Inp) (Q ℓ : ℕ) :
    (argument R F C).WitnessIndistinguishableOfLength (prover R F C H)
      (coinLaw R F C H) eX eW
      (R.hrel relH) Q ℓ
      (Q * (argument R F C).wiError (R.err H) (SPBCS.choiceCount ℓ)) :=
  (F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).witnessIndist eX eW Q ℓ

/-- **Zero knowledge of the configuration's argument in the classical random-oracle model**
(paper `thm:e2e`(3) in the ROM: the `zeroKnowledgeROM` clause of `SPBCS.PrivacyGuarantees` at
`GrantedFacts.e2e`): everlasting zero knowledge for many adaptively chosen proofs (the
distinguisher receives the whole oracle after the last proof query) against query-bounded
classical adversaries (`NARG.ROM.EverlastingZeroKnowledge`), of the prover `prover` against
the compiled simulator, with error `zkErrorROM (err H)`. -/
@[config_template headline]
theorem everlasting_zero_knowledge_rom (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :
    NARG.ROM.EverlastingZeroKnowledgeOn (R.hrel relH) (prover R F C H)
        (coinLaw R F C H)
      (simulator R F C) ((argument R F C).zkErrorROM (R.err H)) :=
  (F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeROM

/-- **The largest round error of the configuration's IOP** (paper `errk`): the largest error of
its soundness data (`maxError`), at most `errorMax / 2^errorExp` (`GrantedFacts.error_le`). -/
@[config_template]
noncomputable abbrev maxRoundError (_F : R.GrantedFacts) (C : R.ProofSystem) : ℝ≥0 :=
  maxError (R.sound C).error

/-- **The simulator's queries per proof query** (paper `def:bcs-quantities`(1), `q_S`):
`ProofSystemTranscript.simQueries` of the configuration's transcript, two per position, one per
round of the composite and one per branch. -/
@[config_template]
abbrev simQueries (C : R.ProofSystem) : ℕ :=
  (R.T C).simQueries R.kS (F.hb C)

/-- **The configuration's simulator in the QROM**: `simulator` run through `queryEncoding`.

Running time: that of `simulator` (its Running time paragraph), each oracle query encoded by
`queryEncoding` in one pass over its bytes. This running time is argued here, not proved in Lean. -/
@[config_template]
abbrev simulatorQROM (C : R.ProofSystem) :=
  (simulator R F C).encode queryEncoding

/-- **The simulation-extraction error in the QROM** (paper `thm:e2e`(5), `errse(t, Q)`): the
spBCS error `SPBCS.simExtractionError` at the verifier's `kq` queries, the largest round error and
`simQueries` simulator queries per proof query. -/
@[config_template]
noncomputable abbrev simExtractionErrorQROM (C : R.ProofSystem) :=
  (argument R F C).simExtractionError R.kq (maxRoundError R F C) (simQueries R F C)

/-- **The simulation-extraction error in the ROM** (paper `thm:e2e`(5), `errse^C(t, Q)`): the
spBCS error `SPBCS.simExtractionErrorROM` at the verifier's `kq` queries, the largest round error
and `simQueries` simulator queries per proof query. -/
@[config_template]
noncomputable abbrev simExtractionErrorROM (C : R.ProofSystem) :=
  (argument R F C).simExtractionErrorROM R.kq (maxRoundError R F C) (simQueries R F C)

/-- **The simulation-extraction error for tests that query the oracle**: at `tq` adversary queries,
`tTest` test queries and `Q` proof queries, `simExtractionErrorQROM` at `tq + tTest` queries plus
the swap error of the test's queries (`SPBCS.swapError`). -/
@[config_template]
noncomputable abbrev simExtractionErrorSimOracle (C : R.ProofSystem) :=
  fun tq tTest Q => simExtractionErrorQROM R F C (tq + tTest) Q + (argument R F C).swapError tTest

open Classical in
/-- **Weak online simulation extractability of the configuration's argument in the QROM** (paper
`thm:e2e`(5) in the QROM, the joint form of `def:bcs-se`:
`SPBCS.ProofSystemTranscript.SimGuarantees.simOnlineExtractability` at `GrantedFacts.e2e`) against
query-bounded adversaries, with the counted simulator of the configuration's simulator (`simulator`) and the
database extractor at `extractor`, at the verifier's `kq` queries: in the extraction run the
joint state of the adversary's output and its auxiliary output is as in the simulated run, and an
accepted proof of a fresh statement from which the extractor obtains no witness of the relation
has probability at most `simExtractionErrorQROM t Q`, the spBCS error
`simExtractionError kq errk q_S t Q` at the largest round error `maxRoundError` and `simQueries`
simulator queries per proof query (`SPBCS.WeakOnlineSimulationExtractable`). -/
@[config_template headline]
theorem weak_online_simulation_extractability_qrom (C : R.ProofSystem) :
    (argument R F C).WeakOnlineSimulationExtractable (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq
      (simulatorQROM R F C) (simExtractionErrorQROM R F C) := by
  rw [extractor_eq R F C]
  exact (F.e2e C R.strategy (verifierQueries_le R F C) (proofFormat R F C)).simOnlineExtractability

open Classical in
/-- **Simulation-sound extractability of the configuration's argument in the QROM** (paper
`thm:e2e`(5) in the QROM: `SPBCS.ProofSystemTranscript.SimGuarantees.simExtractability` at
`GrantedFacts.e2e`; Unruh 2017, Definition 14, p. 21, weak variant, for residual-state tests that
make no oracle queries, with straight-line extraction and freshness in both events) against
query-bounded adversaries, with the counted simulator of the configuration's simulator (`simulator`) and the
database extractor at `extractor`, at the verifier's `kq` queries. -/
@[config_template headline]
theorem unruh_simulation_extractability_qrom (C : R.ProofSystem) :
    (argument R F C).SimulationSoundExtractableFresh (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq
      (simulatorQROM R F C) (simExtractionErrorQROM R F C) := by
  rw [extractor_eq R F C]
  exact (F.e2e C R.strategy (verifierQueries_le R F C) (proofFormat R F C)).simExtractability

/-- **Weak online simulation extractability of the configuration's argument in the classical
random-oracle model** (paper `thm:e2e`(5) in the ROM, the joint form of `def:bcs-se`:
`SPBCS.ProofSystemTranscript.SimGuarantees.simOnlineExtractabilityROM` at `GrantedFacts.e2e`)
against query-bounded classical adversaries with an auxiliary output, with the classical simulator
program of the configuration's simulator (`simulator`) on uniform coins and the database extractor at `extractor`
on the table of the lazily sampled execution, at the verifier's `kq` queries: the extractor's
execution has the simulated execution's law of the claim, the auxiliary output, the statements
of the proof queries and the verdict (oracle simulation error `0`), and wins without extraction with
probability at most `simExtractionErrorROM tq Q`, the spBCS error
`simExtractionErrorROM kq errk q_S tq Q` at the largest round error `maxRoundError` and
`simQueries` simulator queries per proof query. -/
@[config_template headline]
theorem weak_online_simulation_extractability_rom (C : R.ProofSystem) :
    (argument R F C).WeakOnlineSimulationExtractableROM (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq (simulator R F C).prog
      (simQueries R F C) (simExtractionErrorROM R F C) := by
  rw [extractor_eq R F C]
  exact (F.e2e C R.strategy (verifierQueries_le R F C) (proofFormat R F C)).simOnlineExtractabilityROM

open Classical in
/-- **Simulation-sound extractability of the configuration's argument for tests that query the
oracle** (`SPBCS.ProofSystemTranscript.SimGuarantees.simExtractabilitySimOracle` at
`GrantedFacts.e2e`; Unruh
2017, Definition 14, p. 21, weak variant, eq. (6) with the test in Extract′ answered by the
simulated oracle after extraction) against query-bounded adversaries, with the counted simulator of
the configuration's simulator (`simulator`) and the targeted extractor at `extractor`, at the verifier's
`kq` queries: for every adversary with at most `tq` queries and `Q` proof queries and every
residual-state test with at most `tTest` queries, Prove with the test is at most Extract′ with the
test plus `simExtractionErrorSimOracle tq tTest Q`, that is
`simExtractionErrorQROM (tq + tTest) Q + swapError tTest`. -/
@[config_template]
theorem unruh_simulation_extractability_sim_oracle_qrom (C : R.ProofSystem) :
    (argument R F C).SimulationSoundExtractableSimOracle (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq
      (simulatorQROM R F C) (simExtractionErrorSimOracle R F C) := by
  rw [extractor_eq R F C]
  exact (F.e2e C R.strategy (verifierQueries_le R F C) (proofFormat R F C)).simExtractabilitySimOracle

/-- **The bound on the simulator's queries per proof query**: `2 pos + kq`, at least `simQueries`
(`simQueries_le`). -/
@[config_template]
abbrev simQueriesBound (_F : R.GrantedFacts) : ℕ :=
  2 * R.pos + R.kq

/-- **The simulator's queries per proof query are at most `simQueriesBound`**: two per position
(`card_pos`), one per round (`GrantedFacts.rounds_le`) and one per branch, the rounds and the
branches within `kq` (`GrantedFacts.kq_ge`). -/
@[config_template]
theorem simQueries_le (C : R.ProofSystem) : simQueries R F C ≤ simQueriesBound R F := by
  have h1 : Fintype.card (argument R F C).Pos = R.pos := card_pos R F C
  have h2 := F.rounds_le C
  have h3 := F.kq_ge C
  show 2 * Fintype.card (argument R F C).Pos + (R.iop C).shape.term.size (R.iop C).rounds +
    ∑ d, (R.iop C).shape.nb d ≤ 2 * R.pos + R.kq
  rw [SPTerm.size_eq_sum]
  omega

/-- **The simulation-extraction error in the QROM at the configuration's figures**: the spBCS
knowledge error `2 √(kq'/2^(8k)) + 6 T² (errorMax/2^errorExp + D T/2^(8k))` at `kq' = kq + Q q̄`
appended queries and `T = tq + Q q̄ + kq'` queries in all, with `q̄ = simQueriesBound`. It bounds
`simExtractionErrorQROM` (paper `thm:e2e`(5), `errse(t, Q)`) at the configuration's figures
(`simExtractionErrorQROM_le_atFigures`). -/
@[config_template]
noncomputable abbrev simExtractionErrorQROMAtFigures (_F : R.GrantedFacts) (tq Q : ℕ) : ℝ≥0∞ :=
  2 * esqrt (((R.kq + Q * simQueriesBound R _F : ℕ) : ℝ≥0∞) / 2 ^ (8 * R.k)) +
    6 * ((tq + Q * simQueriesBound R _F + (R.kq + Q * simQueriesBound R _F) : ℕ) : ℝ≥0∞) ^ 2 *
      ((((R.errorMax : ℝ≥0) / 2 ^ R.errorExp : ℝ≥0) : ℝ≥0∞) +
        ((R.D * (tq + Q * simQueriesBound R _F + (R.kq + Q * simQueriesBound R _F)) : ℕ) :
          ℝ≥0∞) / 2 ^ (8 * R.k))

/-- **The simulation-extraction error in the ROM at the configuration's figures**: the classical
knowledge error `knowledgeErrorROM` at `tq + Q q̄ + kq` queries, with `q̄ = simQueriesBound`. It
bounds `simExtractionErrorROM` (paper `thm:e2e`(5), `errse^C(t, Q)`) at the configuration's
figures (`simExtractionErrorROM_le_atFigures`). -/
@[config_template]
noncomputable abbrev simExtractionErrorROMAtFigures (_F : R.GrantedFacts) (tq Q : ℕ) : ℝ≥0∞ :=
  knowledgeErrorROM R _F (tq + Q * simQueriesBound R _F + R.kq)

/-- **The simulation-extraction error in the QROM is at most its value at the figures**:
`simQueries_le` bounds the simulator's queries, `GrantedFacts.error_le` the round error,
`GrantedFacts.digests_le` the digests and `Out.two_pow_le_card` the output space. -/
@[config_template]
theorem simExtractionErrorQROM_le_atFigures (C : R.ProofSystem) (tq Q : ℕ) :
    simExtractionErrorQROM R F C tq Q ≤ simExtractionErrorQROMAtFigures R F tq Q := by
  have hq := simQueries_le R F C
  have hkq : R.kq + Q * simQueries R F C ≤ R.kq + Q * simQueriesBound R F := by gcongr
  have hT : tq + Q * simQueries R F C + (R.kq + Q * simQueries R F C) ≤
      tq + Q * simQueriesBound R F + (R.kq + Q * simQueriesBound R F) := by gcongr
  have hD := F.digests_le C
  have hκ := F.error_le C
  have hcard := Out.two_pow_le_card (R.T C).k (fsExtraBytes + (R.T C).maxGrant)
  unfold simExtractionErrorQROM simExtractionErrorQROMAtFigures SPBCS.simExtractionError
    knowledgeError
  rw [← F.k_eq C]
  refine add_le_add ?_ (mul_le_mul' ?_ (add_le_add (by exact_mod_cast hκ) ?_))
  · have hc : ((2 ^ (8 * (R.T C).k) : ℕ) : ℝ≥0∞) ≤
        (Fintype.card (Out (R.T C).k (fsExtraBytes + (R.T C).maxGrant)) : ℝ≥0∞) :=
      Nat.cast_le.mpr hcard
    push_cast at hc
    exact mul_le_mul' le_rfl (esqrt_le_esqrt (ENNReal.div_le_div (Nat.cast_le.mpr hkq) hc))
  · gcongr
  · exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul hD hT)) _

/-- **The simulation-extraction error in the ROM is at most its value at the figures**:
`simQueries_le` bounds the simulator's queries (`knowledgeErrorROM_mono`), and
`Configurations.knowledgeErrorROM_le` the round error and the digests. -/
@[config_template]
theorem simExtractionErrorROM_le_atFigures (C : R.ProofSystem) (tq Q : ℕ) :
    simExtractionErrorROM R F C tq Q ≤ simExtractionErrorROMAtFigures R F tq Q := by
  have hq := simQueries_le R F C
  have hT : tq + Q * simQueries R F C + R.kq ≤ tq + Q * simQueriesBound R F + R.kq := by gcongr
  refine ((Configurations.knowledgeErrorROM_le (k := (R.T C).k)
    (t := tq + Q * simQueries R F C + R.kq) (F.digests_le C) (F.error_le C)).trans_eq
    (by rw [F.k_eq C])).trans (knowledgeErrorROM_mono R F hT)

open Classical in
/-- **Weak online simulation extractability of the configuration's argument in the QROM at the
configuration's figures** (paper `thm:e2e`(5) in the QROM): `weak_online_simulation_extractability_qrom`
with the error `simExtractionErrorQROMAtFigures tq Q`, at least `simExtractionErrorQROM tq Q`
(`simExtractionErrorQROM_le_atFigures`). -/
@[config_template headline]
theorem weak_online_simulation_extractability_qrom_at_figures (C : R.ProofSystem) :
    (argument R F C).WeakOnlineSimulationExtractable (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq
      (simulatorQROM R F C) (simExtractionErrorQROMAtFigures R F) :=
  SPBCS.WeakOnlineSimulationExtractable.mono (hse := weak_online_simulation_extractability_qrom R F C)
    (hε := simExtractionErrorQROM_le_atFigures R F C)

/-- **Weak online simulation extractability of the configuration's argument in the classical
random-oracle model at the configuration's figures** (paper `thm:e2e`(5) in the ROM):
`weak_online_simulation_extractability_rom` with the error `simExtractionErrorROMAtFigures tq Q`,
at least `simExtractionErrorROM tq Q` (`simExtractionErrorROM_le_atFigures`); the extraction law
still reads `simQueries` simulator queries per proof query. -/
@[config_template headline]
theorem weak_online_simulation_extractability_rom_at_figures (C : R.ProofSystem) :
    (argument R F C).WeakOnlineSimulationExtractableROM (proofBound R F)
      (queries R F C) R.rel (extractor R F C) R.kq (simulator R F C).prog
      (simQueries R F C) (simExtractionErrorROMAtFigures R F) :=
  SPBCS.WeakOnlineSimulationExtractableROM.mono (hse := weak_online_simulation_extractability_rom R F C)
    (hε := simExtractionErrorROM_le_atFigures R F C)

/-! ## The fixed honest strategy -/

/-- **Zero knowledge of the configuration's argument on its honest inputs** (`everlasting_zero_knowledge_qrom`
at the fixed honest strategy, whose completeness error is `0`): everlasting zero
knowledge for many adaptively chosen proofs (the distinguisher receives the whole oracle after the
last proof query) against query-bounded adversaries of the compiled honest prover on the
valid honest inputs at their statements, at the configuration's compiled simulator, with error
`zkError 0`. -/
@[config_template headline]
theorem everlasting_zero_knowledge_honest_qrom (C : R.ProofSystem) {X' W' : Type}
    [Fintype X'] [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → R.Stmt)
    (fw : W' → R.HonestIn) :
    NARG.QROM.EverlastingZeroKnowledgeOn (Prod.map fx fw ⁻¹' R.hrel R.relH) queryEncoding
      ((prover R F C R.strategy).comap fx fw) (coinLaw R F C R.strategy) ((simulator R F C).comap fx)
      ((argument R F C).zkError 0) := by
  have h := everlasting_zero_knowledge_qrom R F C R.strategy fx fw
  rwa [F.exact] at h

/-- **Zero knowledge of the configuration's argument in the ROM on its honest inputs**
(`everlasting_zero_knowledge_rom` at the fixed honest strategy, whose completeness error is `0`):
everlasting zero knowledge for many adaptively chosen proofs (the distinguisher receives the whole
oracle after the last proof query) against query-bounded classical adversaries of the compiled
honest prover on the valid honest inputs at their statements, at the configuration's compiled
simulator, with error `zkErrorROM 0`. -/
@[config_template headline]
theorem everlasting_zero_knowledge_honest_rom (C : R.ProofSystem) :
    NARG.ROM.EverlastingZeroKnowledgeOn (R.hrel R.relH) (prover R F C R.strategy)
      (coinLaw R F C R.strategy) (simulator R F C) ((argument R F C).zkErrorROM 0) := by
  have h := everlasting_zero_knowledge_rom R F C R.strategy
  rwa [F.exact] at h


/-- **Completeness of the configuration's argument on its honest inputs** (`Common.completeness` at
the fixed honest strategy, whose completeness error is `0`): on a valid honest input `y` at its
statement, at every value of the honest prover's coins, Merkle salts and salt, over a uniform
oracle the spBCS verifier rejects the compiled honest proof with probability at most
`rounds/2^chernoff + C(rounds, 2)/2^(8k)`. -/
@[config_template headline]
theorem completeness_honest (C : R.ProofSystem)
    (r : HonestCoins R F C R.strategy) (y : R.HonestIn) :
    Pr[h ← Oracle R F C : Rejects R F C h (R.stmtOfHonest y)
        (honestProof R F C R.strategy h (R.stmtOfHonest y) y r)] ≤
      overrunBound R F + keyCollisionBound R F := by
  have h := completeness R F C R.strategy r (F.stmtOfHonest_mem y)
  rwa [completenessError, F.exact, ENNReal.coe_zero, zero_add] at h

end Common

namespace ZeroKnowledgeROM

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **The query-counted zero-knowledge error in the ROM at the configuration's figures**:
`Q t/2^(8 kS) + Q (Q - 1)/(2 · 2^(8 kS)) + Q · keyCollisionBound
+ Q (4 · pos · t + 4 (pos² Q + pos))/2^(16 k) + Q (rounds/2^chernoff + err H)`, a bound of the spBCS
error `SPBCS.zkErrorROMQuery (err H)` (`zero_knowledge_rom`). -/
@[config_template]
noncomputable abbrev zkErrorQueryROM {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (t Q : ℕ) : ℝ :=
  Q * t / 2 ^ (8 * R.kS) + Q * (Q - 1) / (2 * 2 ^ (8 * R.kS)) +
    Q * (keyCollisionBound R F).toReal +
    Q * ((4 * t * R.pos + 4 * (Q * R.pos ^ 2 + R.pos)) / 2 ^ (16 * R.k)) +
    Q * (R.rounds / 2 ^ R.chernoff + R.err H)

/-- **Query-counted zero knowledge of the configuration's argument in the classical random-oracle
model** (the `zeroKnowledgeROMQuery` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`):
adaptive multi-theorem statistical zero knowledge (Unruh 2017 Definition 6, p. 14, with classical
adversaries all of whose queries are counted, `NARG.ROM.ZeroKnowledge`) of the
compiled honest prover against the compiled simulator: every classical adversary with a budget of
`t` queries over all its steps, whose output does not read the final oracle, with `Q` proof
queries answered, has advantage at most
`Q t/2^(8 kS) + Q (Q - 1)/(2 · 2^(8 kS)) + Q · keyCollision rounds k
+ Q (4 · pos · t + 4 (pos² Q + pos))/2^(16 k) + Q (rounds/2^chernoff + err H)`, a bound of the
spBCS error `SPBCS.zkErrorROMQuery (err H)` at the configuration's figures: `card_pos` gives `pos`
positions, `SPBCS.keyCollision_mono` the key collisions of `rounds` rounds, and `overrun_le` the
overrun. -/
@[config_template]
theorem zero_knowledge_rom (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :
    NARG.ROM.ZeroKnowledgeOn (R.hrel relH) (prover R F C H)
        (coinLaw R F C H)
      (simulator R F C) (zkErrorQueryROM R F H) := by
  classical
  unfold NARG.ROM.ZeroKnowledgeOn
  refine GordieHowe.ROM.ZeroKnowledge.mono
    (F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeROMQuery fun t Q => ?_
  have hkc : (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (R.T C).k).toReal ≤
      (SPBCS.keyCollision R.rounds R.k).toReal := by
    rw [← F.k_eq C, SPTerm.size_eq_sum]
    exact ENNReal.toReal_mono (SPBCS.keyCollision_ne_top _ _)
      (SPBCS.keyCollision_mono (F.rounds_le C) _)
  have hov : (argument R F C).overrun.toReal ≤ R.rounds / 2 ^ R.chernoff := by
    have h := ENNReal.toReal_mono (ENNReal.div_lt_top (by simp) (by simp)).ne
      (overrun_le R F C)
    rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
  have hU : (Fintype.card (argument R F C).Pos : ℝ) = R.pos := by
    exact_mod_cast card_pos R F C
  have hN : (2 : ℝ) ^ (8 * (setting R F C).kN) = 2 ^ (16 * R.k) := by
    change (2 : ℝ) ^ (8 * (2 * (R.T C).k)) = _
    rw [F.k_eq C]
    congr 1
    ring
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  rw [zkErrorQueryROM, Common.keyCollisionBound, SPBCS.zkErrorROMQuery, hU, hN]
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl le_rfl)
    (mul_le_mul_of_nonneg_left hkc hQ)) le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add hov le_rfl) hQ)

end ZeroKnowledgeROM

namespace ZeroKnowledgeQROM

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **The query-counted zero-knowledge error in the QROM at the configuration's figures**:
`4 Q t/2^(4 kS) + Q (Q - 1)/2^(8 kS) + Q · keyCollisionBound + Q (4 t √pos/2^(8 k)
+ 3 (pos + pos² Q + pos²)/2^(16 k)) + Q (rounds/2^chernoff + err H)`, a bound of the spBCS error
`SPBCS.zkErrorQuery (err H)` (`zero_knowledge_qrom`). -/
@[config_template]
noncomputable abbrev zkErrorQueryQROM {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (t Q : ℕ) : ℝ :=
  4 * Q * t / 2 ^ (4 * R.kS) + Q * (Q - 1) / 2 ^ (8 * R.kS) +
    Q * (keyCollisionBound R F).toReal +
    Q * (4 * t * √R.pos / 2 ^ (8 * R.k) +
      3 * ((R.pos + Q * R.pos ^ 2 + R.pos ^ 2) / 2 ^ (16 * R.k))) +
    Q * (R.rounds / 2 ^ R.chernoff + R.err H)

/-- **Query-counted zero knowledge of the configuration's argument in the QROM** (the
`zeroKnowledgeQueryCounted` clause of `SPBCS.PrivacyGuarantees` at `GrantedFacts.e2e`): adaptive
multi-theorem statistical zero knowledge with every query counted (Unruh 2017 Definition 6, p. 14,
over the paper's `(t, Q)`-adversaries, `def:adversary`, `NARG.QROM.ZeroKnowledge`)
of the compiled honest prover against the compiled simulator, for all finite statement and witness
types: every adversary making at most `t` queries on every branch, over all its query slots and its
post phase, with `Q` proof queries answered, has advantage at most
`4 Q t/2^(4 kS) + Q (Q - 1)/2^(8 kS) + Q · keyCollision rounds k + Q (4 t √pos/2^(8 k)
+ 3 (pos + pos² Q + pos²)/2^(16 k)) + Q (rounds/2^chernoff + err H)`, a bound of the spBCS error
`SPBCS.zkErrorQuery (err H)` at the configuration's figures: `card_pos` gives `pos` positions,
`SPBCS.keyCollision_mono` the key collisions of `rounds` rounds, and `overrun_le` the overrun. -/
@[config_template]
theorem zero_knowledge_qrom (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) {X' W' : Type} [Fintype X']
    [DecidableEq X'] [Fintype W'] [DecidableEq W'] (fx : X' → R.Stmt) (fw : W' → Inp) :
    NARG.QROM.ZeroKnowledgeOn (Prod.map fx fw ⁻¹' R.hrel relH) queryEncoding
      ((prover R F C H).comap fx fw) (coinLaw R F C H) ((simulator R F C).comap fx)
      (zkErrorQueryQROM R F H) := by
  classical
  refine .of_zeroKnowledge (GordieHowe.QROM.ZeroKnowledge.mono
    ((F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).zeroKnowledge.zeroKnowledgeQueryCounted X' W' fx fw)
    fun t Q => ?_)
  have hkc : (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (R.T C).k).toReal ≤
      (SPBCS.keyCollision R.rounds R.k).toReal := by
    rw [← F.k_eq C, SPTerm.size_eq_sum]
    exact ENNReal.toReal_mono (SPBCS.keyCollision_ne_top _ _)
      (SPBCS.keyCollision_mono (F.rounds_le C) _)
  have hov : (argument R F C).overrun.toReal ≤ R.rounds / 2 ^ R.chernoff := by
    have h := ENNReal.toReal_mono (ENNReal.div_lt_top (by simp) (by simp)).ne
      (overrun_le R F C)
    rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
  have hU : (Fintype.card (argument R F C).Pos : ℝ) = R.pos := by
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
  rw [zkErrorQueryQROM, Common.keyCollisionBound, SPBCS.zkErrorQuery, hU, h4, h8]
  exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl le_rfl)
    (mul_le_mul_of_nonneg_left hkc hQ)) le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add hov le_rfl) hQ)

end ZeroKnowledgeQROM

namespace AdaptiveCompleteness

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **The claim of a proof**: the statement and the proof's bytes (`SPBCS.Claim`), the claim the
verifiers of the completeness games read. -/
@[config_template]
abbrev claimOf (C : R.ProofSystem) :
    R.Stmt → (argument R F C).BProof (Common.proofBound R F) → Claim R.Stmt (argument R F C).NIProof :=
  fun x π => SPBCS.Claim.mk x π.val

/-- **The adaptive completeness error in the ROM** (paper `errcpl^C(t)`, `thm:e2e`(1)): the
completeness error of `H` plus `t/2^(8 kS)` against `t`-query adversaries. -/
@[config_template]
noncomputable abbrev completenessErrorROM {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (t : ℕ) : ℝ≥0∞ :=
  completenessError R F H + t / 2 ^ (8 * R.kS)

/-- **The adaptive completeness error in the QROM** (paper `errcpl(t)`, `thm:e2e`(1)): the
completeness error of `H` plus `2 t/2^(4 kS)` against `t`-query adversaries. -/
@[config_template]
noncomputable abbrev completenessErrorQROM {Inp : Type} {relH : Set (Valuation R F × Inp)}
    (H : HonestStrategy R F relH) (t : ℕ) : ℝ≥0∞ :=
  completenessError R F H + 2 * t / 2 ^ (4 * R.kS)

/-- **Completeness of the configuration's argument in the ROM** (paper `thm:e2e`(1) in the ROM;
`def:narg-complete`, `NARG.ROM.Complete`; Unruh 2017 Definition 5, p. 14;
`ProofSystemTranscript.Guarantees.completeROM` at `GrantedFacts.e2e`): at every honest strategy
`H`, the honest prover `prover`, with uniform coins, Merkle salts and salt, is complete for the
spBCS verifier `verifierROM`: every classical `t`-query adversary that outputs a statement and an
honest input after its queries makes the honest proof of a valid pair rejected with probability at
most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + t/2^(8 kS)`. -/
@[config_template headline]
theorem completeness_adaptive_rom (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :
    NARG.ROM.Complete (prover R F C H) (coinLaw R F C H) (verifierROM R F C) (claimOf R F C)
      (R.hrel relH) (completenessErrorROM R F H) :=
  fun t 𝒜 => ((F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).completeROM t 𝒜).trans <| by
    show _ ≤ (R.err H : ℝ≥0∞) + (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k +
      t / 2 ^ (8 * R.kS)
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
probability at most `err H + rounds/2^chernoff + C(rounds, 2)/2^(8k) + 2 t/2^(4 kS)`. -/
@[config_template headline]
theorem completeness_adaptive_qrom (C : R.ProofSystem) {Inp : Type}
    {relH : Set (Valuation R F × Inp)} (H : HonestStrategy R F relH) :
    NARG.QROM.Complete queryEncoding (prover R F C H) (coinLaw R F C H) (verifierQROM R F C)
      (claimOf R F C) (R.hrel relH) (completenessErrorQROM R F H) :=
  fun t 𝒜 => ((F.e2e C H (verifierQueries_le R F C) (proofFormat R F C)).completeQROM t 𝒜).trans <| by
    show _ ≤ (R.err H : ℝ≥0∞) + (R.rounds : ℝ≥0∞) / 2 ^ R.chernoff + SPBCS.keyCollision R.rounds R.k +
      2 * t / 2 ^ (4 * R.kS)
    rw [← F.k_eq C]
    exact add_le_add (add_le_add (add_le_add le_rfl (overrun_le R F C))
      (SPBCS.keyCollision_mono (F.rounds_le C) _)) le_rfl

/-- **Completeness of the configuration's argument in the ROM on its honest inputs**
(`completeness_adaptive_rom` at the fixed honest strategy, whose completeness error is `0`): the
honest prover is complete for the spBCS verifier at error
`rounds/2^chernoff + C(rounds, 2)/2^(8k) + t/2^(8 kS)` against classical `t`-query adversaries. -/
@[config_template]
theorem completeness_adaptive_honest_rom (C : R.ProofSystem) :
    NARG.ROM.Complete (prover R F C R.strategy) (coinLaw R F C R.strategy) (verifierROM R F C)
      (claimOf R F C) (R.hrel R.relH) fun t =>
        overrunBound R F + keyCollisionBound R F + t / 2 ^ (8 * R.kS) :=
  fun t 𝒜 => (completeness_adaptive_rom R F C R.strategy t 𝒜).trans_eq <| by
    rw [completenessErrorROM, Common.completenessError, F.exact, ENNReal.coe_zero, zero_add]

/-- **Completeness of the configuration's argument in the QROM on its honest inputs**
(`completeness_adaptive_qrom` at the fixed honest strategy, whose completeness error is `0`): the
honest prover is complete for the spBCS verifier at error
`rounds/2^chernoff + C(rounds, 2)/2^(8k) + 2 t/2^(4 kS)` against `t`-query adversaries of
`def:adversary`. -/
@[config_template]
theorem completeness_adaptive_honest_qrom (C : R.ProofSystem) :
    NARG.QROM.Complete queryEncoding (prover R F C R.strategy) (coinLaw R F C R.strategy)
        (verifierQROM R F C)
      (claimOf R F C) (R.hrel R.relH) fun t =>
        overrunBound R F + keyCollisionBound R F + 2 * t / 2 ^ (4 * R.kS) :=
  fun t 𝒜 => (completeness_adaptive_qrom R F C R.strategy t 𝒜).trans_eq <| by
    rw [completenessErrorQROM, Common.completenessError, F.exact, ENNReal.coe_zero, zero_add]

end AdaptiveCompleteness

/-- **The honest inputs of a relation's pairs**: a relation `rel` within the configuration's
relation `R.rel` and, for each of its pairs, an honest input of the fixed strategy at the pair's statement.
It carries the paper's relation (or its restriction to the pairs the honest prover supports, named
at the configuration) to the honest inputs the completeness, zero-knowledge and
witness-indistinguishability statements quantify over. -/
structure HonestOf (R : Configuration) where
  /-- The relation. -/
  rel : Set (R.Stmt × R.Wit)
  /-- It lies within the configuration's relation. -/
  rel_subset : rel ⊆ R.rel
  /-- The honest input of a pair. -/
  honestOf : (x : R.Stmt) → (w : R.Wit) → (x, w) ∈ rel → R.HonestIn
  /-- The honest input of a pair is at the pair's statement. -/
  stmtOfHonest_honestOf : ∀ x w (hp : (x, w) ∈ rel), R.stmtOfHonest (honestOf x w hp) = x

namespace PaperRelation

open Common

variable (R : Configuration) (F : R.GrantedFacts) (B : R.HonestOf)
include F

/-- **Every pair of the relation has an honest input at its statement**: the honest input
`B.honestOf x w hp` of a pair `(x, w)` of `B.rel` is in the honest relation at `x`, so the
completeness, zero-knowledge and witness-indistinguishability statements of the configuration on
its honest inputs hold on the honest inputs of the relation's pairs, the honest prover run on
`B.honestOf x w hp`. -/
@[config_template headline]
theorem honest_input_of_rel {x : R.Stmt} {w : R.Wit} (hp : (x, w) ∈ B.rel) :
    (x, B.honestOf x w hp) ∈ R.hrel R.relH := by
  have h := F.stmtOfHonest_mem (B.honestOf x w hp)
  rwa [B.stmtOfHonest_honestOf x w hp] at h

/-- **Completeness of the configuration's argument on the relation's pairs**
(`Common.completeness_honest` at the honest input `B.honestOf x w hp` of a pair `(x, w)` of `B.rel`,
at the statement `x`): at every value of the honest prover's coins, Merkle salts and salt, over a
uniform oracle the spBCS verifier rejects the compiled honest proof of `p`'s statement with
probability at most `rounds/2^chernoff + C(rounds, 2)/2^(8k)`. -/
@[config_template headline]
theorem completeness_of_rel (C : R.ProofSystem)
    (r : HonestCoins R F C R.strategy) {x : R.Stmt} {w : R.Wit} (hp : (x, w) ∈ B.rel) :
    Pr[h ← Oracle R F C : Rejects R F C h x (honestProof R F C R.strategy h x (B.honestOf x w hp) r)] ≤
      overrunBound R F + keyCollisionBound R F := by
  have h := completeness_honest R F C r (B.honestOf x w hp)
  rwa [B.stmtOfHonest_honestOf x w hp] at h

end PaperRelation

end GordieHowe.Configuration
