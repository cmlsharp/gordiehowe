-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.SPBCS.Extraction.KnowledgeError
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.ProofSystem.Program.Basic
public import GordieHowe.ProofSystem.Program.Transcript.Format
public import GordieHowe.ProofSystem.Program.ForkJoinFormat

@[expose] public section

/-!
# The transcript data of a configuration with forked domains

The data and facts a compiled argument of a configuration with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP`) is
built from, read by its setting with merges (`GordieHowe/ProofSystem/Program/Transcript/MergeSetting.lean`).

- `SPBCS.ProofSystemTranscript C`: the label, the digest length, the statement writes, the branch names of
  the proof system's labels, the codecs of the domains' commit rounds, of the application phase's
  messages, of every branch's and of every join part's messages, the leaf codecs and the challenge
  readers of the same parts; `GordieHowe.SPBCS.ProofSystemTranscript.Bounds`: the facts the settings are built from.
- The readers of every component (`readers`), the C++ stream length of every round (`stream`) and
  the largest grant (`maxGrant`).
- Length budgets: the writes before round 0 (`length_saltedCodec_le`), the
  roots of one write (`roots_le`), the rounds' writes (`rounds_mul_le`); the challenge count
  (`card_chIdx_le`); the digests of one chain input (`digests`).
- `knowledgeError_le`, `knowledgeErrorROM_le`: bounds on the knowledge errors of the compiled
  argument.
-/

namespace GordieHowe.SPBCS

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS GordieHowe.QROM
open scoped NNReal ENNReal

/-- **The largest round count of a configuration**: the commitment round, the four commit rounds
of the two circuits (the low-degree challenge and response of each tableau), the MAC phase's
three rounds and at most `20787` rounds of the two circuit proofs. -/
def Configurations.maxRounds : ℕ := 20795

variable {Stmt W : Type} {rel : Set (Stmt × W)}

variable (C : RealizedProgram.ProofSystem.IOP Stmt W rel) in
/-- **The transcript of a configuration with forked domains**, at its multi-circuit IOP with forked
domains `C`: the label, the digest length `k`, the statement writes, the branch names of the
proof system's labels, the codecs of every domain's commit rounds, of the application phase's messages,
of every branch's and of every join part's messages (each write at most `2^20` bytes), the leaf
codec of every domain's tree and the challenge readers of the same parts. -/
structure ProofSystemTranscript where
  /-- The label write. -/
  label : List Byte
  /-- The digest length in bytes. -/
  k : ℕ
  /-- The codec of the statement writes. -/
  stmt : Codec Stmt
  /-- The name of every branch in its label. -/
  name : (Σ d : Fin C.m, Fin (C.circuit d).nb) → List Byte
  /-- The codecs of every domain's commit rounds. -/
  commitWrites : ∀ d, SpecWrites (C.circuit d).commitRounds (2 ^ 20)
  /-- The codecs of the application phase's messages. -/
  appWrites : SpecWrites C.app.spec (2 ^ 20)
  /-- The codecs of every branch's messages. -/
  branchWrites : ∀ d b, SpecWrites ((C.circuit d).branch b) (2 ^ 20)
  /-- The codecs of every join part's messages. -/
  joinWrites : ∀ d, SpecWrites (C.circuit d).join (2 ^ 20)
  /-- The leaf codec of every domain's tree. -/
  leaf : ∀ d, Codec (C.oracle d).Leaf
  /-- The challenge readers of every domain's commit rounds. -/
  commitReaders : ∀ d, SpecReaders (C.circuit d).commitRounds
  /-- The challenge readers of the application phase. -/
  appReaders : SpecReaders C.app.spec
  /-- The challenge readers of every branch. -/
  branchReaders : ∀ d b, SpecReaders ((C.circuit d).branch b)
  /-- The challenge readers of every join part. -/
  joinReaders : ∀ d, SpecReaders (C.circuit d).join

/-- **A bound on the series–parallel knowledge error**: at most `2^16` verifier queries, the digests
of one input and the seeding's within `D` (`max 2 c + cP + 1 ≤ D`) and every round error within
`δ`. -/
theorem Configurations.knowledgeError_le {k e kq t c cP D : ℕ} {κ δ : ℝ≥0} (hkq : kq ≤ 2 ^ 16)
    (hD : max 2 c + cP + 1 ≤ D) (hκ : κ ≤ δ) :
    knowledgeError k e kq t c cP κ ≤
      2 ^ 9 / 2 ^ (4 * k) + 6 * (t : ℝ≥0∞) ^ 2 * ((δ : ℝ≥0∞) + ((D * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) := by
  unfold knowledgeError
  refine add_le_add ?_ ?_
  · have hcard := Out.two_pow_le_card k e
    have hsq : (kq : ℝ≥0∞) / Fintype.card (Out k e) ≤ (2 ^ 8 / 2 ^ (4 * k)) ^ 2 := by
      calc (kq : ℝ≥0∞) / Fintype.card (Out k e)
          ≤ 2 ^ 16 / 2 ^ (8 * k) :=
            ENNReal.div_le_div (by exact_mod_cast hkq) (by exact_mod_cast hcard)
        _ = (2 ^ 8 / 2 ^ (4 * k)) ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← pow_mul, ← pow_mul]
            congr 3
            ring
    calc 2 * esqrt ((kq : ℝ≥0∞) / Fintype.card (Out k e))
        ≤ 2 * (2 ^ 8 / 2 ^ (4 * k)) := by
          gcongr
          exact esqrt_le_of_le_sq hsq
      _ = 2 ^ 9 / 2 ^ (4 * k) := by
          rw [← mul_div_assoc, ← pow_succ']
  · refine mul_le_mul' le_rfl (add_le_add (by exact_mod_cast hκ) ?_)
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ hD)) _

/-- **A bound on the classical series–parallel knowledge error**, as `knowledgeError_le`. -/
theorem Configurations.knowledgeErrorROM_le {k t c cP D : ℕ} {κ δ : ℝ≥0} (hD : max 2 c + cP + 1 ≤ D)
    (hκ : κ ≤ δ) :
    knowledgeErrorROM k t c cP κ ≤ (t : ℝ≥0∞) * ((δ : ℝ≥0∞) + ((D * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) := by
  unfold knowledgeErrorROM
  refine mul_le_mul' le_rfl (add_le_add (by exact_mod_cast hκ) ?_)
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ hD)) _

namespace ProofSystemTranscript

variable {C : RealizedProgram.ProofSystem.IOP Stmt W rel}

/-- **The facts the settings are built from**: statement writes of at most `2^20` bytes, a
label, a digest and branch names of at most `2^10` bytes, leaves of at most `2^40` bytes, at most
`2^8` domains of at most `2^8` branches each, and at most `maxRounds` rounds in all. -/
structure Bounds (T : ProofSystemTranscript C) : Prop where
  /-- The statement writes have at most `2^20` bytes. -/
  pre_le : ∀ x, (T.stmt.ser x).length ≤ 2 ^ 20
  /-- The label has at most `2^10` bytes. -/
  label_le : T.label.length ≤ 2 ^ 10
  /-- The digest has at most `2^10` bytes. -/
  k_le : T.k ≤ 2 ^ 10
  /-- The digest has at least one byte. -/
  k_pos : 0 < T.k
  /-- A serialized leaf has at most `2^40` bytes. -/
  leaf_le : ∀ d c, ((T.leaf d).ser c).length ≤ 2 ^ 40
  /-- There are at most `2^8` domains. -/
  m_le : C.m ≤ 2 ^ 8
  /-- Every domain has at most `2^8` branches. -/
  nb_le : ∀ d, (C.circuit d).nb ≤ 2 ^ 8
  /-- Every branch name has at most `2^10` bytes. -/
  name_le : ∀ a, (T.name a).length ≤ 2 ^ 10
  /-- There are at most `maxRounds` rounds in all. -/
  n_le : ∑ q : C.shape.term.Leaf, C.rounds q.label ≤ Configurations.maxRounds

variable (T : ProofSystemTranscript C)

/-- **The challenge readers of every component** (`RealizedProgram.ProofSystem.IOP.readersOf`). -/
abbrev readers : ∀ j, SpecReaders (C.P j) :=
  C.readersOf T.commitReaders T.appReaders T.branchReaders T.joinReaders

/-- **The C++ stream length of round `i` of component `j`**: the default budget
`k + fsExtraBytes` and the round's grant. -/
abbrev stream (j : C.shape.Idx) (i : (C.P j).ChallengeIdx) : ℕ :=
  (T.readers j).streamLength (T.k + Configurations.fsExtraBytes) i

/-- **The largest grant of a round** of any component. -/
def maxGrant : ℕ := Finset.univ.sup fun q : C.term.Leaf => (T.readers q.label).maxGrant

/-- Every component's largest grant is at most `maxGrant`. -/
theorem maxGrant_le (j : C.shape.Idx) : (T.readers j).maxGrant ≤ T.maxGrant := by
  have h := Finset.le_sup (f := fun q : C.term.Leaf => (T.readers q.label).maxGrant)
    (Finset.mem_univ (RealizedProgram.ProofSystem.IOP.Shape.leafOf (S := C.shape) j))
  rwa [RealizedProgram.ProofSystem.IOP.Shape.label_leafOf] at h

/-- **Every round's stream fits in `k + fsExtraBytes + maxGrant` bytes.** -/
theorem stream_le (j : C.shape.Idx) (i : (C.P j).ChallengeIdx) :
    T.stream j i ≤ T.k + (Configurations.fsExtraBytes + T.maxGrant) :=
  ((T.readers j).streamLength_le_maxGrant _ i).trans (by have := T.maxGrant_le j; omega)

variable {T}

/-- The roots of the domains' trees fit in one write. -/
theorem roots_le (hb : T.Bounds) : C.m * (9 + T.k) ≤ 2 ^ 20 := by
  have := hb.k_le
  have := Nat.mul_le_mul hb.m_le (show 9 + T.k ≤ 9 + 2 ^ 10 by omega)
  omega

/-- **The length budget of the writes before the first round at `kS`-byte salts**: the label, the
salt write and the statement writes have at most `2^10 + (9 + kS) + 2^20` bytes. -/
theorem length_saltedCodec_le (hb : T.Bounds) {kS : ℕ} (x : SaltedStatement kS Stmt) :
    ((TranscriptEncoding.saltedCodec (kS := kS) T.label T.stmt).ser x).length ≤
      2 ^ 10 + (9 + kS) + 2 ^ 20 := by
  have h1 := hb.label_le
  have h2 := TranscriptEncoding.saltLen_le kS
  have h3 := hb.pre_le x.stmt
  change (T.label ++ TranscriptEncoding.saltBytes x.salt ++ T.stmt.ser x.stmt).length ≤ _
  simp only [List.length_append, TranscriptEncoding.length_saltBytes]
  omega

/-- The rounds' writes fit in `maxRounds · 2^20` bytes. -/
theorem rounds_mul_le (hb : T.Bounds) :
    (∑ q : C.shape.term.Leaf, C.rounds q.label) * max (2 ^ 20) (9 + T.k) ≤ Configurations.maxRounds * 2 ^ 20 := by
  have := hb.k_le
  rw [max_eq_left (by omega)]
  exact Nat.mul_le_mul_right _ hb.n_le
/-- **The composite has at most its rounds' count of challenges.** -/
theorem card_chIdx_le : Fintype.card (ChIdx C.P C.term) ≤ ∑ q : C.shape.term.Leaf, C.rounds q.label := by
  rw [Fintype.card_congr ChIdx.equivSigma, Fintype.card_sigma]
  exact Finset.sum_le_sum fun q _ => (Fintype.card_subtype_le _).trans (by simp)

/-- **The digests of one chain input** of the setting. -/
abbrev digests : ℕ := (∑ q : C.shape.term.Leaf, C.rounds q.label) * C.m

end ProofSystemTranscript

end GordieHowe.SPBCS
