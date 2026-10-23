-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Circuits.HashBatched
public import GordieHowe.Applications.Keccak.Gadgets.WordAbsorb
public import GordieHowe.Applications.Keccak.HashCircuit.Relation

@[expose] public section

/-!
# ML-DSA: the hash constraints of domain H

Used by both ML-DSA configurations: ML-DSA emulated uses ML-DSA native's domain H, MAC field
profile, layout and phases.

The hash constraints of ML-DSA native's domain H (`lib/gordiehowe/examples/mldsa/mldsa_hash.h`,
`hash_to_challenge` and `challenge_from_mu`; `lib/gordiehowe/lib/keccak.h`, `shake256`): three
SHAKE256 calls on one batch of Keccak-f permutations (`h2c.keccak`), at an empty context:

* `μ = SHAKE256(tr ‖ 0x00 ‖ |ctx| ‖ msg, 64)` (`h2c.mu`, one permutation at `msgLen = 32`), the
  constant bytes folded into the absorb circuit's constants;
* `c̃' = SHAKE256(μ ‖ w1Encode(w1), 32)` (`h2c.c_tilde`, seven permutations), reading `μ`'s output
  bits and H's copy `w1` of the UseHint output bits;
* `SHAKE256(c̃', 272)` (`h2c.sib`, `kSibBytes = 272`, two permutations: the absorb and one
  squeeze): its bytes `0 … 7` hold the signs, bytes `8 … 271` the rejection-sampling stream (FIPS
  204 Appendix C requires a bounded SampleInBall to squeeze at least `221` bytes).

* **The batch** (`ghShape`): `nPerms msgLen = nMu + 7 + 2` permutations (`10` at `msgLen = 32`),
  all hooked but the stream's squeeze, which reads the previous output (`KeccakBatch.Shape.pre`);
  the calls `muCall`, `commitCall`, `sibCall` at consecutive permutations, C++ calls
  `(600, 4200, 1200)` round instances.
* **The trace** (`Words`, nodes `h2c.mu.states`, `h2c.c_tilde.states`, `h2c.sib.states`): `100`
  words of `GF(2^16)` per state, `24 nPerms + 1 + (nPerms − 2)` states, indexed in the order of the
  skip link (`HashCircuit.Word`: the start of permutation `0`, the output of every round, the starts
  of the later hooked permutations).
* **The absorb circuits** (`Absorb`): the word-level absorb (`KeccakSponge.WordAbsorb`) of each call
  on its input bytes (`GordieHowe.MLDSA44.HashCircuit.muInput`, `GordieHowe.MLDSA44.HashCircuit.commitInput`, `c̃'`'s output bytes).
* **The Keccak batch** (`KeccakRelation`): the skip relation on the Keccak operand map of the trace
  words' bits, `2^keccakLogs` groups of width `16` (`15` rounds at `msgLen = 32`).
* **The outputs** (`muOut`, `cTildeOut`, `sibOut`; nodes `h2c.mu.out`, `h2c.c_tilde.out`,
  `h2c.sib.out`): the bytes squeezed from the output words of each call's permutations (the bit
  views of the trace).

`HashConstraints` collects these with the bases the soundness reads (the trace words in the
subfield, the message and `w1` bits Boolean). Soundness: each output is SHAKE256 of its input
(`HashConstraints.mu_eq`, `cTilde_eq`, `sib_eq`; `KeccakSponge.wordAbsorb_sound`).
-/

namespace GordieHowe.MLDSA44.Native

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch GordieHowe.KeccakSponge GordieHowe.PackedClaim
  GordieHowe.HashCircuit
open HashBatchedCircuit (muLen nMu nCommit)
open Falcon512.HashCircuit (byteWires byteWires_allBool)

/-! ### The batch -/

/-- The bytes of the SampleInBall stream, `272` (`examples/mldsa/mldsa_hash.h`, `kSibBytes`). -/
abbrev sibLen : ℕ := 272

/-- The permutations of the stream's sponge, `2`: the absorb of `c̃'` and one squeeze. -/
abbrev nSib : ℕ := Shake256.numBlocks .shake256 32 sibLen

theorem nSib_eq : nSib = 2 := rfl

/-- **The permutations of the batch**: `μ`'s, then `c̃'`'s, then the stream's. Irreducible: the
elaborator otherwise evaluates the trace word type's size. -/
@[irreducible] def nPerms (msgLen : ℕ) : ℕ := nMu 0 msgLen + nCommit + nSib

theorem nPerms_def (msgLen : ℕ) : nPerms msgLen = nMu 0 msgLen + nCommit + nSib := by
  unfold nPerms
  rfl

/-- **The permutation count**: `(202 + msgLen) / 136 + 9`. -/
theorem nPerms_eq (msgLen : ℕ) : nPerms msgLen = (202 + msgLen) / 136 + 9 := by
  rw [nPerms_def, HashBatchedCircuit.nMu_eq, nSib_eq, HashBatchedCircuit.nCommit_eq, Nat.add_zero]

variable {msgLen : ℕ}

variable (msgLen) in
/-- The trace states: `24 nPerms + 1 + (nPerms − 2)`. -/
abbrev nStates : ℕ := 24 * nPerms msgLen + 1 + (nPerms msgLen - 2)

variable (msgLen) in
/-- **A word of the Keccak trace**, in the skip link's order. -/
abbrev TraceWord : Type := HashCircuit.Word (nPerms msgLen) (nPerms msgLen - 2)

variable (msgLen) in
/-- **The batch shape** (`examples/mldsa/mldsa_hash.h`, the three `shake256` calls on one batch): the
first `nPerms − 1` permutations are hooked (every absorb), the last (the stream's squeeze) reads
the previous output. -/
def ghShape : Shape (nPerms msgLen) (nPerms msgLen - 2) :=
  Shape.pre _ _ (by rw [nPerms_eq]; omega)

theorem ghShape_hooked_iff {p : Fin (nPerms msgLen)} :
    (ghShape msgLen).Hooked p ↔ (p : ℕ) ≤ nPerms msgLen - 2 :=
  Shape.pre_hooked_iff

/-- **A call of the batch** whose absorb permutations are hooked (before the last permutation)
and whose squeezes, if any, are the last permutation. -/
def ghCall {len outLen : ℕ} (first : ℕ)
    (fits : first + Shake256.numBlocks .shake256 len outLen ≤ nPerms msgLen)
    (habs : first + Shake256.absorbBlocks .shake256 len ≤ nPerms msgLen - 1)
    (hsq : Shake256.squeezeBlocks .shake256 outLen = 0 ∨
      first + Shake256.absorbBlocks .shake256 len = nPerms msgLen - 1) :
    Call .shake256 (ghShape msgLen) len outLen :=
  have hpos := Shake256.absorbBlocks_pos .shake256 len
  have e : Shake256.numBlocks .shake256 len outLen =
      Shake256.absorbBlocks .shake256 len + Shake256.squeezeBlocks .shake256 outLen := rfl
  ⟨first, fits, fun k hk => ghShape_hooked_iff.mpr (by simp only; omega),
    fun k hk h => by
      rw [ghShape_hooked_iff]
      simp only
      omega⟩

theorem nMu_absorb : Shake256.absorbBlocks .shake256 (muLen 0 msgLen) = nMu 0 msgLen := rfl

theorem nPerms_eq_add : nPerms msgLen = nMu 0 msgLen + 7 + 2 := nPerms_def msgLen

/-- The `μ` call, from permutation `0`. -/
def muCall : Call .shake256 (ghShape msgLen) (muLen 0 msgLen) 64 :=
  ghCall 0 (by rw [nPerms_eq_add]; show 0 + nMu 0 msgLen ≤ _; omega)
    (by rw [nPerms_eq_add, nMu_absorb]; omega) (Or.inl rfl)

/-- The `c̃'` call, after `μ`. -/
def commitCall : Call .shake256 (ghShape msgLen) (64 + 768) 32 :=
  ghCall (nMu 0 msgLen) (by rw [nPerms_eq_add]; show nMu 0 msgLen + 7 ≤ _; omega)
    (by rw [nPerms_eq_add]; show nMu 0 msgLen + 7 ≤ _; omega) (Or.inl rfl)

/-- The stream's call, after `c̃'`: its absorb is the last hooked permutation, its squeeze the last
permutation. -/
def sibCall : Call .shake256 (ghShape msgLen) 32 sibLen :=
  ghCall (nMu 0 msgLen + nCommit) (by rw [nPerms_eq_add]; show nMu 0 msgLen + 7 + 2 ≤ _; omega)
    (by rw [nPerms_eq_add]; show nMu 0 msgLen + 7 + 1 ≤ _; omega)
    (Or.inr (by rw [nPerms_eq_add]; show nMu 0 msgLen + 7 + 1 = _; omega))

theorem muCall_perm (k : Fin (nMu 0 msgLen)) : ((muCall (msgLen := msgLen)).perm k : ℕ) = k := by
  simp [Call.perm, muCall, ghCall]

theorem commitCall_perm (k : Fin nCommit) :
    ((commitCall (msgLen := msgLen)).perm k : ℕ) = nMu 0 msgLen + k := rfl

theorem sibCall_perm (k : Fin nSib) :
    ((sibCall (msgLen := msgLen)).perm k : ℕ) = nMu 0 msgLen + nCommit + k := rfl

/-! ### The trace and the outputs -/

variable {KH : Type} [Field KH]

/-- **The words of the Keccak trace** (`h2c.*.states`), in the skip link's order. -/
abbrev Words (KH : Type) (msgLen : ℕ) : Type := TraceWord msgLen → KH

/-- The start words of permutation `p` (its hook, or the previous output for the squeeze). -/
def hookWords (states : Words KH msgLen) (p : Fin (nPerms msgLen)) : Fin 5 → Fin 5 → Fin 4 → KH :=
  KeccakOperands.stateWords states (startState (ghShape msgLen) p)

/-- The output words of permutation `p`. -/
def outWords (states : Words KH msgLen) (p : Fin (nPerms msgLen)) : Fin 5 → Fin 5 → Fin 4 → KH :=
  KeccakOperands.stateWords states (endState p)

/-- **`μ`'s output bytes** (`h2c.mu.out`). -/
def muOut (B : PackedBasis KH 4) (states : Words KH msgLen) : Fin 64 → BitWires KH 8 :=
  squeezeOut (sp := .shake256) (len := muLen 0 msgLen)
    (fun k => endOf (statesOf B states) ((muCall (msgLen := msgLen)).perm k))

/-- **`c̃'`'s output bytes** (`h2c.c_tilde.out`). -/
def cTildeOut (B : PackedBasis KH 4) (states : Words KH msgLen) : Fin 32 → BitWires KH 8 :=
  squeezeOut (sp := .shake256) (len := 64 + 768)
    (fun k => endOf (statesOf B states) ((commitCall (msgLen := msgLen)).perm k))

/-- **The SampleInBall stream's output bytes** (`h2c.sib.out`): block `0` from the absorb
permutation's output, block `1` from the squeeze's. -/
def sibOut (B : PackedBasis KH 4) (states : Words KH msgLen) : Fin sibLen → BitWires KH 8 :=
  squeezeOut (sp := .shake256) (len := 32)
    (fun k => endOf (statesOf B states) ((sibCall (msgLen := msgLen)).perm k))

variable (msgLen) in
/-- **The number of sumcheck rounds of the Keccak batch**: `⌈log₂ (2400 nPerms)⌉` (`15` at
`msgLen = 32`). Irreducible: it indexes coordinate types. -/
@[irreducible] def keccakLogs : ℕ := Nat.clog 2 (2400 * nPerms msgLen)

theorem keccakGroups_le : 24 * nPerms msgLen * 100 ≤ 2 ^ keccakLogs msgLen := by
  rw [show 24 * nPerms msgLen * 100 = 2400 * nPerms msgLen by ring]
  unfold keccakLogs
  exact Nat.le_pow_clog (by norm_num) _

/-- **The Keccak batch relation** (`h2c.keccak`): `Q(a, b, c) = a b + c` vanishes on the operand
arrays of the trace words' bits. -/
def KeccakRelation (B : PackedBasis KH 4) (states : Words KH msgLen) : Prop :=
  (Packed.Opening.toOperands (KeccakOperands.keccakOperands (K := KH) (n := keccakLogs msgLen)
    (stateMap (ghShape msgLen)) (wordBits B states))).Holds

/-- **The empty context**, as bits. -/
def noCtx : BitWires KH (8 * 0) := fun i => Fin.elim0 i

/-- **The absorb circuits** of the three calls: `μ` on `tr ‖ 0x00 ‖ 0x00 ‖ msg`, `c̃'` on
`μ ‖ w1`, the stream on `c̃'`. -/
structure Absorb (B : PackedBasis KH 4) (tr : BitWires KH (8 * 64)) (msg : BitWires KH (8 * msgLen))
    (w1 : BitWires KH (8 * 768)) (states : Words KH msgLen) : Prop where
  /-- The `μ` call. -/
  mu : WordAbsorb B (muCall (msgLen := msgLen)) (hookWords states) (outWords states)
    (HashCircuit.muInput tr noCtx msg)
  /-- The `c̃'` call. -/
  cTilde : WordAbsorb B (commitCall (msgLen := msgLen)) (hookWords states)
    (outWords states) (HashCircuit.commitInput (muOut B states) w1)
  /-- The stream's call. -/
  sib : WordAbsorb B (sibCall (msgLen := msgLen)) (hookWords states) (outWords states)
    (cTildeOut B states)

/-- **The hash constraints of domain H**: the trace words lie in the subfield, the message and
`w1` bits are bits (the domain's bases: relative and bit packing), the absorb circuits and the
Keccak batch relation, with `tr` the bits of the statement's `tr = H(pk)`. -/
structure HashConstraints (B : PackedBasis KH 4) (tr : BitWires KH (8 * 64))
    (msg : BitWires KH (8 * msgLen)) (w1 : BitWires KH (8 * 768)) (states : Words KH msgLen) :
    Prop where
  /-- The trace words lie in the subfield. -/
  words : ∀ v, states v ∈ B.E
  /-- The message bits are bits. -/
  msgBool : AllBool msg
  /-- H's `w1` bits are bits. -/
  w1Bool : AllBool w1
  /-- The absorb circuits. -/
  absorb : Absorb B tr msg w1 states
  /-- The Keccak batch relation. -/
  keccak : KeccakRelation B states

section Sound

variable [DecidableEq KH] [CharP KH 2] {B : PackedBasis KH 4} {tr : BitWires KH (8 * 64)}
  {msg : BitWires KH (8 * msgLen)} {w1 : BitWires KH (8 * 768)} {states : Words KH msgLen}

/-- **The batch relation on the decoded trace**, from the Keccak batch relation on subfield words
(`KeccakOperands.holds_iff`, `KeccakBatch.holds_of_rounds`). -/
theorem HashConstraints.holds (h : HashConstraints B tr msg w1 states) :
    Holds (ghShape msgLen) (startOf (ghShape msgLen) (statesOf B states))
      (endOf (statesOf B states)) :=
  holds_of_rounds (fun t x y => statesOf_allBool B h.words t x y)
    ((KeccakOperands.holds_iff _ (keccakGroups_le (msgLen := msgLen)) (wordBits B states)).mp
      h.keccak)

omit [DecidableEq KH] in
theorem HashConstraints.start_allBool (h : HashConstraints B tr msg w1 states)
    (p : Fin (nPerms msgLen)) (x y : Fin 5) :
    AllBool (startOf (ghShape msgLen) (statesOf B states) p x y) :=
  statesOf_allBool B h.words _ x y

/-- **`μ`'s output bytes are Boolean.** -/
theorem HashConstraints.muOut_allBool (h : HashConstraints B tr msg w1 states) (o : Fin 64) :
    AllBool (muOut B states o) :=
  wordAbsorb_out_allBool (c := muCall (msgLen := msgLen)) h.holds h.start_allBool o

/-- **`c̃'`'s output bytes are Boolean.** -/
theorem HashConstraints.cTildeOut_allBool (h : HashConstraints B tr msg w1 states) (o : Fin 32) :
    AllBool (cTildeOut B states o) :=
  wordAbsorb_out_allBool (c := commitCall (msgLen := msgLen)) h.holds h.start_allBool o

/-- **The stream's output bytes are Boolean.** -/
theorem HashConstraints.sibOut_allBool (h : HashConstraints B tr msg w1 states) (o : Fin sibLen) :
    AllBool (sibOut B states o) :=
  wordAbsorb_out_allBool (c := sibCall (msgLen := msgLen)) h.holds h.start_allBool o

/-- **`μ` is SHAKE256 of its input** `tr ‖ 0x00 ‖ 0x00 ‖ msg` (with Boolean `tr` bits). -/
theorem HashConstraints.mu_eq (h : HashConstraints B tr msg w1 states) (htr : AllBool tr)
    (o : Fin 64) :
    natOfBits (muOut B states o) =
      xofFin shake256 (inputBytes (HashCircuit.muInput tr noCtx msg)) 64 o :=
  wordAbsorb_sound h.holds h.start_allBool (fun p x y z => statesOf_startState B _ states p x y z)
    (fun _ _ _ _ => rfl)
    (HashCircuit.muInput_allBool htr (fun i => Fin.elim0 i) h.msgBool) h.absorb.mu o

/-- **`c̃'` is SHAKE256 of `μ ‖ w1`.** -/
theorem HashConstraints.cTilde_eq (h : HashConstraints B tr msg w1 states) (o : Fin 32) :
    natOfBits (cTildeOut B states o) =
      xofFin shake256 (inputBytes (HashCircuit.commitInput (muOut B states) w1)) 32 o :=
  wordAbsorb_sound h.holds h.start_allBool (fun p x y z => statesOf_startState B _ states p x y z)
    (fun _ _ _ _ => rfl) (HashCircuit.commitInput_allBool h.muOut_allBool h.w1Bool) h.absorb.cTilde o

/-- **The stream is SHAKE256 of `c̃'`.** -/
theorem HashConstraints.sib_eq (h : HashConstraints B tr msg w1 states) (o : Fin sibLen) :
    natOfBits (sibOut B states o) = xofFin shake256 (inputBytes (cTildeOut B states)) sibLen o :=
  wordAbsorb_sound h.holds h.start_allBool (fun p x y z => statesOf_startState B _ states p x y z)
    (fun _ _ _ _ => rfl) h.cTildeOut_allBool h.absorb.sib o

end Sound

end GordieHowe.MLDSA44.Native
