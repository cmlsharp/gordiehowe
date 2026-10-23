-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.HashCircuit.KeccakOperands
public import GordieHowe.Applications.Keccak.Gadgets.Sponge

@[expose] public section

/-!
# The committed Keccak words of the batched-Keccak H circuit

The committed Keccak words of the batched-Keccak H circuit and their decoding: `np` permutations
with `a + 1` committed permutation inputs give `24 np + 1 + a` states of 100 words (`Word`); the
words decode to bits (`wordBits`) and trace states (`statesOf`, `statesOf_chunk`,
`statesOf_startState`); a trace packs into words (`packStates`), and decoding the packed words of
Boolean states recovers them (`statesOf_packStates`). Subfield-valued words decode to Boolean
states (`wordBits_bool`, `statesOf_allBool`). The skip argument proves a batch of Keccak-f chains
and nothing else (`KeccakBatch.Holds`): no input map (`keccak_skip_circuit_link.h` at `e5daf0a`).
The fields are generic: `K` of characteristic two with a packing basis `B : PackedBasis K 4` of
`E = GF(2^16)`.

* Committed words. Word `(t, x, y, c)` is chunk `c` of lane `(x, y)` of state `t`
  (`state_inputs`, `keccak_skip_circuit_link.h` lines 25-29). Bit `z` of the lane is bit
  `z mod 16` of chunk `z / 16` (`of_scalar(word >> 16c)`).
-/

namespace GordieHowe.HashCircuit

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace PackedClaim
open Sumcheck.UnivariateSkip Packed.Opening Sumcheck.EqFactored

variable {K : Type} [Field K]

/-! ### Committed Keccak words -/

/-- The committed Keccak words of `np` permutations with `a + 1` committed permutation
inputs: `24 np + 1 + a` states of 100 words (`HashCircuit.KeccakOperands.Word`); word
`HashCircuit.KeccakOperands.wordIdx t x y c` is chunk `c` of lane `(x, y)` of state `t`. -/
abbrev Word (np a : ℕ) := KeccakOperands.Word (24 * np + 1 + a)

/-- The trace states whose bit `z` of lane `(x, y)` of state `t` is bit `z mod 16` of
word `wordIdx t x y (z / 16)` (`HashCircuit.KeccakOperands.stateOf`). -/
def statesOfBits {np a : ℕ} (bits : Word np a → Fin (2 ^ 4) → K) :
    Fin (24 * np + 1 + a) → State K :=
  KeccakOperands.stateOf bits

/-- The decoded bits of packed words. -/
def wordBits (B : PackedBasis K 4) {np a : ℕ} (p : Word np a → K) : Word np a → Fin (2 ^ 4) → K :=
  fun y i => decode B (p y) i

/-- The trace states of the decoded packed words. -/
def statesOf (B : PackedBasis K 4) {np a : ℕ} (p : Word np a → K) :
    Fin (24 * np + 1 + a) → State K :=
  statesOfBits (wordBits B p)

/-- Bit `16 c + b` of lane `(x, y)` of a decoded state is bit `b` of its word `c`. -/
theorem statesOf_chunk (B : PackedBasis K 4) {np a : ℕ} (p : Word np a → K)
    (t : Fin (24 * np + 1 + a)) (x y : Fin 5) (c : Fin 4) (b : Fin (2 ^ 4)) :
    statesOf B p t x y ⟨16 * (c : ℕ) + b, by omega⟩ =
      decode B (p (KeccakOperands.wordIdx t x y c)) b := by
  have hb := b.isLt
  have e1 : (⟨(16 * (c : ℕ) + b) / 16, by omega⟩ : Fin 4) = c := Fin.ext (by simp only; omega)
  have e2 : (⟨(16 * (c : ℕ) + b) % 16, by show _ < 16; omega⟩ : Fin (2 ^ 4)) = b :=
    Fin.ext (by simp only; omega)
  simp only [statesOf, statesOfBits, KeccakOperands.stateOf, wordBits, e1, e2]

/-- The decoded input of a permutation is the decode of its hook words. -/
theorem statesOf_startState (B : PackedBasis K 4) {np a : ℕ} (sh : KeccakBatch.Shape np a)
    (words : Word np a → K) (p : Fin np) (x y : Fin 5) (z : Fin 64) :
    statesOf B words (KeccakBatch.startState sh p) x y z =
      decode B (KeccakOperands.stateWords words (KeccakBatch.startState sh p) x y
        (zChunk z)) (zBit z) :=
  rfl

/-! ### Packing a trace into words -/

section Pack

variable {S : ℕ}

/-- The state of word `v`: `v / 100`. -/
def wordState (v : KeccakOperands.Word S) : Fin S :=
  ⟨(v : ℕ) / 100, by have := v.isLt; omega⟩

/-- The lane column of word `v`: `(v mod 100) / 4 / 5`. -/
def wordX (v : KeccakOperands.Word S) : Fin 5 :=
  ⟨(v : ℕ) % 100 / 4 / 5, by omega⟩

/-- The lane row of word `v`: `(v mod 100) / 4 mod 5`. -/
def wordY (v : KeccakOperands.Word S) : Fin 5 :=
  ⟨(v : ℕ) % 100 / 4 % 5, Nat.mod_lt _ (by decide)⟩

/-- The lane bit of bit `j` of word `v`: `16 (v mod 4) + j`. -/
def wordBit (v : KeccakOperands.Word S) (j : Fin (2 ^ 4)) : Fin 64 :=
  ⟨16 * ((v : ℕ) % 4) + j, by have := KeccakOperands.fin16_lt j; omega⟩

theorem wordState_wordIdx (t : Fin S) (x y : Fin 5) (c : Fin 4) :
    wordState (KeccakOperands.wordIdx t x y c) = t :=
  Fin.ext (by simp only [wordState, KeccakOperands.wordIdx]; omega)

theorem wordX_wordIdx (t : Fin S) (x y : Fin 5) (c : Fin 4) :
    wordX (KeccakOperands.wordIdx t x y c) = x :=
  Fin.ext (by simp only [wordX, KeccakOperands.wordIdx]; omega)

theorem wordY_wordIdx (t : Fin S) (x y : Fin 5) (c : Fin 4) :
    wordY (KeccakOperands.wordIdx t x y c) = y :=
  Fin.ext (by simp only [wordY, KeccakOperands.wordIdx]; omega)

theorem wordBit_wordIdx (t : Fin S) (x y : Fin 5) (c : Fin 4) (j : Fin (2 ^ 4)) :
    wordBit (KeccakOperands.wordIdx t x y c) j =
      ⟨16 * (c : ℕ) + j, by have := c.isLt; have := KeccakOperands.fin16_lt j; omega⟩ :=
  Fin.ext (by simp only [wordBit, KeccakOperands.wordIdx]; omega)

variable [DecidableEq K]

/-- **The packed words of a trace**: bit `j` of word `wordIdx t x y c` is bit `16c + j` of
lane `(x, y)` of state `t`, packed by `B` (`of_scalar(word >> 16c)`). -/
-- spec-side
def packStates (B : PackedBasis K 4) (states : Fin S → State K) :
    KeccakOperands.Word S → K :=
  fun v => pack B fun j => decide (states (wordState v) (wordX v) (wordY v) (wordBit v j) = 1)

theorem packStates_mem (B : PackedBasis K 4) (states : Fin S → State K)
    (v : KeccakOperands.Word S) : packStates B states v ∈ B.E :=
  pack_mem B _

/-- A Boolean field element is `1` or `0` according to whether it equals `1`. -/
theorem ite_decide_eq_one {v : K} (h : v = 0 ∨ v = 1) :
    (if decide (v = 1) = true then (1 : K) else 0) = v := by
  rcases h with rfl | rfl <;> simp

variable [CharP K 2]

/-- The committed words of a packed Boolean trace state are the packed lane words of that
state. -/
theorem stateWords_packStates (B : PackedBasis K 4) {states : Fin S → State K}
    {t : Fin S} (h : ∀ x y, AllBool (states t x y)) (x y : Fin 5) (c : Fin 4) :
    KeccakOperands.stateWords (packStates B states) t x y c =
      KeccakHook.packLane B (states t x y) c := by
  simp only [KeccakOperands.stateWords, packStates, wordState_wordIdx, wordX_wordIdx,
    wordY_wordIdx, wordBit_wordIdx]
  rw [KeccakHook.packLane_eq_pack B (h x y)]
  rfl

/-- Decoding the packed words of Boolean states recovers the states. -/
theorem statesOf_packStates (B : PackedBasis K 4) {np a : ℕ}
    {states : Fin (24 * np + 1 + a) → State K}
    (h : ∀ t x y, AllBool (states t x y)) : statesOf B (packStates B states) = states := by
  funext t x y z
  have hz : (⟨16 * ((z : ℕ) / 16) + ((⟨(z : ℕ) % 16, by omega⟩ : Fin (2 ^ 4)) : ℕ), by omega⟩ :
      Fin 64) = z := Fin.ext (by simp only; omega)
  simp only [statesOf, statesOfBits, KeccakOperands.stateOf, wordBits, packStates,
    decode_pack, wordState_wordIdx, wordX_wordIdx, wordY_wordIdx, wordBit_wordIdx, hz]
  exact ite_decide_eq_one (h t x y z)

end Pack

variable {Rest : Type} {n w : ℕ} {dom : SkipDomain K w} {np a : ℕ} {sh : KeccakBatch.Shape np a}

/-! ### Subfield-valued words decode to Boolean states -/

variable [CharP K 2]

theorem wordBits_bool (B : PackedBasis K 4) {p : Word np a → K} (h : ∀ y, p y ∈ B.E)
    (y : Word np a) (i : Fin (2 ^ 4)) : wordBits B p y i = 0 ∨ wordBits B p y i = 1 :=
  decode_bool B (h y) i

theorem statesOf_allBool (B : PackedBasis K 4) {p : Word np a → K} (h : ∀ y, p y ∈ B.E)
    (t : Fin (24 * np + 1 + a)) (x y : Fin 5) : AllBool (statesOf B p t x y) :=
  fun _ => wordBits_bool B h _ _

end GordieHowe.HashCircuit
