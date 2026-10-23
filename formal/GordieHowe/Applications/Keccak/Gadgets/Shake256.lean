-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Basic
public import GordieHowe.Applications.Keccak.Gadgets.Shake256Spec
public import GordieHowe.Applications.Keccak.Sponge

@[expose] public section

/-!
# The Keccak sponge gadget (`lib/circuits/tests/sha3/sha3_circuit.h`)

A transcription of Longfellow's `Sha3Circuit::assert_shake256`: absorb `len` message bytes with the
sponge padding, squeeze `outLen` bytes, one block witness per permutation (`Keccak.permute`).
Generic over the slicing and the packing of `GordieHowe/Applications/Keccak/Gadgets/Basic.lean`, and over the sponge
configuration (`SpongeSpec`: rate and domain suffix, as in
`lib/circuits/keccak/keccak_sponge.h:43-51` at `e5daf0a`). `assert_shake256` itself is the
configuration `SpongeSpec.shake256`. Soundness concludes the generic spec `keccakSponge`
(`GordieHowe/Applications/Keccak/Sponge.lean`) at the configuration's rate and suffix (`SpongeSpec.xof`), which at
SHAKE256 is `GordieHowe.shake256` (`SpongeSpec.xof_shake256`).
-/

namespace GordieHowe.Shake256

open GordieHowe.Bits GordieHowe.Keccak

/-- **A sponge configuration** (C++ `SpongeSpec`, `keccak_sponge.h:43-51`): the rate in bytes and
the domain suffix. The fields that are parameter conditions: the rate is positive, a whole
number of lanes and below the 200-byte state (`check_spec`, `keccak_sponge.h:65-66`), and the suffix
is below `0x80`, so that xoring `0x80` into the last padding byte (`pad`, `keccak_sponge.h:53-58`)
is FIPS 202's `suffix ||| 0x80` when the padding is one byte. A fixed digest length (the C++
`digest`) is the caller's `outLen`. -/
structure SpongeSpec where
  rate : ℕ
  suffix : ℕ
  rate_pos : 0 < rate
  rate_mod : rate % 8 = 0
  rate_lt : rate < 200
  suffix_lt : suffix < 0x80

namespace SpongeSpec

/-- SHAKE128 (`kShake128{168, 0x1f}`). -/
def shake128 : SpongeSpec := ⟨168, 0x1f, by decide, by decide, by decide, by decide⟩

/-- SHAKE256 (`kShake256{136, 0x1f}`). -/
def shake256 : SpongeSpec := ⟨136, 0x1f, by decide, by decide, by decide, by decide⟩

/-- The configuration's specification: the Keccak sponge at its rate and suffix. -/
def xof (sp : SpongeSpec) : XOF := spongeXof sp.rate sp.suffix.toUInt8

theorem xof_shake256 : shake256.xof = GordieHowe.shake256 := spongeXof_shake256

/-- Xoring `0x80` into a byte below `0x80` sets its top bit. -/
theorem xor_0x80 {n : ℕ} (hn : n < 0x80) : n ^^^ 0x80 = n ||| 0x80 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases hi : i = 7
  · subst hi
    have : n.testBit 7 = false := Nat.testBit_lt_two_pow (by simpa using hn)
    simp [this]
  · have : (0x80 : ℕ).testBit i = false := by
      rw [show (0x80 : ℕ) = 2 ^ 7 by rfl, Nat.testBit_two_pow]
      simp [Ne.symm hi]
    simp [this]

/-- The suffix is a byte. -/
theorem suffix_lt_256 (sp : SpongeSpec) : sp.suffix < 256 :=
  sp.suffix_lt.trans (by decide)

/-- The suffix is its own byte value. -/
theorem toNat_suffix (sp : SpongeSpec) : sp.suffix.toUInt8.toNat = sp.suffix :=
  UInt8.toNat_ofNat_of_lt' sp.suffix_lt_256

/-- The last padding byte when it is also the first: the suffix with `0x80` xored in is the
suffix with its top bit set. -/
theorem suffix_xor (sp : SpongeSpec) : sp.suffix ^^^ 0x80 = (sp.suffix.toUInt8 ||| 0x80).toNat := by
  rw [xor_0x80 sp.suffix_lt, UInt8.toNat_or, toNat_suffix]
  rfl

end SpongeSpec

variable {K : Type*} [Field K] [DecidableEq K] {sp : SpongeSpec}

/-- Absorbed blocks: the message and its padding, which always adds a block
(`blocks = n / rate + 1`, `keccak_sponge.h:87`). -/
def absorbBlocks (sp : SpongeSpec) (len : ℕ) : ℕ := len / sp.rate + 1

/-- Extra permutations for output beyond the first block. -/
def squeezeBlocks (sp : SpongeSpec) (outLen : ℕ) : ℕ :=
  if outLen = 0 then 0 else (outLen - 1) / sp.rate

/-- Block witnesses required (`assert_shake256`'s `check`). -/
def numBlocks (sp : SpongeSpec) (len outLen : ℕ) : ℕ := absorbBlocks sp len + squeezeBlocks sp outLen

/-- A constant byte. -/
def constByte (c : ℕ) : BitWires K 8 := fun j => constBit c j

theorem natOfBits_constByte (c : ℕ) : natOfBits (constByte (K := K) c) = c % 256 :=
  natOfBits_constBit c

/-- Byte `i` of absorbed block `k` (`assert_shake256`, `sha3_circuit.h:274-296`):
message bytes, then the suffix right after the message, and in the last absorbed
block `0x80` xored into its last byte. Full message blocks carry no padding. -/
def paddedByte (sp : SpongeSpec) {len : ℕ} (input : Fin len → BitWires K 8) (k : ℕ) (i : Fin sp.rate) : BitWires K 8 :=
  let p := sp.rate * k + i
  let byte : BitWires K 8 :=
    if h : p < len then input ⟨p, h⟩ else if p = len then constByte sp.suffix else constByte 0
  if (i : ℕ) = sp.rate - 1 ∧ k = absorbBlocks sp len - 1 then fun j => bxor (byte j) (constByte 0x80 j)
  else byte

/-- `xorin_block` (`sha3_circuit.h:57-73`): byte `8L + b` of the block, bit `j`,
is xored into lane `L = x + 5y` at bit `8b + j`, for the first `rate / 8` lanes. -/
def xorinBlock (sp : SpongeSpec) (A : State K) (block : Fin sp.rate → BitWires K 8) : State K :=
  fun x y z =>
    let L := (x : ℕ) + 5 * y
    if h : L < sp.rate / 8 then
      bxor (A x y z) (block ⟨8 * L + z / 8, by omega⟩ ⟨z % 8, Nat.mod_lt _ (by decide)⟩)
    else A x y z

/-- **`assert_shake256`** (`sha3_circuit.h:221-323`) on `len` message bytes, for
`outLen` output bytes. Absorbed block `k` starts from the round-23 advice of
block `k − 1` (zero for `k = 0`); squeeze permutation `j` starts from the
round-23 advice of block `absorbBlocks sp len − 1 + j`; output byte `o` is read from
the round-23 advice of block `absorbBlocks sp len − 1 + o / rate`. -/
def run (sl : Slicing) (pk : Packing K) {len outLen : ℕ} (input : Fin len → BitWires K 8)
    (bws : Fin (numBlocks sp len outLen) → BlockAdvice K sl) :
    Bool × (Fin outLen → BitWires K 8) :=
  let prior (k : ℕ) : State K :=
    if h : 0 < k ∧ k - 1 < numBlocks sp len outLen then finalState (bws ⟨k - 1, h.2⟩) else fun _ _ _ => 0
  let absorbOk := (List.finRange (numBlocks sp len outLen)).all fun k =>
    if (k : ℕ) < absorbBlocks sp len then
      permute sl pk (xorinBlock sp (prior k) (paddedByte sp input k)) (bws k)
    else
      permute sl pk (prior k) (bws k)
  let boolOk := (List.finRange (numBlocks sp len outLen)).all fun k => adviceBool (bws k)
  let out : Fin outLen → BitWires K 8 := fun o j =>
    let blk := absorbBlocks sp len - 1 + (o : ℕ) / sp.rate
    let i := (o : ℕ) % sp.rate
    let L := i / 8
    if h : blk < numBlocks sp len outLen then
      finalState (bws ⟨blk, h⟩) ⟨L % 5, Nat.mod_lt _ (by decide)⟩
        ⟨L / 5 % 5, Nat.mod_lt _ (by decide)⟩ ⟨8 * (i % 8) + j, by omega⟩
    else 0
  (absorbOk && boolOk, out)

/-- The input bytes of `run` as naturals below 256. -/
-- spec-side
def inputBytes {len : ℕ} (input : Fin len → BitWires K 8) : List ℕ :=
  List.ofFn fun i => natOfBits (input i)

/-- The padded message byte values, as `paddedByte` on constant wires. -/
-- spec-side
def paddedByteNat (sp : SpongeSpec) {len : ℕ} (bytes : Fin len → ℕ) (k : ℕ) (i : Fin sp.rate) : ℕ :=
  let p := sp.rate * k + i
  let byte := if h : p < len then bytes ⟨p, h⟩ else if p = len then sp.suffix else 0
  if (i : ℕ) = sp.rate - 1 ∧ k = absorbBlocks sp len - 1 then byte ^^^ 0x80 else byte

/-- `xorin_block` on lanes, as the vendored `absorb` performs it: byte `i` is
xored into lane `i / 8` at bit offset `8 (i mod 8)`. -/
-- spec-side
def xorinLanes (sp : SpongeSpec) (s : Array UInt64) (block : Fin sp.rate → ℕ) : Array UInt64 :=
  (List.finRange sp.rate).foldl
    (fun (s : Array UInt64) (i : Fin sp.rate) =>
      s.set! ((i : ℕ) / 8)
        (s[(i : ℕ) / 8]! ^^^ ((block i).toUInt64 <<< (((i : ℕ) % 8) * 8).toUInt64))) s

/-- The input state of permutation `k` in the honest computation. -/
-- spec-side
def honestInput (sp : SpongeSpec) {len : ℕ} (outLen : ℕ) (bytes : Fin len → ℕ) : ℕ → Array UInt64
  | 0 => xorinLanes sp (Array.replicate 25 0) (paddedByteNat sp bytes 0)
  | k + 1 =>
    let prev := SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes k)
    if k + 1 < absorbBlocks sp len then xorinLanes sp prev (paddedByteNat sp bytes (k + 1)) else prev

theorem honestInput_zero {len : ℕ} (outLen : ℕ) (bytes : Fin len → ℕ) :
    honestInput sp outLen bytes 0 = xorinLanes sp (Array.replicate 25 0) (paddedByteNat sp bytes 0) :=
  rfl

theorem honestInput_succ_of_lt {len : ℕ} (outLen : ℕ) (bytes : Fin len → ℕ) {k : ℕ}
    (hk : k + 1 < absorbBlocks sp len) :
    honestInput sp outLen bytes (k + 1) =
      xorinLanes sp (SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes k))
        (paddedByteNat sp bytes (k + 1)) := by
  simp only [honestInput, hk, ↓reduceIte]

theorem honestInput_succ_of_le {len : ℕ} (outLen : ℕ) (bytes : Fin len → ℕ) {k : ℕ}
    (hk : absorbBlocks sp len ≤ k + 1) :
    honestInput sp outLen bytes (k + 1) =
      SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes k) := by
  simp only [honestInput, show ¬k + 1 < absorbBlocks sp len by omega, ↓reduceIte]

/-! ### Boolean states and their lanes -/

/-- `A` is a Boolean state whose lanes, as the vendored reference stores them, are `s`. -/
structure Encodes (A : State K) (s : Array UInt64) : Prop where
  bool : ∀ x y, AllBool (A x y)
  lanes : toLanes A = s

/-- Lane `x + 5y` of `toLanes A` is lane `(x, y)` of `A`. -/
theorem toLanes_getElem (A : State K) (x y : Fin 5) (h : (x : ℕ) + 5 * y < (toLanes A).size) :
    (toLanes A)[(x : ℕ) + 5 * y] = (natOfBits (A x y)).toUInt64 := by
  simp only [toLanes, Array.getElem_ofFn]
  have hx : ((x : ℕ) + 5 * y) % 5 = x := by omega
  have hy : ((x : ℕ) + 5 * y) / 5 = y := by omega
  simp only [hx, hy]

theorem toLanes_getElem! (A : State K) (x y : Fin 5) :
    (toLanes A)[(x : ℕ) + 5 * y]! = (natOfBits (A x y)).toUInt64 := by
  rw [getElem!_pos _ _ (by rw [size_toLanes]; omega), toLanes_getElem]

/-- The state whose lane `(x, y)` holds the bits of `s[x + 5y]`. -/
-- spec-side
def ofLanes (s : Array UInt64) : State K := fun x y z => constBit (s[(x : ℕ) + 5 * y]!).toNat z

theorem encodes_ofLanes {s : Array UInt64} (hs : s.size = 25) : Encodes (ofLanes (K := K) s) s := by
  refine ⟨fun x y z => constBit_bool _ _, ?_⟩
  apply Array.ext
  · rw [size_toLanes, hs]
  · intro i hi _
    rw [size_toLanes] at hi
    simp only [toLanes, Array.getElem_ofFn]
    show (natOfBits fun z : Fin 64 =>
      constBit (K := K) (s[i % 5 + 5 * (i / 5)]!).toNat z).toUInt64 = s[i]
    rw [natOfBits_constBit, show i % 5 + 5 * (i / 5) = i by omega]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), getElem!_pos _ i (by omega)]
    simp

/-- A Boolean state is determined by its lanes. -/
theorem Encodes.eq_ofLanes {A : State K} {s : Array UInt64} (h : Encodes A s) : A = ofLanes s := by
  funext x y z
  show A x y z = constBit (s[(x : ℕ) + 5 * y]!).toNat z
  rw [← h.lanes, toLanes_getElem!, toNat_toUInt64_natOfBits _ le_rfl,
    constBit_natOfBits (h.bool x y)]

theorem encodes_zero : Encodes (fun _ _ _ => (0 : K)) (Array.replicate 25 0) := by
  have h : (fun _ _ _ => (0 : K)) = ofLanes (Array.replicate 25 (0 : UInt64)) := by
    funext x y z
    rw [ofLanes, getElem!_pos _ _ (by simp; omega)]
    simp [constBit]
  rw [h]
  exact encodes_ofLanes Array.size_replicate

/-- A gadget round on a Boolean state is the vendored round on its lanes. -/
theorem Encodes.round {A : State K} {s : Array UInt64} (h : Encodes A s) (r : Fin 24) :
    Encodes (Keccak.round r A)
      (SLHDSA.Concrete.Keccak.round s SLHDSA.Concrete.Keccak.roundConstants[r]!) where
  bool := round_allBool h.bool r
  lanes := h.lanes ▸ toLanes_round h.bool r

/-! ### Absorbed blocks -/

/-- `xorinBlock` restricted to the first `n` bytes of the block. -/
-- spec-side
def xorinPrefix (sp : SpongeSpec) (A : State K) (block : Fin sp.rate → BitWires K 8) (n : ℕ) : State K :=
  fun x y z =>
    let L := (x : ℕ) + 5 * y
    if h : 8 * L + z / 8 < n ∧ L < sp.rate / 8 then
      bxor (A x y z) (block ⟨8 * L + z / 8, by omega⟩ ⟨z % 8, Nat.mod_lt _ (by decide)⟩)
    else A x y z

omit [DecidableEq K] in
theorem xorinPrefix_zero (A : State K) (block : Fin sp.rate → BitWires K 8) :
    xorinPrefix sp A block 0 = A := by
  funext x y z
  simp [xorinPrefix]

omit [DecidableEq K] in
theorem xorinPrefix_rate (A : State K) (block : Fin sp.rate → BitWires K 8) :
    xorinPrefix sp A block sp.rate = xorinBlock sp A block := by
  funext x y z
  simp only [xorinPrefix, xorinBlock]
  by_cases hL : (x : ℕ) + 5 * y < sp.rate / 8
  · have h8 : 8 * ((x : ℕ) + 5 * y) + (z : ℕ) / 8 < sp.rate := by omega
    simp only [h8, hL, and_self, ↓reduceDIte]
  · simp only [hL, and_false, ↓reduceDIte]

/-- Xoring in byte `n` is `xorinLanes`' step on the lanes. -/
theorem Encodes.xorinPrefix_succ {A : State K} {block : Fin sp.rate → BitWires K 8}
    (hA : ∀ x y, AllBool (A x y)) (hblock : ∀ i, AllBool (block i)) {n : ℕ} (hn : n < sp.rate)
    {t : Array UInt64} (h : Encodes (xorinPrefix sp A block n) t) :
    Encodes (xorinPrefix sp A block (n + 1))
      (t.set! (n / 8) (t[n / 8]! ^^^
        ((natOfBits (block ⟨n, hn⟩)).toUInt64 <<< ((n % 8) * 8).toUInt64))) := by
  obtain ⟨-, rfl⟩ := h
  have hbool : ∀ m x y, AllBool (xorinPrefix sp A block m x y) := by
    intro m x y z
    simp only [xorinPrefix]
    split_ifs
    · exact bxor_bool (hA x y z) (hblock _ _)
    · exact hA x y z
  refine ⟨hbool (n + 1), ?_⟩
  apply Array.ext
  · simp [size_toLanes]
  · intro j hj _
    rw [size_toLanes] at hj
    obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 5, j = x + 5 * y :=
      ⟨⟨j % 5, Nat.mod_lt _ (by decide)⟩, ⟨j / 5, by omega⟩, by simp only; omega⟩
    simp only [Array.set!_eq_setIfInBounds, toLanes_getElem]
    rw [Array.getElem_setIfInBounds (by rw [size_toLanes]; omega)]
    split_ifs with hnj
    · rw [hnj, toLanes_getElem!,
        ← natOfBits_xorByte (hbool n x y) (hblock _) (Nat.mod_lt _ (by decide))]
      congr 2
      funext z
      simp only [xorinPrefix]
      have hrate := sp.rate_mod
      have hrate' := sp.rate_lt
      split_ifs <;> first | rfl | omega | (congr 3; omega)
    · rw [toLanes_getElem]
      congr 2
      funext z
      simp only [xorinPrefix]
      split_ifs <;> first | rfl | omega

/-- `xorinBlock` on an encoded state is `xorinLanes` on its lanes. -/
theorem Encodes.xorinBlock {A : State K} {s : Array UInt64} {block : Fin sp.rate → BitWires K 8}
    (h : Encodes A s) (hblock : ∀ i, AllBool (block i)) :
    Encodes (Shake256.xorinBlock sp A block) (xorinLanes sp s fun i => natOfBits (block i)) := by
  have h0 : Encodes (xorinPrefix sp A block 0) s := by
    rw [xorinPrefix_zero]
    exact h
  rw [← xorinPrefix_rate, xorinLanes]
  exact List.foldl_finRange_induction (fun n t => Encodes (xorinPrefix sp A block n) t) h0
    fun i t ht => ht.xorinPrefix_succ h.bool hblock i.2

omit [DecidableEq K] in
/-- **A padded byte past the input** is the padding: the suffix at the input's end, `0` after it,
with `0x80` xored into the last byte of the last absorb block. -/
theorem paddedByte_of_ge {len : ℕ} (input : Fin len → BitWires K 8) (k : ℕ) (i : Fin sp.rate)
    (h : len ≤ sp.rate * k + i) :
    paddedByte sp input k i =
      if (i : ℕ) = sp.rate - 1 ∧ k = absorbBlocks sp len - 1 then
        fun j => bxor (constByte (if sp.rate * k + i = len then sp.suffix else 0) j)
          (constByte 0x80 j)
      else constByte (if sp.rate * k + i = len then sp.suffix else 0) := by
  unfold paddedByte
  dsimp only
  rw [dif_neg (by omega)]
  split_ifs <;> rfl

omit [DecidableEq K] in
theorem paddedByte_allBool {len : ℕ} {input : Fin len → BitWires K 8}
    (hin : ∀ i, AllBool (input i)) (k : ℕ) (i : Fin sp.rate) : AllBool (paddedByte sp input k i) := by
  unfold paddedByte constByte
  dsimp only
  split_ifs <;> intro j
  · exact bxor_bool (hin _ j) (constBit_bool _ _)
  · exact bxor_bool (constBit_bool _ _) (constBit_bool _ _)
  · exact bxor_bool (constBit_bool _ _) (constBit_bool _ _)
  · exact hin _ j
  · exact constBit_bool _ _
  · exact constBit_bool _ _

theorem natOfBits_paddedByte {len : ℕ} {input : Fin len → BitWires K 8}
    (hin : ∀ i, AllBool (input i)) (k : ℕ) (i : Fin sp.rate) :
    natOfBits (paddedByte sp input k i) = paddedByteNat sp (fun i => natOfBits (input i)) k i := by
  have hc : ∀ c, AllBool (constByte (K := K) c) := fun c j => constBit_bool _ _
  unfold paddedByte paddedByteNat
  dsimp only
  split_ifs
  · rw [natOfBits_bxor (hin _) (hc _)]
    simp [natOfBits_constByte]
  · rw [natOfBits_bxor (hc _) (hc _)]
    simp [natOfBits_constByte, Nat.mod_eq_of_lt sp.suffix_lt_256]
  · rw [natOfBits_bxor (hc _) (hc _)]
    simp [natOfBits_constByte]
  · rfl
  · simp [natOfBits_constByte, Nat.mod_eq_of_lt sp.suffix_lt_256]
  · simp [natOfBits_constByte]

/-! ### Block chaining -/

theorem absorbBlocks_pos (sp : SpongeSpec) (len : ℕ) : 0 < absorbBlocks sp len :=
  Nat.succ_pos _

/-- The state block `k` starts from in `run`: the round-23 advice of block `k − 1`, and the
zero state for `k = 0`. -/
def priorState {sl : Slicing} {n : ℕ} (bws : Fin n → BlockAdvice K sl) (k : ℕ) : State K :=
  if h : 0 < k ∧ k - 1 < n then finalState (bws ⟨k - 1, h.2⟩) else fun _ _ _ => 0

/-- The state block `k` starts from, read from the blocks' final states `fin`: the final state
of block `k − 1`, and the zero state for `k = 0` (`priorState` on final states). -/
def priorOf {n : ℕ} (fin : Fin n → State K) (k : ℕ) : State K :=
  if h : 0 < k ∧ k - 1 < n then fin ⟨k - 1, h.2⟩ else fun _ _ _ => 0

/-- The input state of permutation `k`, read from the blocks' final states `fin` (the state `run`
permutes at block `k`). -/
def inputOf (sp : SpongeSpec) {len n : ℕ} (input : Fin len → BitWires K 8) (fin : Fin n → State K) (k : ℕ) :
    State K :=
  if k < absorbBlocks sp len then xorinBlock sp (priorOf fin k) (paddedByte sp input k) else priorOf fin k

/-- The squeezed output bytes, read from the blocks' final states (the output of `run`). -/
def squeezeOut {len outLen : ℕ} (fin : Fin (numBlocks sp len outLen) → State K) :
    Fin outLen → BitWires K 8 := fun o j =>
  let blk := absorbBlocks sp len - 1 + (o : ℕ) / sp.rate
  let i := (o : ℕ) % sp.rate
  let L := i / 8
  if h : blk < numBlocks sp len outLen then
    fin ⟨blk, h⟩ ⟨L % 5, Nat.mod_lt _ (by decide)⟩ ⟨L / 5 % 5, Nat.mod_lt _ (by decide)⟩
      ⟨8 * (i % 8) + j, by omega⟩
  else 0

/-- `run`'s output is `squeezeOut` of its blocks' round-23 advice. -/
theorem run_snd_eq (sl : Slicing) (pk : Packing K) {len outLen : ℕ}
    (input : Fin len → BitWires K 8) (bws : Fin (numBlocks sp len outLen) → BlockAdvice K sl) :
    (run sl pk input bws).2 = squeezeOut fun k => finalState (bws k) :=
  rfl

/-- **Block inputs read from final states.** If every block maps an encoding of its honest input
to an encoding of that input's permutation, every block input read from the final states `fin`
encodes the honest input. -/
theorem encodes_inputOf {len outLen : ℕ} {input : Fin len → BitWires K 8}
    {fin : Fin (numBlocks sp len outLen) → State K} (hin : ∀ i, AllBool (input i))
    (hstep : ∀ j : Fin (numBlocks sp len outLen),
      Encodes (inputOf sp input fin j) (honestInput sp outLen (fun i => natOfBits (input i)) j) →
      Encodes (fin j)
        (SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen (fun i => natOfBits (input i)) j)))
    {k : ℕ} (hk : k < numBlocks sp len outLen) :
    Encodes (inputOf sp input fin k) (honestInput sp outLen (fun i => natOfBits (input i)) k) := by
  induction k with
  | zero =>
    have hp : priorOf fin 0 = fun _ _ _ => 0 := by simp [priorOf]
    simp only [inputOf, absorbBlocks_pos sp len, ↓reduceIte, hp]
    have h := encodes_zero.xorinBlock (paddedByte_allBool (sp := sp) hin 0)
    simp only [natOfBits_paddedByte hin] at h
    exact h
  | succ k ih =>
    have hprev := hstep ⟨k, by omega⟩ (ih (by omega))
    have hp : priorOf fin (k + 1) = fin ⟨k, by omega⟩ := by
      simp [priorOf, show k < numBlocks sp len outLen by omega]
    rw [inputOf, hp]
    split_ifs with hk'
    · have h := hprev.xorinBlock (paddedByte_allBool (sp := sp) hin (k + 1))
      simp only [natOfBits_paddedByte hin] at h
      rwa [honestInput_succ_of_lt outLen _ hk']
    · rwa [honestInput_succ_of_le outLen _ (by omega)]

omit [DecidableEq K] in
/-- Squeezed bytes of Boolean final states are Boolean. -/
theorem squeezeOut_allBool {len outLen : ℕ} {fin : Fin (numBlocks sp len outLen) → State K}
    (h : ∀ k x y, AllBool (fin k x y)) (o : Fin outLen) : AllBool (squeezeOut fin o) := by
  intro j
  unfold squeezeOut
  dsimp only
  split_ifs
  · exact h _ _ _ _
  · exact Or.inl rfl

/-! ### The vendored sponge on the honest inputs -/

/-- Position `r b + i` of block `b ≤ q` is the last of `q + 1` blocks of `r` bytes exactly when
it is the last byte of block `q`. -/
theorem mul_add_eq_last_iff {r q b i : ℕ} (hi : i < r) (hb : b ≤ q) :
    (r * b + i = r * (q + 1) - 1) ↔ ((i : ℕ) = r - 1 ∧ b = q) := by
  rcases Nat.lt_or_ge b q with h | h
  · have h' : r * (b + 1) ≤ r * q := Nat.mul_le_mul_left _ h
    rw [Nat.mul_succ] at h' ⊢
    constructor
    · omega
    · rintro ⟨_, rfl⟩
      omega
  · obtain rfl : b = q := le_antisymm hb h
    rw [Nat.mul_succ]
    omega

/-- `absorb` computes the permutation of the last absorbed honest input. -/
theorem absorb_eq_honestInput {len : ℕ} (outLen : ℕ) {bytes : Fin len → ℕ}
    (hbytes : ∀ i, bytes i < 256) :
    SLHDSA.Concrete.Keccak.absorb (ByteArray.mk ((List.ofFn bytes).map Nat.toUInt8).toArray)
        sp.rate sp.suffix.toUInt8 =
      SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes (absorbBlocks sp len - 1)) := by
  have hr := sp.rate_pos
  have ha : absorbBlocks sp len = len / sp.rate + 1 := rfl
  have hlen : len < sp.rate * (len / sp.rate + 1) := Nat.lt_mul_div_succ len hr
  set msg := ByteArray.mk ((List.ofFn bytes).map Nat.toUInt8).toArray
  have hsize : msg.size = len := by
    show ((List.ofFn bytes).map Nat.toUInt8).toArray.size = len
    simp
  have hbyte : ∀ p (hp : p < len), (msg[p]!).toNat = bytes ⟨p, hp⟩ := by
    intro p hp
    rw [getElem!_pos msg p (by omega)]
    show (((List.ofFn bytes).map Nat.toUInt8).toArray[p]'(by simpa using hp)).toNat = _
    simp [UInt8.toNat_ofNat_of_lt' (hbytes _)]
  have hpad : ∀ b < absorbBlocks sp len, ∀ i : Fin sp.rate,
      ((Keccak.absorbPadded msg sp.rate sp.suffix.toUInt8)[b * sp.rate + i]!).toNat =
        paddedByteNat sp bytes b i := by
    intro b hb i
    have hi : (i : ℕ) < sp.rate := i.2
    have hb' : b ≤ len / sp.rate := by rw [ha] at hb; omega
    have hp : b * sp.rate + i < sp.rate * (msg.size / sp.rate + 1) := by
      rw [hsize, Nat.mul_comm b]
      have := Nat.mul_le_mul_left sp.rate hb'
      rw [Nat.mul_succ]
      omega
    rw [Keccak.absorbPadded_getElem! msg hr sp.suffix.toUInt8 hp, hsize]
    have hlast : (sp.rate * b + i = sp.rate * (len / sp.rate + 1) - 1) =
        ((i : ℕ) = sp.rate - 1 ∧ b = absorbBlocks sp len - 1) := by
      rw [ha, Nat.add_sub_cancel]
      exact propext (mul_add_eq_last_iff hi hb')
    have hlast' : sp.rate * b + i ≤ sp.rate * (len / sp.rate + 1) - 1 := by
      have := Nat.mul_le_mul_left sp.rate hb'
      rw [Nat.mul_succ]
      omega
    unfold paddedByteNat
    dsimp only
    rw [show b * sp.rate + (i : ℕ) = sp.rate * b + i from by rw [Nat.mul_comm]]
    simp only [hlast]
    have hq : sp.rate * (len / sp.rate + 1) = sp.rate * (len / sp.rate) + sp.rate := Nat.mul_succ _ _
    split_ifs with hlt hl hn hn
    · obtain ⟨hi1, hb1⟩ := hl
      rw [ha, Nat.add_sub_cancel] at hb1
      subst hb1
      omega
    · exact hbyte _ hlt
    · exact sp.suffix_xor.symm
    · simpa using sp.suffix_lt_256
    · decide
    · decide
  rw [Keccak.absorb_eq_foldl, Keccak.absorbPadded_size msg hr,
    hsize, Nat.mul_div_cancel_left _ hr, ← ha]
  rw [List.foldl_ext _
    (fun s b => SLHDSA.Concrete.Keccak.f1600 (xorinLanes sp s (paddedByteNat sp bytes b))) _
    (fun s b hb => ?_)]
  · have claim : ∀ k < absorbBlocks sp len, (List.range (k + 1)).foldl
        (fun s b => SLHDSA.Concrete.Keccak.f1600 (xorinLanes sp s (paddedByteNat sp bytes b)))
        (Array.replicate 25 0) = SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes k) := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [List.range_one, List.foldl_cons, List.foldl_nil, honestInput_zero]
      | succ k ih =>
        intro hk
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
          honestInput_succ_of_lt outLen bytes hk]
    have h := claim (absorbBlocks sp len - 1) (by have := absorbBlocks_pos sp len; omega)
    rwa [Nat.sub_add_cancel (absorbBlocks_pos sp len)] at h
  · rw [List.mem_range] at hb
    refine congrArg SLHDSA.Concrete.Keccak.f1600 ?_
    rw [xorinLanes, ← List.map_coe_finRange_eq_range, List.foldl_map]
    exact List.foldl_ext _ _ _ fun t i _ => by rw [hpad b hb i]

/-- Past the absorbed blocks, each honest input is the permutation of the previous one. -/
theorem iterate_f1600_honestInput {len : ℕ} (outLen : ℕ) (bytes : Fin len → ℕ) (n : ℕ) :
    SLHDSA.Concrete.Keccak.f1600^[n]
        (SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes (absorbBlocks sp len - 1))) =
      SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen bytes (absorbBlocks sp len - 1 + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha := absorbBlocks_pos sp len
    rw [Function.iterate_succ_apply', ih, ← Nat.add_assoc,
      honestInput_succ_of_le outLen bytes (by omega)]

/-- **The squeezed output is the sponge `sp.xof`** when every block maps an encoding of its honest input,
read from the final states `fin`, to an encoding of that input's permutation. -/
theorem squeezeOut_sound {len outLen : ℕ} {input : Fin len → BitWires K 8}
    {fin : Fin (numBlocks sp len outLen) → State K} (hin : ∀ i, Bits.AllBool (input i))
    (hstep : ∀ j : Fin (numBlocks sp len outLen),
      Encodes (inputOf sp input fin j) (honestInput sp outLen (fun i => natOfBits (input i)) j) →
      Encodes (fin j)
        (SLHDSA.Concrete.Keccak.f1600 (honestInput sp outLen (fun i => natOfBits (input i)) j)))
    (o : Fin outLen) :
    natOfBits (squeezeOut fin o) = xofFin sp.xof (inputBytes input) outLen o := by
  have ha := absorbBlocks_pos sp len
  have hblk : absorbBlocks sp len - 1 + (o : ℕ) / sp.rate < numBlocks sp len outLen := by
    have ho := o.2
    unfold numBlocks squeezeBlocks
    simp only [show outLen ≠ 0 by omega, ↓reduceIte]
    have : (o : ℕ) / sp.rate ≤ (outLen - 1) / sp.rate := Nat.div_le_div_right (by omega)
    omega
  have henc := hstep ⟨_, hblk⟩ (encodes_inputOf hin hstep hblk)
  have hi : (o : ℕ) % sp.rate < sp.rate := Nat.mod_lt _ sp.rate_pos
  have hlt := sp.rate_lt
  have hout : squeezeOut fin o = fun j : Fin 8 =>
      fin ⟨_, hblk⟩ ⟨(o : ℕ) % sp.rate / 8 % 5, Nat.mod_lt _ (by decide)⟩
        ⟨(o : ℕ) % sp.rate / 8 / 5 % 5, Nat.mod_lt _ (by decide)⟩
        ⟨8 * ((o : ℕ) % sp.rate % 8) + j, by omega⟩ := by
    funext j
    simp only [squeezeOut, hblk, ↓reduceDIte]
  rw [hout, natOfBits_laneByte (henc.bool _ _) (Nat.mod_lt _ (by decide)), ← toLanes_getElem!,
    henc.lanes, show (o : ℕ) % sp.rate / 8 % 5 + 5 * ((o : ℕ) % sp.rate / 8 / 5 % 5) = (o : ℕ) % sp.rate / 8
      by omega,
    SpongeSpec.xof, xofFin_spongeXof_eq_getElem! sp.rate_pos, inputBytes,
    Keccak.squeezeXof_getElem! _ sp.rate_pos _ _ o.2,
    Keccak.squeeze_getElem! _ _ _ hi,
    Keccak.squeezeFullBlocks_fst,
    absorb_eq_honestInput outLen fun i => natOfBits_lt (input i),
    iterate_f1600_honestInput]

end GordieHowe.Shake256
