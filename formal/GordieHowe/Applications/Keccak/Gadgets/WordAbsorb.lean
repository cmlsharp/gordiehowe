-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Sponge

@[expose] public section

/-!
# The word-level absorb of a sponge over a batch

GordieHowe's SHAKE256 (`lib/gordiehowe/lib/keccak.h`, `sponge`) adds each padded block to the
previous permutation's output. This file states that absorb on the trace words: for every absorbed
block `j` and every start word `(x, y, c)` (word `4 (5x + y) + c` of the state, bits
`16c … 16c + 15` of lane `(x, y)`),

  `start_j[x][y][c] = const + Σ_b β_b · (bit b of the block word) + (j > 0 ? out_{j-1}[x][y][c] : 0)`,

where the block word holds the padded block's bytes `8 (x + 5y) + 2c` and `8 (x + 5y) + 2c + 1`
(message bits as wires, the padding as the constant; capacity words have no block part), and
`out_{j-1}` is the output word of the previous permutation (`round_word(24 (j - 1) + 23, q)`). In
characteristic two the sum is the XOR of packed words.

The C++ `KeccakSponge::hash` (`lib/circuits/keccak/keccak_sponge.h`) asserts instead that the
start words pack the bit-level input state `xorinBlock (previous output bits) (padded block)`.
The two agree on subfield words, since decoding (`PackedClaim.decode`) is additive and inverts
`packLane` on bits.

* `blockWord`: the packed word of the padded block's lane chunk (`packLane` of `xorinBlock` on the
  zero state, zero in the capacity).
* `WordAbsorb`: the word-level absorb of a call, on its hook words and the words of the
  permutations' outputs.
* `start_eq_inputOf_of_wordAbsorb`: on the batch relation, Boolean permutation inputs decoded from
  the hook words, outputs decoded from the output words and Boolean input bytes, the word-level
  absorb starts every permutation of the call at its block input (`inputOf`).
* `wordAbsorb_sound`: then every output byte is the sponge `sp.xof` of the input, and
  `wordAbsorb_out_allBool`: the output is Boolean.
-/

namespace GordieHowe.KeccakSponge

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch GordieHowe.KeccakHook GordieHowe.PackedClaim

variable {np a : ℕ} {K : Type*} [Field K] [DecidableEq K]

/-- **The packed block word** of absorbed block `k`, lane `(x, y)`, chunk `c`: `packLane` of the
padded block's bits xored into the zero state (`keccak.h`: `const + Σ_b β_b · wire_b`, the message
bits as wires and the padding as the constant; zero for a capacity lane). -/
def blockWord (B : PackedBasis K 4) (sp : SpongeSpec) {len : ℕ} (input : Fin len → BitWires K 8)
    (k : ℕ) (x y : Fin 5) (c : Fin 4) : K :=
  packLane B (xorinBlock sp (fun _ _ _ => 0) (paddedByte sp input k) x y) c

/-- **The word-level absorb** of the call `c` (`keccak.h`, the absorb circuit of `shake256_words`):
for every absorbed block `k`, the start word `(x, y, q)` of its permutation (`hook`) is the packed
block word plus, after block `0`, the output word `(x, y, q)` of the previous permutation of the
call (`outWord`). -/
def WordAbsorb (B : PackedBasis K 4) {sp : SpongeSpec} {sh : Shape np a} {len outLen : ℕ}
    (c : Call sp sh len outLen) (hook outWord : Fin np → Fin 5 → Fin 5 → Fin 4 → K)
    (input : Fin len → BitWires K 8) : Prop :=
  ∀ k : Fin (numBlocks sp len outLen), (k : ℕ) < absorbBlocks sp len → ∀ x y q,
    hook (c.perm k) x y q = blockWord B sp input k x y q +
      if h : 0 < (k : ℕ) then outWord (c.perm ⟨(k : ℕ) - 1, by omega⟩) x y q else 0

section Sound

variable [CharP K 2] {B : PackedBasis K 4} {sp : SpongeSpec} {sh : Shape np a} {len outLen : ℕ}
  {c : Call sp sh len outLen} {hook outWord : Fin np → Fin 5 → Fin 5 → Fin 4 → K}
  {input : Fin len → BitWires K 8}

/-- **The word-level absorb starts every permutation of the call at its block input.** On the
batch relation (`hH`), Boolean permutation inputs (`hstart`) decoded from the hook words (`hdec`),
permutation outputs decoded from the output words (`hfin`) and Boolean input bytes (`hin`), the
word-level absorb (`h`) makes the input of the call's permutation `k` the block input
`inputOf sp input (fun k => fin (c.perm k)) k`: an absorb block by additivity of decoding, a squeeze
by the batch's chaining. -/
theorem start_eq_inputOf_of_wordAbsorb {start fin : Fin np → State K} (hH : Holds sh start fin)
    (hstart : ∀ p x y, AllBool (start p x y))
    (hdec : ∀ p x y z, start p x y z = decode B (hook p x y (zChunk z)) (zBit z))
    (hfin : ∀ p x y z, fin p x y z = decode B (outWord p x y (zChunk z)) (zBit z))
    (hin : ∀ i, AllBool (input i)) (h : WordAbsorb B c hook outWord input)
    (k : Fin (numBlocks sp len outLen)) :
    start (c.perm k) = inputOf sp input (fun k => fin (c.perm k)) k := by
  have hF : ∀ k x y, AllBool (fin (c.perm k) x y) := fun k x y => by
    rw [hH.perm]
    exact keccakF_allBool (hstart _) x y
  by_cases hk : (k : ℕ) < absorbBlocks sp len
  · funext x y z
    have hblk : AllBool (xorinBlock sp (fun _ _ _ => 0) (paddedByte sp input k) x y) := by
      intro j
      unfold xorinBlock
      dsimp only
      split_ifs
      · exact bxor_bool (Or.inl rfl) (paddedByte_allBool hin _ _ _)
      · exact Or.inl rfl
    rw [hdec, h k hk x y (zChunk z), decode_add, blockWord, decode_packLane B hblk,
      laneBit_zChunk_zBit]
    have hp : decode B (if h : 0 < (k : ℕ) then outWord (c.perm ⟨(k : ℕ) - 1, by omega⟩) x y
        (zChunk z) else 0) (zBit z) = priorOf (fun k => fin (c.perm k)) k x y z := by
      unfold priorOf
      split_ifs with h0 h1 h1
      · rw [← hfin]
      · exact absurd ⟨h0, by omega⟩ h1
      · exact absurd h1.1 h0
      · exact decode_zero B _
    rw [hp]
    unfold inputOf xorinBlock
    rw [if_pos hk]
    dsimp only
    split_ifs
    · rw [bxor_eq, bxor_eq, zero_add, add_comm]
    · rw [zero_add]
  · have ha := absorbBlocks_pos sp len
    obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
    have hkl := k.isLt
    have hfits := c.fits
    have hnh := c.chained k hkl (by omega)
    have hc := hH.chain (c.first + j) (by omega) (by
      rw [show (⟨c.first + j + 1, _⟩ : Fin np) = ⟨c.first + k, by omega⟩ from Fin.ext (by
        simp only; omega)]
      exact hnh)
    have e1 : c.perm k = ⟨c.first + j + 1, by omega⟩ := Fin.ext (by simp only [Call.perm]; omega)
    rw [e1, hc]
    unfold inputOf priorOf
    rw [if_neg hk, dif_pos ⟨by omega, by omega⟩]
    exact congrArg fin (Fin.ext (by simp only [Call.perm]; omega))

/-- **Soundness of the sponge with the word-level absorb.** Under the hypotheses of
`start_eq_inputOf_of_wordAbsorb`, every byte squeezed from the call's permutation outputs is the
sponge `sp.xof` of the input. -/
theorem wordAbsorb_sound {start fin : Fin np → State K} (hH : Holds sh start fin)
    (hstart : ∀ p x y, AllBool (start p x y))
    (hdec : ∀ p x y z, start p x y z = decode B (hook p x y (zChunk z)) (zBit z))
    (hfin : ∀ p x y z, fin p x y z = decode B (outWord p x y (zChunk z)) (zBit z))
    (hin : ∀ i, AllBool (input i)) (h : WordAbsorb B c hook outWord input) (o : Fin outLen) :
    natOfBits (squeezeOut (sp := sp) (fun k => fin (c.perm k)) o) =
      xofFin sp.xof (inputBytes input) outLen o := by
  have hs := start_eq_inputOf_of_wordAbsorb hH hstart hdec hfin hin h
  refine squeezeOut_sound hin (fun j he => ?_) o
  rw [← hs j] at he
  rw [hH.perm]
  exact KeccakBatch.Encodes.keccakF he

omit [CharP K 2] in
/-- **The squeezed output is Boolean** when the permutations' inputs are (`hH`, `hstart`). -/
theorem wordAbsorb_out_allBool {start fin : Fin np → State K} (hH : Holds sh start fin)
    (hstart : ∀ p x y, AllBool (start p x y)) (o : Fin outLen) :
    AllBool (squeezeOut (sp := sp) (len := len) (fun k => fin (c.perm k)) o) := by
  exact squeezeOut_allBool (fun k x y => by rw [hH.perm]; exact keccakF_allBool (hstart _) x y) o

end Sound

/-! ### The honest absorb -/

section Complete

variable [CharP K 2] {B : PackedBasis K 4} {sp : SpongeSpec} {sh : Shape np a} {len outLen : ℕ}

omit [DecidableEq K] in
/-- **Packing distributes over the absorb's xor** in characteristic two: the packed word of the
block xored into `A` is the block word plus the packed word of `A` (bit `j` of the xor is
`A + blk`, `Bits.bxor_eq`; a capacity lane is `A` itself). -/
theorem packLane_xorinBlock (A : State K) (blk : Fin sp.rate → BitWires K 8) (x y : Fin 5)
    (c : Fin 4) :
    packLane B (xorinBlock sp A blk x y) c =
      packLane B (xorinBlock sp (fun _ _ _ => 0) blk x y) c + packLane B (A x y) c := by
  unfold packLane
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold xorinBlock
  dsimp only
  split_ifs
  · rw [bxor_eq, bxor_eq, zero_add, mul_add, add_comm]
  · rw [mul_zero, zero_add]

omit [DecidableEq K] in
/-- **Completeness of the word-level absorb.** When the call's permutations start at the honest
inputs `spongeStart` (`hs`), the hook words pack the inputs (`hhook`) and the output words pack
the outputs (`hout`), the word-level absorb holds. No Booleanity is needed:
`packLane_xorinBlock` holds on every state. -/
theorem wordAbsorb_complete {c : Call sp sh len outLen} {input : Fin len → BitWires K 8}
    {start : Fin np → State K}
    (hs : ∀ k : Fin (numBlocks sp len outLen), start (c.perm k) = spongeStart sp input k)
    {hook outWord : Fin np → Fin 5 → Fin 5 → Fin 4 → K}
    (hhook : ∀ p x y q, hook p x y q = packLane B (start p x y) q)
    (hout : ∀ p x y q, outWord p x y q = packLane B (keccakF (start p) x y) q) :
    WordAbsorb B c hook outWord input := by
  intro k hk x y q
  have hab : absorbBlocks sp len = len / sp.rate + 1 := rfl
  rw [hhook, hs k, blockWord]
  obtain ⟨kv, hkv⟩ := k
  cases kv with
  | zero =>
    rw [dif_neg (lt_irrefl 0), add_zero]
    rfl
  | succ j =>
    rw [dif_pos (Nat.succ_pos j), hout, hs]
    simp only [Nat.add_sub_cancel]
    rw [show spongeStart sp input (j + 1) =
        xorinBlock sp (keccakF (spongeStart sp input j)) (paddedByte sp input (j + 1)) from
      if_pos (by simp only at hk; omega)]
    exact packLane_xorinBlock _ _ x y q

end Complete

end GordieHowe.KeccakSponge
