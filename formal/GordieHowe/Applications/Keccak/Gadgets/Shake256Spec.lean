-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Bits
public import GordieHowe.Applications.Keccak.Xof

@[expose] public section

/-!
# Facts behind the SHAKE256 gadget's proofs

Two groups of facts used by `GordieHowe/Applications/Keccak/Gadgets/Shake256.lean`:

* bit wires read as the binary digits of a natural number, and lanes of 64 bit
  wires read as the vendored reference's `UInt64` lanes;
* the vendored sponge (`Vendor/HashSig/SLHDSA/Concrete/Keccak.lean`): `absorb` as a fold over padded
  blocks, the padding it appends, and the state `squeezeFullBlocks` passes on.
-/

namespace GordieHowe.Bits

variable {K : Type*} [Field K] [DecidableEq K]

/-- Bit `i` of the natural a Boolean bit vector denotes is the wire `i`. -/
theorem testBit_natOfBits {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) (i : Fin m) :
    (natOfBits bits).testBit i = decide (bits i = 1) := by
  have h := constBit_natOfBits hb i
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold constBit at h
  rcases hb i with h0 | h1
  · rw [h0] at h ⊢
    split_ifs at h with hc
    · exact absurd h one_ne_zero
    · simp [hc]
  · rw [h1] at h ⊢
    split_ifs at h with hc
    · simp [hc]
    · exact absurd h zero_ne_one

/-- Bits of `natOfBits` at or above the width are zero. -/
theorem testBit_natOfBits_of_le {m i : ℕ} (bits : BitWires K m) (hi : m ≤ i) :
    (natOfBits bits).testBit i = false :=
  Nat.testBit_lt_two_pow ((natOfBits_lt bits).trans_le (Nat.pow_le_pow_right (by decide) hi))

/-- `bxor` of two bits is `1` exactly when one of them is. -/
theorem decide_bxor_eq_one {a b : K} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    decide (bxor a b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [bxor, ← one_add_one_eq_two]

/-- `natOfBits` turns bitwise `bxor` of Boolean vectors into `^^^`. -/
theorem natOfBits_bxor {m : ℕ} {u v : BitWires K m} (hu : AllBool u) (hv : AllBool v) :
    natOfBits (fun i => bxor (u i) (v i)) = natOfBits u ^^^ natOfBits v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases Nat.lt_or_ge i m with hi | hi
  · rw [testBit_natOfBits (fun j => bxor_bool (hu j) (hv j)) ⟨i, hi⟩,
      testBit_natOfBits hu ⟨i, hi⟩, testBit_natOfBits hv ⟨i, hi⟩,
      decide_bxor_eq_one (hu _) (hv _)]
  · simp [testBit_natOfBits_of_le _ hi]

/-- A 64-bit vector's natural fits in a `UInt64`. -/
theorem toNat_toUInt64_natOfBits {m : ℕ} (bits : BitWires K m) (hm : m ≤ 64) :
    (natOfBits bits).toUInt64.toNat = natOfBits bits :=
  UInt64.toNat_ofNat' ▸ Nat.mod_eq_of_lt ((natOfBits_lt bits).trans_le
    (Nat.pow_le_pow_right (by decide) hm))

/-- Xoring byte wires `b` into bits `8c, …, 8c + 7` of a lane xors the byte, shifted by
`8c`, into the lane's `UInt64` value (`xorin_block` on one byte). -/
theorem natOfBits_xorByte {u : BitWires K 64} {b : BitWires K 8} (hu : AllBool u)
    (hb : AllBool b) {c : ℕ} (hc : c < 8) :
    (natOfBits fun z : Fin 64 => if (z : ℕ) / 8 = c then
        bxor (u z) (b ⟨z % 8, Nat.mod_lt _ (by decide)⟩) else u z).toUInt64 =
      (natOfBits u).toUInt64 ^^^ ((natOfBits b).toUInt64 <<< (c * 8).toUInt64) := by
  have hbool : AllBool fun z : Fin 64 =>
      if (z : ℕ) / 8 = c then bxor (u z) (b ⟨z % 8, Nat.mod_lt _ (by decide)⟩) else u z := by
    intro z
    dsimp only
    split_ifs
    · exact bxor_bool (hu z) (hb _)
    · exact hu z
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor, UInt64.toNat_shiftLeft, toNat_toUInt64_natOfBits _ le_rfl,
    toNat_toUInt64_natOfBits _ le_rfl, toNat_toUInt64_natOfBits _ (by decide),
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : c * 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : c * 8 < 64)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i 64 with hi | hi
  · rw [testBit_natOfBits hbool ⟨i, hi⟩, testBit_natOfBits hu ⟨i, hi⟩]
    by_cases hic : i / 8 = c
    · have hlo : i - c * 8 = i % 8 := by omega
      rw [hlo, testBit_natOfBits hb ⟨i % 8, Nat.mod_lt _ (by decide)⟩]
      simp only [hic, ite_true, decide_bxor_eq_one (hu _) (hb _)]
      simp [hi, show c * 8 ≤ i by omega]
    · simp only [hic, ite_false]
      rcases Nat.lt_or_ge i (c * 8) with hlt | hge
      · simp [hi, Nat.not_le.mpr hlt]
      · simp [testBit_natOfBits_of_le b (show 8 ≤ i - c * 8 by omega)]
  · simp [testBit_natOfBits_of_le _ hi, Nat.not_lt.mpr hi]

/-- Bits `8c, …, 8c + 7` of a lane are byte `c` of its `UInt64` value, as `squeeze`
reads it. -/
theorem natOfBits_laneByte {u : BitWires K 64} (hu : AllBool u) {c : ℕ} (hc : c < 8) :
    natOfBits (fun j : Fin 8 => u ⟨8 * c + j, by omega⟩) =
      (((natOfBits u).toUInt64 >>> (c * 8).toUInt64) &&& 0xFF).toUInt8.toNat := by
  have hbool : AllBool fun j : Fin 8 => u ⟨8 * c + j, by omega⟩ := fun j => hu _
  rw [UInt64.toNat_toUInt8, UInt64.toNat_and, UInt64.toNat_shiftRight,
    toNat_toUInt64_natOfBits _ le_rfl, UInt64.toNat_ofNat', UInt64.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : c * 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c * 8 < 64)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_shiftRight,
    show (255 % 2 ^ 64 : ℕ) = 2 ^ 8 - 1 by decide, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i 8 with hi | hi
  · rw [testBit_natOfBits hbool ⟨i, hi⟩, testBit_natOfBits hu ⟨c * 8 + i, by omega⟩]
    simp [hi, show 8 * c + i = c * 8 + i by omega]
  · simp [testBit_natOfBits_of_le _ hi, Nat.not_lt.mpr hi]

end GordieHowe.Bits

/-- Induction along a fold over `List.finRange n`, with an invariant indexed by the number of
elements processed. A fact about `List.foldl`; a candidate for `PQ/ToMathlib`. -/
theorem List.foldl_finRange_induction {β : Type*} {n : ℕ} (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → Fin n → β}
    (hf : ∀ (i : Fin n) (b : β), motive i b → motive (i + 1) (f b i)) :
    motive n ((List.finRange n).foldl f init) := by
  have h := Array.foldl_induction (as := (List.finRange n).toArray) motive h0 (f := f)
    (fun i b hb => by
      have hi : (i : ℕ) < n := by simpa using i.2
      have hri : (List.finRange n).toArray[i] = ⟨i, hi⟩ := by
        rw [Fin.getElem_fin]
        ext
        simp
      rw [hri]
      exact hf ⟨i, hi⟩ b hb)
  simpa using h

namespace GordieHowe.Keccak
open SLHDSA.Concrete.Keccak

/-- The state `squeezeFullBlocks` passes on after `n` blocks is the `n`-th iterate of the
permutation. -/
theorem squeezeFullBlocks_fst (initial : Array UInt64) (rate n : ℕ) :
    (squeezeFullBlocks initial rate n).1 = f1600^[n] initial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The `T` padding bytes `absorb` appends: `padByte`, zeros, and `0x80` in the last byte,
merged into one byte `padByte ||| 0x80` when `T = 1`. -/
-- spec-side
def padBytes (padByte : UInt8) (T : ℕ) : List UInt8 :=
  if T = 1 then [padByte ||| 0x80] else padByte :: (List.replicate (T - 2) 0 ++ [0x80])

theorem padBytes_length (padByte : UInt8) {T : ℕ} (hT : 0 < T) :
    (padBytes padByte T).length = T := by
  unfold padBytes
  split_ifs with h
  · simp [h]
  · simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
    omega

theorem padBytes_getElem (padByte : UInt8) {T j : ℕ} (hT0 : 0 < T)
    (hj : j < (padBytes padByte T).length) :
    (padBytes padByte T)[j] =
      (if j = 0 then padByte else 0) ||| (if j = T - 1 then 0x80 else 0) := by
  unfold padBytes at hj ⊢
  split_ifs at hj ⊢ with hT
  · simp only [List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    simp [hT]
  · simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil] at hj
    cases j with
    | zero => simp [show 0 ≠ T - 1 by omega, UInt8.or_zero]
    | succ j =>
      simp only [List.getElem_cons_succ, List.getElem_append, List.length_replicate,
        List.getElem_replicate, List.getElem_singleton, Nat.succ_ne_zero, ite_false, UInt8.zero_or]
      split_ifs <;> first | rfl | omega

/-- The padded input `absorb` reads. -/
-- spec-side
def absorbPadded (input : ByteArray) (rate : ℕ) (padByte : UInt8) : ByteArray :=
  input ++ ByteArray.mk (padBytes padByte (rate - input.size % rate)).toArray

/-- `absorb` xors each padded block into the first `rate` bytes of the state, lane `i / 8`
at bit offset `8 (i mod 8)`, and permutes. -/
theorem absorb_eq_foldl (input : ByteArray) (rate : ℕ) (padByte : UInt8) :
    absorb input rate padByte =
      (List.range ((absorbPadded input rate padByte).size / rate)).foldl
        (fun s b => f1600 ((List.range rate).foldl
          (fun s i => s.set! (i / 8) (s[i / 8]! ^^^
            ((absorbPadded input rate padByte)[b * rate + i]!).toNat.toUInt64 <<<
              ((i % 8) * 8).toUInt64)) s))
        (Array.replicate 25 0) := by
  unfold absorb
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, bind_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rfl

/-- The padding appends `rate − (size mod rate)` bytes, completing the last block. -/
theorem absorbPadded_size (input : ByteArray) {rate : ℕ} (hrate : 0 < rate) (padByte : UInt8) :
    (absorbPadded input rate padByte).size = rate * (input.size / rate + 1) := by
  have hmod := Nat.mod_lt input.size hrate
  have hdiv := Nat.div_add_mod input.size rate
  rw [absorbPadded, ByteArray.size_append]
  change input.size + (padBytes padByte (rate - input.size % rate)).length = _
  rw [padBytes_length _ (by omega), Nat.mul_add, Nat.mul_one]
  omega

/-- Byte `p` of the padded input: an input byte, or `padByte` right after the input
together with `0x80` in the last byte. -/
theorem absorbPadded_getElem! (input : ByteArray) {rate : ℕ} (hrate : 0 < rate) (padByte : UInt8)
    {p : ℕ} (hp : p < rate * (input.size / rate + 1)) :
    (absorbPadded input rate padByte)[p]! =
      if p < input.size then input[p]!
      else (if p = input.size then padByte else 0) |||
        (if p = rate * (input.size / rate + 1) - 1 then 0x80 else 0) := by
  have hmod := Nat.mod_lt input.size hrate
  have hdiv := Nat.div_add_mod input.size rate
  have hsize := absorbPadded_size input hrate padByte
  rw [getElem!_pos _ p (by omega)]
  simp only [absorbPadded]
  by_cases hlt : p < input.size
  · simp only [hlt, ↓reduceIte]
    rw [ByteArray.getElem_append_left hlt, getElem!_pos _ p hlt]
  · simp only [hlt, ↓reduceIte]
    rw [ByteArray.getElem_append_right (by omega)]
    change (padBytes padByte (rate - input.size % rate))[p - input.size]'(by
      rw [padBytes_length _ (by omega)]; rw [Nat.mul_add, Nat.mul_one] at hp; omega) = _
    rw [padBytes_getElem _ (by omega), Nat.mul_add, Nat.mul_one]
    congr 2 <;> apply propext <;> omega

end GordieHowe.Keccak
