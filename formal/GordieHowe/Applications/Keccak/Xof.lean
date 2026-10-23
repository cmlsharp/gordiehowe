-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin
public import GordieHowe.Applications.Keccak.Bytes
public import HashSig.SLHDSA.Concrete.Keccak

@[expose] public section

/-!
# Fixed-length XOF output, and `SHAKE256` itself

An XOF takes a variable-length byte string and a requested output length. The
output has that length, so it is a `Fin m → ℕ`. `xofFin` is the one place a
`List`-valued output is read as such; `shake256_length` below makes the read exact
for `shake256`.

`shake256 : XOF` wires our `XOF` type to the vendored sponge
`SLHDSA.Concrete.Keccak.shake256` (`Vendor/HashSig/SLHDSA/Concrete/Keccak.lean`), which
works over `ByteArray`/`UInt8`. Bytes are naturals below 256 everywhere else in this
development; this file is the one adapter between the two representations.
-/

/-! ### Prefix consistency of the vendored sponge

`SLHDSA.Concrete.Keccak.squeezeXof` squeezes complete `rate`-byte permutation blocks and then
a residual partial block; byte `k` of its output is determined by `k` alone (which block it
falls in, and which offset within that block), not by the requested output length, as long as
`k` is within range. `squeezeXof_prefix` is the resulting fact that two `squeezeXof` calls with
different requested lengths agree on every byte both of them produce; it is what lets the
fixed-stream sampler (`GordieHowe.Falcon512.acceptedCandidates`) share the first `S` samples of a larger-budget
sampler's stream (`Falcon.Concrete.hashToPoint`), since both draw from the same SHAKE256 output.
These are general facts about the vendored sponge, not about our own `XOF` adapter below. -/

namespace GordieHowe.Keccak

open SLHDSA.Concrete.Keccak

/-- `squeeze`'s value at a byte position does not depend on the requested output length, only
on whether that position is within range. -/
theorem squeeze_getElem! (s : Array UInt64) (len i : ℕ) (hi : i < len) :
    (squeeze s len)[i]! =
      ((s[i / 8]! >>> ((i % 8) * 8).toUInt64) &&& 0xFF).toUInt8 := by
  have hsize : i < (squeeze s len).size := by rw [squeeze_size]; exact hi
  rw [getElem!_pos (squeeze s len) i hsize]
  show (Array.ofFn fun j : Fin len =>
    ((s[j.val / 8]! >>> ((j.val % 8) * 8).toUInt64) &&& 0xFF).toUInt8)[i]'(by simpa using hsize) = _
  rw [Array.getElem_ofFn]

/-- If `k` lies in the half-open block `[q * rate, q * rate + rate)`, its quotient and
remainder by `rate` are `q` and `k - q * rate`. The one arithmetic fact behind both
`squeezeFullBlocks_snd_getElem!` and `squeezeXof_getElem!`: `rate` is a variable, so
`omega` cannot relate `k / rate` and `k % rate` to it on its own. -/
theorem div_mod_of_mul_le_lt {rate : ℕ} (hrate : 0 < rate) {q k : ℕ}
    (hlo : q * rate ≤ k) (hhi : k < q * rate + rate) :
    k / rate = q ∧ k % rate = k - q * rate := by
  generalize hr_def : k - q * rate = r
  have hkeq : k = r + q * rate := by rw [← hr_def]; omega
  have hrlt : r < rate := by rw [hkeq] at hhi; omega
  refine ⟨?_, ?_⟩
  · rw [hkeq, Nat.add_mul_div_right _ q hrate, Nat.div_eq_of_lt hrlt, Nat.zero_add]
  · rw [hkeq, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hrlt

/-- Byte `k` of the concatenation of `blocks` full permutation blocks, for `k` within range,
is byte `k % rate` of the state after `k / rate` full rounds: the value at a position does not
depend on how many further blocks are squeezed. -/
theorem squeezeFullBlocks_snd_getElem! (initial : Array UInt64) {rate : ℕ} (hrate : 0 < rate)
    (blocks k : ℕ) (hk : k < blocks * rate) :
    (squeezeFullBlocks initial rate blocks).2[k]! =
      (squeeze (squeezeFullBlocks initial rate (k / rate)).1 rate)[k % rate]! := by
  induction blocks with
  | zero => omega
  | succ blocks ih =>
    rw [Nat.succ_mul] at hk
    rcases Nat.lt_or_ge k (blocks * rate) with h | h
    · have hsize : k < (squeezeFullBlocks initial rate blocks).2.size := by
        rw [squeezeFullBlocks_size]; exact h
      show ((squeezeFullBlocks initial rate blocks).2 ++
        squeeze (squeezeFullBlocks initial rate blocks).1 rate)[k]! = _
      rw [getElem!_pos _ k (by rw [ByteArray.size_append]; omega),
        ByteArray.getElem_append_left hsize]
      rw [← getElem!_pos _ k hsize]
      exact ih h
    · obtain ⟨hkd, hkm⟩ := div_mod_of_mul_le_lt hrate h hk
      rw [hkd, hkm]
      have hle : (squeezeFullBlocks initial rate blocks).2.size ≤ k := by
        rw [squeezeFullBlocks_size]; exact h
      have hsize2 : k < (squeezeFullBlocks initial rate blocks).2.size +
          (squeeze (squeezeFullBlocks initial rate blocks).1 rate).size := by
        rw [squeezeFullBlocks_size, squeeze_size]; omega
      show ((squeezeFullBlocks initial rate blocks).2 ++
        squeeze (squeezeFullBlocks initial rate blocks).1 rate)[k]! = _
      rw [getElem!_pos _ k (by rw [ByteArray.size_append]; exact hsize2),
        ByteArray.getElem_append_right hle]
      rw [← getElem!_pos _ _ (by rw [squeezeFullBlocks_size, squeeze_size]; omega)]
      congr 1
      rw [squeezeFullBlocks_size]

/-- Byte `k` of `squeezeXof`'s output depends only on `k` (and `initial`, `rate`), not on the
requested output length, as long as `k` is within range: it is byte `k % rate` of the state
after `k / rate` full permutation rounds. This is the prefix-consistency fact for the vendored
XOF squeeze: two calls with different `outLen` agree on every byte both of them produce. -/
theorem squeezeXof_getElem! (initial : Array UInt64) {rate : ℕ} (hrate : 0 < rate)
    (outLen k : ℕ) (hk : k < outLen) :
    (squeezeXof initial rate outLen)[k]! =
      (squeeze (squeezeFullBlocks initial rate (k / rate)).1 rate)[k % rate]! := by
  unfold squeezeXof
  simp only [show rate ≠ 0 by omega, ite_false]
  rcases Nat.lt_or_ge k (outLen / rate * rate) with hcase | hcase
  · have hsize : k < (squeezeFullBlocks initial rate (outLen / rate)).2.size := by
      rw [squeezeFullBlocks_size]; exact hcase
    rw [getElem!_pos _ k (by rw [ByteArray.size_append]; omega),
      ByteArray.getElem_append_left hsize, ← getElem!_pos _ k hsize]
    exact squeezeFullBlocks_snd_getElem! initial hrate _ k hcase
  · have heq : outLen / rate * rate + outLen % rate = outLen := by
      rw [Nat.mul_comm (outLen / rate) rate]; exact Nat.div_add_mod outLen rate
    have hmodlt : outLen % rate < rate := Nat.mod_lt outLen hrate
    have hhi : k < outLen / rate * rate + rate := by omega
    obtain ⟨hkd, hkm⟩ := div_mod_of_mul_le_lt hrate hcase hhi
    have hle : (squeezeFullBlocks initial rate (outLen / rate)).2.size ≤ k := by
      rw [squeezeFullBlocks_size]; exact hcase
    have hsize2 : k < (squeezeFullBlocks initial rate (outLen / rate)).2.size +
        (squeeze (squeezeFullBlocks initial rate (outLen / rate)).1 (outLen % rate)).size := by
      rw [squeezeFullBlocks_size, squeeze_size]; omega
    rw [getElem!_pos _ k (by rw [ByteArray.size_append]; exact hsize2),
      ByteArray.getElem_append_right hle,
      ← getElem!_pos _ _ (by omega)]
    have hidx : k - (squeezeFullBlocks initial rate (outLen / rate)).2.size = k % rate := by
      rw [squeezeFullBlocks_size]; omega
    rw [hkd, hidx]
    have hkmlt : k % rate < outLen % rate := by omega
    rw [squeeze_getElem! _ _ _ hkmlt, squeeze_getElem! _ rate _ (Nat.mod_lt k hrate)]

/-- Corollary of `squeezeXof_getElem!`: two `squeezeXof` calls with different requested
lengths agree on every byte within both ranges. -/
theorem squeezeXof_prefix (initial : Array UInt64) {rate : ℕ} (hrate : 0 < rate)
    {m m' k : ℕ} (hk : k < m) (hm : m ≤ m') :
    (squeezeXof initial rate m)[k]! = (squeezeXof initial rate m')[k]! := by
  rw [squeezeXof_getElem! initial hrate m k hk, squeezeXof_getElem! initial hrate m' k (by omega)]

end GordieHowe.Keccak

namespace GordieHowe

/-- The first `m` output bytes of `shake` on `input`, as a fixed-length vector. -/
def xofFin (shake : XOF) (input : List ℕ) (m : ℕ) (i : Fin m) : ℕ := (shake input m).getD i 0

/-- `SHAKE256`, wired to the vendored sponge `SLHDSA.Concrete.Keccak.shake256`. Bytes
below 256 are converted to and from `UInt8` here, the one place in this development
that conversion happens. -/
def shake256 : XOF := fun input m =>
  (SLHDSA.Concrete.Keccak.shake256 (ByteArray.mk (input.map Nat.toUInt8).toArray) m).data.toList.map
    UInt8.toNat

/-- `shake256`'s output always has the requested length, from the vendored sponge's own
size lemma `SLHDSA.Concrete.Keccak.shake256_size`. -/
theorem shake256_length (input : List ℕ) (m : ℕ) : (shake256 input m).length = m := by
  simp only [shake256, List.length_map, Array.length_toList]
  exact SLHDSA.Concrete.Keccak.shake256_size _ m

/-- `xofFin shake256 input m` reads coefficient `i` directly off the (exactly
`m`-long) `shake256` output; the `getD` fallback default is never reached. -/
theorem xofFin_shake256_eq_getElem (input : List ℕ) (m : ℕ) (i : Fin m) :
    xofFin shake256 input m i =
      (shake256 input m)[i.1]'(by rw [shake256_length]; exact i.2) := by
  unfold xofFin
  exact (List.getElem_eq_getD 0).symm

/-- Generic core fact: mapping a function over a list reads the corresponding source entry,
for a position within range. -/
theorem _root_.List.getElem!_map' {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β)
    (l : List α) {i : ℕ} (h : i < l.length) :
    (l.map f)[i]! = f (l[i]!) := by
  rw [getElem!_pos _ i (by simpa using h), getElem!_pos _ i h, List.getElem_map]

/-- Generic core fact: a `ByteArray`'s indexing agrees with its underlying `Array`'s, including
past the end (both fall back to the same default). -/
theorem _root_.ByteArray.getElem!_data (a : ByteArray) (i : ℕ) : a.data[i]! = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a.data i (by simpa using h), getElem!_pos a i h,
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg a.data i (by simpa using h), getElem!_neg a i h]

/-- `shake256`'s output, read at a position below the requested length, agrees with reading
the same position off the underlying vendored sponge output and casting to `ℕ`: `shake256` is
`SLHDSA.Concrete.Keccak.shake256` composed with the byte-representation adapter, nothing else. -/
theorem xofFin_shake256_eq_getElem! (input : List ℕ) (m : ℕ) (i : Fin m) :
    xofFin shake256 input m i =
      (SLHDSA.Concrete.Keccak.shake256 (ByteArray.mk (input.map Nat.toUInt8).toArray) m)[i.1]!.toNat := by
  rw [xofFin_shake256_eq_getElem, ← getElem!_pos (shake256 input m) i.1
    (by rw [shake256_length]; exact i.2)]
  unfold shake256
  rw [List.getElem!_map' UInt8.toNat _
      (by simp [SLHDSA.Concrete.Keccak.shake256_size]),
    Array.getElem!_toList, ByteArray.getElem!_data]

/-- Prefix consistency of `shake256` itself, lifted from `Keccak.squeezeXof_prefix`
through the byte-representation adapter: `shake256`'s output at a position does not depend on
how many bytes were requested, as long as that position is within range for both requests. This
is what lets `GordieHowe.Falcon512.acceptedCandidates`'s fixed-length sample stream (`S` samples) agree with a
larger-budget sampler's stream on their shared prefix. -/
theorem xofFin_shake256_prefix (input : List ℕ) {m m' : ℕ} (hm : m ≤ m') (i : Fin m) :
    xofFin shake256 input m i = xofFin shake256 input m' ⟨i, lt_of_lt_of_le i.2 hm⟩ := by
  rw [xofFin_shake256_eq_getElem!, xofFin_shake256_eq_getElem!]
  exact congrArg UInt8.toNat
    (Keccak.squeezeXof_prefix _ (by decide) i.2 hm)

end GordieHowe
