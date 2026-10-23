-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.Basic
public import GordieHowe.Applications.Keccak.Gadgets.Shake256
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Applications.Falcon512.Gadgets.SelectFirstN

@[expose] public section

/-!
# Falcon: H's byte and sample wires

The wire readings of Falcon's H circuit: bit wires read as bytes (`byteWires`, least significant
bit first) and bytes as bit wires (`wiresOfBytes`, `wiresOfByteVec`), with their booleanity and
decoding facts; and the sixteen-bit sample from two SHAKE output bytes (`sampleAt`: the second
byte supplies the low bits, the first the high bits; `sampleAt_low`, `sampleAt_high`,
`sampleAt_decode`).
-/

namespace GordieHowe.Falcon512.HashCircuit

variable {K : Type*} [Field K] [DecidableEq K]

/-- Bit wires read as bytes: bit `j` of byte `i` is wire `8 i + j`, least
significant bit first. -/
def byteWires {m : ℕ} (bits : BitWires K (8 * m)) (i : Fin m) : BitWires K 8 :=
  fun j => bits ⟨8 * i + j, by omega⟩

omit [DecidableEq K] in
theorem byteWires_allBool {m : ℕ} {bits : BitWires K (8 * m)} (hb : Bits.AllBool bits)
    (i : Fin m) : Bits.AllBool (byteWires bits i) :=
  fun _ => hb _

/-- Bytes as bit wires: bit `j` of byte `i` at wire `8 i + j`, the inverse of `byteWires`. -/
-- spec-side
def wiresOfBytes {m : ℕ} (bytes : Fin m → BitWires K 8) : BitWires K (8 * m) :=
  fun k => bytes ⟨k / 8, by omega⟩ ⟨k % 8, by omega⟩

/-- Rearrange two SHAKE bytes into one little-endian sixteen-bit sample.
The second byte supplies low bits; the first supplies high bits. -/
def sampleAt {S : ℕ} (out : Fin (2 * S) → BitWires K 8) (i : Fin S) (b : Fin falconSampleBits) : K :=
  if hb : (b : ℕ) < 8 then out ⟨2 * i + 1, by omega⟩ ⟨b, hb⟩
  else out ⟨2 * i, by omega⟩
    ⟨b - 8, by have := b.isLt; simp only [falconSampleBits] at this; omega⟩

omit [Field K] [DecidableEq K] in
theorem sampleAt_low {S : ℕ} (out : Fin (2 * S) → BitWires K 8) (i : Fin S) (b : Fin 8) :
    sampleAt out i (Fin.castAdd 8 b) = out ⟨2 * i + 1, by omega⟩ b := by
  simp [sampleAt]

omit [Field K] [DecidableEq K] in
theorem sampleAt_high {S : ℕ} (out : Fin (2 * S) → BitWires K 8) (i : Fin S) (b : Fin 8) :
    sampleAt out i (Fin.natAdd 8 b) = out ⟨2 * i, by omega⟩ b := by
  simp [sampleAt]

theorem sampleAt_decode {S : ℕ} (out : Fin (2 * S) → BitWires K 8) (i : Fin S) :
    Bits.natOfBits (sampleAt out i) = samples16 (fun o => Bits.natOfBits (out o)) i := by
  rw [Bits.natOfBits_add (m := 8) (n := 8)]
  simp only [sampleAt_low, sampleAt_high, samples16]
  exact Nat.add_comm _ _

variable (P : Params) {sl : Keccak.Slicing} {w msgLen : ℕ}

/-! ### Completeness -/

/-- Bytes as bit wires, little-endian within each byte. -/
-- spec-side
def wiresOfByteVec {m : ℕ} (bytes : Fin m → ℕ) : BitWires K (8 * m) :=
  fun k => Bits.constBit (bytes ⟨k / 8, by omega⟩) (k % 8)

omit [DecidableEq K] in
theorem wiresOfByteVec_allBool {m : ℕ} (bytes : Fin m → ℕ) :
    Bits.AllBool (wiresOfByteVec (K := K) bytes) :=
  fun _ => Bits.constBit_bool _ _

omit [DecidableEq K] in
theorem byteWires_wiresOfByteVec {m : ℕ} (bytes : Fin m → ℕ) (i : Fin m) :
    byteWires (wiresOfByteVec (K := K) bytes) i = fun j : Fin 8 => Bits.constBit (bytes i) j := by
  funext j
  simp only [byteWires, wiresOfByteVec]
  have hd : (8 * (i : ℕ) + j) / 8 = i := by omega
  have hm : (8 * (i : ℕ) + j) % 8 = j := by omega
  simp [hd, hm]

theorem natOfBits_byteWires_wiresOfByteVec {m : ℕ} {bytes : Fin m → ℕ}
    (hb : ∀ i, bytes i < 256) (i : Fin m) :
    Bits.natOfBits (byteWires (wiresOfByteVec (K := K) bytes) i) = bytes i := by
  rw [byteWires_wiresOfByteVec, Bits.natOfBits_constBit]
  exact Nat.mod_eq_of_lt (hb i)

end GordieHowe.Falcon512.HashCircuit
