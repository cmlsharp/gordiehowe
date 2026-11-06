-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Equiv.Defs
public import GordieHowe.Language.Library.Select.First

@[expose] public section

/-!
# Byte strings and streams

Shared by both signature specifications.  `SHAKE256` enters every
specification through the function type `XOF`.
-/

namespace GordieHowe

/-- A hash function from bytes and a requested output length to bytes. -/
abbrev XOF := List ℕ → ℕ → List ℕ

/-- 16-bit big-endian samples from a fixed-length byte string: sample `i` is
formed from bytes `2i` and `2i+1`. -/
def samples16 {S : ℕ} (bytes : Fin (2 * S) → ℕ) (i : Fin S) : ℕ :=
  256 * bytes ⟨2 * (i : ℕ), by have := i.isLt; omega⟩
    + bytes ⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩

/-- The byte at position `j` recovered from `S` 16-bit samples: the high byte
of the sample at `j / 2` if `j` is even, the low byte if `j` is odd. Inverse
to `samples16`. -/
def sampleByte {S : ℕ} (v : Fin S → ℕ) (j : Fin (2 * S)) : ℕ :=
  if (j : ℕ) % 2 = 0 then v ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩ / 256
  else v ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩ % 256

theorem sampleByte_lt {S : ℕ} {v : Fin S → ℕ} (hv : ∀ i, v i < 65536) (j : Fin (2 * S)) :
    sampleByte v j < 256 := by
  unfold sampleByte
  have := hv ⟨(j : ℕ) / 2, by have := j.isLt; omega⟩
  split_ifs <;> omega

theorem samples16_sampleByte {S : ℕ} (v : Fin S → ℕ) (hv : ∀ i, v i < 65536) (i : Fin S) :
    samples16 (fun j => sampleByte v j) i = v i := by
  have hidx1 : (⟨((⟨2 * (i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * S)) : ℕ) / 2,
      by have := i.isLt; omega⟩ : Fin S) = i := by
    apply Fin.ext
    show (2 * (i : ℕ)) / 2 = (i : ℕ)
    omega
  have hidx2 : (⟨((⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩ : Fin (2 * S)) : ℕ) / 2,
      by have := i.isLt; omega⟩ : Fin S) = i := by
    apply Fin.ext
    show (2 * (i : ℕ) + 1) / 2 = (i : ℕ)
    omega
  have hv' := hv i
  unfold samples16 sampleByte
  dsimp only
  rw [if_pos (show (2 * (i : ℕ)) % 2 = 0 by omega),
    if_neg (show ¬ (2 * (i : ℕ) + 1) % 2 = 0 by omega),
    hidx1, hidx2]
  omega

theorem sampleByte_samples16 {S : ℕ} (bytes : Fin (2 * S) → ℕ) (hb : ∀ j, bytes j < 256)
    (j : Fin (2 * S)) : sampleByte (fun i => samples16 bytes i) j = bytes j := by
  have hqlt : (j : ℕ) / 2 < S := by have := j.isLt; omega
  have hsamp : samples16 bytes (⟨(j : ℕ) / 2, hqlt⟩ : Fin S)
      = 256 * bytes ⟨2 * ((j : ℕ) / 2), by omega⟩
        + bytes ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩ := rfl
  unfold sampleByte
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with h0 | h1
  · rw [if_pos h0, hsamp]
    have hb1 := hb ⟨2 * ((j : ℕ) / 2), by omega⟩
    have hb2 := hb ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩
    have hjeq : j = (⟨2 * ((j : ℕ) / 2), by omega⟩ : Fin (2 * S)) :=
      Fin.ext (show (j : ℕ) = 2 * ((j : ℕ) / 2) by omega)
    conv_rhs => rw [hjeq]
    omega
  · rw [if_neg (by omega), hsamp]
    have hb1 := hb ⟨2 * ((j : ℕ) / 2), by omega⟩
    have hb2 := hb ⟨2 * ((j : ℕ) / 2) + 1, by omega⟩
    have hjeq : j = (⟨2 * ((j : ℕ) / 2) + 1, by omega⟩ : Fin (2 * S)) :=
      Fin.ext (show (j : ℕ) = 2 * ((j : ℕ) / 2) + 1 by omega)
    conv_rhs => rw [hjeq]
    omega

/-- Pairing bytes into 16-bit big-endian samples is a bijection between `2S`
bytes below `256` and `S` samples below `65536`: `samples16` read as the
forward direction, `sampleByte` as the inverse. -/
def samples16Equiv (S : ℕ) : (Fin (2 * S) → Fin 256) ≃ (Fin S → Fin 65536) where
  toFun bytes i := ⟨samples16 (fun j => (bytes j : ℕ)) i, by
    unfold samples16
    dsimp only
    have h1 := (bytes ⟨2 * (i : ℕ), by have := i.isLt; omega⟩).isLt
    have h2 := (bytes ⟨2 * (i : ℕ) + 1, by have := i.isLt; omega⟩).isLt
    omega⟩
  invFun v j := ⟨sampleByte (fun i => (v i : ℕ)) j,
    sampleByte_lt (fun i => (v i).isLt) j⟩
  left_inv bytes := by
    funext j
    apply Fin.ext
    exact sampleByte_samples16 (fun j' => (bytes j' : ℕ)) (fun j' => (bytes j').isLt) j
  right_inv v := by
    funext i
    apply Fin.ext
    exact samples16_sampleByte (fun i' => (v i' : ℕ)) (fun i' => (v i').isLt) i

theorem samples16Equiv_apply {S : ℕ} (bytes : Fin (2 * S) → Fin 256) (i : Fin S) :
    ((samples16Equiv S bytes i : ℕ)) = samples16 (fun j => (bytes j : ℕ)) i := rfl

end GordieHowe
