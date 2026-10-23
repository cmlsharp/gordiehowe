-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Foundations.ToMathlib.Array
public import HashSig.SLHDSA.Concrete.Keccak

@[expose] public section

/-!
# Keccak-f[1600] on bits

The proof that the Keccak gadget (`GordieHowe/Applications/Keccak/Gadgets/Basic.lean`) computes the vendored permutation
goes through a model of one round on Boolean states, `Fin 5 → Fin 5 → Fin 64 → Bool` (lane `(x, y)`,
bit `z`). This file defines the model and proves that the vendored `round` computes it on the bits
of its lanes (`laneBit`); the gadget file proves the same of the gadget round on field states whose
wires are `0` or `1` (`ofBool`).
-/

namespace GordieHowe.Keccak

open SLHDSA.Concrete.Keccak

/-- A Keccak state as bits: lane `(x, y)`, bit `z`. -/
abbrev BitState := Fin 5 → Fin 5 → Fin 64 → Bool

/-- The xor of column `x`, bit `z`. -/
-- spec-side
def column (f : BitState) (x : Fin 5) (z : Fin 64) : Bool :=
  f x 0 z ^^ f x 1 z ^^ f x 2 z ^^ f x 3 z ^^ f x 4 z

/-- `theta` on bits. -/
-- spec-side
def thetaBits (f : BitState) : BitState :=
  fun x y z => f x y z ^^ (column f (x + 4) z ^^ column f (x + 1) (z - 1))

/-- The `rho` rotation of lane `(x, y)`, from the vendored table. -/
-- spec-side
def rhoOffset (x y : Fin 5) : ℕ := rhoLUT[(x : ℕ) + 5 * y]!

theorem rhoOffset_lt (x y : Fin 5) : rhoOffset x y < 64 := by
  revert x y
  decide

/-- `rho` on bits: lane `(x, y)` rotated left by `rhoOffset x y`. -/
-- spec-side
def rhoBits (f : BitState) : BitState := fun x y z => f x y (z - Fin.ofNat 64 (rhoOffset x y))

/-- `pi` on bits. -/
-- spec-side
def piBits (f : BitState) : BitState := fun x y z => f (x + 3 * y) x z

/-- `chi` on bits. -/
-- spec-side
def chiBits (f : BitState) : BitState :=
  fun x y z => f x y z ^^ (!f (x + 1) y z && f (x + 2) y z)

/-- `iota` on bits, with round constant `c`. -/
-- spec-side
def iotaBits (c : ℕ) (f : BitState) : BitState :=
  fun x y z => f x y z ^^ (decide (x = 0 ∧ y = 0) && c.testBit z)

/-- One round on bits, with round constant `c`. -/
-- spec-side
def roundBits (c : ℕ) (f : BitState) : BitState :=
  iotaBits c (chiBits (piBits (rhoBits (thetaBits f))))

/-! ### The vendored round on lane bits -/

/-- Bit `z` of lane `(x, y)` of a vendored state (index `x + 5y`). -/
-- spec-side
def laneBit (s : Array UInt64) : BitState :=
  fun x y z => s[(x : ℕ) + 5 * y]!.toBitVec.getLsbD z

/-- Two vendored states of 25 lanes with the same bits are equal. -/
theorem eq_of_laneBit_eq {s t : Array UInt64} (hs : s.size = 25) (ht : t.size = 25)
    (h : laneBit s = laneBit t) : s = t := by
  refine Array.ext (hs.trans ht.symm) fun i his _ => ?_
  have hi : i < 25 := hs ▸ his
  have hxy : i = ((⟨i % 5, by omega⟩ : Fin 5) : ℕ) + 5 * ((⟨i / 5, by omega⟩ : Fin 5) : ℕ) := by
    simp only
    omega
  apply UInt64.toBitVec_inj.mp
  refine BitVec.eq_of_getLsbD_eq fun z hz => ?_
  have hb := congrFun (congrFun (congrFun h ⟨i % 5, by omega⟩) ⟨i / 5, by omega⟩) ⟨z, hz⟩
  simp only [laneBit, ← hxy] at hb
  simpa [getElem!_pos, his, ht ▸ hs ▸ his] using hb

theorem getLsbD_rotl64 (w : UInt64) {n : ℕ} (hn : n < 64) (z : Fin 64) :
    (rotl64 w n).toBitVec.getLsbD z = w.toBitVec.getLsbD (z - Fin.ofNat 64 n : Fin 64) := by
  have hz := z.isLt
  simp only [rotl64, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_or]
  simp only [Fin.sub_def, Fin.val_ofNat, Nat.mod_eq_of_lt hn]
  simp [Nat.toUInt64, BitVec.toNat_umod, Nat.mod_eq_of_lt hn]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Nat.mod_eq_of_lt hz]
  · by_cases hzn : (z : ℕ) < n
    · rw [Nat.mod_eq_of_lt (by omega : 64 - n < 64), Nat.mod_eq_of_lt (by omega)]
      simp [hzn]
    · rw [Nat.mod_eq_of_lt (by omega : 64 - n < 64), BitVec.getLsbD_of_ge _ _ (by omega)]
      rw [show (64 - n + z) % 64 = z - n by omega]
      simp [hzn, BitVec.getLsbD_eq_getElem (by omega : (z : ℕ) - n < 64)]

theorem getElem!_map_range {α : Type*} [Inhabited α] {n i : ℕ} (h : i < n) (f : ℕ → α) :
    ((List.range n).toArray.map f)[i]! = f i := by
  simp [h]

/-- `piLUT` sends the lane `(x + 3y, x)` to `(x, y)`. -/
theorem piLUT_getElem! (x y : Fin 5) :
    piLUT[((x + 3 * y : Fin 5) : ℕ) + 5 * x]! = x + 5 * y := by
  revert x y
  decide

theorem piLUT_nodup : ((List.range 25).map (piLUT[·]!)).Nodup := by decide

theorem piLUT_lt : ∀ i ∈ List.range 25, piLUT[i]! < 25 := by decide

theorem size_round (s : Array UInt64) (rc : UInt64) : (round s rc).size = 25 := by
  simp [round]

/-- The vendored round computes `roundBits` on the bits of its lanes. -/
theorem laneBit_round (s : Array UInt64) (rc : UInt64) :
    laneBit (round s rc) = roundBits rc.toNat (laneBit s) := by
  unfold round
  extract_lets C D s1 B s2
  have hidx (x y : Fin 5) : (x : ℕ) + 5 * y < 25 := by omega
  have hC (x : Fin 5) (z : Fin 64) : C[(x : ℕ)]!.toBitVec.getLsbD z = column (laneBit s) x z := by
    simp [C, column, laneBit]
  have hD (x : Fin 5) (z : Fin 64) : D[(x : ℕ)]!.toBitVec.getLsbD z =
      (column (laneBit s) (x + 4) z ^^ column (laneBit s) (x + 1) (z - 1)) := by
    simp only [D, getElem!_map_range x.isLt, UInt64.toBitVec_xor, BitVec.getLsbD_xor,
      getLsbD_rotl64 _ (by decide : 1 < 64)]
    have h1 : ((x : ℕ) + 1) % 5 = ((x + 1 : Fin 5) : ℕ) := by simp [Fin.val_add]
    have h4 : ((x : ℕ) + 4) % 5 = ((x + 4 : Fin 5) : ℕ) := by simp [Fin.val_add]
    rw [h1, h4, hC, hC]
    rfl
  have hs1 (x y : Fin 5) (z : Fin 64) :
      s1[(x : ℕ) + 5 * y]!.toBitVec.getLsbD z = thetaBits (laneBit s) x y z := by
    simp only [s1, getElem!_map_range (hidx x y), UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    rw [show ((x : ℕ) + 5 * y) % 5 = x by omega, hD]
    rfl
  have hB (x y : Fin 5) (z : Fin 64) :
      B[(x : ℕ) + 5 * y]!.toBitVec.getLsbD z = piBits (rhoBits (thetaBits (laneBit s))) x y z := by
    rw [← piLUT_getElem!]
    simp only [B]
    rw [Array.getElem!_foldl_set! (fun i => piLUT[i]!) _ piLUT_nodup
      (fun i hi => by simpa using piLUT_lt i hi) (by simp; omega),
      show rhoLUT[((x + 3 * y : Fin 5) : ℕ) + 5 * x]! = rhoOffset (x + 3 * y) x from rfl,
      getLsbD_rotl64 _ (rhoOffset_lt (x + 3 * y) x), hs1]
    rfl
  have hs2 (x y : Fin 5) (z : Fin 64) :
      s2[(x : ℕ) + 5 * y]!.toBitVec.getLsbD z =
        chiBits (piBits (rhoBits (thetaBits (laneBit s)))) x y z := by
    simp only [s2, getElem!_map_range (hidx x y), UInt64.toBitVec_xor, UInt64.toBitVec_and,
      UInt64.toBitVec_not, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not]
    rw [show ((x : ℕ) + 5 * y) % 5 = x by omega, show ((x : ℕ) + 5 * y) / 5 = y by omega]
    have h1 : ((x : ℕ) + 1) % 5 = ((x + 1 : Fin 5) : ℕ) := by simp [Fin.val_add]
    have h2 : ((x : ℕ) + 2) % 5 = ((x + 2 : Fin 5) : ℕ) := by simp [Fin.val_add]
    rw [h1, h2, hB, hB, hB]
    simp [chiBits]
  funext x y z
  have hsize : 0 < s2.size := by simp [s2]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [laneBit, Fin.isValue, Fin.val_zero, mul_zero, add_zero]
    rw [Array.getElem!_set!_self _ _ _ hsize, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    have h := hs2 0 0 z
    simp only [Fin.isValue, Fin.val_zero, mul_zero, add_zero] at h
    rw [h, ← BitVec.testBit_toNat, UInt64.toNat_toBitVec]
    simp [roundBits, iotaBits]
  · have hne : 0 ≠ (x : ℕ) + 5 * y := by
      intro h
      apply h0
      constructor <;> ext <;> simp <;> omega
    simp only [laneBit]
    rw [Array.getElem!_set!_ne _ _ _ _ hne, hs2]
    simp [roundBits, iotaBits, h0]

end GordieHowe.Keccak
