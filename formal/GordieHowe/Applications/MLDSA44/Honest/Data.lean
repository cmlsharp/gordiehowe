-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.Hash
public import GordieHowe.Applications.MLDSA44.System.Honest
public import GordieHowe.Applications.MLDSA44.System.Fields
public import GordieHowe.Applications.MLDSA44.Native.System.Honest

@[expose] public section

/-!
# GordieHowe: the honest data of domain `H`'s hash

The honest hash inputs of an ML-DSA-44 honest input (`honestData`: `tr = H(pk)`, the message
buffer padded by SHAKE256, `μ` from the absorbed state, `w1Encode(w1)`), whose ten permutation
inputs (`HashData.states`) are the honest Keccak inputs of `GordieHowe.MLDSA44.PoP.Native`
(`GordieHowe.MLDSA44.Native.honestStarts`: `KeccakTrace.spongeStart` of each call's input), so the honest facts
of `GordieHowe.MLDSA44.PoP.Native` (the outputs are SHAKE256's, `c̃'` is the input's `c̃`) read through them.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch
open Native (honestW1Bytes honestMsg noCtx trWires)

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K] [CharP K 2] {L : ℕ}

/-- **The bytes of `tr`** of an honest input, `0` past `64`. -/
-- spec-side
def trNat (y : MLDSA44.PoP.HonestInput 0 L) (k : ℕ) : ℕ :=
  if h : k < 64 then (MLDSA44.PoP.Compose.trOf y.key ⟨k, h⟩).toNat else 0

/-- **The message bytes** of an honest input, `0` past `L`. -/
-- spec-side
def msgNat (y : MLDSA44.PoP.HonestInput 0 L) (k : ℕ) : ℕ :=
  if h : k < L then (y.message ⟨k, h⟩).toNat else 0

/-- **The bytes of `w1Encode(w1)`** of an honest input, `0` past `768`. -/
-- spec-side
noncomputable def w1Nat (y : MLDSA44.PoP.HonestInput 0 L) (k : ℕ) : ℕ :=
  if h : k < 768 then (honestW1Bytes y ⟨k, h⟩).toNat else 0

/-- **The honest hash inputs before `μ`**: `tr`, the padded message buffer. -/
-- spec-side
def data0 (y : MLDSA44.PoP.HonestInput 0 L) : HashData K :=
  ⟨fun j => constBit (trNat y (j / 8)) (j % 8),
    fun j => constBit (bufNat L (msgNat y) (66 + j / 8)) (j % 8), fun _ => 0, fun _ => 0⟩

/-- **The honest hash inputs** (`HashData`): `tr`, the padded message buffer, `μ` the first `512`
bits of Keccak-f of the absorbed state, `w1Encode(w1)`.

Running time: one Keccak-f permutation on a bit state. This running time is argued here, not proved
in Lean. -/
-- spec-side
noncomputable def honestData (y : MLDSA44.PoP.HonestInput 0 L) : HashData K :=
  { data0 y with
    mu := fun j => RealizedProgram.stateBit (iterRounds (data0 (K := K) y).muState 24) j
    w1 := fun j => constBit (w1Nat y (j / 8)) (j % 8) }

/-- **The honest data are bits.** -/
theorem honestData_bool (y : MLDSA44.PoP.HonestInput 0 L) : (honestData (K := K) y).Bool where
  tr _ := constBit_bool _ _
  buf _ := constBit_bool _ _
  mu j := RealizedProgram.stateBit_bool (iterRounds_allBool (HashData.states_bool (D := data0 y)
    ⟨fun _ => constBit_bool _ _, fun _ => constBit_bool _ _, fun _ => Or.inl rfl,
      fun _ => Or.inl rfl⟩ 0) 24) j
  w1 _ := constBit_bool _ _

/-- **`μ`'s input byte `i`, bit `b`**: `tr`, two zero bytes, the message. -/
theorem muInput_bit (y : MLDSA44.PoP.HonestInput 0 L) (i : Fin (64 + (2 + (0 + L)))) (b : Fin 8) :
    HashCircuit.muInput (trWires y.pk) noCtx (honestMsg (KH := K) y) i b =
      if (i : ℕ) < 64 then constBit (trNat y i) b else if (i : ℕ) < 66 then 0
      else constBit (msgNat y (i - 66)) b := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have hi := i.isLt
    rw [HashCircuit.muInput, Fin.append_left]
    simp only [Fin.val_castAdd, if_pos hi, Falcon512.HashCircuit.byteWires, trWires,
      Falcon512.HashCircuit.wiresOfByteVec, trNat, dif_pos hi]
    congr 2
    · show MLDSA44.PoP.Compose.trOf (Native.Statement.pk y.pk) _ =
        MLDSA44.PoP.Compose.trOf (Native.Statement.pk y.pk) _
      congr 1
      ext
      show (8 * (i : ℕ) + b) / 8 = i
      omega
    · omega
  · rw [HashCircuit.muInput, Fin.append_right]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hj := j.isLt
      rw [Fin.append_left]
      simp only [Fin.val_natAdd, Fin.val_castAdd, show ¬ (64 + (j : ℕ) < 64) by omega, if_false,
        show 64 + (j : ℕ) < 66 by omega, if_true]
      fin_cases j <;> simp [Shake256.constByte, constBit]
    · rw [Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · exact Fin.elim0 j
      · have hj := j.isLt
        rw [Fin.append_right]
        simp only [Fin.val_natAdd, show ¬ (64 + (2 + (0 + (j : ℕ))) < 64) by omega, if_false,
          show ¬ (64 + (2 + (0 + (j : ℕ))) < 66) by omega, Falcon512.HashCircuit.byteWires, honestMsg,
          Falcon512.HashCircuit.wiresOfByteVec, msgNat]
        rw [dif_pos (by omega)]
        have h1 : (⟨(8 * (j : ℕ) + b) / 8, by omega⟩ : Fin L) = ⟨64 + (2 + (0 + (j : ℕ))) - 66, by omega⟩ :=
          Fin.ext (by show (8 * (j : ℕ) + b) / 8 = 64 + (2 + (0 + (j : ℕ))) - 66; omega)
        rw [h1, show (8 * (j : ℕ) + b) % 8 = b by omega]

theorem constBit_zero' (b : ℕ) : constBit (K := K) 0 b = 0 := by simp [constBit]

/-- **The honest absorbed state of `μ` is `Native`'s**: `xorinBlock` of `μ`'s padded block
(`KeccakTrace.spongeStart` at block `0`). -/
theorem muState_eq_spongeStart (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) :
    (data0 (K := K) y).muState =
      spongeStart .shake256 (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg (KH := K) y)) 0 := by
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (64 + (2 + (0 + L))) = 1 := by
    unfold Shake256.absorbBlocks
    change (64 + (2 + (0 + L))) / 136 + 1 = 1
    omega
  show _ = Shake256.xorinBlock .shake256 (fun _ _ _ => 0) (Shake256.paddedByte .shake256 _ 0)
  rw [show (fun _ _ _ => (0 : K)) = RealizedProgram.stateOf (fun _ => 0) from rfl,
    xorinBlock_stateOf _ (fun j => if j < 512 then (data0 (K := K) y).tr j else if j < 528 then 0
      else (data0 (K := K) y).buf (j - 528)) _ (fun i b => ?_)]
  · unfold HashData.muState
    refine stateOf_congr fun j hj => ?_
    split_ifs <;> simp
  · have hr : Shake256.SpongeSpec.shake256.rate = 136 := rfl
    have hi : (i : ℕ) < 136 := hr ▸ i.isLt
    have hb := b.isLt
    rw [paddedByte_bit, hab, show 136 * 0 + (i : ℕ) = i by ring]
    simp only [data0]
    by_cases h64 : (i : ℕ) < 64
    · rw [dif_pos (by omega), muInput_bit, if_pos (by simpa using h64),
        if_neg (by omega), add_zero, if_pos (by omega),
        show (8 * (i : ℕ) + b) / 8 = i by omega, show (8 * (i : ℕ) + b) % 8 = b by omega]
    · by_cases h66 : (i : ℕ) < 66
      · rw [dif_pos (by omega), muInput_bit, if_neg (by simpa using h64), if_pos (by simpa using h66),
          if_neg (by omega), add_zero, if_neg (by omega), if_pos (by omega)]
      · have h512 : ¬ (8 * (i : ℕ) + b < 512) := by omega
        have h528 : ¬ (8 * (i : ℕ) + b < 528) := by omega
        have hbuf1 : (8 * (i : ℕ) + b - 528) / 8 = i - 66 := by omega
        have hbuf2 : (8 * (i : ℕ) + b - 528) % 8 = b := by omega
        simp only [h512, h528, if_false, hbuf1, hbuf2, show 66 + ((i : ℕ) - 66) = i by omega]
        by_cases hm : (i : ℕ) < 64 + (2 + (0 + L))
        · have h135' : (i : ℕ) ≠ 135 := by omega
          have hlt : (i : ℕ) < 66 + L := by omega
          rw [dif_pos hm, muInput_bit]
          simp only [h64, h66, if_false, h135', false_and, add_zero, bufNat, hlt,
            if_true]
        · rw [dif_neg hm]
          unfold bufNat
          by_cases he : (i : ℕ) = 64 + (2 + (0 + L))
          · have h135' : (i : ℕ) ≠ 135 := by omega
            have hn : ¬ ((i : ℕ) < 66 + L) := by omega
            have he' : (i : ℕ) = 66 + L := by omega
            have e1 : ¬ (64 + (2 + (0 + L)) = 135) := by omega
            have e2 : ¬ (64 + (2 + (0 + L)) < 66 + L) := by omega
            have e3 : 64 + (2 + (0 + L)) = 66 + L := by omega
            have e4 : ¬ (66 + L = 135) := by omega
            simp only [he, e3, e4, lt_irrefl, if_false]
            simp
          · simp only [he, if_false, zero_add, show ¬ ((i : ℕ) < 66 + L) by omega,
              show ¬ ((i : ℕ) = 66 + L) by omega]
            by_cases h135 : (i : ℕ) = 135
            · have : (64 + (2 + L)) ≠ 135 := by omega
              simp [h135, this]
              omega
            · have h' : (i : ℕ) ≠ 64 + (2 + L) := by omega
              simp [h135, h', constBit_zero']

/-- **The bits of `Native`'s honest `μ` are the honest data's** (`μ`'s first `64` squeezed
bytes). -/
theorem honestMu_bit (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) (o : Fin 64) (b : Fin 8) :
    HashBatchedCircuit.honestMu (trWires y.pk) noCtx (honestMsg (KH := K) y) o b =
      (honestData (K := K) y).mu (8 * o + b) := by
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (64 + (2 + (0 + L))) = 1 := by
    unfold Shake256.absorbBlocks
    change (64 + (2 + (0 + L))) / 136 + 1 = 1
    omega
  have ho := o.isLt
  unfold HashBatchedCircuit.honestMu
  rw [squeezeOut_stateOf (fin := fun k => keccakF (spongeStart .shake256
      (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg (KH := K) y)) k))
    (fun k i => RealizedProgram.stateBit (keccakF (spongeStart .shake256
      (HashCircuit.muInput (trWires y.pk) noCtx (honestMsg (KH := K) y)) k)) i)
    (fun k => (RealizedProgram.stateOf_stateBit _).symm) o b (by
      rw [hab]
      unfold Shake256.numBlocks Shake256.squeezeBlocks
      rw [hab]
      change 1 - 1 + (o : ℕ) / 136 < 1 + _
      omega)]
  rw [hab, show 1 - 1 + (o : ℕ) / 136 = 0 by omega, Nat.mod_eq_of_lt (show (o : ℕ) < 136 by omega),
    ← muState_eq_spongeStart y hL]
  rfl

/-- `Native`'s honest `μ` of the honest input. -/
-- spec-side
abbrev muH (y : MLDSA44.PoP.HonestInput 0 L) : Fin 64 → BitWires K 8 :=
  HashBatchedCircuit.honestMu (trWires y.pk) noCtx (honestMsg (KH := K) y)

/-- **`c̃'`'s padded block `k`, byte `i`, bit `b`** is the honest data's padded input `ctIn` at
`1088 k + 8 i + b`. -/
theorem paddedCt_bit (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) {k : ℕ} (hk : k < 7)
    (i : Fin Shake256.SpongeSpec.shake256.rate) (b : Fin 8) :
    Shake256.paddedByte Shake256.SpongeSpec.shake256
        (HashCircuit.commitInput (muH (K := K) y) (Native.honestW1 y)) k i b =
      (honestData (K := K) y).ctIn (1088 * k + (8 * i + b)) := by
  have hr : Shake256.SpongeSpec.shake256.rate = 136 := rfl
  have hi : (i : ℕ) < 136 := hr ▸ i.isLt
  have hb := b.isLt
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (64 + 768) = 7 := rfl
  rw [paddedByte_bit, hab]
  unfold HashData.ctIn
  by_cases h64 : 136 * k + (i : ℕ) < 64
  · have hj : 1088 * k + (8 * i + b) < 512 := by omega
    rw [dif_pos (by omega), if_pos hj,
      show (HashCircuit.commitInput (muH (K := K) y) (Native.honestW1 y))
        ⟨136 * k + i, by omega⟩ = muH y ⟨136 * k + i, h64⟩ from by
          rw [show (⟨136 * k + i, by omega⟩ : Fin (64 + 768)) = Fin.castAdd 768 ⟨136 * k + i, h64⟩
            from rfl, HashCircuit.commitInput, Fin.append_left],
      if_neg (by omega), add_zero]
    simp only [muH]
    rw [honestMu_bit y hL]
    congr 1
    show 8 * (136 * k + (i : ℕ)) + b = 1088 * k + (8 * i + b)
    ring
  · by_cases hlt : 136 * k + (i : ℕ) < 832
    · have hj : ¬ (1088 * k + (8 * i + b) < 512) := by omega
      have hj2 : 1088 * k + (8 * i + b) < 6656 := by omega
      rw [dif_pos (by omega), if_neg hj, if_pos hj2, if_neg (by omega), add_zero]
      rw [show (⟨136 * k + i, by omega⟩ : Fin (64 + 768)) =
          Fin.natAdd 64 ⟨136 * k + i - 64, by omega⟩ from
            Fin.ext (show 136 * k + (i : ℕ) = 64 + (136 * k + i - 64) by omega),
        HashCircuit.commitInput, Fin.append_right]
      simp only [Falcon512.HashCircuit.byteWires, Native.honestW1, Falcon512.HashCircuit.wiresOfByteVec,
        honestData, w1Nat]
      rw [dif_pos (by omega)]
      have e1 : (8 * (136 * k + (i : ℕ) - 64) + b) / 8 = (1088 * k + (8 * i + b) - 512) / 8 := by
        omega
      have e2 : (8 * (136 * k + (i : ℕ) - 64) + b) % 8 = (1088 * k + (8 * i + b) - 512) % 8 := by
        omega
      simp only [e1, e2]
    · have hj : ¬ (1088 * k + (8 * i + b) < 512) := by omega
      have hj2 : ¬ (1088 * k + (8 * i + b) < 6656) := by omega
      rw [dif_neg (by omega), if_neg hj, if_neg hj2]
      by_cases he : 136 * k + (i : ℕ) = 832
      · have hj6 : 1088 * k + (8 * (i : ℕ) + b) - 6656 = b := by omega
        rw [if_pos (by omega), if_neg (by omega), add_zero, constBit_1F hb, hj6]
        by_cases hb5 : (b : ℕ) < 5
        · rw [if_pos hb5, if_pos (Or.inl hb5)]
        · rw [if_neg hb5, if_neg (by omega)]
      · rw [if_neg (by omega), zero_add]
        by_cases h135 : (i : ℕ) = 135 ∧ k = 6
        · have hj6 : 1088 * k + (8 * (i : ℕ) + b) - 6656 = 952 + b := by omega
          rw [if_pos (by omega), constBit_80 hb, hj6]
          by_cases hb7 : (b : ℕ) = 7
          · rw [if_pos hb7, if_pos (Or.inr (by omega))]
          · rw [if_neg hb7, if_neg (by omega)]
        · have hgt : 1088 * k + (8 * (i : ℕ) + b) - 6656 ≥ 5 := by omega
          have hne : 1088 * k + (8 * (i : ℕ) + b) - 6656 ≠ 959 := by omega
          rw [if_neg (by omega), if_neg (by omega)]

/-- **The honest absorbed states of `c̃'` are `Native`'s** (`KeccakTrace.spongeStart` of
`μ ‖ w1`). -/
theorem ctState_eq_spongeStart (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) :
    ∀ k, k < 7 → (honestData (K := K) y).ctState k =
      spongeStart .shake256 (HashCircuit.commitInput (muH (K := K) y) (Native.honestW1 y)) k
  | 0, _ => by
    show _ = Shake256.xorinBlock .shake256 (fun _ _ _ => 0) (Shake256.paddedByte .shake256 _ 0)
    rw [show (fun _ _ _ => (0 : K)) = RealizedProgram.stateOf (fun _ => 0) from rfl,
      xorinBlock_stateOf _ (fun j => (honestData (K := K) y).ctIn (1088 * 0 + j)) _
        (fun i b => paddedCt_bit y hL (by norm_num) i b)]
    unfold HashData.ctState
    refine stateOf_congr fun j hj => ?_
    split_ifs <;> simp
  | k + 1, hk => by
    have ih := ctState_eq_spongeStart y hL k (by omega)
    show _ = if k + 1 ≤ (64 + 768) / Shake256.SpongeSpec.shake256.rate then _ else _
    rw [if_pos (by change k + 1 ≤ 832 / 136; omega), ← ih,
      ← RealizedProgram.stateOf_stateBit (iterRounds ((honestData (K := K) y).ctState k) 24),
      xorinBlock_stateOf _ (fun j => (honestData (K := K) y).ctIn (1088 * (k + 1) + j)) _
        (fun i b => paddedCt_bit y hL hk i b)]
    rw [HashData.ctState.eq_2]
    refine stateOf_congr fun j hj => ?_
    split_ifs <;> simp

/-- `Native`'s honest `c̃'` of the honest input. -/
-- spec-side
noncomputable abbrev ctH (y : MLDSA44.PoP.HonestInput 0 L) : Fin 32 → BitWires K 8 :=
  HashBatchedCircuit.honestCommit (trWires y.pk) noCtx (honestMsg (KH := K) y)
    (Native.honestW1 y)

/-- **The bits of `Native`'s honest `c̃'`** are the last absorb's output bits. -/
theorem honestCommit_bit (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) (o : Fin 32) (b : Fin 8) :
    ctH (K := K) y o b = RealizedProgram.stateBit (iterRounds ((honestData (K := K) y).ctState 6) 24) (8 * o + b) := by
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 (64 + 768) = 7 := rfl
  have ho := o.isLt
  simp only [ctH]
  unfold HashBatchedCircuit.honestCommit
  rw [squeezeOut_stateOf (fin := fun k => keccakF (spongeStart .shake256
      (HashCircuit.commitInput (muH (K := K) y) (Native.honestW1 y)) k))
    (fun k i => RealizedProgram.stateBit (keccakF (spongeStart .shake256
      (HashCircuit.commitInput (muH (K := K) y) (Native.honestW1 y)) k)) i)
    (fun k => (RealizedProgram.stateOf_stateBit _).symm) o b (by
      rw [hab]
      unfold Shake256.numBlocks Shake256.squeezeBlocks
      rw [hab]
      change 7 - 1 + (o : ℕ) / 136 < 7 + _
      omega)]
  rw [hab, show 7 - 1 + (o : ℕ) / 136 = 6 by omega, Nat.mod_eq_of_lt (show (o : ℕ) < 136 by omega),
    ← ctState_eq_spongeStart y hL 6 (by norm_num)]
  rfl

/-- **The honest absorbed state of the stream is `Native`'s** (`KeccakTrace.spongeStart` of
`c̃'` at block `0`). -/
theorem sbState_eq_spongeStart (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) :
    (honestData (K := K) y).sbState = spongeStart .shake256 (ctH (K := K) y) 0 := by
  show _ = Shake256.xorinBlock .shake256 (fun _ _ _ => 0) (Shake256.paddedByte .shake256 _ 0)
  rw [show (fun _ _ _ => (0 : K)) = RealizedProgram.stateOf (fun _ => 0) from rfl,
    xorinBlock_stateOf _ (fun j => if j < 256 then
        RealizedProgram.stateBit (iterRounds ((honestData (K := K) y).ctState 6) 24) j
      else if j - 256 < 5 ∨ j - 256 = 831 then 1 else 0) _ (fun i b => ?_)]
  · unfold HashData.sbState
    refine stateOf_congr fun j hj => ?_
    split_ifs <;> simp
  · have hr : Shake256.SpongeSpec.shake256.rate = 136 := rfl
    have hi : (i : ℕ) < 136 := hr ▸ i.isLt
    have hb := b.isLt
    have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 32 = 1 := rfl
    rw [paddedByte_bit, hab, show 136 * 0 + (i : ℕ) = i by ring]
    by_cases h32 : (i : ℕ) < 32
    · rw [dif_pos h32, if_neg (by omega), add_zero, if_pos (by omega),
        honestCommit_bit y hL ⟨i, h32⟩ b]
    · rw [dif_neg h32, if_neg (show ¬ (8 * (i : ℕ) + b < 256) by omega)]
      by_cases he : (i : ℕ) = 32
      · have hj : 8 * (i : ℕ) + b - 256 = b := by omega
        rw [if_pos he, if_neg (show ¬ ((i : ℕ) = 135 ∧ 0 = 1 - 1) by omega), add_zero,
          constBit_1F hb, hj]
        by_cases hb5 : (b : ℕ) < 5
        · rw [if_pos hb5, if_pos (Or.inl hb5)]
        · rw [if_neg hb5, if_neg (by omega)]
      · rw [if_neg he, zero_add]
        by_cases h135 : (i : ℕ) = 135
        · have hj : 8 * (i : ℕ) + b - 256 = 824 + b := by omega
          rw [if_pos (show (i : ℕ) = 135 ∧ 0 = 1 - 1 from ⟨h135, rfl⟩), constBit_80 hb, hj]
          by_cases hb7 : (b : ℕ) = 7
          · rw [if_pos hb7, if_pos (Or.inr (by omega))]
          · rw [if_neg hb7, if_neg (by omega)]
        · rw [if_neg (show ¬ ((i : ℕ) = 135 ∧ 0 = 1 - 1) from fun h => h135 h.1),
            if_neg (show ¬ (8 * (i : ℕ) + b - 256 < 5 ∨ 8 * (i : ℕ) + b - 256 = 831) by omega)]

/-- **The honest stream's squeeze state is `Native`'s** (block `1`). -/
theorem sbSqueeze_eq_spongeStart (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32) :
    iterRounds (honestData (K := K) y).sbState 24 = spongeStart .shake256 (ctH (K := K) y) 1 := by
  show _ = if 0 + 1 ≤ 32 / Shake256.SpongeSpec.shake256.rate then _ else _
  rw [if_neg (by change ¬ (1 ≤ 32 / 136); norm_num), sbState_eq_spongeStart y hL]

/-! ## The honest facts of `Native` at domain `H`'s field -/

/-- **The `Native` field data of domain `H`'s field** (`Native.FieldData`): a profile,
an A field and a masking subfield with their instances, and field data over `FH.K` whose selection
field, `θ` and packing basis are `HField`'s. The honest facts of `Native` (the honest
stream, selection and shuffle) are read through it. Instantiated for `GF(2^128)`
(`Native.ROMParams.fieldData`) and `GF(2^256)` (`Native.QROMParams.fieldData`). -/
class MldsaHNativeData (FH : RealizedProgram.FieldInterp) [HField FH] where
  /-- The profile. -/
  P : Native.Params.Profile
  /-- The A field of `Native`'s field data. -/
  F : Type
  /-- The masking subfield of `Native`'s field data. -/
  S : Type
  [instField : Field F]
  [instFintype : Fintype F]
  [instDecEq : DecidableEq F]
  [instCharP : CharP F _root_.MLDSA.modulus]
  [instFieldS : Field S]
  /-- The field data. -/
  D : Native.FieldData P FH.K F S
  /-- The selection field is `HField`'s. -/
  sel_eq : D.sel = HField.sel
  /-- `θ` is `HField`'s. -/
  Θ_eq : D.Θ = HField.Θ
  /-- The packing basis is `HField`'s. -/
  packing_eq : D.packing = HField.packing

attribute [instance] MldsaHNativeData.instField MldsaHNativeData.instFintype MldsaHNativeData.instDecEq
  MldsaHNativeData.instCharP MldsaHNativeData.instFieldS

/-- `GF(2^128)`'s `Native` field data is that of the ROM parameters. -/
instance : MldsaHNativeData RealizedProgram.gf128 where
  P := Native.Params.Profile.rom
  F := MLDSANativeField6
  S := ZMod 8380417
  D := Native.ROMParams.fieldData
  sel_eq := rfl
  Θ_eq := rfl
  packing_eq := rfl

/-- `GF(2^256)`'s `Native` field data is that of the QROM parameters. -/
instance : MldsaHNativeData RealizedProgram.gf256 where
  P := Native.Params.Profile.qrom
  F := MLDSANativeField11
  S := ZMod 8380417
  D := Native.QROMParams.fieldData
  sel_eq := rfl
  Θ_eq := rfl
  packing_eq := rfl

section Legacy

variable {FH : RealizedProgram.FieldInterp} [HField FH] [MldsaHNativeData FH]

/-- **`Native`'s honest stream is the honest stream absorb's and squeeze's output**: byte `o`,
bit `u` is bit `8 (o mod 136) + u` of Keccak-f of the stream's state `o / 136`. -/
theorem sibOut_honest_bit (y : MLDSA44.PoP.HonestInput 0 L) (hL : L ≤ 32)
    (o : Fin Native.sibLen) (u : Fin 8) :
    Native.sibOut (MldsaHNativeData.D (FH := FH)).packing
        (Native.honestStates (MldsaHNativeData.D (FH := FH)).packing y) o u =
      RealizedProgram.stateBit (iterRounds (if (o : ℕ) < 136 then (honestData (K := FH.K) y).sbState
        else iterRounds (honestData (K := FH.K) y).sbState 24) 24) (8 * ((o : ℕ) % 136) + u) := by
  have ho : (o : ℕ) < 272 := o.isLt
  have hab : Shake256.absorbBlocks Shake256.SpongeSpec.shake256 32 = 1 := rfl
  unfold Native.sibOut
  have hf : (fun k : Fin Native.nSib => endOf (HashCircuit.statesOf
      (MldsaHNativeData.D (FH := FH)).packing
      (Native.honestStates (MldsaHNativeData.D (FH := FH)).packing y))
        ((Native.sibCall (msgLen := L)).perm k)) =
      fun k : Fin Native.nSib =>
        (fun k : ℕ => keccakF (spongeStart .shake256 (ctH (K := FH.K) y) k)) k := by
    funext k
    rw [Native.statesOf_honestStates, endOf_trace]
    exact congrArg keccakF (Native.honestStarts_sib y k)
  rw [hf, squeezeOut_stateOf (fin := fun k => keccakF (spongeStart .shake256 (ctH (K := FH.K) y) k))
    (fun k i => RealizedProgram.stateBit (keccakF (spongeStart .shake256 (ctH (K := FH.K) y) k)) i)
    (fun k => (RealizedProgram.stateOf_stateBit _).symm) o u (by
      rw [hab]
      change 1 - 1 + (o : ℕ) / 136 < 2
      omega), hab]
  by_cases h : (o : ℕ) < 136
  · rw [if_pos h, show 1 - 1 + (o : ℕ) / 136 = 0 by omega, ← sbState_eq_spongeStart y hL]
    rfl
  · rw [if_neg h, show 1 - 1 + (o : ℕ) / 136 = 1 by omega, ← sbSqueeze_eq_spongeStart y hL]
    rfl

end Legacy

end GordieHowe.MLDSA44.Native.ROMParams
