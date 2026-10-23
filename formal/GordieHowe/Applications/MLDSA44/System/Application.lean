-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.System.MAC
public import GordieHowe.Applications.MLDSA44.PoP.Native.Algebra

@[expose] public section

/-!
# ML-DSA: the application's readings

The readings of the source assignment that both ML-DSA configurations conclude on: the message and
the commitment hash read from their bits (`messageOf`, `cTildeOf`), the byte views of the hash
inputs (`inputBytes_cTildeOut`, `inputBytes_muInput`), the agreement of the crossings of `w1` and
the challenge (`cross_agree`, `w1_agree`, `w1H_eq`), and the statement check the verifier runs first
(`stmtOk`). The application constraints and the extraction are each configuration's.
-/

namespace GordieHowe.MLDSA44.Native

open IOP RealizedProgram.ProofSystem.PhaseLayout GordieHowe.Bits Params
open _root_.MLDSA.Concrete (sigEncode useHintCoeff)
open scoped NNReal

variable {P : Profile} {KH F S : Type} [Field KH] [Fintype KH] [DecidableEq KH] [Field F]
  [Fintype F] [DecidableEq F] [Field S] [Fintype S] (D : FieldData P KH F S) {msgLen : ℕ}

/-- **The extracted message** (`msg`). -/
-- spec-side
def messageOf (msg : BitWires KH (8 * msgLen)) : Fin msgLen → UInt8 :=
  fun i => (natOfBits (Falcon512.HashCircuit.byteWires msg i)).toUInt8

/-- **The extracted `c̃`**: the bytes of `c̃'`, H's `h2c.c_tilde.out`. -/
-- spec-side
def cTildeOf (a : Source KH F msgLen) : _root_.MLDSA.CommitHashBytes _root_.MLDSA.mldsa44 :=
  Vector.ofFn fun i => (natOfBits (cTildeOut D.packing a.states ⟨i, by
    have := i.isLt
    change (i : ℕ) < 32 at this
    exact this⟩)).toUInt8

omit [Fintype KH] in
/-- A Boolean bit vector's bit is its natural's bit. -/
theorem bit_eq_testBit {m : ℕ} {bits : BitWires KH m} (hb : AllBool bits) (i : Fin m) :
    bits i = 1 ↔ (natOfBits bits).testBit i := by
  have h := Bits.constBit_natOfBits hb i
  rw [SelectFirstTau.constBit_eq_ite_testBit] at h
  rw [← h]
  split_ifs with ht
  · simp [ht]
  · simp [ht]

omit [Fintype KH] in
/-- **The signs are SampleInBall's sign bits** of the stream (`MLDSA44.sampleInBallSign`): bit
`s mod 8` of byte `s / 8`. -/
theorem signBoolsOf_signWires {C : ℕ} {out : Fin (C + 8) → BitWires KH 8}
    (hout : ∀ o, AllBool (out o)) :
    SampleInBall.signBoolsOf (HashCircuit.signWires out) =
      fun s : Fin τ => MLDSA44.sampleInBallSign (fun o => natOfBits (out o)) s := by
  funext s
  have hs : (s : ℕ) < 64 := by have := s.isLt; change (s : ℕ) < 39 at this; omega
  rw [SampleInBall.signBoolsOf, MLDSA44.sampleInBallSign, dite_eq_left hs]
  have h := bit_eq_testBit (hout ⟨(s : ℕ) / 8, by omega⟩) ⟨(s : ℕ) % 8, by omega⟩
  unfold HashCircuit.signWires
  by_cases ht : (natOfBits (out ⟨(s : ℕ) / 8, by omega⟩)).testBit ((s : ℕ) % 8)
  · rw [ht]
    exact decide_eq_true (h.mpr ht)
  · rw [Bool.not_eq_true] at ht
    rw [ht]
    exact decide_eq_false fun h1 => by simp [h.mp h1] at ht

omit [Fintype KH] [Fintype F] [DecidableEq F] [Fintype S] in
/-- The bytes of `c̃'` are the extracted `c̃`. -/
theorem inputBytes_cTildeOut (a : Source KH F msgLen) :
    Shake256.inputBytes (cTildeOut D.packing a.states) = (cTildeOf D a).toList.map UInt8.toNat := by
  apply List.ext_getElem
  · simp only [Shake256.inputBytes, cTildeOf, List.length_ofFn, List.length_map,
      Vector.length_toList]
    rfl
  · intro i hi hj
    simp only [Shake256.inputBytes, cTildeOf, Vector.toList_ofFn, List.getElem_map,
      List.getElem_ofFn]
    rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Bits.natOfBits_lt _)]

omit [Fintype KH] in
theorem toNat_toUInt8_natOfBits (bits : BitWires KH 8) :
    (natOfBits bits).toUInt8.toNat = natOfBits bits := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Bits.natOfBits_lt bits)]

omit [Fintype KH] in
/-- **`μ`'s input reads `tr ‖ frame([], msg)`.** -/
theorem inputBytes_muInput (x : Statement) (msg : BitWires KH (8 * msgLen)) :
    Shake256.inputBytes (HashCircuit.muInput (trWires x) noCtx msg) =
      (List.ofFn fun i => (MLDSA44.PoP.Compose.trOf x.pk i).toNat) ++
        (MLDSA44.frame [] (List.ofFn (messageOf msg))).map UInt8.toNat := by
  rw [Shake256.inputBytes, List.ofFn_add, MLDSA44.frame, List.map_cons, List.map_cons]
  congr 1
  · refine congrArg List.ofFn (funext fun i => ?_)
    simp only [HashCircuit.muInput]
    rw [show Fin.castLE (by omega) i = Fin.castAdd (2 + (0 + msgLen)) i from Fin.ext rfl,
      Fin.append_left]
    exact Falcon512.HashCircuit.natOfBits_byteWires_wiresOfByteVec (K := KH)
      (bytes := fun i => (MLDSA44.PoP.Compose.trOf x.pk i).toNat) (fun i => UInt8.toNat_lt _) i
  · rw [List.ofFn_add, List.ofFn_add]
    simp only [HashCircuit.muInput, Fin.append_right, List.length_nil,
      List.nil_append, List.map_ofFn, Function.comp_def, messageOf, toNat_toUInt8_natOfBits]
    simp [Shake256.natOfBits_constByte]

omit [Fintype KH] [Fintype F] [DecidableEq KH] [DecidableEq F] in
/-- **The crossings agree bit for bit** where their chunks agree (the MAC's source). -/
theorem cross_agree {a : Source KH F msgLen} (h : BitsAgree (xhOf P a) (xaOf P a))
    (t : Fin (P.macWidth * P.nch)) :
    HashCircuit.crossBits a.w1H (cBitsH a) t = 1 ↔ HashCircuit.crossBits a.w1A (cBitsA a) t = 1 := by
  obtain ⟨c, j, rfl⟩ := exists_chunk P t
  exact h.agree c j

omit [Fintype KH] [Fintype F] [DecidableEq KH] [DecidableEq F] in
/-- H's `w1` agrees with A's `hint.w1`. -/
theorem w1_agree {a : Source KH F msgLen} (h : BitsAgree (xhOf P a) (xaOf P a)) (t : Fin (8 * 768)) :
    a.w1H t = 1 ↔ a.w1A t = 1 := by
  have hcov : P.macWidth * P.nch = 6656 := HashCircuit.cover (mw := P.macWidth)
  have h1 := cross_agree h ⟨t, by have := t.isLt; omega⟩
  simp only [HashCircuit.crossBits, t.isLt, dite_true] at h1
  exact h1

variable [CharP KH 2] [CharP F _root_.MLDSA.modulus]

omit [Fintype KH] [Fintype F] [Fintype S] [CharP KH 2] [DecidableEq KH]
  [CharP F _root_.MLDSA.modulus] in
/-- **H's `w1` is the `w1Encode` bit string of A's extracted `w1`** (`MLDSA44.PoP.Native.decodeW1`):
bit `b` of coefficient `c` of polynomial `i` at `(i N + c) 6 + b`. -/
theorem w1H_eq {a : Source KH F msgLen} (h : BitsAgree (xhOf P a) (xaOf P a))
    (hw1H : AllBool a.w1H) (hw1A : AllBool a.w1A) (i : Fin _root_.MLDSA.mldsa44.k)
    (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6) :
    a.w1H ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ =
      Bits.constBit (((MLDSA44.PoP.Native.decodeW1 a.w1A).get i).get c).val b := by
  have hidx : (⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩ :
      Fin (8 * 768)) = ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (nRows * N)) + b, by
        have := HashCircuit.w1Bit_lt i c b
        simp only [finProdFinEquiv_apply_val]
        change 6 * ((c : ℕ) + 256 * i) + b < 8 * 768
        change ((i : ℕ) * 256 + c) * 6 + b < 8 * 768 at this
        omega⟩ := Fin.ext (by
    simp only [finProdFinEquiv_apply_val]
    change ((i : ℕ) * 256 + c) * 6 + b = 6 * ((c : ℕ) + 256 * i) + b
    ring)
  have hbits : AllBool (NativeAlgebraCircuit.outputBits a.w1A (finProdFinEquiv (i, c))) := fun _ => hw1A _
  rw [MLDSA44.PoP.Native.decodeW1_get, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((MLDSA44.PoP.Native.w1Coeff_lt a.w1A i c).trans (by decide)),
    NativeAlgebraCircuit.w1Coeff, SelectFirstTau.constBit_eq_ite_testBit]
  have hiff := bit_eq_testBit hbits b
  have hag := w1_agree h ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, HashCircuit.w1Bit_lt i c b⟩
  rw [hidx] at hag ⊢
  by_cases ht : (natOfBits (NativeAlgebraCircuit.outputBits a.w1A (finProdFinEquiv (i, c)))).testBit b = true
  · simp only [ht, ite_true]
    exact hag.mpr (hiff.mpr ht)
  · simp only [ht, ite_false, Bool.false_eq_true]
    exact (hw1H _).resolve_right fun h1 => ht (hiff.mp (hag.mp h1))

end GordieHowe.MLDSA44.Native
