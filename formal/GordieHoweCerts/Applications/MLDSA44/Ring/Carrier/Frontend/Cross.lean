-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Readings

@[expose] public section

/-!
# GordieHowe frontend: the crossing of the ML-DSA-44 ring carriers

`mac.equal` (predicate `247`; `ring_crossing` and the hash's copies of `μ` and `w1` in
`lib/gordiehowe/examples/rings/mldsa_ring.h`, merged into one MAC per domain pair) is
`cross(H, x, A, y)` with `x` the shared expression `505` (H's `μ`, H's `w1`, then H's decoded
support and sign of each coefficient alternately) and `y` the shared expression `42` (A's
`member.mu`, `hint.w1`, `challenge.c`, in order). The compiler's contract
(`GordieHowe.RealizedProgram.HoldsWith` of a cross-field `equal`) gives the readings' equality
where every reading of `x` is below `2`: `μ` and `w1` are bit views, the support and sign bits by
hypothesis (SampleInBall's soundness).

* `RingCrossAt`, `ringCross`: the crossing on the carrier's readings.
* `crossW1`, `crossSup`, `crossSgn`: the crossing on the native readers of domain `H` and the
  emulated readers of domain `A`, each in the environment read as its program's.
* `w1HBits_eq`, `cPoly_eq`: H's `w1` bits are the bits of A's UseHint outputs, and A's challenge
  polynomial is H's decoded challenge (as `Emulated.w1HBits_eq`, `Emulated.cPolyA_eq`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt)

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

/-! ## The two operands' coordinates -/

section Operands

variable (rd : program.Valuation interp)

/-- The crossing's `x` read through its parts. -/
theorem x_part {i j k : ℕ} (hj : j < 4)
    (hk : k < program.exprLen (([.leaf 71, .leaf 73, .ref 503, .ref 504] : List Expr)[j]'
      (by simpa using hj)))
    (he : ∀ m : IndexMap, (∀ t < 6656, m.entry t = t) →
      (∀ k < 256, m.entry (6656 + 2 * k) = 6656 + k) →
      (∀ k < 256, m.entry (6656 + (2 * k + 1)) = 6912 + k) →
      m.entry i = partBase program [.leaf 71, .leaf 73, .ref 503, .ref 504] j + k) :
    program.evalE rd 1 (.ref 505) i = program.evalE rd 1
      (([.leaf 71, .leaf 73, .ref 503, .ref 504] : List Expr)[j]'(by simpa using hj)) k := by
  obtain ⟨m, hm, hlo, hev, hod⟩ := MldsaCarrierFront.exprH (program := program)
  rw [RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _ MldsaCarrierFront.lt505, hm]
  exact RealizedProgram.evalE_wiring_part rd 1 m _ _ (by simpa using hj) hk (he m hlo hev hod)

/-- **`x` below `512`** is H's `μ` bit. -/
theorem x_mu {t : ℕ} (ht : t < 512) :
    program.evalE rd 1 (.ref 505) t = program.evalE rd 1 (.leaf 71) t :=
  x_part rd (j := 0) (by norm_num) (by simp [exprLen_leaf, MldsaCarrierFront.lens.2.1, ht])
    fun m hlo _ _ => by rw [hlo t (by omega)]; simp [partBase]

/-- **`x` at `512 + t`** is H's `w1` bit `t`. -/
theorem x_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE rd 1 (.ref 505) (512 + t) = program.evalE rd 1 (.leaf 73) t :=
  x_part rd (j := 1) (by norm_num) (by simp [exprLen_leaf, MldsaCarrierFront.lens.2.2.1, ht])
    fun m hlo _ _ => by
      rw [hlo _ (by omega)]
      simp [partBase, exprLen_leaf, MldsaCarrierFront.lens.2.1]

/-- **`x` at `6656 + 2 k`** is H's decoded support of coefficient `k`. -/
theorem x_sup {k : ℕ} (hk : k < 256) :
    program.evalE rd 1 (.ref 505) (6656 + 2 * k) = program.evalE rd 1 (.ref 503) k :=
  x_part rd (j := 2) (by norm_num) (by simp [MldsaCarrierFront.lens.2.2.2.1, hk])
    fun m _ hev _ => by
      rw [hev k hk]
      simp [partBase, exprLen_leaf, MldsaCarrierFront.lens.2.1, MldsaCarrierFront.lens.2.2.1]

/-- **`x` at `6656 + 2 k + 1`** is H's decoded sign of coefficient `k`. -/
theorem x_sgn {k : ℕ} (hk : k < 256) :
    program.evalE rd 1 (.ref 505) (6656 + (2 * k + 1)) = program.evalE rd 1 (.ref 504) k :=
  x_part rd (j := 3) (by norm_num) (by simp [MldsaCarrierFront.lens.2.2.2.2.1, hk])
    fun m _ _ hod => by
      rw [hod k hk]
      simp [partBase, exprLen_leaf, MldsaCarrierFront.lens.2.1, MldsaCarrierFront.lens.2.2.1,
        MldsaCarrierFront.lens.2.2.2.1]

/-- The crossing's `y` read through its parts. -/
theorem y_part {i j k : ℕ} (hj : j < 3)
    (hk : k < program.exprLen (([.leaf 57, .leaf 66, .leaf 62] : List Expr)[j]'
      (by simpa using hj)))
    (he : i = partBase program [.leaf 57, .leaf 66, .leaf 62] j + k) (hi : i < 7168) :
    program.evalE rd 0 (.ref 42) i = program.evalE rd 0
      (([.leaf 57, .leaf 66, .leaf 62] : List Expr)[j]'(by simpa using hj)) k := by
  obtain ⟨m, hm, hid⟩ := MldsaCarrierFront.exprA (program := program)
  rw [RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _
    (by have := MldsaCarrierFront.lt505 (program := program); omega), hm]
  exact RealizedProgram.evalE_wiring_part rd 0 m _ _ (by simpa using hj) hk
    (by rw [hid i hi]; exact he)

/-- **`y` below `512`** is A's `μ` bit. -/
theorem y_mu {t : ℕ} (ht : t < 512) :
    program.evalE rd 0 (.ref 42) t = program.evalE rd 0 (.leaf 57) t :=
  y_part rd (j := 0) (by norm_num) (by simp [exprLen_leaf, MldsaCarrierFront.muSize, ht])
    (by simp [partBase]) (by omega)

/-- **`y` at `512 + t`** is A's `w1` bit `t`. -/
theorem y_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE rd 0 (.ref 42) (512 + t) = program.evalE rd 0 (.leaf 66) t :=
  y_part rd (j := 1) (by norm_num) (by simp [exprLen_leaf, MldsaCarrierFront.lens.2.2.2.2.2, ht])
    (by simp [partBase, exprLen_leaf, MldsaCarrierFront.muSize]) (by omega)

/-- **`y` at `6656 + i`** is A's challenge bit `i`. -/
theorem y_c {i : ℕ} (hi : i < 512) :
    program.evalE rd 0 (.ref 42) (6656 + i) = program.evalE rd 0 (.leaf 62) i :=
  y_part rd (j := 2) (by norm_num)
    (by simp [exprLen_leaf, MldsaCarrierRelation.size62, hi])
    (by simp [partBase, exprLen_leaf, MldsaCarrierFront.muSize, MldsaCarrierFront.lens.2.2.2.2.2])
    (by omega)

end Operands

/-! ## The crossing -/

variable [MLDSA44.HField FH]

/-- **The crossing at a valuation** (`mac.equal`): A's `μ`, `w1` and challenge bits read as
naturals are H's `μ`, `w1`, decoded support and sign. -/
structure RingCrossAt (rd : program.Valuation interp) : Prop where
  /-- The `μ` bits agree. -/
  mu : ∀ t < 512, (interp 0).toNat (program.evalE rd 0 (.leaf 57) t) =
    (interp 1).toNat (program.evalE rd 1 (.leaf 71) t)
  /-- The `w1` bits agree. -/
  w1 : ∀ t < 6144, (interp 0).toNat (program.evalE rd 0 (.leaf 66) t) =
    (interp 1).toNat (program.evalE rd 1 (.leaf 73) t)
  /-- The supports agree. -/
  sup : ∀ k < 256, (interp 0).toNat (program.evalE rd 0 (.leaf 62) (2 * k)) =
    (interp 1).toNat (program.evalE rd 1 (.ref 503) k)
  /-- The signs agree. -/
  sgn : ∀ k < 256, (interp 0).toNat (program.evalE rd 0 (.leaf 62) (2 * k + 1)) =
    (interp 1).toNat (program.evalE rd 1 (.ref 504) k)

/-- An element of domain `H`'s field that is a bit is read below `2`. -/
theorem toNat_lt_two_of_bool1 {x : (interp 1).K} (h : x = 0 ∨ x = 1) :
    (interp 1).toNat x < 2 := by
  rcases h with rfl | rfl
  · exact (MLDSA44.HField.toNat_zero (FH := FH)).symm ▸ Nat.two_pos
  · exact (MLDSA44.HField.toNat_one (FH := FH)).symm ▸ Nat.one_lt_two

/-- **`mac.equal` gives the crossing** wherever the source program holds and H's decoded support
and sign are bits: the compiler's contract (`RealizedProgram.HoldsWith` of a cross-field `equal`)
at its premise, every reading of `x` below `2`. -/
theorem ringCross {e : program.Env interp} (hs : program.SourceSatAt e)
    (hsup : ∀ k < 256, (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 503) k) < 2)
    (hsgn : ∀ k < 256, (interp 1).toNat (program.evalE (program.reader e) 1 (.ref 504) k) < 2) :
    RingCrossAt (program.reader e) := by
  obtain ⟨hl, hsrc, c, hc⟩ := MldsaCarrierFront.cross (program := program)
  have hmac : program.HoldsAt e (program.predicate 247).body :=
    hs.preds _ (RealizedProgram.predicate_mem hl) hsrc
  rw [hc] at hmac
  obtain ⟨-, hxy⟩ := hmac
  change (∀ i < program.exprLen (.ref 505),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 505) i) < 2) → ∀ i < program.exprLen (.ref 505),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 505) i) =
      (interp (program.domainField 0)).toNat (program.evalE (program.reader e)
        (program.domainField 0) (.ref 42) i) at hxy
  rw [MldsaCarrierFront.domains.2, MldsaCarrierFront.domains.1, MldsaCarrierFront.lens.1] at hxy
  set rd := program.reader e
  have hpre : ∀ i < 7168, (interp 1).toNat (program.evalE rd 1 (.ref 505) i) < 2 := by
    intro i hi
    by_cases h1 : i < 512
    · rw [x_mu rd h1]
      exact toNat_lt_two_of_bool1
        (RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaCarrierFront.bitViews.1 1 i)
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [x_w1 rd ht]
      exact toNat_lt_two_of_bool1
        (RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaCarrierFront.bitViews.2 1 t)
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6656 + 2 * k ∨ i = 6656 + (2 * k + 1) :=
        ⟨(i - 6656) / 2, by omega, by omega⟩
      · rw [x_sup rd hk]
        exact hsup k hk
      · rw [x_sgn rd hk]
        exact hsgn k hk
  have heq := hxy hpre
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have h := heq t (by omega)
    rw [x_mu rd ht, y_mu rd ht] at h
    exact h.symm
  · have h := heq (512 + t) (by omega)
    rw [x_w1 rd ht, y_w1 rd ht] at h
    exact h.symm
  · have h := heq (6656 + 2 * k) (by omega)
    rw [x_sup rd hk, y_c rd (by omega)] at h
    exact h.symm
  · have h := heq (6656 + (2 * k + 1)) (by omega)
    rw [x_sgn rd hk, y_c rd (by omega)] at h
    exact h.symm

/-! ## The crossing on the proofs of possession's readers -/

section Readers

variable {e : program.Env interp} (h : RingCrossAt (program.reader e))
include h

/-- **The `w1` crossing on the readers**: A's `hint.w1` bits read as the emulated program's and
H's `w1` bits read as the native program's agree as naturals. -/
theorem crossW1 (t : Fin (8 * 768)) :
    (interp 0).toNat (Emulated.w1ABits ((emu).reader (pullA e)) t) =
      (interp 1).toNat (MLDSA44.w1HBits ((nat).reader (pullH e)) t) := by
  rw [w1ABits_pullA, w1HBits_pull]
  exact h.w1 t t.isLt

/-- **The support crossing on the readers**: A's support bit is H's decoded support. -/
theorem crossSup (k : Fin _root_.MLDSA.ringDegree) :
    (interp 0).toNat (cBits (program.reader e) k 0) =
      MLDSA44.supH ((nat).reader (pullH e)) k := by
  rw [supH_pull e k]
  unfold cBits
  simpa using h.sup k k.isLt

/-- **The sign crossing on the readers**: A's sign bit is H's decoded sign. -/
theorem crossSgn (k : Fin _root_.MLDSA.ringDegree) :
    (interp 0).toNat (cBits (program.reader e) k 1) =
      MLDSA44.sgnH ((nat).reader (pullH e)) k := by
  rw [sgnH_pull e k]
  unfold cBits
  simpa using h.sgn k k.isLt

variable [RealizedProgram.PrimeCastField F0 pGold]

/-- **A's challenge polynomial is H's decoded challenge**, given the crossing and the Booleanity
of A's challenge bits. -/
theorem cPoly_eq (hb : ∀ k s, cBits (program.reader e) k s = 0 ∨ cBits (program.reader e) k s = 1) :
    cPoly (program.reader e) = MLDSA44.ofCoeff fun k =>
      (MLDSA44.chalH ((nat).reader (pullH e)) k : _root_.MLDSA.Coeff) := by
  unfold cPoly
  refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
  rw [Emulated.bitCoeff_eq_toNat (FH := FH) (hb k 0),
    Emulated.bitCoeff_eq_toNat (FH := FH) (hb k 1),
    crossSup h k, crossSgn h k]
  change _ = (((MLDSA44.supH ((nat).reader (pullH e)) k : ℤ) -
    2 * (MLDSA44.sgnH ((nat).reader (pullH e)) k : ℤ) : ℤ) : _root_.MLDSA.Coeff)
  push_cast
  ring

/-- **H's `w1` bits are the bits of A's UseHint outputs**, given the crossing and the Booleanity of
A's `w1` bits (as `Emulated.w1HBits_eq`). -/
theorem w1HBits_eq (hb : AllBool (Emulated.w1ABits ((emu).reader (pullA e))))
    (i : Fin _root_.MLDSA.mldsa44.k) (c : Fin _root_.MLDSA.ringDegree) (b : Fin 6) :
    MLDSA44.w1HBits ((nat).reader (pullH e))
        ⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b, MLDSA44.HashCircuit.w1Bit_lt i c b⟩ =
      Bits.constBit (((MLDSA44.PoP.Native.decodeW1
        (Emulated.w1ABits ((emu).reader (pullA e)))).get i).get c).val b := by
  have hidx : (⟨((i : ℕ) * _root_.MLDSA.ringDegree + c) * 6 + b,
      MLDSA44.HashCircuit.w1Bit_lt i c b⟩ : Fin (8 * 768)) =
      ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, by
        have := MLDSA44.HashCircuit.w1Bit_lt i c b
        simp only [finProdFinEquiv_apply_val]
        change 6 * ((c : ℕ) + 256 * i) + b < 8 * 768
        change ((i : ℕ) * 256 + c) * 6 + b < 8 * 768 at this
        omega⟩ := Fin.ext (by
    simp only [finProdFinEquiv_apply_val]
    change ((i : ℕ) * 256 + c) * 6 + b = 6 * ((c : ℕ) + 256 * i) + b
    ring)
  set ard := (emu).reader (pullA e)
  have hbits : AllBool (MLDSA44.NativeAlgebraCircuit.outputBits (Emulated.w1ABits ard)
      (finProdFinEquiv (i, c))) := fun _ => hb _
  rw [MLDSA44.PoP.Native.decodeW1_get, ZMod.val_natCast,
    Nat.mod_eq_of_lt ((MLDSA44.PoP.Native.w1Coeff_lt (Emulated.w1ABits ard) i c).trans
      (by decide)),
    MLDSA44.NativeAlgebraCircuit.w1Coeff, MLDSA44.SelectFirstTau.constBit_eq_ite_testBit]
  have hiff := MLDSA44.Native.bit_eq_testBit hbits b
  rw [hidx]
  set t : Fin (8 * 768) := ⟨mldsa44.r1_bits * (finProdFinEquiv (i, c) : Fin (4 * 256)) + b, _⟩
  have hA : Emulated.w1ABits ard t = 1 ↔ (natOfBits (MLDSA44.NativeAlgebraCircuit.outputBits
      (Emulated.w1ABits ard) (finProdFinEquiv (i, c)))).testBit b := hiff
  have hlt : (interp 0).toNat (Emulated.w1ABits ard t) < 2 := by
    rw [Emulated.toNat_bool (FH := FH) (hb t)]
    split_ifs <;> omega
  have hH := MLDSA44.HField.eq_of_toNat_lt_two (crossW1 h t).symm hlt
  rw [hH]
  have hone : Emulated.w1ABits ard t = 1 ↔ (interp 0).toNat (Emulated.w1ABits ard t) = 1 := by
    rw [Emulated.toNat_bool (FH := FH) (hb t)]
    split_ifs with h' <;> simp [h']
  by_cases ht : (natOfBits (MLDSA44.NativeAlgebraCircuit.outputBits (Emulated.w1ABits ard)
      (finProdFinEquiv (i, c)))).testBit b
  · rw [if_pos (hone.1 (hA.2 ht)), if_pos ht]
  · rw [if_neg fun h' => ht (hA.1 (hone.2 h')), if_neg ht]

end Readers

end GordieHowe.MLDSA44.Ring.Carrier
