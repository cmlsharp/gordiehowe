-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestMember

@[expose] public section

/-!
# GordieHowe: the signature relation of the ML-DSA-44 ring carriers at the honest values

The signature relation of an ML-DSA-44 ring carrier (`carrier_relation` in
`lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) commits the quotient `q′`
(`signature.relation.q`, value `65`, bound to its digits) of `w′ − (Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c)`
by `q` at the offset `qlo = −134137327`, and the high halves `Q` (`signature.Q`, value `66`) of the
rows' products by `X^256 + 1`; its rows `signature.relation.0 … 3` (predicates `1 … 4`) are the row
polynomials `E_i + (X^256 + 1) Q_i + T_i c − Σ_j A_ij z_j` read at `r`. At the source environment of
the honest values:

* **The honest integer** (`sigZ_dvd`, `sigZ_bounds`): `sigZ` is a multiple of `q` (the honest `w′`
  is `computeWApprox(Â, c, z, t1)`, `Emulated.Rows.congruent_of_computeWApprox`) within
  `±(1024 (q − 1) · 130993 + 256 (q − 1) + q)`, so the honest quotient `quotN` lies in `[0, qmax]`.
* **The honest readings** (`spectraOf_honest`, `rd_w`, `rd_z`, `rd_c`, `rd_q`, `rd_Q`): the spectra
  are the signer's key's transforms; `w′` reads `wNR`, `z` the centered response, the challenge
  bits the challenge's support and sign, the quotient `quotN`, the high halves `qHonC`.
* **The predicates** (`sig_row`, `qRange_holds`): row `rel0 + i`'s polynomial is `0`: the
  products split into negacyclic and high halves (`Ops.polyOf_mul_polyOf`), the honest high halves
  cancel theirs, and the negacyclic part, the casts of integers (`Ops.intCast_sum_negCoef`), cancels
  `E_i = w′_i − q (q′_i + qlo)`, the cast of `w′ − sigZ`; the quotient lies in its range.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open MLDSA44.NativeAlgebraCircuit (flat)
open MLDSA44.NativeAlgebraCircuit.Honest (wCoeff zCentered)
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt cA)
open MLDSA44.Emulated (MldsaELayout MldsaEAlgebra MldsaEmulatedHonest DigitLayout rdA fm fmz)

set_option linter.unusedSectionVars false

attribute [local instance] factPrimeModulus

variable {msgLen : ℕ}

/-! ## The program facts -/

/-- **The program facts of a carrier's quotient** (decided per carrier): `signature.relation.q`
(predicate `18`) bounds the quotient (value `65`) below some `B > qmax = 268274655`; the quotient
lies in field `0` with `1024` coordinates. -/
class MldsaCarrierQuot (program : RealizedProgram) where
  /-- `signature.relation.q`, the quotient's range. -/
  qPred : ℕ
  /-- `signature.relation.q` bounds the quotient. -/
  qRange : ∃ r B, (program.predicate qPred).body = .mem 0 [.leaf 65] (.range B) r ∧ 268274655 < B
  /-- The quotient lies in field `0`. -/
  field65 : program.valueField 65 = 0
  /-- The quotient has `1024` coordinates. -/
  size65 : (program.value 65).size = 1024
  /-- The quotient is a value of the program. -/
  lt65 : 65 < program.values.length

/-! ## Digits -/

section Digits

variable {program : RealizedProgram} {I : RealizedProgram.Interp} [RealizedProgram.PrimeCastField (I 0) pGold]

/-- **The digits' sum from position `t` on reads its terms** in field `0`. -/
theorem evalE_exprFrom0 (rd : program.Valuation I) (b j : ℕ) :
    ∀ (t : ℕ) (acc : Expr) (ds : List ℕ), b ^ (t + ds.length) ≤ pGold →
      program.evalE rd 0 (DigitLayout.exprFrom b t acc ds) j =
        program.evalE rd 0 acc j + ∑ s ∈ Finset.range ds.length,
          ((b ^ (t + s) : ℕ) : (I 0).K) * program.evalE rd 0 (.leaf (ds.getD s 0)) j
  | t, acc, [], _ => by simp
  | t, acc, d :: ds, hb => by
    have hbt : b ^ t < pGold := by
      rcases Nat.lt_or_ge b 2 with h | h
      · exact (pow_le_one₀ (Nat.zero_le b) (by omega)).trans_lt (by norm_num [pGold])
      · exact (Nat.pow_lt_pow_right h (by simp)).trans_le hb
    rw [DigitLayout.exprFrom_cons, evalE_exprFrom0 rd b j (t + 1) _ _
        (by rw [List.length_cons, ← add_assoc, add_right_comm] at hb; exact hb), List.length_cons,
      Finset.sum_range_succ', evalE_add, evalE_scale_const, decode_lt0 hbt]
    have hs : ∑ s ∈ Finset.range ds.length, ((b ^ (t + (s + 1)) : ℕ) : (I 0).K) *
        program.evalE rd 0 (.leaf ((d :: ds).getD (s + 1) 0)) j =
        ∑ s ∈ Finset.range ds.length, ((b ^ (t + 1 + s) : ℕ) : (I 0).K) *
          program.evalE rd 0 (.leaf (ds.getD s 0)) j :=
      Finset.sum_congr rfl fun s _ => by
        rw [List.getD_cons_succ, show t + (s + 1) = t + 1 + s by omega]
    rw [hs, List.getD_cons_zero, Nat.add_zero]
    ring

/-- **A value bound to digits reads the natural they hold** in field `0`: where digit `s` reads
digit `s` of a natural `n` the digits hold (`DigitLayout.Fits` at a bound above `n`). -/
theorem evalE_digits0 {D : DigitLayout} {n N : ℕ} (hD : D.Fits N) (hn : n < N)
    (rd : program.Valuation I) (j : ℕ)
    (h : ∀ s (hs : s < D.ids.length), program.evalE rd 0 (.leaf D.ids[s]) j =
      (DigitLayout.digitAt D.base n s : (I 0).K)) :
    program.evalE rd 0 D.expr j = (n : (I 0).K) := by
  obtain ⟨b, _ | ⟨d, ds⟩⟩ := D
  · exact absurd rfl hD.ne
  have hlt : n < b ^ (ds.length + 1) := lt_trans hn hD.le
  have h' : ∀ s < ds.length + 1, program.evalE rd 0 (.leaf ((d :: ds).getD s 0)) j =
      (DigitLayout.digitAt b n s : (I 0).K) := fun s hs => by
    rw [List.getD_eq_getElem _ _ (by simpa using hs)]
    exact h s (by simpa using hs)
  have hn' : (n : (I 0).K) =
      ((∑ s ∈ Finset.range (ds.length + 1), b ^ s * DigitLayout.digitAt b n s : ℕ) :
        (I 0).K) := by
    rw [DigitLayout.sum_digitAt, Nat.mod_eq_of_lt hlt]
  have h0 := h' 0 (by omega)
  rw [List.getD_cons_zero] at h0
  rw [DigitLayout.expr_cons, evalE_exprFrom0 rd b j 1 _ _
      (by rw [add_comm]; exact hD.weight_le.trans (by norm_num [pGold])),
    hn', Finset.sum_range_succ', Nat.cast_add, Nat.cast_sum, h0, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    have := h' (s + 1) (by simp only [Finset.mem_range] at hs; omega)
    rw [List.getD_cons_succ] at this
    rw [this, Nat.cast_mul, Nat.add_comm 1 s]
  · simp

end Digits

/-! ## The honest integer of the relation -/

section HonestInt

variable (y : RingIn msgLen)

/-- **The honest shifted `z`**: `z + 130993`. -/
-- spec-side
def zvR (j : Fin 4) (m : Fin 256) : ℕ := (zCentered y.z j m + 130993).toNat

theorem zCentered_abs_le (j : Fin 4) (m : Fin 256) : |zCentered y.z j m| ≤ 130993 := by
  have := Native.zCentered_natAbs_lt y j m
  change _ < 130994 at this
  rw [Int.abs_eq_natAbs]
  omega

theorem signedZ_zvR (j : Fin 4) (m : Fin 256) :
    Emulated.Rows.signedZ (zvR y) j m = zCentered y.z j m := by
  have := abs_le.mp (zCentered_abs_le y j m)
  have hsh : ((mldsa44.normBound - 1 : ℕ) : ℤ) = 130993 := by decide
  simp only [Emulated.Rows.signedZ, Emulated.Rows.shift, zvR, hsh]
  omega

/-- **The response read from the shifted honest naturals is the input's `z`.** -/
theorem zVec_zvR : Emulated.Rows.zVec (zvR y) = y.z := by
  have hc : ∀ j m, ((Emulated.Rows.signedZ (zvR y) j m : ℤ) : _root_.MLDSA.Coeff) =
      MLDSA44.coeff (y.z.get j) m := fun j m => by
    erw [signedZ_zvR]
    rw [zCentered, ← LatticeCrypto.centeredRepr_intCast]
  unfold Emulated.Rows.zVec
  rw [← MLDSA44.NativeAlgebraCircuit.Honest.ofFn_ofCoeff_coeff y.z]
  exact congrArg Vector.ofFn (funext fun j => congrArg MLDSA44.ofCoeff (funext fun m => hc j m))

/-- **The honest naturals satisfy the congruence** `w′ ≡ Σ_j A_ij z_j − c t_i (mod q)`: the honest
`w′` is `computeWApprox(Â, c, z, t1)` (`Emulated.Rows.congruent_of_computeWApprox`). -/
theorem congruent_honest :
    Emulated.Rows.Congruent (Emulated.Rows.aKeyOf y.key) (Emulated.Rows.tKeyOf y.key) (zvR y)
      (fun i k => wNR y (finProdFinEquiv (i, k))) y.c := by
  refine Emulated.Rows.congruent_of_computeWApprox fun i k => ?_
  rw [zVec_zvR, wNR, MLDSA44.NativeAlgebraCircuit.flat_apply, ZMod.natCast_zmod_val]
  rfl

set_option maxRecDepth 8192 in
/-- **The honest integer is a multiple of `q`.** -/
theorem sigZ_dvd (i : Fin 4) (k : Fin 256) : (8380417 : ℤ) ∣ sigZ y i k := by
  have h1 := congruent_honest y i k
  have hA : ∀ j : Fin 4,
      ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf y.key i j)) k t * zZ y j t : ℤ) :
        _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => ((Emulated.Rows.aKeyOf y.key i j m : ℕ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.signedZ (zvR y) j m : ℤ) : _root_.MLDSA.Coeff)) k := by
    intro j
    refine (Ops.intCast_sum_negCoef (keyZ (Emulated.Rows.aKeyOf y.key i j)) (zZ y j) k.isLt).trans ?_
    congr 1
    · funext m
      simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
    · funext m
      erw [signedZ_zvR]
      rw [zZ, dif_pos m.isLt]
      rfl
  have hT : ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf y.key i)) k t * cZ y t : ℤ) :
        _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff (fun m : Fin 256 => ((y.c m : ℤ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.tKeyOf y.key i m : ℕ) : _root_.MLDSA.Coeff)) k := by
    refine (Ops.intCast_sum_negCoef (keyZ (Emulated.Rows.tKeyOf y.key i)) (cZ y) k.isLt).trans ?_
    rw [Falcon512.negacyclicConvCoeff_comm]
    congr 1
    · funext m
      rw [cZ, dif_pos m.isLt]
      rfl
    · funext m
      simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
  simp only at h1
  have h0 : ((sigZ y i k : ℤ) : _root_.MLDSA.Coeff) = 0 := by
    rw [sigZ, Int.cast_sub, Int.cast_sub, hT, Int.cast_natCast, Int.cast_sum]
    simp only [hA]
    exact sub_eq_zero.mpr h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

/-- **The honest integer's bounds**: `sigZ = q t` with `|t| ≤ 134137072`. -/
theorem sigZ_bounds (i : Fin 4) (k : Fin 256) :
    -134137072 ≤ sigZ y i k / 8380417 ∧ sigZ y i k / 8380417 ≤ 134137072 := by
  obtain ⟨t, ht⟩ := sigZ_dvd y i k
  have hz : ∀ (j : Fin 4), ∀ t < 256, |zZ y j t| ≤ 130993 := fun j t ht => by
    rw [zZ, dif_pos ht]
    exact zCentered_abs_le y j _
  have hc : ∀ t < 256, |cZ y t| ≤ 1 := fun t ht => by
    rw [cZ, dif_pos ht]
    have h : y.c ⟨t, ht⟩ = 0 ∨ y.c ⟨t, ht⟩ = 1 ∨ y.c ⟨t, ht⟩ = -1 :=
      MLDSA44.PoP.challenge_ternary _ _ _
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have hA := fun j : Fin 4 => abs_le.mp (abs_sum_negCoef_le
    (Emulated.Rows.aKeyOf_lt y.key i j) (hz j) k)
  have hT := abs_le.mp (abs_sum_negCoef_le (fun s => KeyNTT.vals_lt _ s) hc k
    (key := Emulated.Rows.tKeyOf y.key i))
  have hw := wNR_lt y (finProdFinEquiv (i, k))
  have e := ht
  rw [sigZ, Fin.sum_univ_four] at e
  rw [ht, Int.mul_ediv_cancel_left _ (by norm_num)]
  obtain ⟨a0, b0⟩ := hA 0
  obtain ⟨a1, b1⟩ := hA 1
  obtain ⟨a2, b2⟩ := hA 2
  obtain ⟨a3, b3⟩ := hA 3
  obtain ⟨a4, b4⟩ := hT
  constructor <;> omega

/-- **The honest quotient at coefficient `(i, k)`**: `sigZ / q − qlo`. -/
theorem quotN_eq {i k : ℕ} (hi : i < 4) (hk : k < 256) :
    (quotN y (i * 256 + k) : ℤ) = sigZ y ⟨i, hi⟩ ⟨k, hk⟩ / 8380417 + 134137327 := by
  have hb := sigZ_bounds y ⟨i, hi⟩ ⟨k, hk⟩
  unfold quotN
  rw [dif_pos (by omega)]
  have e1 : (⟨(i * 256 + k) / 256, by omega⟩ : Fin 4) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  have e2 : (⟨(i * 256 + k) % 256, by omega⟩ : Fin 256) = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
  rw [e1, e2, Int.toNat_of_nonneg (by omega)]

/-- **The honest quotient is at most `qmax = 268274655`.** -/
theorem quotN_le (j : ℕ) : quotN y j ≤ 268274655 := by
  by_cases hj : j < 1024
  · obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < 4 ∧ k < 256 ∧ j = i * 256 + k :=
      ⟨j / 256, j % 256, by omega, by omega, by omega⟩
    have h := quotN_eq y hi hk
    have hb := sigZ_bounds y ⟨i, hi⟩ ⟨k, hk⟩
    omega
  · unfold quotN
    rw [dif_neg hj]
    omega

end HonestInt

/-! ## The relation at the honest values -/

section HonestSig

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] [MldsaCarrierSelect program] [MldsaCarrierQuot program]
  {F0 FH : FieldInterp} [RealizedProgram.PrimeCastField F0 pGold] [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "emu" => CarrierAEmbed.emu program

set_option hygiene false in
local notation "qD" => MldsaCarrierHonest.qD program

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [hE : MldsaEmulatedHonest emu F0 FH]

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

set_option hygiene false in
local notation "RD" => program.reader E

/-- **The committed spectra are the signer's key's transforms** (`SpectraOf`): `member.a_hat` and
`member.t1` hold the scheme-order transforms of `A = NTT⁻¹(ExpandA(ρ))` (within the byte budget,
`RingIn.expandAWithin`) and of `2^d t1`. -/
theorem spectraOf_honest : SpectraOf y.key RD where
  a i j m hm := by
    have hi := i.isLt; have hj := j.isLt
    change (i : ℕ) < 4 at hi; change (j : ℕ) < 4 at hj
    have hlt : ((i : ℕ) * 4 + j) * 256 + m < 4096 := by omega
    rw [evalE_member y x c π (by simp) (by rw [(MldsaCarrierRelation.sizes (program := program)).1]; exact hlt),
      (honestVal_member y _).1, if_pos hlt, specE_lt y _ (by omega)]
    have e1 : (((i : ℕ) * 4 + j) * 256 + m) / 256 = (i : ℕ) * 4 + j := by omega
    have e2 : (((i : ℕ) * 4 + j) * 256 + m) % 256 = m := by omega
    rw [e1, e2]
    refine nttScheme_congr _ (fun k hk => ?_) _
    rw [show 256 * ((i : ℕ) * 4 + j) + k = ((i : ℕ) * 4 + j) * 256 + (⟨k, hk⟩ : Fin 256) by
        simp only; ring, keyEntry_a]
    simp only [keyPoly, Ops.ofFin_of_lt _ hk]
    congr 2
    unfold aNat Emulated.Rows.aKeyOf MLDSA44.Native.Rows.aEntry MLDSA44.Native.Rows.aHat
    rw [MLDSA44.expandABounded_eq_expandAFull y.expandAWithin]
  t i m hm := by
    have hi := i.isLt
    change (i : ℕ) < 4 at hi
    have hlt : (i : ℕ) * 256 + m < 1024 := by omega
    rw [evalE_member y x c π (by simp) (by rw [(MldsaCarrierRelation.sizes (program := program)).2.1]; exact hlt),
      (honestVal_member y _).2.1, if_pos hlt, specE_lt y _ (by omega)]
    have e1 : (4096 + ((i : ℕ) * 256 + m)) / 256 = 16 + i := by omega
    have e2 : (4096 + ((i : ℕ) * 256 + m)) % 256 = m := by omega
    rw [e1, e2]
    refine nttScheme_congr _ (fun k hk => ?_) _
    rw [show 256 * (16 + (i : ℕ)) + k = 4096 + ((i : ℕ) * 256 + (⟨k, hk⟩ : Fin 256)) by
        simp only; ring, keyEntry_t]
    simp only [keyPoly, Ops.ofFin_of_lt _ hk]
    rfl

/-- **`w′` reads the honest `w′`** (through domain `A`'s renaming). -/
theorem rd_w {m : ℕ} (hm : m < 1024) :
    program.evalE RD 0 (.leaf 64) m = ((wNR y (fm m hm) : ℕ) : (interp 0).K) := by
  have h := evalE_pullA E (f := 0) (v := 61) (CarrierAEmbed.readV 61 (by decide)) m
  rw [MldsaCarrierFront.valsA.2.2.2.1, w_eq] at h
  rw [← h]
  exact rdAE_61 (readsAE_pullA y x c π) hm

/-- **`z` reads the centered response.** -/
theorem rd_z {m : ℕ} (hm : m < 1024) :
    program.evalE RD 0 (.leaf 61) m = ((flat (zCentered y.z) (fmz m hm) : ℤ) : (interp 0).K) := by
  have h := evalE_pullA E (f := 0) (v := 58) (CarrierAEmbed.readV 58 (by decide)) m
  rw [MldsaCarrierFront.valsA.1, z_eq] at h
  rw [← h]
  exact rdAE_58 (readsAE_pullA y x c π) hm

/-- **The challenge bits read the challenge's support and sign.** -/
theorem rd_c {s : ℕ} (hs : s < 512) :
    program.evalE RD 0 (.leaf 63) s = cA y (interp 0).K ⟨s / 2, by change s / 2 < 256; omega⟩
      ⟨s % 2, by omega⟩ := by
  have h := evalE_pullA E (f := 0) (v := 60) (CarrierAEmbed.readV 60 (by decide)) s
  rw [MldsaCarrierFront.valsA.2.2.1, c_eq] at h
  rw [← h]
  exact (rdAE_fixed (readsAE_pullA y x c π) (v := 60) (by simp)
    (by rw [MldsaEmulatedHonest.size61 (program := emu)]; exact hs)).trans (aValE_60 y _ _ hs)

theorem toNat0_ite (p : Prop) [Decidable p] :
    (interp 0).toNat (if p then (1 : (interp 0).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact_mod_cast toNat_lt0 (I := interp) (k := 1) (by norm_num [pGold])
  · exact_mod_cast toNat_lt0 (I := interp) (k := 0) (by norm_num [pGold])

theorem rd_c_bool {s : ℕ} (hs : s < 512) :
    program.evalE RD 0 (.leaf 63) s = 0 ∨ program.evalE RD 0 (.leaf 63) s = 1 := by
  rw [rd_c y x c π hs]
  unfold cA
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).1
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).2

/-- **`w′`'s integer reading** is the honest `w′`. -/
theorem intOf_wH {m : ℕ} (hm : m < 1024) :
    program.intOf RD 64 m = (wNR y (fm m hm) : ℤ) := by
  refine intOf_of_boundInt (MldsaCarrierRelation.kinds (program := program)).2.1
    ((MldsaCarrierRelation.fields (program := program)) 64 (by simp)) ?_
    (by rw [rd_w y x c π hm, Int.cast_natCast])
  have := wNR_lt y (fm m hm)
  rw [abs_of_nonneg (by positivity)]
  norm_num [pGold]
  omega

/-- **`z`'s integer reading** is the centered response. -/
theorem intOf_zH {m : ℕ} (hm : m < 1024) :
    program.intOf RD 61 m = flat (zCentered y.z) (fmz m hm) := by
  refine intOf_of_boundInt (MldsaCarrierRelation.kinds (program := program)).1
    ((MldsaCarrierRelation.fields (program := program)) 61 (by simp)) ?_
    (rd_z y x c π hm)
  have h := zCentered_abs_le y (finProdFinEquiv.symm (fmz m hm)).1 (finProdFinEquiv.symm (fmz m hm)).2
  unfold flat
  have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
  rw [hp]
  linarith

/-- **The challenge polynomial's integers are the challenge.** -/
theorem cInt_honest {t : ℕ} (ht : t < 256) : cInt RD t = cZ y t := by
  have hb : ∀ n : ℕ, n < 2 → (interp 0).toNat ((n : ℕ) : (interp 0).K) = n := fun n hn =>
    toNat_lt0 (by norm_num [pGold]; omega)
  have e1 : (⟨(2 * t) / 2, by change (2 * t) / 2 < 256; omega⟩ : Fin MLDSA44.Native.Params.N) =
      ⟨t, ht⟩ := Fin.ext (by simp only; omega)
  have e2 : (⟨(2 * t + 1) / 2, by change (2 * t + 1) / 2 < 256; omega⟩ :
      Fin MLDSA44.Native.Params.N) = ⟨t, ht⟩ := Fin.ext (by simp only; omega)
  have e3 : (⟨(2 * t) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp only; omega)
  have e4 : (⟨(2 * t + 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
  have hv : ∀ s (hs : s < 512) (n : ℕ), cA y (interp 0).K ⟨s / 2, by change s / 2 < 256; omega⟩
      ⟨s % 2, by omega⟩ = ((n : ℕ) : (interp 0).K) →
      program.evalE RD 0 (.leaf 63) s = ((n : ℕ) : (interp 0).K) :=
    fun s hs n h => (rd_c y x c π hs).trans h
  have h3 : y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = 0 ∨
      y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = 1 ∨
      y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = -1 :=
    MLDSA44.PoP.challenge_ternary _ _ _
  unfold cInt
  have hp := (MldsaCarrierRelation.kinds (program := program)).2.2.2
  have hf := (MldsaCarrierRelation.fields (program := program)) 63 (by simp)
  rw [intOf_of_priv _ hp hf, intOf_of_priv _ hp hf, cZ, dif_pos ht]
  rcases h3 with h | h | h
  · have h' : y.c ⟨t, ht⟩ = 0 := h
    rw [hv (2 * t) (by omega) 0 (by rw [e1, e3]; simp [cA, HashCircuit.ternaryBits, h]),
      hv (2 * t + 1) (by omega) 0 (by rw [e2, e4]; simp [cA, HashCircuit.ternaryBits, h]),
      hb 0 (by norm_num), h']
    norm_num
  · have h' : y.c ⟨t, ht⟩ = 1 := h
    rw [hv (2 * t) (by omega) 1 (by rw [e1, e3]; simp [cA, HashCircuit.ternaryBits, h]),
      hv (2 * t + 1) (by omega) 0 (by rw [e2, e4]; simp [cA, HashCircuit.ternaryBits, h]),
      hb 0 (by norm_num), hb 1 (by norm_num), h']
    norm_num
  · have h' : y.c ⟨t, ht⟩ = -1 := h
    rw [hv (2 * t) (by omega) 1 (by rw [e1, e3]; simp [cA, HashCircuit.ternaryBits, h]),
      hv (2 * t + 1) (by omega) 1 (by rw [e2, e4]; simp [cA, HashCircuit.ternaryBits, h]),
      hb 1 (by norm_num), h']
    norm_num

/-- **The quotient's integer reading and value**: the honest quotient. -/
theorem rd_q {j : ℕ} (hj : j < 1024) :
    program.evalE RD 0 (.leaf 65) j = ((quotN y j : ℕ) : (interp 0).K) := by
  have hf := MldsaCarrierQuot.field65 (program := program)
  rw [evalE_leaf, reader_bindAsg_of_boundOk MldsaCarrierHonest.bound rfl MldsaCarrierQuot.lt65
    MldsaCarrierHonest.kind65]
  have key : program.evalE RD 0 (qD).expr j = ((quotN y j : ℕ) : (interp 0).K) := by
    refine evalE_digits0 MldsaCarrierHonest.qFits (Nat.lt_succ_of_le (quotN_le y j)) _ j
      fun s hs => ?_
    have hv : (qD).ids[s] ∈ [56, 57, 58, 59, 66] ++ (qD).ids :=
      List.mem_append_right _ (List.getElem_mem hs)
    rw [evalE_member y x c π hv (by rw [MldsaCarrierHonest.qSizes _ (List.getElem_mem hs)]; exact hj),
      (honestVal_member y j).2.2.2.2.2 _ (List.getElem_mem hs),
      DigitLayout.digit_getElem (List.nodup_append.1 MldsaCarrierHonest.member_nodup).2.1]
  rw [← key]
  revert hf
  generalize program.valueField 65 = a
  rintro rfl
  rfl

theorem intOf_q {j : ℕ} (hj : j < 1024) : program.intOf RD 65 j = (quotN y j : ℤ) := by
  have hb : (program.value 65).kind.isBound = true := by
    rw [MldsaCarrierHonest.kind65]
    rfl
  refine intOf_of_boundInt hb MldsaCarrierQuot.field65 ?_ (by rw [rd_q y x c π hj, Int.cast_natCast])
  have := quotN_le y j
  rw [abs_of_nonneg (by positivity)]
  norm_num [pGold]
  omega

omit [MldsaCarrierQuot program] [MLDSA44.MldsaHNativeData FH]
  [MLDSA44.MldsaHSample (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MLDSA44.MldsaHConsts (MLDSA44.Emulated.MldsaEmbed.nat emu) FH]
  [MldsaHHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)]
  [MldsaHSelHonest (MLDSA44.Emulated.MldsaEmbed.nat emu)] [MLDSA44.MldsaHNodes FH]
  [MldsaEmulatedHonest emu F0 FH] in
/-- **The high halves read `qHonC`**: row `t / 255` at `t % 255`. -/
theorem rd_Q {i : Fin 4} {s : ℕ} (hs : s < 255) :
    program.evalE RD 0 (.leaf 66) ((i : ℕ) * 255 + s) = qHonC y (interp 0).K i s := by
  have hi := i.isLt
  have hlt : (i : ℕ) * 255 + s < 1020 := by omega
  rw [evalE_member y x c π (by simp)
      (by rw [(MldsaCarrierRelation.sizes (program := program)).2.2.2.2.2.2]; exact hlt),
    (honestVal_member y _).2.2.2.2.1, dif_pos hlt]
  have e : (⟨((i : ℕ) * 255 + s) / 255, by omega⟩ : Fin 4) = i := Fin.ext (by simp only; omega)
  rw [e, show ((i : ℕ) * 255 + s) % 255 = s by omega]

/-- **A challenge bit is its integer reading's cast** at the honest values. -/
theorem rd_c_cast {s : ℕ} (hs : s < 512) :
    program.evalE RD 0 (.leaf 63) s = ((program.intOf RD 63 s : ℤ) : (interp 0).K) := by
  rw [intOf_of_priv _ (MldsaCarrierRelation.kinds (program := program)).2.2.2
    ((MldsaCarrierRelation.fields (program := program)) 63 (by simp))]
  rcases rd_c_bool y x c π hs with h | h <;> rw [h]
  · rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm,
      toNat_lt0 (by norm_num [pGold])]
    simp
  · rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      toNat_lt0 (by norm_num [pGold])]
    simp

open Polynomial in
/-- **Row `i` of the signature relation holds** at the honest values: row `i`'s polynomial is `0`.
The committed spectra invert to the signer's keys (`inverseNtt_spectrum`), the products split as
`Ops.polyOf_mul_polyOf`, the honest high halves `qHonC` cancel theirs, and the negacyclic part,
`Σ_j A_ij ⊛ z_j − t_i ⊛ c` over the integers' casts (`Ops.intCast_sum_negCoef`), cancels
`E_i = w′_i − q (q′_i + qlo)`, which is the cast of `w′ − sigZ` (`quotN_eq`, `sigZ_dvd`). -/
theorem sig_row (i : Fin 4) :
    program.HoldsAt E (program.predicate (MldsaRandomPoint.rel0 program + i)).body := by
  haveI : RealizedProgram.PrimeCastField (interp 0) pGold :=
    inferInstanceAs (RealizedProgram.PrimeCastField F0 pGold)
  haveI : MldsaRandomPointField program (interp 0) := instRandomPointField
  rw [holdsAt_row_iff]
  suffices h0 : rowPoly E i = 0 by rw [h0, Polynomial.eval_zero]
  have hi := i.isLt
  have hS := spectraOf_honest y x c π
  set TZ : ℕ → ℤ := keyZ (Emulated.Rows.tKeyOf y.key i)
  set AZ : Fin 4 → ℕ → ℤ := fun j => keyZ (Emulated.Rows.aKeyOf y.key i j)
  set ZZ : Fin 4 → ℕ → ℤ := fun j => zZ y j
  set CZ : ℕ → ℤ := cZ y
  set Tf : ℕ → (interp 0).K := fun s => ((TZ s : ℤ) : (interp 0).K)
  set Cf : ℕ → (interp 0).K := fun s => ((CZ s : ℤ) : (interp 0).K)
  set Af : Fin 4 → ℕ → (interp 0).K := fun j s => ((AZ j s : ℤ) : (interp 0).K)
  set Zf : Fin 4 → ℕ → (interp 0).K := fun j s => ((ZZ j s : ℤ) : (interp 0).K)
  -- the honest readings
  have hT : ∀ s < 256, Ops.inverseNtt 256 ((interp 0).decode psi512) (tRow E i) s = Tf s :=
    fun s hs' => inverseNtt_spectrum (fun m hm => by unfold tRow; rw [t1_eq]; exact hS.t i m hm) hs'
  have hA : ∀ (j : Fin 4), ∀ s < 256,
      Ops.inverseNtt 256 ((interp 0).decode psi512) (aRow E i j) s = Af j s := fun j s hs' =>
    inverseNtt_spectrum (fun m hm => by
      unfold aRow
      rw [aHat_eq, ← hS.a i j m hm, show (i : ℕ) * 1024 + ((j : ℕ) * 256 + m) = ((i : ℕ) * 4 + j) * 256 + m by
        ring]) hs'
  have hZ : ∀ (j : Fin 4), ∀ s < 256, zRow E j s = Zf j s := fun j s hs' => by
    have hj := j.isLt
    have hm : (j : ℕ) * 256 + s < 1024 := by omega
    unfold zRow
    rw [z_eq, rd_z y x c π hm, Emulated.fmz_eq j ⟨s, hs'⟩ (by simp only; omega),
      MLDSA44.NativeAlgebraCircuit.flat_apply]
    simp only [Zf, ZZ, zZ, dif_pos hs']
  have hC : ∀ s < 256, cRow E s = Cf s := fun s hs' => by
    unfold cRow
    rw [c_eq, rd_c_cast y x c π (by omega), rd_c_cast y x c π (by omega)]
    simp only [Cf, CZ, ← cInt_honest y x c π hs', cInt]
    push_cast
    ring
  have hQ : ∀ s < 255, qRow E i s =
      (∑ j : Fin 4, Ops.high 256 (Af j) (Zf j) s) - Ops.high 256 Tf Cf s := fun s hs' => by
    unfold qRow
    rw [q_eq, rd_Q y x c π hs']
    rfl
  have hE : ∀ s < 256, eRow E i s =
      ((∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (AZ j) s t * ZZ j t -
        ∑ t : Fin 256, Ops.negCoef 256 TZ s t * CZ t : ℤ) : (interp 0).K) := fun s hs' => by
    have hm : (i : ℕ) * 256 + s < 1024 := by omega
    have hQn := quotN_eq y hi hs'
    have hdv := sigZ_dvd y i ⟨s, hs'⟩
    have hsz : sigZ y i ⟨s, hs'⟩ = (wNR y (finProdFinEquiv (i, ⟨s, hs'⟩)) : ℤ) -
        (∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (AZ j) s t * ZZ j t -
          ∑ t : Fin 256, Ops.negCoef 256 TZ s t * CZ t) := rfl
    rw [eRow_eq E i hs']
    unfold wRow rqRow
    rw [w_eq, rd_w y x c π hm, rd_q y x c π hm, Emulated.fm_eq i ⟨s, hs'⟩ (by simp only; omega)]
    have hq : (8380417 : ℤ) * (quotN y ((i : ℕ) * 256 + s) : ℤ) =
        sigZ y i ⟨s, hs'⟩ + 1124126735525359 := by
      rw [hQn, mul_add, Int.mul_ediv_cancel' hdv]; norm_num
    have hint : ((wNR y (finProdFinEquiv (i, ⟨s, hs'⟩)) : ℕ) : ℤ) -
        8380417 * (quotN y ((i : ℕ) * 256 + s) : ℤ) + 1124126735525359 =
        ∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (AZ j) s t * ZZ j t -
          ∑ t : Fin 256, Ops.negCoef 256 TZ s t * CZ t := by
      rw [hq, hsz]
      ring
    rw [← hint]
    push_cast
    ring
  have hmul : ∀ a b : ℕ → (interp 0).K, Ops.polyOf 256 a * Ops.polyOf 256 b =
      Ops.polyOf 256 (Ops.negacyclic 256 a b) +
        (Polynomial.X ^ 256 + 1 : Polynomial (interp 0).K) * Ops.polyOf 255 (Ops.high 256 a b) :=
    fun a b => Ops.polyOf_mul_polyOf (n := 256) (by norm_num) a b
  have hEN : ∀ s < 256, eRow E i s =
      (∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s) - Ops.negacyclic 256 Tf Cf s :=
    fun s hs' => by
      have hN : ∀ h x : ℕ → ℤ, Ops.negacyclic 256 (fun t => (h t : (interp 0).K))
          (fun t => (x t : (interp 0).K)) s =
          ((∑ t : Fin 256, Ops.negCoef 256 h s t * x t : ℤ) : (interp 0).K) := fun h x => by
        rw [Ops.negacyclic, Ops.ofFin_of_lt _ hs', Ops.intCast_sum_negCoef h x hs']
        rfl
      rw [hE s hs']
      simp only [Af, Zf, Tf, Cf, hN]
      push_cast
      ring
  unfold rowPoly
  rw [(MldsaCarrierRelation.consts (program := program)).1, Ops.polyOf_congr hEN, Ops.polyOf_congr hQ, Ops.polyOf_congr hT, Ops.polyOf_congr hC,
    Finset.sum_congr rfl fun j _ => by
      rw [Ops.polyOf_congr (hA j), Ops.polyOf_congr (hZ j)], hmul]
  simp only [hmul]
  rw [show (fun s => (∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s) -
      Ops.negacyclic 256 Tf Cf s) = (fun s => ∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s) -
        Ops.negacyclic 256 Tf Cf from rfl,
    show (fun s => (∑ j : Fin 4, Ops.high 256 (Af j) (Zf j) s) - Ops.high 256 Tf Cf s) =
      (fun s => ∑ j : Fin 4, Ops.high 256 (Af j) (Zf j) s) - Ops.high 256 Tf Cf from rfl,
    Ops.polyOf_sub, Ops.polyOf_sub, Ops.polyOf_sum, Ops.polyOf_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- **`signature.relation.q` holds**: the honest quotient lies below the range's bound. -/
theorem qRange_holds :
    program.HoldsAt E (program.predicate (MldsaCarrierQuot.qPred program)).body := by
  obtain ⟨r, B, hb, hB⟩ := MldsaCarrierQuot.qRange (program := program)
  rw [HoldsAt, hb]
  intro i hi e he
  rw [List.mem_singleton] at he
  subst he
  simp only [List.headD_cons, exprLen_leaf, MldsaCarrierQuot.size65] at hi
  refine ⟨quotN y i, lt_of_le_of_lt (quotN_le y i) hB, ?_⟩
  unfold evalWith
  rw [MldsaRandomPoint.domainField0]
  exact rd_q y x c π hi

end HonestSig

end GordieHowe.MLDSA44.Ring.Carrier
