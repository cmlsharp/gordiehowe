-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestMember

@[expose] public section

/-!
# GordieHowe: the signature relation of the ML-DSA-44 ring carriers at the honest values

The signature relation of an ML-DSA-44 ring carrier (`signature.relation`, predicate `3`;
`carrier_relation` in `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) is one `mod_q` of the
spectral product form, `w′ ≡ Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c (mod q)` with its quotient `Q`
(`signature.relation.q`, value `64`, bound to its digits): `w′ − (Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c) =
q (qlo + Q)` on the integers, `0 ≤ Q ≤ qmax`. At the source environment of the honest values:

* **The casts** (`castAt_sigP`, `castAt_sigN`): at any reading whose committed spectra hold a key's
  transforms (`SpectraOf`) and whose `w′`, `z` and challenge bits are small integers, every integer
  reading of the relation's sides casts to its field value (the inverse transform of a spectrum is
  the key, whose negacyclic coefficients are small integers).
* **The honest readings** (`spectraOf_honest`, `rd_w`, `rd_z`, `rd_c`): the spectra are the
  signer's key's transforms; `w′` reads `wNR`, `z` the centered response, the challenge bits the
  challenge's support and sign.
* **The honest integer** (`sigZ_dvd`, `sigZ_bounds`): `sigZ` is a multiple of `q` (the honest `w′`
  is `computeWApprox(Â, c, z, t1)`, `Emulated.Rows.congruent_of_computeWApprox`) within
  `±(1024 (q − 1) · 130993 + 256 (q − 1) + q)`, so the honest quotient `quotN` lies in `[0, qmax]`.
* **The predicates** (`sig_holds`, `qRange_holds`): `signature.relation` and the quotient's range.
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

/-- **The program facts of a carrier's quotient** (decided per carrier): `signature.relation` has
the quotient `64` at `qlo = −134137327`, `qmax = 268274655`; `signature.relation.q` (predicate
`22`) bounds the quotient below some `B > qmax`; the quotient lies in field `0` with `1024`
coordinates. -/
class MldsaCarrierQuot (program : RealizedProgram) : Prop where
  /-- `signature.relation`'s realization. -/
  sigReal : ∃ real, (program.predicate 3).body = .mod 0 8380417 sigP sigN real ∧
    real.form = .spectralProduct ∧ real.quotient = some (.leaf 64) ∧
    real.quotientLo = -134137327 ∧ real.qmax = 268274655
  /-- `signature.relation.q` bounds the quotient. -/
  qRange : ∃ r B, (program.predicate 22).body = .mem 0 [.leaf 64] (.range B) r ∧ 268274655 < B
  /-- The quotient lies in field `0`. -/
  field64 : program.valueField 64 = 0
  /-- The quotient has `1024` coordinates. -/
  size64 : (program.value 64).size = 1024
  /-- The quotient is a value of the program. -/
  lt64 : 64 < program.values.length

/-! ## The casts of the relation's integer readings -/

section Cast

variable {program : RealizedProgram} [MldsaCarrierRelation program] {I : RealizedProgram.Interp}
  [RealizedProgram.PrimeCastField (I 0) pGold] (rd : program.Valuation I)

/-- **An integer reading casting to its field value** at coordinate `i`, in domain `0`. -/
def CastAt (e : Expr) (i : ℕ) : Prop :=
  ((program.evalIntWith rd 0 e i : ℤ) : (I 0).K) = program.evalE rd 0 e i

variable {rd}

theorem natCast_gold_sub {k : ℕ} (hk : k ≤ pGold) :
    (((pGold - k : ℕ) : ℕ) : (I 0).K) = -((k : ℕ) : (I 0).K) := by
  rw [Nat.cast_sub hk, CharP.cast_eq_zero, zero_sub]

theorem decode_mOne0 : (I 0).decode 18446744069414584320 = -1 := by
  rw [decode_lt0 (by norm_num [pGold]), show (18446744069414584320 : ℕ) = pGold - 1 by
    norm_num [pGold], natCast_gold_sub (by norm_num [pGold]), Nat.cast_one]

theorem decode_mTwo0 : (I 0).decode 18446744069414584319 = -2 := by
  rw [decode_lt0 (by norm_num [pGold]), show (18446744069414584319 : ℕ) = pGold - 2 by
    norm_num [pGold], natCast_gold_sub (by norm_num [pGold])]
  norm_num

theorem castAt_add {a b : Expr} {i : ℕ} (ha : CastAt rd a i) (hb : CastAt rd b i) :
    CastAt rd (.add a b) i := by
  unfold CastAt at *
  rw [evalIntWith_add, evalE_add, Int.cast_add, ha, hb]

theorem castAt_scale_mOne {a : Expr} {i : ℕ} (ha : CastAt rd a i) :
    CastAt rd (.scale (.const 18446744069414584320) a) i := by
  unfold CastAt at *
  rw [evalIntWith_scale_const, evalE_scale_const, MldsaCarrierRelation.domainField0,
    centered_mOne, decode_mOne0, Int.cast_mul, ha]
  norm_num

theorem castAt_scale_mTwo {a : Expr} {i : ℕ} (ha : CastAt rd a i) :
    CastAt rd (.scale (.const 18446744069414584319) a) i := by
  unfold CastAt at *
  rw [evalIntWith_scale_const, evalE_scale_const, MldsaCarrierRelation.domainField0,
    centered_mTwo, decode_mTwo0, Int.cast_mul, ha]
  norm_num

theorem castAt_reindex {a : Expr} {m : IndexMap} {i : ℕ} (ha : CastAt rd a (m.entry i)) :
    CastAt rd (.reindex m a) i := by
  unfold CastAt at *
  rw [evalIntWith_reindex, evalE_reindex, ha]

theorem castAt_concat {a b : Expr} {i : ℕ} (ha : i < program.exprLen a → CastAt rd a i)
    (hb : program.exprLen a ≤ i → CastAt rd b (i - program.exprLen a)) :
    CastAt rd (.concat a b) i := by
  unfold CastAt at *
  rw [evalIntWith_concat, evalE_concat]
  split_ifs with h
  · exact ha h
  · exact hb (by omega)

theorem castAt_ref {k i : ℕ} (hk : k < program.exprs.length) (ha : CastAt rd (program.expr k) i) :
    CastAt rd (.ref k) i := by
  unfold CastAt at *
  rw [evalIntWith_ref MldsaCarrierRelation.refsOrdered rd 0 hk,
    evalE_ref MldsaCarrierRelation.refsOrdered rd 0 hk, ha]

/-- **A small integer's cast reads back** through `coefInt` and casts to itself. -/
theorem cast_coefInt_small {e : (I 0).K} {z : ℤ} (hz : 2 * |z| < pGold) (he : e = (z : (I 0).K)) :
    (((I 0).coefInt e : ℤ) : (I 0).K) = e := by
  rw [he, coefInt_small hz]

/-- **A `polyBroadcast` operator's integer reading casts to its field value** at output `j`, where
its matrix entries at row `j` read back through `coefInt` and the operand's integer readings cast
to its field values. -/
theorem cast_applyInt_pb (t K : ℕ) (form : ConvForm) (xi : ℕ → ℤ) (xf : ℕ → (I 0).K) (j : ℕ)
    (hent : ∀ k : Fin ((program.value t).size / K),
      (((I 0).coefInt (NamedOp.pbEntryForm program rd t K form
        (j % NamedOp.rows program (.polyBroadcast t K form)) k) : ℤ) : (I 0).K) =
        NamedOp.pbEntryForm program rd t K form (j % NamedOp.rows program (.polyBroadcast t K form)) k)
    (hx : ∀ k : Fin ((program.value t).size / K),
      (xi (j / NamedOp.rows program (.polyBroadcast t K form) *
        NamedOp.cols program (.polyBroadcast t K form) + k) : (I 0).K) =
      xf (j / NamedOp.rows program (.polyBroadcast t K form) *
        NamedOp.cols program (.polyBroadcast t K form) + k)) :
    ((NamedOp.applyInt program 0 rd (.polyBroadcast t K form) xi j : ℤ) : (I 0).K) =
      NamedOp.apply program 0 rd (.polyBroadcast t K form) xf j := by
  rw [NamedOp.applyInt_polyBroadcast_form, NamedOp.apply_polyBroadcast_form, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Int.cast_mul, hent k, hx k]

/-- **An integer negacyclic coefficient cast into the field** is the coefficient of the casts,
where the entries agree below `n`. -/
theorem cast_negCoef_of {n : ℕ} {h : ℕ → (I 0).K} {z : ℕ → ℤ}
    (hz : ∀ s < n, h s = (z s : (I 0).K)) (j k : ℕ) :
    ((Ops.negCoef n z j k : ℤ) : (I 0).K) = Ops.negCoef n h j k := by
  have hm := Ops.negCoef_map (Int.castAddHom (I 0).K) n z j k
  simp only [Int.coe_castAddHom] at hm
  rw [hm, Ops.negCoef_eq, Ops.negCoef_eq]
  split_ifs with h1 h2 h2
  · rw [hz _ h1.2, hz _ h2.2]
  · rw [hz _ h1.2]
  · rw [hz _ h2.2]
  · rfl

/-- **A key's negacyclic coefficients are small**: below `q` in absolute value. -/
theorem abs_negCoef_keyZ_le {key : Fin 256 → ℕ} (hkey : ∀ s, key s < Emulated.Rows.q) (j k : ℕ) :
    |Ops.negCoef 256 (keyZ key) j k| ≤ 8380416 := by
  rcases Ops.negCoef_signed 256 (keyZ key) j k with h | ⟨s, hs, h | h⟩
  · rw [h]; norm_num
  all_goals
    rw [h]
    have hk := hkey ⟨s, hs⟩
    change key ⟨s, hs⟩ < 8380417 at hk
    simp only [keyZ, dif_pos hs, abs_neg, Nat.abs_cast]
    exact_mod_cast Nat.le_of_lt_succ hk

/-- **The polynomial of a key's spectrum is the key**, coefficient by coefficient. -/
theorem formPoly_spectrum {a : ℕ} {x : ℕ → (I a).K} {key : Fin 256 → ℕ}
    (hx : ∀ m < 256, (castElt (x m) : (I 0).K) =
      Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K key) m) {s : ℕ} (hs : s < 256) :
    NamedOp.formPoly (I := I) 0 256 (fun s => castElt (x s)) (.ntt psi512) s =
      ((keyZ key s : ℤ) : (I 0).K) := by
  show Ops.inverseNtt 256 ((I 0).decode psi512) (fun s => castElt (x s)) s = _
  rw [decode_lt0 (by norm_num [pGold]), Ops.inverseNtt_congr hx,
    Ops.inverseNtt_nttScheme (k := 8) (by norm_num) psi512_isPrimitiveRoot natCast_256_ne_zero _ hs]
  simp only [keyPoly, keyZ, Ops.ofFin_of_lt _ hs, dif_pos hs, Int.cast_natCast]

/-- **The entries of a `polyBroadcast` of committed spectra read back**: where every block of the
broadcast value holds a key's transform, every matrix entry is a small integer's cast. -/
theorem pbEntry_castBack {t K : ℕ} (hsz : (program.value t).size = K * 256) (hK : 0 < K)
    (keys : ℕ → Fin 256 → ℕ) (hkey : ∀ r s, keys r s < Emulated.Rows.q)
    (hS : ∀ r < K, ∀ m < 256, (castElt (rd t (r * 256 + m)) : (I 0).K) =
      Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K (keys r)) m) (j k : ℕ) :
    (((I 0).coefInt (NamedOp.pbEntryForm program rd t K (.ntt psi512) j k) : ℤ) : (I 0).K) =
      NamedOp.pbEntryForm program rd t K (.ntt psi512) j k := by
  have hn : (program.value t).size / K = 256 := by rw [hsz, Nat.mul_div_cancel_left _ hK]
  unfold NamedOp.pbEntryForm NamedOp.pbPolyForm
  rw [hn]
  split_ifs with hj
  · have hr : j / 256 < K := by omega
    have hcast := cast_negCoef_of (n := 256)
      (h := NamedOp.formPoly (I := I) 0 256 (fun s => castElt (rd t (j / 256 * 256 + s))) (.ntt psi512))
      (z := keyZ (keys (j / 256))) (fun s hs => formPoly_spectrum (hS _ hr) hs) (j % 256) k
    refine cast_coefInt_small ?_ hcast.symm
    have := abs_negCoef_keyZ_le (hkey (j / 256)) (j % 256) k
    norm_num [pGold]
    omega
  · exact cast_coefInt_small (z := 0) (by norm_num [pGold]) (by simp)

/-- **Four blocks of `256` cast** where each block does. -/
theorem castAt_concat4 (f : ℕ → Expr) (hf : ∀ r < 4, program.exprLen (f r) = 256)
    (h : ∀ r < 4, ∀ k < 256, CastAt rd (f r) k) {i : ℕ} (hi : i < 1024) :
    CastAt rd (.concat (f 0) (.concat (f 1) (.concat (f 2) (f 3)))) i := by
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  refine castAt_concat (fun hi' => h 0 (by norm_num) i (by omega)) fun hi' => ?_
  rw [h0] at hi' ⊢
  refine castAt_concat (fun hi'' => h 1 (by norm_num) _ (by omega)) fun hi'' => ?_
  rw [h1] at hi'' ⊢
  refine castAt_concat (fun h3 => h 2 (by norm_num) _ (by omega)) fun h3 => ?_
  rw [h2] at h3 ⊢
  exact h 3 (by norm_num) _ (by omega)

/-- **The relation's left side casts** where `w′`'s readings do. -/
theorem castAt_sigP (hw : ∀ m < 1024, CastAt rd (.leaf 63) m) {i : ℕ} (hi : i < 1024) :
    CastAt rd sigP i :=
  castAt_concat4 rowP (fun _ hr => exprLen_rowP hr) (fun r hr k hk =>
    castAt_ref wRef_lt (by
      rw [expr_wRef hr]
      exact castAt_reindex (by rw [rowSeg_entry _ hk]; exact hw _ (by omega)))) hi

variable {pk : Native.Rows.PublicKey} (hS : SpectraOf pk rd)
  (hz : ∀ m < 1024, CastAt rd (.leaf 60) m) (hc : ∀ m < 512, CastAt rd (.leaf 62) m)
include hS hz hc

/-- **The product `A_ij ⊛ z_j` casts.** -/
theorem castAt_aTerm (i j : Fin 4) {k : ℕ} (hk : k < 256) : CastAt rd (aTerm i j) k := by
  have h55 := MldsaCarrierRelation.size55 (program := program)
  have hJ : 256 * (4 * (i : ℕ) + j) + k < 4096 := by omega
  refine castAt_reindex ?_
  rw [rowSeg_entry _ hk]
  unfold CastAt
  rw [evalIntWith_apply, evalE_apply, MldsaCarrierRelation.domainField0]
  refine cast_applyInt_pb 55 16 (.ntt psi512) _ _ _ (fun k' => pbEntry_castBack
    (by rw [h55]) (by norm_num) (fun r => Emulated.Rows.aKeyOf pk ⟨r / 4 % 4, by change _ < 4; omega⟩ ⟨r % 4, by change _ < 4; omega⟩)
    (fun r => Emulated.Rows.aKeyOf_lt pk _ _) (fun r hr m hm => ?_) _ _) (fun k' => ?_)
  · have h := hS.a ⟨r / 4 % 4, by change _ < 4; omega⟩ ⟨r % 4, by change _ < 4; omega⟩ m hm
    rw [evalE_leaf] at h
    have hr' : ((r / 4 % 4 : ℕ) * 4 + r % 4) * 256 + m = r * 256 + m := by omega
    simp only at h
    rw [hr'] at h
    exact h
  · have hrows : NamedOp.rows program (.polyBroadcast 55 16 (.ntt psi512)) = 4096 := by
      simp only [NamedOp.rows, h55]
    have hk' : (k' : ℕ) < 256 := by
      have := k'.isLt
      have h' : (program.value 55).size / 16 = 256 := by rw [h55]
      omega
    rw [hrows, Nat.div_eq_of_lt hJ, Nat.zero_mul, Nat.zero_add]
    exact castAt_reindex (by rw [rowSeg_entry _ hk']; exact hz _ (by omega))

/-- **The challenge polynomial casts.** -/
theorem castAt_cExpr {t : ℕ} (ht : t < 256) : CastAt rd cExpr t := by
  have hl := MldsaCarrierRelation.exprsLen (program := program)
  refine castAt_add (castAt_ref (by omega) ?_) (castAt_scale_mTwo (castAt_ref (by omega) ?_))
  · rw [MldsaCarrierRelation.expr37]
    exact castAt_reindex (by rw [evenSeg_entry ht]; exact hc _ (by omega))
  · rw [MldsaCarrierRelation.expr38]
    exact castAt_reindex (by rw [oddSeg_entry ht]; exact hc _ (by omega))

/-- **The product `2^d t1_i ⊛ c` casts.** -/
theorem castAt_tTerm (i : Fin 4) {k : ℕ} (hk : k < 256) : CastAt rd (tTerm i) k := by
  have h56 := MldsaCarrierRelation.size56 (program := program)
  have hJ : 256 * (i : ℕ) + k < 1024 := by omega
  refine castAt_reindex ?_
  rw [rowSeg_entry _ hk]
  unfold CastAt
  rw [evalIntWith_apply, evalE_apply, MldsaCarrierRelation.domainField0]
  refine cast_applyInt_pb 56 4 (.ntt psi512) _ _ _ (fun k' => pbEntry_castBack
    (by rw [h56]) (by norm_num) (fun r => Emulated.Rows.tKeyOf pk ⟨r % 4, by change _ < 4; omega⟩)
    (fun r s => KeyNTT.vals_lt _ s) (fun r hr m hm => ?_) _ _) (fun k' => ?_)
  · have h := hS.t ⟨r % 4, by change _ < 4; omega⟩ m hm
    rw [evalE_leaf] at h
    have hr' : (r % 4 : ℕ) * 256 + m = r * 256 + m := by rw [Nat.mod_eq_of_lt hr]
    simp only at h
    rw [hr'] at h
    exact h
  · have hrows : NamedOp.rows program (.polyBroadcast 56 4 (.ntt psi512)) = 1024 := by
      simp only [NamedOp.rows, h56]
    have hk' : (k' : ℕ) < 256 := by
      have := k'.isLt
      have h' : (program.value 56).size / 4 = 256 := by rw [h56]
      omega
    rw [hrows, Nat.div_eq_of_lt hJ, Nat.zero_mul, Nat.zero_add]
    exact castAt_cExpr hS hz hc hk'

/-- **The relation's right side casts** where the committed spectra hold a key's transforms and
`z`'s and the challenge bits' readings cast. -/
theorem castAt_sigN {i : ℕ} (hi : i < 1024) : CastAt rd sigN i :=
  castAt_concat4 rowN (fun r _ => exprLen_rowN r) (fun r hr k hk => by
    have e := fun j : Fin 4 => castAt_aTerm hS hz hc ⟨r, hr⟩ j hk
    exact castAt_add (castAt_add (castAt_add (castAt_add (e 0) (e 1)) (e 2)) (e 3))
      (castAt_scale_mOne (castAt_tTerm hS hz hc ⟨r, hr⟩ hk))) hi

end Cast

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
    refine (cast_sum_negCoef (keyZ (Emulated.Rows.aKeyOf y.key i j)) (zZ y j) k.isLt).trans ?_
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
    refine (cast_sum_negCoef (keyZ (Emulated.Rows.tKeyOf y.key i)) (cZ y) k.isLt).trans ?_
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

/-- **A sum against a key's negacyclic row** is bounded by `256` times the key's and the operand's
bounds. -/
theorem abs_sum_negCoef_le {key : Fin 256 → ℕ} (hkey : ∀ s, key s < Emulated.Rows.q) {x : ℕ → ℤ}
    {B : ℤ} (hx : ∀ t < 256, |x t| ≤ B) (k : ℕ) :
    |∑ t : Fin 256, Ops.negCoef 256 (keyZ key) k t * x t| ≤ 256 * (8380416 * B) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hB : 0 ≤ B := (abs_nonneg _).trans (hx 0 (by norm_num))
  calc ∑ t : Fin 256, |Ops.negCoef 256 (keyZ key) k t * x t|
      ≤ ∑ _t : Fin 256, 8380416 * B := Finset.sum_le_sum fun t _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_negCoef_keyZ_le hkey k t) (hx t t.isLt) (abs_nonneg _) (by norm_num)
    _ = 256 * (8380416 * B) := by simp

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
    rw [evalE_member y x c π (by simp) (by rw [MldsaCarrierRelation.size55]; exact hlt),
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
    rw [evalE_member y x c π (by simp) (by rw [MldsaCarrierRelation.size56]; exact hlt),
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
    program.evalE RD 0 (.leaf 63) m = ((wNR y (fm m hm) : ℕ) : (interp 0).K) := by
  have h := evalE_pullA E (f := 0) (v := 61) (by decide) m
  rw [σA_vals.2.2.2.1] at h
  rw [← h]
  exact rdAE_61 (readsAE_pullA y x c π) hm

/-- **`z` reads the centered response.** -/
theorem rd_z {m : ℕ} (hm : m < 1024) :
    program.evalE RD 0 (.leaf 60) m = ((flat (zCentered y.z) (fmz m hm) : ℤ) : (interp 0).K) := by
  have h := evalE_pullA E (f := 0) (v := 58) (by decide) m
  rw [σA_vals.1] at h
  rw [← h]
  exact rdAE_58 (readsAE_pullA y x c π) hm

/-- **The challenge bits read the challenge's support and sign.** -/
theorem rd_c {s : ℕ} (hs : s < 512) :
    program.evalE RD 0 (.leaf 62) s = cA y (interp 0).K ⟨s / 2, by change s / 2 < 256; omega⟩
      ⟨s % 2, by omega⟩ := by
  have h := evalE_pullA E (f := 0) (v := 60) (by decide) s
  rw [σA_vals.2.2.1] at h
  rw [← h]
  exact (rdAE_fixed (readsAE_pullA y x c π) (v := 60) (by simp)
    (by rw [MldsaEmulatedHonest.size61 (program := emu)]; exact hs)).trans (aValE_60 y _ _ hs)

theorem toNat0_ite (p : Prop) [Decidable p] :
    (interp 0).toNat (if p then (1 : (interp 0).K) else 0) = if p then 1 else 0 := by
  split_ifs
  · exact_mod_cast toNat_lt0 (I := interp) (k := 1) (by norm_num [pGold])
  · exact_mod_cast toNat_lt0 (I := interp) (k := 0) (by norm_num [pGold])

theorem rd_c_bool {s : ℕ} (hs : s < 512) :
    program.evalE RD 0 (.leaf 62) s = 0 ∨ program.evalE RD 0 (.leaf 62) s = 1 := by
  rw [rd_c y x c π hs]
  unfold cA
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).1
  · simp only [h]
    exact (MLDSA44.Native.ternaryBits_bool _).2

/-- **`w′`'s integer reading** is the honest `w′`. -/
theorem intOf_wH {m : ℕ} (hm : m < 1024) :
    program.intOf RD 63 m = (wNR y (fm m hm) : ℤ) := by
  refine intOf_of_boundInt MldsaCarrierRelation.kind63 MldsaCarrierRelation.field63 ?_
    (by rw [rd_w y x c π hm, Int.cast_natCast])
  have := wNR_lt y (fm m hm)
  rw [abs_of_nonneg (by positivity)]
  norm_num [pGold]
  omega

/-- **`z`'s integer reading** is the centered response. -/
theorem intOf_zH {m : ℕ} (hm : m < 1024) :
    program.intOf RD 60 m = flat (zCentered y.z) (fmz m hm) := by
  refine intOf_of_boundInt MldsaCarrierRelation.kind60 MldsaCarrierRelation.field60 ?_
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
      program.evalE RD 0 (.leaf 62) s = ((n : ℕ) : (interp 0).K) :=
    fun s hs n h => (rd_c y x c π hs).trans h
  have h3 : y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = 0 ∨
      y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = 1 ∨
      y.c (⟨t, ht⟩ : Fin MLDSA44.Native.Params.N) = -1 :=
    MLDSA44.PoP.challenge_ternary _ _ _
  unfold cInt
  rw [intOf_of_priv _ MldsaCarrierRelation.kind62 MldsaCarrierRelation.field62,
    intOf_of_priv _ MldsaCarrierRelation.kind62 MldsaCarrierRelation.field62, cZ, dif_pos ht]
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
    program.evalE RD 0 (.leaf 64) j = ((quotN y j : ℕ) : (interp 0).K) := by
  have hf := MldsaCarrierQuot.field64 (program := program)
  rw [evalE_leaf, reader_bindAsg_of_boundOk MldsaCarrierHonest.bound rfl MldsaCarrierQuot.lt64
    MldsaCarrierHonest.kind64]
  have key : program.evalE RD 0 (qD).expr j = ((quotN y j : ℕ) : (interp 0).K) := by
    refine evalE_digits0 MldsaCarrierHonest.qFits (Nat.lt_succ_of_le (quotN_le y j)) _ j
      fun s hs => ?_
    have hv : (qD).ids[s] ∈ [55, 56, 57, 58] ++ (qD).ids :=
      List.mem_append_right _ (List.getElem_mem hs)
    rw [evalE_member y x c π hv (by rw [MldsaCarrierHonest.qSizes _ (List.getElem_mem hs)]; exact hj),
      (honestVal_member y j).2.2.2.2 _ (List.getElem_mem hs),
      DigitLayout.digit_getElem (List.nodup_append.1 MldsaCarrierHonest.member_nodup).2.1]
  rw [← key]
  revert hf
  generalize program.valueField 64 = a
  rintro rfl
  rfl

theorem intOf_q {j : ℕ} (hj : j < 1024) : program.intOf RD 64 j = (quotN y j : ℤ) := by
  have hb : (program.value 64).kind.isBound = true := by
    rw [MldsaCarrierHonest.kind64]
    rfl
  refine intOf_of_boundInt hb MldsaCarrierQuot.field64 ?_ (by rw [rd_q y x c π hj, Int.cast_natCast])
  have := quotN_le y j
  rw [abs_of_nonneg (by positivity)]
  norm_num [pGold]
  omega

/-- **The relation's left side on the honest integers**: `w′`. -/
theorem sigP_honest {i k : ℕ} (hi : i < 4) (hk : k < 256) :
    program.evalIntWith RD 0 sigP (i * 256 + k) = (wNR y (finProdFinEquiv (⟨i, hi⟩, ⟨k, hk⟩)) : ℤ) := by
  rw [evalIntWith_sigP _ hi hk, intOf_wH y x c π (by omega),
    Emulated.fm_eq ⟨i, hi⟩ ⟨k, hk⟩ (by simp only; omega)]

set_option maxRecDepth 8192 in
/-- **The relation's right side on the honest integers**:
`Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c`. -/
theorem sigN_honest (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalIntWith RD 0 sigN ((i : ℕ) * 256 + k) =
      ∑ j : Fin 4, ∑ t : Fin 256,
          Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf y.key i j)) k t * zZ y j t -
        ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf y.key i)) k t * cZ y t := by
  rw [evalIntWith_sigN (spectraOf_honest y x c π) i hk]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    have hj := j.isLt
    have hdeg : MLDSA44.Native.Rows.deg = 256 := rfl
    have ht := t.isLt
    rw [intOf_zH y x c π (by omega), Emulated.fmz_eq j t (by omega),
      MLDSA44.NativeAlgebraCircuit.flat_apply, zZ, dif_pos t.isLt]
    rfl
  · exact Finset.sum_congr rfl fun t _ => by rw [cInt_honest y x c π t.isLt]

/-- **The relation's sides differ by the honest integer.** -/
theorem sigPN_honest {i k : ℕ} (hi : i < 4) (hk : k < 256) :
    program.evalIntWith RD 0 sigP (i * 256 + k) - program.evalIntWith RD 0 sigN (i * 256 + k) =
      sigZ y ⟨i, hi⟩ ⟨k, hk⟩ := by
  rw [sigP_honest y x c π hi hk, sigN_honest y x c π ⟨i, hi⟩ hk, sigZ]
  rfl

/-- **`signature.relation` holds** at the honest values: the sides differ by the honest integer
`sigZ = q (qlo + Q)` (`sigZ_dvd`, `quotN_eq`), `0 ≤ Q ≤ qmax`, and every integer reading casts to
its value (`castAt_sigP`, `castAt_sigN`). -/
theorem sig_holds : program.HoldsAt E (program.predicate 3).body := by
  obtain ⟨real, hb, hform, hq, hlo, hqmax⟩ := MldsaCarrierQuot.sigReal (program := program)
  have hS := spectraOf_honest y x c π
  have hw : ∀ m < 1024, CastAt RD (.leaf 63) m := fun m hm => by
    unfold CastAt
    rw [evalIntWith_leaf, intOf_wH y x c π hm, rd_w y x c π hm, Int.cast_natCast]
  have hz : ∀ m < 1024, CastAt RD (.leaf 60) m := fun m hm => by
    unfold CastAt
    rw [evalIntWith_leaf, intOf_zH y x c π hm, rd_z y x c π hm]
  have hc : ∀ m < 512, CastAt RD (.leaf 62) m := fun m hm => by
    unfold CastAt
    rw [evalIntWith_leaf, intOf_of_priv _ MldsaCarrierRelation.kind62 MldsaCarrierRelation.field62]
    rcases rd_c_bool y x c π hm with h | h <;> rw [h]
    · rw [show (0 : (interp 0).K) = ((0 : ℕ) : (interp 0).K) from Nat.cast_zero.symm,
        toNat_lt0 (by norm_num [pGold])]
      simp
    · rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
        toNat_lt0 (by norm_num [pGold])]
      simp
  have hd := MldsaCarrierRelation.domainField0 (program := program)
  rw [HoldsAt, hb]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [exprLen_sigP] at hi
    obtain ⟨a, b, ha, hb', rfl⟩ : ∃ a b, a < 4 ∧ b < 256 ∧ i = a * 256 + b :=
      ⟨i / 256, i % 256, by omega, by omega, by omega⟩
    rw [sigPN_honest y x c π ha hb']
    exact_mod_cast sigZ_dvd y ⟨a, ha⟩ ⟨b, hb'⟩
  · unfold ProductQuotWith
    rw [hq]
    intro _ _ i hi
    rw [exprLen_sigP] at hi
    obtain ⟨a, b, ha, hb', rfl⟩ : ∃ a b, a < 4 ∧ b < 256 ∧ i = a * 256 + b :=
      ⟨i / 256, i % 256, by omega, by omega, by omega⟩
    have hQ := quotN_eq y ha hb'
    have hQle := quotN_le y (a * 256 + b)
    have hdv := sigZ_dvd y ⟨a, ha⟩ ⟨b, hb'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sigPN_honest y x c π ha hb', evalIntWith_leaf, intOf_q y x c π (by omega), hQ, hlo]
      rw [show (-134137327 : ℤ) + (sigZ y ⟨a, ha⟩ ⟨b, hb'⟩ / 8380417 + 134137327) =
        sigZ y ⟨a, ha⟩ ⟨b, hb'⟩ / 8380417 by ring]
      push_cast
      exact (Int.mul_ediv_cancel' hdv).symm
    · rw [evalIntWith_leaf, intOf_q y x c π (by omega)]
      positivity
    · rw [evalIntWith_leaf, intOf_q y x c π (by omega), hqmax]
      exact_mod_cast hQle
    · unfold evalWith
      rw [hd]
      exact castAt_sigP hw (by omega)
    · unfold evalWith
      rw [hd]
      exact castAt_sigN hS hz hc (by omega)
    · unfold evalWith
      rw [hd, evalIntWith_leaf, intOf_q y x c π (by omega), rd_q y x c π (by omega)]
      push_cast
      rfl

/-- **`signature.relation.q` holds**: the honest quotient lies below the range's bound. -/
theorem qRange_holds : program.HoldsAt E (program.predicate 22).body := by
  obtain ⟨r, B, hb, hB⟩ := MldsaCarrierQuot.qRange (program := program)
  rw [HoldsAt, hb]
  intro i hi e he
  rw [List.mem_singleton] at he
  subst he
  simp only [List.headD_cons, exprLen_leaf, MldsaCarrierQuot.size64] at hi
  refine ⟨quotN y i, lt_of_le_of_lt (quotN_le y i) hB, ?_⟩
  unfold evalWith
  rw [MldsaCarrierRelation.domainField0]
  exact rd_q y x c π hi

end HonestSig

end GordieHowe.MLDSA44.Ring.Carrier
