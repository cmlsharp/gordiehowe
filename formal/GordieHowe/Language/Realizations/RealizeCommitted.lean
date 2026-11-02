-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeMod

@[expose] public section

/-!
# GordieHowe: the committed-digits form of `mod_q`, realized

The lemma that turns a `mod_q` in the committed-digits form (`GordieHowe.RealizedProgram.CommittedFormOk`;
compiler/mod.h, `kCommittedDigits`) into its integer congruence
(`GordieHowe.RealizedProgram.holdsWith_mod_of_committed`): the field equation `e − e' − q·qlo − q·Σ_j R^j d_j = 0` is a
field `equal` of the program (a leaf fact), each committed digit lies in `[0, N_j)` by its direct or
digit `in` (leaf facts), and the sides' integer readings lie in the exported intervals; the no-wrap
conditions lift the field equation to `e − e' = q·qlo + q·Q` over the integers for the natural
`Q ≤ Σ_j R^j (N_j − 1)` the digits' value is the cast of (`IntIn.sub_eq_natCast`), so `q` divides
`e − e'`.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **The digit terms of a committed-digits row** (`commPeel`): the row's left side is its head plus
`Σ_{(D, j)} c_j · D` with each `c_j` decoding to `−q R^j`. -/
theorem evalE_of_commPeel (rd : ir.Valuation I) {f p q R : ℕ} [CharP (I f).K p]
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) (ts : List (Expr × ℕ)) :
    ∀ (L : Expr) {h : Expr}, commPeel p q R L ts = some h →
      (∀ i, ir.evalE rd f L i = ir.evalE rd f h i -
        (ts.map fun Dj => ((q * R ^ Dj.2 : ℕ) : (I f).K) * ir.evalE rd f Dj.1 i).sum) ∧
        ir.exprLen L = ir.exprLen h := by
  induction ts with
  | nil =>
    intro L h hp
    simp only [commPeel, Option.some.injEq] at hp
    subst hp
    simp
  | cons Dj ts ih =>
    obtain ⟨D', j⟩ := Dj
    intro L h hp
    simp only [commPeel] at hp
    split at hp
    · rename_i rest c D hpt
      rw [eq_of_peelTerm hpt]
      split_ifs at hp with hc
      obtain ⟨hD, hcp, hmod⟩ := hc
      obtain ⟨hev, hlen⟩ := ih rest hp
      refine ⟨fun i => ?_, by rw [exprLen_add, hlen]⟩
      have hneg : (I f).decode c = -((q * R ^ j : ℕ) : (I f).K) := by
        rw [hdec c hcp, eq_neg_iff_add_eq_zero, ← Nat.cast_add,
          (CharP.cast_eq_zero_iff (I f).K p _).2 (Nat.dvd_of_mod_eq_zero hmod)]
      rw [evalE_add, evalE_scale_const, hneg, hev i, Expr.eq_of_beq hD]
      simp only [List.map_cons, List.sum_cons]
      ring
    · cases hp

/-- **A negated term** (`negTermB`): `a · t` is `−v`. -/
theorem evalE_of_negTermB (rd : ir.Valuation I) {f p : ℕ} [CharP (I f).K p]
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {v t : Expr} {a : ℕ}
    (h : negTermB p v a t = true) (i : ℕ) :
    (I f).decode a * ir.evalE rd f t i = -ir.evalE rd f v i := by
  unfold negTermB at h
  split at h
  · rename_i c t'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨ht, hc⟩, ha⟩, hm⟩ := h
    have hac : ((a : ℕ) : (I f).K) = -(c : (I f).K) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add,
        (CharP.cast_eq_zero_iff (I f).K p _).2 (Nat.dvd_of_mod_eq_zero hm)]
    rw [← Expr.eq_of_beq ht, evalE_scale_const, hdec a ha, hdec c hc, hac]
    ring
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ht, ha⟩ := h
    have h1 : ((a : ℕ) : (I f).K) = -1 := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ha, CharP.cast_eq_zero]
    rw [← Expr.eq_of_beq ht, hdec a (by omega), h1]
    ring

/-- **A difference term by term** (`subB`): `X` evaluates to `e − e'`, of `e`'s length. -/
theorem evalE_of_subB (rd : ir.Valuation I) {f p : ℕ} [CharP (I f).K p]
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) (e : Expr) :
    ∀ (e' Xh : Expr), subB p e e' Xh = true →
      (∀ i, ir.evalE rd f Xh i = ir.evalE rd f e i - ir.evalE rd f e' i) ∧
        ir.exprLen Xh = ir.exprLen e
  | e', Xh, h => by
    unfold subB at h
    split at h
    · rename_i Yh a t
      rcases Bool.or_eq_true_iff.1 h with h | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨ha, ht⟩, hY⟩ := h
        rw [Expr.eq_of_beq ht, Expr.eq_of_beq hY]
        refine ⟨fun i => ?_, exprLen_add _ _⟩
        have h1 : ((a : ℕ) : (I f).K) = -1 := by
          rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ha, CharP.cast_eq_zero]
        rw [evalE_add, evalE_scale_const, hdec a (by omega), h1]
        ring
      · by_cases hu : ∃ u v, e' = .add u v
        · obtain ⟨u, v, rfl⟩ := hu
          simp only [Bool.and_eq_true] at h
          obtain ⟨hn, hs⟩ := h
          obtain ⟨hev, hlen⟩ := evalE_of_subB rd hdec e u Yh hs
          refine ⟨fun i => ?_, by rw [exprLen_add, hlen]⟩
          rw [evalE_add, evalE_scale_const, evalE_of_negTermB rd hdec hn i, hev i, evalE_add]
          ring
        · split at h
          · exact absurd ⟨_, _, rfl⟩ hu
          · simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨hn, hY⟩ := h
            rw [Expr.eq_of_beq hY]
            refine ⟨fun i => ?_, exprLen_add _ _⟩
            rw [evalE_add, evalE_scale_const, evalE_of_negTermB rd hdec hn i]
            ring
    · cases h
  termination_by e' Xh _ => sizeOf Xh

/-- **Weighted digit terms are `q R^n` times the digits' value** (`digitsVal`). -/
theorem sum_zipIdx_mul {K : Type} [CommRing K] (q R : ℕ) (v : Expr → K) :
    ∀ (Ds : List Expr) (n : ℕ),
      ((Ds.zipIdx n).map fun Dj => ((q * R ^ Dj.2 : ℕ) : K) * v Dj.1).sum =
        ((q * R ^ n : ℕ) : K) * digitsVal (R : K) (Ds.map v)
  | [], n => by simp [digitsVal]
  | D :: Ds, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_mul q R v Ds (n + 1)]
    simp only [List.map_cons, digitsVal, List.foldr_cons]
    push_cast
    ring

/-- **The shift of a committed-digits row** decodes to `q · qlo`: the reduction of `q · qlo` modulo
`p` is below `p` and casts to `q · qlo` in characteristic `p`. -/
theorem commShift_spec {K : Type} [Ring K] {p : ℕ} [CharP K p] (hp : 0 < p) (q : ℕ)
    (real : ModRealization) :
    commShift p q real < p ∧ ((commShift p q real : ℕ) : K) = (((q : ℤ) * real.quotientLo : ℤ) : K) := by
  have h0 : 0 ≤ ((q : ℤ) * real.quotientLo) % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : ((q : ℤ) * real.quotientLo) % (p : ℤ) < p := Int.emod_lt_of_pos _ (by omega)
  refine ⟨by unfold commShift; omega, ?_⟩
  unfold commShift
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  exact (CharP.intCast_eq_intCast K p).2 (Int.mod_modEq _ _)

/-- **Committed digits bounded by direct or digit `in`s** (`commRangeOf`): under the leaf facts, at a
coordinate below the left side's length, the digits' value in base `B` is the cast of a number at
most `Σ_j B^j (N_j − 1)`. -/
theorem digitsVal_of_commRanges {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d : ℕ} {e : Expr}
    (B : ℕ) {i : ℕ} (hi : i < ir.exprLen e) :
    ∀ (Ds : List Expr) (rs N : List ℕ),
      (Ds.zip rs).mapM (fun Dr => ir.commRangeOf d e Dr.1 Dr.2) = some N → Ds.length = rs.length →
        ∃ Q ≤ digitsMax B N, digitsVal (B : (I (ir.domainField d)).K)
          (Ds.map fun D => ir.evalWith rd d D i) = (Q : _)
  | [], rs, N, h, hl => by
    simp only [List.zip_nil_left, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨0, le_rfl, by simp [digitsVal]⟩
  | D :: Ds, r :: rs, N, h, hl => by
    rw [List.zip_cons_cons, List.mapM_cons] at h
    cases hn : ir.commRangeOf d e D r with
    | none => simp [hn] at h
    | some n =>
    cases hN' : (Ds.zip rs).mapM (fun Dr => ir.commRangeOf d e Dr.1 Dr.2) with
    | none => simp [hn, hN'] at h
    | some N' =>
    simp [hn, hN'] at h
    subst h
    obtain ⟨Q, hQ, hQv⟩ := digitsVal_of_commRanges hF B hi Ds rs N' hN' (by simpa using hl)
    unfold commRangeOf at hn
    split_ifs at hn with hr
    split at hn
    · rename_i d' D' N'' r' hbody
      split_ifs at hn with hc
      cases hn
      obtain ⟨rfl, hk, hb, hlen, -⟩ := hc
      have hH : ir.HoldsWith rd (ir.predicate r).body := by
        rcases hk with hk | hk
        · exact hF.directs r hr _ _ _ _ hbody hk
        · exact hF.digits r hr _ _ _ _ hbody hk
      rw [hbody] at hH
      obtain ⟨k, hkN, hkv⟩ := hH i (by simpa [hlen] using hi) _ (List.mem_singleton_self _)
      rw [Expr.eq_of_beq hb] at hkv
      refine ⟨k + B * Q, ?_, ?_⟩
      · simp only [digitsMax]
        have := Nat.mul_le_mul_left B hQ
        omega
      · simp only [List.map_cons, digitsVal, List.foldr_cons] at hQv ⊢
        rw [hkv, hQv]
        push_cast
        ring
    · cases hn
  | _ :: _, [], _, _, hl => by simp at hl

/-- **A `mod_q` in the committed-digits form holds** (`CommittedFormOk`): under the leaf facts, the
field equation (a field `equal`, `commRowB`) gives `e − e' − q·qlo = q · Σ_j R^j d_j` in the field
(`evalE_of_commPeel`, `commShift_spec`), the digits' `in`s make `Σ_j R^j d_j` the cast of a number
`Q ≤ Σ_j R^j (N_j − 1)` (`digitsVal_of_commRanges`), the sides' integer readings lie in the exported
intervals, and the no-wrap conditions lift the equation to the integers
(`IntIn.sub_eq_natCast`): `e − e' = q (qlo + Q)`. -/
theorem holdsWith_mod_of_committed (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd)
    {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L)
    {d q : ℕ} {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hok : ir.CommittedFormOk L d q e e' real) :
    ir.HoldsWith rd (.mod d q e e' real) := by
  obtain ⟨hex, hlen⟩ := hpo
  have he := hex (d, e) (by simp [PredBody.exprs])
  have he' := hex (d, e') (by simp [PredBody.exprs])
  obtain ⟨-, hchar, -, hdec0⟩ := modData hwf hI hL he.1 hok.char
  have hdec : ∀ c < ir.charOf (ir.domainField d),
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K) := hdec0
  have hf : ir.domainField d < ir.fields.length := domainField_lt hwf he.1
  have hp0 : 0 < ir.charOf (ir.domainField d) := by have := hok.char; omega
  refine (holdsWith_mod_iff (.inl (by rw [hok.form]; rfl))).2 ?_
  intro i hi
  obtain ⟨⟨ha1, ha2⟩, hca⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he.2 hok.lhs hi
  obtain ⟨⟨hb1, hb2⟩, hcb⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he'.2 hok.rhs
    (hlen ▸ hi)
  have hbd := hok.bounds
  unfold commBounds at hbd
  split_ifs at hbd with hl
  obtain ⟨Q, hQ, hQv⟩ := digitsVal_of_commRanges hF real.radix hi real.digits real.ranges _ hbd hl
  obtain ⟨pr, hpr, hrow⟩ := List.any_eq_true.1 hok.row
  obtain ⟨qi, hqi, rfl⟩ := exists_index_of_mem hpr
  have hneg : ∀ c, c + 1 = ir.charOf (ir.domainField d) →
      (I (ir.domainField d)).decode c = -1 := by
    intro c hc
    rw [hdec c (by omega), eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, hc,
      CharP.cast_eq_zero]
  obtain ⟨hshl, hshc⟩ := commShift_spec (K := (I (ir.domainField d)).K) hp0 q real
  unfold commRowB at hrow
  split at hrow
  · rename_i d' L z t hbody
    simp only [Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨⟨hd', hz⟩, hm⟩ := hrow
    rw [hd'] at hbody
    split at hm
    · rename_i h hpeel
      obtain ⟨hev, hlenL⟩ := evalE_of_commPeel rd hdec _ L hpeel
      unfold commHeadB at hm
      split at hm
      · rename_i Xh b sh
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨⟨hX, hb⟩, hsh⟩ := hm
        obtain ⟨hXe, hXl⟩ := evalE_of_subB rd hdec e e' Xh hX
        have hH := hF.equals qi hqi (by rw [hbody]; rfl)
        rw [hbody] at hH
        have hrow := hH i (by rw [hlenL, exprLen_add, hXl]; exact hi)
        simp only [evalWith] at hrow
        rw [hev i, evalE_add, evalE_scale_const, hXe i, hneg b hb,
          evalE_leaf_constAll hL hF hsh hf hshl hi,
          evalE_leaf_constAll hL hF hz hf hp0 hi, hshc, List.map_reverse, List.sum_reverse,
          sum_zipIdx_mul q real.radix (fun D => ir.evalE rd (ir.domainField d) D i) real.digits 0]
          at hrow
        have hQv' : digitsVal (real.radix : (I (ir.domainField d)).K)
            (real.digits.map fun D => ir.evalE rd (ir.domainField d) D i) = (Q : _) := hQv
        rw [hQv'] at hrow
        have hz' : IntIn (real.lhsLo - real.rhsHi) (real.lhsHi - real.rhsLo)
            (ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i)
            (ir.evalWith rd d e i - ir.evalWith rd d e' i) :=
          ⟨by linarith, by linarith, by push_cast; rw [hca, hcb]⟩
        have hM : (((q * digitsMax real.radix (ir.commN d e real) + 1 : ℕ) : ℤ)) - 1 +
            ((q : ℤ) * real.quotientLo - (real.lhsLo - real.rhsHi)) <
              ir.charOf (ir.domainField d) := by
          have := hok.noWrapDigits
          push_cast at this ⊢
          linarith
        have hQle : Q ≤ digitsMax real.radix (ir.commN d e real) := hQ
        have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d))
          (c := (q : ℤ) * real.quotientLo) (n := q * Q) hz' (by linarith [hok.noWrap]) hM
          (Nat.lt_succ_of_le (Nat.mul_le_mul_left q hQle))
          (by
            simp only [evalWith]
            push_cast
            push_cast at hrow
            linear_combination hrow)
        exact ⟨real.quotientLo + Q, by push_cast at hlift; linarith⟩
      · cases hm
    · cases hm
  · cases hrow

end

end GordieHowe.RealizedProgram
