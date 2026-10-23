-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeLookup
public import GordieHowe.Language.Realizations.ModEquality

@[expose] public section

/-!
# GordieHowe: the one-digit form of `mod_q`, realized

The lemmas that turn a `mod_q` in the one-digit form (`GordieHowe.RealizedProgram.OneDigitOk`; compiler/mod.h,
`kOneDigit`) into its integer congruence:

* **The field equation** (`GordieHowe.RealizedProgram.fieldEq_of_quotDerived`): the quotient is derived from the sides
  (`Q = q⁻¹ · (e − e') − qlo` as linear forms, `GordieHowe.RealizedProgram.quotDerivedB`,
  `GordieHowe.RealizedProgram.evalE_linForm`), so `e − e' = q · (qlo + Q)` holds in the field at every reader
  reading constants as constants. The C++ places no row for it (the export's `target` is `none`): the quotient is a derived
  value, and its only constraint is its range request.
* **The congruence** (`GordieHowe.RealizedProgram.holdsWith_mod_of_oneDigit`): the field equation `e − e' = q · Q`,
  the quotient's direct `in` `Q ∈ [0, N)` (a leaf fact), and the sides' integer readings in the
  exported intervals give `e − e' = q · (qlo + k)` over the integers for the natural `k < N` the
  quotient is the cast of, under the no-wrap conditions (`IntIn.sub_eq_natCast`), so `q` divides `e − e'`.

The honest prover needs no lemma: the quotient's `in` is a predicate of the program, so the honest
strategy's `sat` gives it, and the field equation holds at every reader.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-! ## Linear forms -/

section LinForm

/-- **A sum splits over a filter and its complement.** -/
theorem sum_map_filter_add_not {α M : Type*} [AddCommMonoid M] (P : α → Bool) (F : α → M) :
    ∀ l : List α, (l.map F).sum = ((l.filter P).map F).sum + ((l.filter fun a => !P a).map F).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_filter_add_not P F l]
    cases h : P a <;> simp [List.filter_cons, h, add_left_comm, add_assoc]

/-- **A linear combination whose coefficients cancel modulo the characteristic vanishes**: where
the coefficients of the terms equal to each term sum to a multiple of `p` (`linZeroB`'s terms
condition), the combination `Σ_j a_j · g(t_j)` is `0` in a ring of characteristic `p`. -/
theorem sum_eq_zero_of_groups {K : Type*} [CommRing K] {p : ℕ} [CharP K p] (g : Expr → K) :
    ∀ (n : ℕ) (ts : List (ℤ × Expr)), ts.length ≤ n →
      (∀ t ∈ ts, ((ts.filter fun u => u.2.beq t.2).map (·.1)).sum % (p : ℤ) = 0) →
      (ts.map fun t => (t.1 : K) * g t.2).sum = 0
  | _, [], _, _ => by simp
  | 0, _ :: _, hn, _ => absurd hn (by simp)
  | n + 1, t :: rest, hn, h => by
    set ts := t :: rest with hts
    rw [sum_map_filter_add_not (fun u => u.2.beq t.2) _ ts]
    have hS : ((ts.filter fun u => u.2.beq t.2).map fun u => (u.1 : K) * g u.2).sum = 0 := by
      have hmap : ((ts.filter fun u => u.2.beq t.2).map fun u => (u.1 : K) * g u.2) =
          ((ts.filter fun u => u.2.beq t.2).map fun u => (u.1 : K) * g t.2) := by
        refine List.map_congr_left fun u hu => ?_
        have hb : u.2.beq t.2 = true := (List.mem_filter.1 hu).2
        rw [Expr.eq_of_beq hb]
      rw [hmap, List.sum_map_mul_right]
      have hz := h t (List.mem_cons_self ..)
      have hc : Int.cast (R := K) (((ts.filter fun u => u.2.beq t.2).map (·.1)).sum) = 0 :=
        (CharP.intCast_eq_zero_iff K p _).2 (Int.dvd_of_emod_eq_zero hz)
      have hc' : ((ts.filter fun u => u.2.beq t.2).map fun u => (u.1 : K)).sum = 0 := by
        simpa [Int.cast_list_sum, List.map_map, Function.comp_def] using hc
      rw [hc', zero_mul]
    rw [hS, zero_add]
    set R := ts.filter fun u => !(u.2.beq t.2) with hR
    have hlen : R.length ≤ n := by
      have : R.length < ts.length := by
        refine List.length_filter_lt_length_iff_exists.2 ⟨t, List.mem_cons_self .., ?_⟩
        simp [Expr.beq_self]
      rw [hts, List.length_cons] at this hn
      omega
    refine sum_eq_zero_of_groups g n R hlen fun u hu => ?_
    have hu' := List.mem_filter.1 hu
    have hne : u.2 ≠ t.2 := fun he => by simp [he, Expr.beq_self] at hu'
    have hf : (R.filter fun w => w.2.beq u.2) = ts.filter fun w => w.2.beq u.2 := by
      rw [hR, List.filter_filter]
      refine List.filter_congr fun w _ => ?_
      cases hw : w.2.beq u.2
      · simp
      · have := Expr.eq_of_beq hw
        have hwt : w.2.beq t.2 = false := by
          cases hb : w.2.beq t.2
          · rfl
          · exact absurd (this.symm.trans (Expr.eq_of_beq hb)) hne
        simp [hwt]
    rw [hf]
    exact h u hu'.1

/-- **Negating a linear form's coefficients negates its value.** -/
theorem linSum_neg {K : Type*} [CommRing K] (g : Expr → K) (l : List (ℤ × Expr)) :
    ((l.map fun t => (-t.1, t.2)).map fun t => (t.1 : K) * g t.2).sum =
      -(l.map fun t => (t.1 : K) * g t.2).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    ring

/-- **Scaling a linear form's coefficients scales its value.** -/
theorem linSum_scale {K : Type*} [CommRing K] (g : Expr → K) (k : ℤ) (l : List (ℤ × Expr)) :
    ((l.map fun t => (k * t.1, t.2)).map fun t => (t.1 : K) * g t.2).sum =
      (k : K) * (l.map fun t => (t.1 : K) * g t.2).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    push_cast
    ring

variable {rd : ir.Valuation I} (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
  rd v i = (I (ir.valueField v)).decode (es.getD i 0))

include hK in
/-- **An expression is its linear form** (`linForm`) at its first `n` coordinates, at a reader
reading constants as constants and lawful integer readings. -/
theorem evalE_linForm (hL : I.Lawful ir primeNodes) {f n : ℕ} (hf : f < ir.fields.length) :
    ∀ (e : Expr) (x : ℤ × List (ℤ × Expr)), ir.linForm f n e = some x → ∀ i < n,
      ir.evalE rd f e i = (x.1 : (I f).K) + (x.2.map fun t => (t.1 : (I f).K) * ir.evalE rd f t.2 i).sum
  | .add a b, x, h, i, hi => by
    simp only [linForm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    rw [evalE_add, evalE_linForm hL hf a xa ha i hi, evalE_linForm hL hf b xb hb i hi]
    simp only [List.map_append, List.sum_append]
    push_cast
    ring
  | .sub a b, x, h, i, hi => by
    simp only [linForm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    rw [evalE_sub, evalE_linForm hL hf a xa ha i hi, evalE_linForm hL hf b xb hb i hi]
    simp only [List.map_append, List.sum_append]
    rw [linSum_neg (fun t => ir.evalE rd f t i)]
    push_cast
    ring
  | .scale (.const k) a, x, h, i, hi => by
    simp only [linForm] at h
    split_ifs at h with hk
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨xa, ha, rfl⟩ := h
    rw [evalE_scale_const, hL.decode_natCast _ hf k hk, evalE_linForm hL hf a xa ha i hi]
    simp only
    rw [linSum_scale (fun t => ir.evalE rd f t i)]
    push_cast
    ring
  | .leaf v, x, h, i, hi => by
    simp only [linForm] at h
    split at h
    · rename_i c hc
      cases h
      unfold constEntry at hc
      split at hc
      · split_ifs at hc with hc'
        cases hc
        simp only [List.map_nil, List.sum_nil, add_zero, Int.cast_natCast]
        exact evalE_leaf_constAll_of hL hK hc'.1 hf hc'.2 hi
      · cases hc
    · cases h
      simp
  | .scale (.node _ _) _, x, h, _, _ => by cases h; simp
  | .mul _ _, x, h, _, _ => by cases h; simp
  | .reindex _ _, x, h, _, _ => by cases h; simp
  | .concat _ _, x, h, _, _ => by cases h; simp
  | .linear _ _, x, h, _, _ => by cases h; simp
  | .prod _ _, x, h, _, _ => by cases h; simp
  | .mux _ _ _, x, h, _, _ => by cases h; simp
  | .apply _ _, x, h, _, _ => by cases h; simp
  | .ref _, x, h, _, _ => by cases h; simp
  | .logic _ _ _, x, h, _, _ => by cases h; simp

include hK in
/-- **A quotient derived from the sides satisfies the field equation** `e − e' = q · (qlo + Q)`
below the left side's length (`quotDerivedB`: the linear form of `q · Q − e + e' + q · qlo`
vanishes modulo `p`, `evalE_linForm`, `sum_eq_zero_of_groups`), at a reader reading constants as
constants. -/
theorem fieldEq_of_quotDerived (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hd : d < ir.domains.length) (h : ir.quotDerivedB d q e e' real = true)
    {i : ℕ} (hi : i < ir.exprLen e) :
    ir.evalWith rd d e i - ir.evalWith rd d e' i =
      (q : (I (ir.domainField d)).K) *
        ((real.quotientLo : (I (ir.domainField d)).K) + ir.evalWith rd d real.quotExpr i) := by
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  unfold quotDerivedB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  simp only [evalWith]
  rw [← evalE_deref hwf.refsOrdered rd _ real.quotExpr]
  split at h
  · rename_i xQ x x' hQ hx hx'
    unfold linZeroB at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hc, ht⟩ := h
    have h0 := sum_eq_zero_of_groups (K := (I (ir.domainField d)).K)
      (p := ir.charOf (ir.domainField d)) (fun t => ir.evalE rd (ir.domainField d) t i) _ _ le_rfl
      fun t htm => ht t htm
    have hc0 : (((q * xQ.1 - x.1 + x'.1 + q * real.quotientLo : ℤ)) : (I (ir.domainField d)).K) = 0 :=
      (CharP.intCast_eq_zero_iff _ (ir.charOf (ir.domainField d)) _).2 (Int.dvd_of_emod_eq_zero hc)
    rw [evalE_linForm hK hL hf _ _ hQ i hi, evalE_linForm hK hL hf _ _ hx i hi,
      evalE_linForm hK hL hf _ _ hx' i hi]
    simp only [List.map_append, List.sum_append] at h0
    rw [linSum_scale (fun t => ir.evalE rd (ir.domainField d) t i),
      linSum_neg (fun t => ir.evalE rd (ir.domainField d) t i)] at h0
    push_cast at h0 hc0
    linear_combination -h0 - hc0
  · cases h

/-- **A derived quotient's modulus is invertible in the field** (`quotDerivedB`: `q` is not a
multiple of the characteristic). -/
theorem quot_ne_zero_of_quotDerivedB (hwf : ir.WellFormed) (hI : I.Registered ir) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hd : d < ir.domains.length)
    (h : ir.quotDerivedB d q e e' real = true) : (q : (I (ir.domainField d)).K) ≠ 0 := by
  have hchar := charP_field hI (domainField_lt hwf hd)
  unfold quotDerivedB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro h0
  exact h.1 (Nat.mod_eq_zero_of_dvd ((CharP.cast_eq_zero_iff _ _ q).1 h0))

end LinForm

/-- **A `mod_q` in the one-digit form holds where its field equation does** (`OneDigitOk`): under
the leaf facts, the quotient's direct `in` makes it the cast of a natural `k < N`, the sides'
integer readings lie in the exported intervals and cast to the sides' values, and the no-wrap
conditions `lhsHi − rhsLo < p` and `q (N − 1) + rhsHi − lhsLo < p` lift `e − e' = q k` to the
integers (`IntIn.sub_eq_natCast`). -/
theorem holdsWith_mod_of_oneDigit (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hok : ir.OneDigitOk L d q e e' real)
    (h : ∀ i < ir.exprLen e, ir.evalWith rd d e i - ir.evalWith rd d e' i =
      (q : (I (ir.domainField d)).K) *
        ((real.quotientLo : (I (ir.domainField d)).K) + ir.evalWith rd d real.quotExpr i)) :
    ir.HoldsWith rd (.mod d q e e' real) := by
  obtain ⟨hex, hlen⟩ := hpo
  have he := hex (d, e) (by simp [PredBody.exprs])
  have he' := hex (d, e') (by simp [PredBody.exprs])
  have hchar := (modData hwf hI hL he.1 hok.char).2.1
  intro i hi
  obtain ⟨⟨ha1, ha2⟩, hca⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he.2 hok.lhs hi
  obtain ⟨⟨hb1, hb2⟩, hcb⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he'.2 hok.rhs
    (hlen ▸ hi)
  -- the quotient's direct `in`
  obtain ⟨rid, -, hq⟩ := List.any_eq_true.1 hok.range
  unfold quotRangeB at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨hrid, hq⟩ := hq
  split at hq
  · rename_i d' Q' N r hbody
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    obtain ⟨⟨⟨⟨⟨hd', hk⟩, hQ⟩, hlenQ⟩, hN⟩, hwrap⟩ := hq
    have hH := hF.directs rid hrid d' [Q'] (.range N) r hbody hk
    rw [hbody] at hH
    obtain ⟨k, hkN, hkv⟩ := hH i (by simpa [hlenQ] using hi) Q' (List.mem_singleton_self _)
    rw [Expr.eq_of_beq hQ, hd'] at hkv
    -- the integer lift
    have hz : IntIn (real.lhsLo - real.rhsHi) (real.lhsHi - real.rhsLo)
        (ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i)
        (ir.evalWith rd d e i - ir.evalWith rd d e' i) :=
      ⟨by linarith, by linarith, by push_cast; rw [hca, hcb]⟩
    have hM : (((q * (N - 1) + 1 : ℕ) : ℤ)) - 1 + (q * real.quotientLo - (real.lhsLo - real.rhsHi)) <
        ir.charOf (ir.domainField d) := by
      push_cast [Nat.cast_add] at hwrap ⊢
      linarith
    have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d))
      (c := q * real.quotientLo) (n := q * k) hz (by linarith [hok.noWrap]) hM
      (Nat.lt_succ_of_le (Nat.mul_le_mul_left q (by omega)))
      (by rw [h i hi, hkv]; push_cast; ring)
    exact ⟨real.quotientLo + k, by push_cast at hlift; linarith⟩
  · cases hq

/-! ## An `in` implied by intervals -/

/-- **A direct `in` on an expression bounds it** (`exprRange`): under the leaf facts, every
coordinate below its length is the cast of a natural below the bound. -/
theorem exprRange_sound {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d N : ℕ} {a : Expr}
    (h : ir.exprRange d a = some N) {i : ℕ} (hi : i < ir.exprLen a) :
    ∃ k < N, ir.evalWith rd d a i = k := by
  obtain ⟨q, hq, hqm⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hq
  unfold exprRangeOf at hqm
  split at hqm
  · rename_i d' a' N' r hbody
    split_ifs at hqm with hc
    cases hqm
    obtain ⟨rfl, hk, hb, -⟩ := hc
    have hH := hF.directs pid hpid _ _ _ _ hbody hk
    rw [hbody] at hH
    obtain rfl := Expr.eq_of_beq hb
    exact hH i (by simpa using hi) _ (List.mem_singleton_self _)
  · cases hqm

/-! ## The digit form -/

/-- **The value of the digits `l ++ [t]`** in base `T`: the value of `l` plus `T^|l| · t`. -/
theorem digitsVal_append_singleton {K : Type} [CommSemiring K] (T t : K) :
    ∀ l : List K, digitsVal T (l ++ [t]) = digitsVal T l + T ^ l.length * t
  | [] => by simp [digitsVal]
  | y :: l => by
    have := digitsVal_append_singleton T t l
    simp only [digitsVal] at this ⊢
    simp only [List.cons_append, List.foldr_cons, this, List.length_cons, pow_succ]
    ring

/-- **The accumulator row's left side is `acc − e`** (`accTerms`), where `p − 1` decodes to `−1`. -/
theorem evalE_of_accTerms (rd : ir.Valuation I) {f p acc : ℕ}
    (hneg : ∀ c, c + 1 = p → (I f).decode c = -1) :
    ∀ (n : ℕ) (e L : Expr), sizeOf e < n → accTerms p acc L e = true → ∀ i,
      ir.evalE rd f L i = castElt (rd acc i) - ir.evalE rd f e i
  | 0, _, _, he, _, _ => absurd he (Nat.not_lt_zero _)
  | n + 1, e, L, he, h, i => by
    unfold accTerms at h
    split at h
    · rename_i L' c t e₁ e₂
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hc, ht⟩, hrec⟩ := h
      rw [evalE_add, evalE_scale_const, hneg c hc, Expr.eq_of_beq ht,
        evalE_of_accTerms rd hneg n e₁ L' (by simp at he; omega) hrec i, evalE_add]
      ring
    · rename_i a c t e'
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, hc⟩, ht⟩ := h
      rw [evalE_add, evalE_leaf, evalE_scale_const, hneg c hc, Expr.eq_of_beq ht]
      ring
    · cases h

/-- **The accumulator row's left side has the accumulator's length** (`accTerms`). -/
theorem exprLen_of_accTerms {p acc : ℕ} :
    ∀ (n : ℕ) (e L : Expr), sizeOf e < n → accTerms p acc L e = true →
      ir.exprLen L = (ir.value acc).size
  | 0, _, _, he, _ => absurd he (Nat.not_lt_zero _)
  | n + 1, e, L, he, h => by
    unfold accTerms at h
    split at h
    · rename_i L' c t e₁ e₂
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact exprLen_of_accTerms n e₁ L' (by simp at he; omega) h.2
    · rename_i a c t e'
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      rfl
    · cases h

/-- **The accumulator commits the left side** (`accRowB`): under the leaf facts, `acc` and `e` agree
at every coordinate below `e`'s length. -/
theorem evalWith_acc_of_accRowB (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d acc : ℕ}
    {e : Expr} (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d))
    (h : ir.accRowB d acc e = true) :
    ∀ i < ir.exprLen e, ir.evalWith rd d (.leaf acc) i = ir.evalWith rd d e i := by
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  intro i hi
  unfold accRowB at h
  rcases Bool.or_eq_true_iff.1 h with hb | h
  · rw [Expr.eq_of_beq hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨hacc, hvf⟩, hsz⟩, q, hq, hm⟩ := h
  obtain ⟨qi, hqi, rfl⟩ := exists_index_of_mem hq
  split at hm
  · rename_i d' L z t hbody
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨rfl, hz⟩, hL'⟩ := hm
    have hneg : ∀ c, c + 1 = ir.charOf (ir.domainField d') →
        (I (ir.domainField d')).decode c = -1 := by
      intro c hc
      rw [hL.decode_natCast _ hf c (by simp only [charOf] at hc; omega), eq_neg_iff_add_eq_zero,
        ← Nat.cast_one,
        ← Nat.cast_add, hc, CharP.cast_eq_zero]
    have hH := hF.equals qi hqi (by rw [hbody]; rfl)
    rw [hbody] at hH
    have hlenL := exprLen_of_accTerms (ir := ir) _ e L (Nat.lt_succ_self _) hL'
    have := hH i (by rw [hlenL, hsz]; exact hi)
    simp only [evalWith] at this ⊢
    rw [evalE_of_accTerms rd hneg _ e L (Nat.lt_succ_self _) hL' i,
      evalE_leaf_constAll hL hF hz hf (by omega) hi, Nat.cast_zero, sub_eq_zero] at this
    rw [evalE_leaf, this]
  · cases hm

/-- **The terms `c_j · d_j` of a derived top digit** (`topDerivedB`), each with
`P c_j + q B^(s+j) ≡ 0` modulo `p`: `P` times their sum is `−q B^s` times the value of the `d_j` in
base `B`. -/
theorem sum_terms_mul {K : Type} [Field K] {p : ℕ} [CharP K p] (dec : ℕ → K)
    (hdec : ∀ c < p, dec c = (c : K)) (x : ℕ → K) (P q B : ℕ) :
    ∀ (ts : List (ℕ × ℕ)) (s : ℕ), (ts.zipIdx s).all (fun cuj => decide (cuj.1.1 < p) &&
        decide ((P * cuj.1.1 + q * B ^ cuj.2) % p = 0)) = true →
      (P : K) * (ts.map fun cu => dec cu.1 * x cu.2).sum =
        -(q : K) * (B : K) ^ s * digitsVal (B : K) (ts.map fun cu => x cu.2)
  | [], _, _ => by simp [digitsVal]
  | (c, u) :: ts, s, h => by
    simp only [List.zipIdx_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hm⟩, hrest⟩ := h
    have hcK : (P : K) * c = -((q : K) * (B : K) ^ s) := by
      have h0 : ((P * c + q * B ^ s : ℕ) : K) = 0 :=
        (CharP.cast_eq_zero_iff K p _).2 (Nat.dvd_of_mod_eq_zero hm)
      push_cast at h0
      linear_combination h0
    have ih := sum_terms_mul dec hdec x P q B ts (s + 1) hrest
    simp only [List.map_cons, List.sum_cons, digitsVal, List.foldr_cons] at ih ⊢
    rw [mul_add, ← mul_assoc, hdec c hc, hcK, ih]
    ring

/-- **A derived top digit satisfies the field equation** `acc − e' = q · Σ_j B^j d_j` at every
reader (`topDerivedB`). -/
theorem fieldEq_of_topDerived (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (rd : ir.Valuation I) {d q : ℕ} {e' : Expr}
    {real : ModRealization} {acc : ℕ} (hd : d < ir.domains.length)
    (h : ir.topDerivedB d q e' real acc = true) (i : ℕ) :
    ir.evalWith rd d (.leaf acc) i - ir.evalWith rd d e' i =
      (q : (I (ir.domainField d)).K) *
        digitsVal (real.radix : (I (ir.domainField d)).K)
          (real.digits.map fun D => ir.evalWith rd d D i) := by
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  have hdec := hL.decode_natCast _ hf
  unfold topDerivedB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i top lowerRev hrev
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, h⟩ := h
    split at h
    · rename_i a acc' b e₂ ts hpl
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨rfl, he₂⟩, ha⟩, hb⟩, hPa⟩, hPb⟩, hlow⟩, hts⟩ := h
      have hdig : real.digits = lowerRev.reverse ++ [top] := List.reverse_eq_cons_iff.1 hrev
      have hlower := Expr.eq_of_beqList hlow
      obtain ⟨hev, -⟩ := peel_spec rd (ir.domainField d) _ _ hpl
      set P := q * real.radix ^ lowerRev.reverse.length
      have hPa' : (P : (I (ir.domainField d)).K) * a = 1 := by
        rw [← Nat.cast_mul, CharP.cast_eq_mod (I (ir.domainField d)).K
          (ir.charOf (ir.domainField d)), hPa, Nat.cast_one]
      have hPb' : (P : (I (ir.domainField d)).K) * b + 1 = 0 := by
        rw [← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add,
          CharP.cast_eq_mod (I (ir.domainField d)).K (ir.charOf (ir.domainField d)), hPb,
          Nat.cast_zero]
      have hsum := sum_terms_mul (p := ir.charOf (ir.domainField d)) _ hdec
        (fun u => castElt (rd u i)) P q real.radix ts 0 hts
      have htop : ir.evalWith rd d top i = a * ir.evalWith rd d (.leaf acc') i +
          b * ir.evalWith rd d e' i +
          (ts.map fun cu => (I (ir.domainField d)).decode cu.1 * castElt (rd cu.2 i)).sum := by
        simp only [evalWith]
        rw [← evalE_deref hwf.refsOrdered rd _ top, hev, evalE_add, evalE_scale_const,
          evalE_scale_const, Expr.eq_of_beq he₂, hdec a ha, hdec b hb]
      have hlow' : lowerRev.reverse.map (fun D => ir.evalWith rd d D i) =
          ts.map fun cu => castElt (rd cu.2 i) := by
        rw [hlower, List.map_map]
        rfl
      have hlen : lowerRev.reverse.length = ts.length := by
        rw [hlower, List.length_map]
      rw [hdig, List.map_append, List.map_singleton, digitsVal_append_singleton, hlow',
        List.length_map, ← hlen]
      simp only [pow_zero, mul_one, neg_mul] at hsum
      have hP : (P : (I (ir.domainField d)).K) =
          (q : (I (ir.domainField d)).K) * (real.radix : (I (ir.domainField d)).K) ^
            lowerRev.reverse.length := by
        simp only [P]
        push_cast
        ring
      rw [htop]
      rw [hP] at hPa' hPb' hsum
      linear_combination (-(ir.evalWith rd d (.leaf acc') i)) * hPa' -
        ir.evalWith rd d e' i * hPb' - hsum
    · cases h
  · cases h

/-- **Digits bounded by direct `in`s** (`digitRangeOf`): under the leaf facts, at a coordinate
below the left side's length, the digits' value in base `B` is the cast of a number at most
`Σ_j B^j (N_j − 1)`. -/
theorem digitsVal_of_digitRanges {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d : ℕ} {e : Expr}
    (B : ℕ) {i : ℕ} (hi : i < ir.exprLen e) :
    ∀ (Ds : List Expr) (rs N : List ℕ),
      (Ds.zip rs).mapM (fun Dr => ir.digitRangeOf d e Dr.1 Dr.2) = some N → Ds.length = rs.length →
        ∃ Q ≤ digitsMax B N, digitsVal (B : (I (ir.domainField d)).K)
          (Ds.map fun D => ir.evalWith rd d D i) = (Q : _)
  | [], rs, N, h, hl => by
    simp only [List.zip_nil_left, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨0, le_rfl, by simp [digitsVal]⟩
  | D :: Ds, r :: rs, N, h, hl => by
    rw [List.zip_cons_cons, List.mapM_cons] at h
    cases hn : ir.digitRangeOf d e D r with
    | none => simp [hn] at h
    | some n =>
    cases hN' : (Ds.zip rs).mapM (fun Dr => ir.digitRangeOf d e Dr.1 Dr.2) with
    | none => simp [hn, hN'] at h
    | some N' =>
    simp [hn, hN'] at h
    subst h
    obtain ⟨Q, hQ, hQv⟩ := digitsVal_of_digitRanges hF B hi Ds rs N' hN' (by simpa using hl)
    unfold digitRangeOf at hn
    split_ifs at hn with hr
    split at hn
    · rename_i d' D' N'' r' hbody
      split_ifs at hn with hc
      cases hn
      obtain ⟨rfl, hk, hb, hlen, -⟩ := hc
      have hH := hF.directs r hr _ _ _ _ hbody hk
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

/-- **A `mod_q` in the digit form holds** (`DigitsFormOk`): under the leaf facts, the accumulator
commits the left side (`evalWith_acc_of_accRowB`), the derived top digit gives
`e − e' = q · Σ_j B^j d_j` in the field (`fieldEq_of_topDerived`), the digits' direct `in`s make
`Σ_j B^j d_j` the cast of a number `Q ≤ Σ_j B^j (N_j − 1)`, the sides' integer readings lie in the
exported intervals, and the no-wrap conditions lift `e − e' = q Q` to the integers
(`IntIn.sub_eq_natCast`). -/
theorem holdsWith_mod_of_digits (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d q : ℕ}
    {e e' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q e e' real))
    (hok : ir.DigitsFormOk L d q e e' real) :
    ir.HoldsWith rd (.mod d q e e' real) := by
  obtain ⟨hex, hlen⟩ := hpo
  have he := hex (d, e) (by simp [PredBody.exprs])
  have he' := hex (d, e') (by simp [PredBody.exprs])
  have hchar := (modData hwf hI hL he.1 hok.char).2.1
  intro i hi
  obtain ⟨⟨ha1, ha2⟩, hca⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he.2 hok.lhs hi
  obtain ⟨⟨hb1, hb2⟩, hcb⟩ := exprIvl_within hwf hI hL hF hK hLok he.1 hok.char he'.2 hok.rhs
    (hlen ▸ hi)
  have hacc := evalWith_acc_of_accRowB hwf hI hL hF he.1 hok.char hok.acc i hi
  have htop := fieldEq_of_topDerived hwf hI hL rd he.1 hok.derived i
  have hbd := hok.bounds
  unfold digitBounds at hbd
  split_ifs at hbd with hl
  obtain ⟨Q, hQ, hQv⟩ := digitsVal_of_digitRanges hF real.radix hi real.digits real.ranges _ hbd hl
  have hz : IntIn (real.lhsLo - real.rhsHi) (real.lhsHi - real.rhsLo)
      (ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i)
      (ir.evalWith rd d e i - ir.evalWith rd d e' i) :=
    ⟨by linarith, by linarith, by push_cast; rw [hca, hcb]⟩
  have hM : (((q * digitsMax real.radix (ir.digitsN d e real) + 1 : ℕ) : ℤ)) - 1 +
      (0 - (real.lhsLo - real.rhsHi)) < ir.charOf (ir.domainField d) := by
    have := hok.noWrapDigits
    push_cast at this ⊢
    linarith
  have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d)) (c := 0)
    (n := q * Q) hz (by simpa using hok.noWrap) hM
    (Nat.lt_succ_of_le (Nat.mul_le_mul_left q hQ))
    (by rw [← hacc, htop, hQv]; push_cast; ring)
  exact ⟨Q, by push_cast at hlift; linarith⟩

end

end GordieHowe.RealizedProgram
