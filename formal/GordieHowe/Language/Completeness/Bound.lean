-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Env

@[expose] public section

/-!
# GordieHowe: completeness certificates, the values bound to their digits

The digits of a two-sided or digit lookup are generated as its digits (`Gen.lookupDigit`): the
honest committed value at digit `j` is digit `j` in base `T` of the record's integer reading in the
environment of the execution (`genCommitted_lookupDigit`; of `N − 1` minus it for the second set,
`genCommitted_lookupSecond`), at the lookup's facts (`DigitLookupFactsC`). A value bound to its
digits is the record `v` or `v + c` of such a lookup (`boundRecB`), so at the honest committed
values it reads `0` past its size (`bindAsgC_bound_zero_past`) and its phase-`0` value below it
where the execution accepts (`bindAsgC_bound_honest`); at every environment whose assignment binds
the values to their digits, a bound value reads its expression (`boundReads_of_boundRecs`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir) in
/-- **The facts of a two-sided or digit lookup** `pid` with body `mem d [rec] (range N) (lookup r)`
at the certificate's generators `G`: a source
predicate of a domain with `k` digit values (and `k` second digits for a two-sided lookup, none for
a digit lookup), each generated as this lookup's digit at its position; the digits committed cells
of the record's length in the domain's field and no source values; the base above `1`; the range
within the digits and within the characteristic; the record reading source values that read no
challenge and no late value. -/
structure DigitLookupFactsC (G : Gens) (pid d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) :
    Prop where
  /-- A two-sided or digit lookup. -/
  kind : r.kind = .twoSided ∨ r.kind = .digits
  /-- A source predicate. -/
  source : ir.inSource (ir.predicate pid) = true
  /-- A domain of the program. -/
  domain : d < ir.domains.length
  /-- `k` digit values. -/
  len : r.digitValues.length = r.digits
  /-- `k` second digits for a two-sided lookup, none for a digit lookup. -/
  second : (r.kind = .twoSided → r.second.length = r.digits) ∧ (r.kind = .digits → r.second = [])
  /-- The digit values are generated as this lookup's at their positions. -/
  ownFirst : ∀ j (hj : j < r.digitValues.length), G.at r.digitValues[j] = .lookupDigit pid false j
  /-- The second digits are generated as this lookup's at their positions. -/
  ownSecond : ∀ j (hj : j < r.second.length), G.at r.second[j] = .lookupDigit pid true j
  /-- The digits are committed cells of the record's length in the domain's field, no source
  values. -/
  cells : ∀ u ∈ r.digitValues ++ r.second, ir.privCellB u = true ∧
    (ir.value u).size = ir.exprLen rec ∧ ir.valueField u = ir.domainField d ∧
      ¬ ir.IsSourceValue u
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- The range lies within the digits. -/
  honestRange : N ≤ r.base ^ r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : N ≤ ir.charOf (ir.domainField d)
  /-- The record reads source values that read no challenge and no late value. -/
  recReads : ∀ w ∈ ir.exprNodes rec, ir.IsSourceValue w ∧ (ir.readsT.getD w []).isEmpty = true

instance (G : Gens) (pid d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) :
    Decidable (ir.DigitLookupFactsC G pid d rec N r) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩,
     fun h => ⟨h.kind, h.source, h.domain, h.len, h.second, h.ownFirst, h.ownSecond, h.cells,
      h.baseGt, h.honestRange, h.rangeLe, h.recReads⟩⟩

/-- **The honest committed value at digit `j` of a two-sided or digit lookup**: digit `j` in base
`T` of the record's integer reading in the environment of the execution. -/
theorem genCommitted_lookupDigit {G : Gens} {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (x s : ir.Valuation I) (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r) {j : ℕ} (hj : j < r.digitValues.length) (i : ℕ) :
    ir.genCommitted I G x s r.digitValues[j] i =
      (((I (ir.domainField d)).toNat (ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d
        rec i) / r.base ^ j % r.base : ℕ) : (I (ir.valueField r.digitValues[j])).K) := by
  obtain ⟨-, -, -, hns⟩ := hF.cells _ (List.mem_append_left _ (List.getElem_mem hj))
  simp only [genCommitted, withGens, if_neg hns, hF.ownFirst j hj, lookupDigitNat, hb,
    List.headD_cons, Bool.false_eq_true, ite_false]

/-- **The honest committed value at second digit `j` of a two-sided lookup**: digit `j` in base `T`
of `N − 1` minus the record's integer reading in the environment of the execution. -/
theorem genCommitted_lookupSecond {G : Gens} {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (x s : ir.Valuation I) (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r) {j : ℕ} (hj : j < r.second.length) (i : ℕ) :
    ir.genCommitted I G x s r.second[j] i =
      (((N - 1 - (I (ir.domainField d)).toNat (ir.evalWith
        (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d rec i)) / r.base ^ j % r.base : ℕ) :
          (I (ir.valueField r.second[j])).K) := by
  obtain ⟨-, -, -, hns⟩ := hF.cells _ (List.mem_append_right _ (List.getElem_mem hj))
  simp only [genCommitted, withGens, if_neg hns, hF.ownSecond j hj, lookupDigitNat, hb,
    List.headD_cons, ite_true, InSet.bound]

variable (ir) in
/-- **Every two-sided and digit lookup whose record is no quotient digit has its facts** at the
certificate's generators `G` (`commRecOf? pid = none`), its digits generated as its digits. -/
abbrev DigitLookupsC (G : Gens) : Prop :=
  ∀ pid < ir.predicates.length, ∀ d rec N r,
    (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) →
      (r.kind = .twoSided ∨ r.kind = .digits) → (ir.commRecOf? pid).isNone →
        ir.DigitLookupFactsC G pid d rec N r

variable (ir) in
/-- **Every value bound to its digits is a source value and the record of a two-sided or digit
lookup** (`boundRecB`). -/
abbrev BoundRecs : Prop :=
  ∀ v < ir.values.length, (ir.value v).kind.isBound = true →
    ir.IsSourceValue v ∧ ir.boundRecB v = true

/-- **A value bound to its digits reads `0` past its size** at every honest assignment: its record is `v` or `v + c` of a two-sided or digit lookup whose
digits are cells of `v`'s size, reading `0` past it, and the constant `c` has at most `v`'s size
entries. -/
theorem bindAsgC_bound_zero_past (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {G : Gens} (hB : ir.BoundRecs) (hD : ir.DigitLookupsC G)
    (V : ir.Valuation I) (π : (ir.layout I).Pads) {v i : ℕ} (hv : v < ir.values.length)
    (hb : (ir.value v).kind.isBound = true) (hi : (ir.value v).size ≤ i) :
    (ir.bindAsg (ir.honestAsg I V π)).val v i = 0 := by
  obtain ⟨-, hBv⟩ := hB v hv hb
  obtain ⟨pid, hpid, d, rec, N, r, hbody, hk, hnc, hbd, hrec⟩ := exists_of_boundRecB hBv
  have hF := hD pid hpid d rec N r hbody hk (by rw [hnc]; rfl)
  have hf := domainField_lt hwf hF.domain
  have hchar := charP_field hI hf
  have hzero : ¬ i < ir.exprLen rec → ∀ u ∈ r.digitValues,
      (castElt (ir.committedRead (ir.honestAsg I V π) u i) : (I (ir.domainField d)).K) = 0 := by
    intro hil u hu
    obtain ⟨hc, hsz, -, -⟩ := hF.cells u (List.mem_append_left _ hu)
    rw [committedRead_of_priv _ (kind_of_privCellB hc),
      honestAsg_val_of_privCellB_of_le hc (by rw [hsz]; omega), castElt_zero]
  rcases hrec with rfl | ⟨cst, es, rfl, hkc, hes, -⟩
  · unfold boundDigitsOk at hbd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' hkx
      have hval : (ir.bindAsg (ir.honestAsg I V π)).val v i =
          ir.evalE (ir.committedRead (ir.honestAsg I V π)) (ir.valueField v) x' i := by
        simp only [bindAsg, hkx]
      rw [hval]
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf, evalE_of_digitsExprOk_zero hL hf hx
        (hzero (by change ¬ i < (ir.value v).size; omega)), castElt_zero]
    · cases hx
  · unfold boundDigitsOk at hbd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' c' u' hkx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨hu', -⟩, hx⟩ := hx
      rw [hu'] at hkx
      have hcl : cst < ir.values.length := by
        by_contra hcl
        rw [value_eq_default (Nat.le_of_not_lt hcl)] at hkc
        cases hkc
      have hval : (ir.bindAsg (ir.honestAsg I V π)).val v i =
          ir.evalE (ir.committedRead (ir.honestAsg I V π)) (ir.valueField v)
            (.add x' (.scale (.const c') (.leaf cst))) i := by
        simp only [bindAsg, hkx]
      rw [hval]
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf, evalE_add, evalE_scale_const, evalE_leaf,
        evalE_of_digitsExprOk_zero hL hf hx (hzero (by change ¬ i < (ir.value v).size; omega))]
      simp only [committedRead, hkc]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
        hL.decode_natCast _ (valueField_lt hwf hcl) 0 (by
          have := charP_field hI (valueField_lt hwf hcl)
          exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.valueField cst)).K _)),
        Nat.cast_zero, castElt_zero, castElt_zero]
      ring
    · cases hx

/-- **The honest digits rebuild a value bound to them** at the honest committed values where the
execution accepts: the value is the record `v` or `v + c` of a two-sided or
digit lookup (`boundRecB`), the honest digits are those of the record's integer reading in the
execution (`genCommitted_lookupDigit`), which is a natural below `N ≤ T^k` by the lookup's `in`; so
its digits' number is the record, and the value bound to them reads its phase-`0` value below its
size and `0` past it. -/
theorem bindAsgC_bound_honest (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {G : Gens} (hB : ir.BoundRecs) (hD : ir.DigitLookupsC G)
    {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
    (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads) {v : ℕ}
    (hv : v < ir.values.length) (hb : (ir.value v).kind.isBound = true) :
    (ir.bindAsg (ir.honestAsg I (ir.genCommitted I G x s) π)).val v = fun i =>
      if i < (ir.value v).size then s v i else 0 := by
  funext i
  split_ifs with hi
  swap
  · exact bindAsgC_bound_zero_past hwf hI hL hB hD _ π hv hb (by omega)
  obtain ⟨-, hBv⟩ := hB v hv hb
  obtain ⟨pid, hpid, d, rec, N, r, hbody, hk, hnc, hbd, hrec⟩ := exists_of_boundRecB hBv
  have hF := hD pid hpid d rec N r hbody hk (by rw [hnc]; rfl)
  have hf := domainField_lt hwf hF.domain
  have hchar := charP_field hI hf
  have hin : ∀ i < ir.exprLen rec, IsNatBelow N
      (ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d rec i) := by
    have hh := hA.sat.preds _ (predicate_mem hpid) hF.source
    rw [hbody] at hh
    intro i hi
    have := (inRows_range_iff _ d rec i N).1 (hh i hi)
    rwa [show ir.evalWith (ir.reader (ir.execEnv I x s l c)) d rec =
        ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d rec from
      funext fun i => congrFun (evalE_congr fun w hw =>
        reader_execEnv_congr_of_isEmpty hwf x s l 0 c (ir.chal0 I) (hF.recReads w hw).2) i] at this
  have hcr : ∀ j (hj : j < r.digitValues.length) i,
      ir.committedRead (ir.honestAsg I (ir.genCommitted I G x s) π) r.digitValues[j] i =
        if i < ir.exprLen rec then ir.genCommitted I G x s r.digitValues[j] i else 0 := by
    intro j hj i
    obtain ⟨hc, hsz, -, -⟩ := hF.cells _ (List.mem_append_left _ (List.getElem_mem hj))
    rw [committedRead_of_priv _ (kind_of_privCellB hc)]
    split_ifs with hi'
    · exact honestAsg_val_of_privCellB hc (by rw [hsz]; exact hi')
    · exact honestAsg_val_of_privCellB_of_le hc (by rw [hsz]; omega)
  have hdig : ∀ i < ir.exprLen rec, ∀ j (hj : j < r.digitValues.length),
      (castElt (ir.committedRead (ir.honestAsg I (ir.genCommitted I G x s) π) r.digitValues[j] i) :
        (I (ir.domainField d)).K) =
        (((I (ir.domainField d)).toNat (ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I)))
          d rec i) / r.base ^ j % r.base : ℕ) : _) := by
    intro i hi j hj
    obtain ⟨-, -, hfu, -⟩ := hF.cells _ (List.mem_append_left _ (List.getElem_mem hj))
    rw [hcr j hj i, if_pos hi, genCommitted_lookupDigit x s hbody hF hj, castElt_natCast hfu]
  have hlenT : ∀ i < ir.exprLen rec,
      (I (ir.domainField d)).toNat
          (ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d rec i) <
        r.base ^ r.digitValues.length := fun i hi => by
    rw [hF.len]
    exact lt_of_lt_of_le (natCast_toNat_of_isNatBelow hL hf hF.rangeLe (hin i hi)).2 hF.honestRange
  rcases hrec with rfl | ⟨cst, es, rfl, hkc, hes, -⟩
  · unfold boundDigitsOk at hbd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' hkx
      have hval : (ir.bindAsg (ir.honestAsg I (ir.genCommitted I G x s) π)).val v i =
          ir.evalE (ir.committedRead (ir.honestAsg I (ir.genCommitted I G x s) π))
            (ir.valueField v) x' i := by
        simp only [bindAsg, hkx]
      rw [hval]
      have hlen : ir.exprLen (.leaf v) = (ir.value v).size := rfl
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf,
        evalE_of_digitsExprOk_digits hL hf hx (hdig i (by rw [hlen]; exact hi)),
        Nat.mod_eq_of_lt (hlenT i (by rw [hlen]; exact hi)),
        (natCast_toNat_of_isNatBelow hL hf hF.rangeLe (hin i (by rw [hlen]; exact hi))).1]
      change castElt (ir.reader _ v i) = _
      rw [reader_execEnv_bound x s 0 _ hkx hi]
    · cases hx
  · unfold boundDigitsOk at hbd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' c' u' hkx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨hu', hc'⟩, hx⟩ := hx
      rw [hu'] at hkx
      have hcK : (I (ir.domainField d)).decode c' = -1 := by
        rw [hL.decode_natCast _ hf c' (by simp only [charOf] at hc'; omega), eq_neg_iff_add_eq_zero,
          ← Nat.cast_one, ← Nat.cast_add, hc', CharP.cast_eq_zero]
      have hcr0 : ir.committedRead (ir.honestAsg I (ir.genCommitted I G x s) π) cst i =
          ir.reader (ir.execEnv I x s 0 (ir.chal0 I)) cst i := by
        rw [reader_of_constant _ hkc]
        simp only [committedRead, hkc]
      have hval : (ir.bindAsg (ir.honestAsg I (ir.genCommitted I G x s) π)).val v i =
          ir.evalE (ir.committedRead (ir.honestAsg I (ir.genCommitted I G x s) π)) (ir.valueField v)
            (.add x' (.scale (.const c') (.leaf cst))) i := by
        simp only [bindAsg, hkx]
      rw [hval]
      have hlen : ir.exprLen (.add (.leaf v) (.leaf cst)) = (ir.value v).size := rfl
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf, evalE_add, evalE_scale_const, hcK, evalE_leaf, hcr0,
        evalE_of_digitsExprOk_digits hL hf hx (hdig i (by rw [hlen]; exact hi)),
        Nat.mod_eq_of_lt (hlenT i (by rw [hlen]; exact hi)),
        (natCast_toNat_of_isNatBelow hL hf hF.rangeLe (hin i (by rw [hlen]; exact hi))).1]
      change castElt (ir.reader _ v i) + castElt (ir.reader _ cst i) + -1 * _ = _
      rw [reader_execEnv_bound x s 0 _ hkx hi]
      ring
    · cases hx

/-- **Every value bound to its digits reads its expression** at an environment whose assignment is
the realized assignment of a committed assignment `a` (`BoundReads`): the value is the record `v` or `v + c` of a two-sided or digit lookup
(`boundRecB`), its expression is the number of the lookup's digits (and `c`), which are committed
cells reading `a` there, and `c` a constant. -/
theorem boundReads_of_boundRecs (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) {G : Gens}
    (hB : ir.BoundRecs) (hD : ir.DigitLookupsC G) {e : ir.Env I} {a : ir.Assignment I}
    (he : e.asg = ir.bindAsg a) : ir.BoundReads (ir.reader e) := by
  intro v hv x hk
  have hb : (ir.value v).kind.isBound = true := by rw [hk]; rfl
  obtain ⟨-, hBv⟩ := hB v hv hb
  obtain ⟨pid, hpid, d, rec, N, r, hbody, hkd, hnc, hbd, hrec⟩ := exists_of_boundRecB hBv
  have hF := hD pid hpid d rec N r hbody hkd (by rw [hnc]; rfl)
  have hf := domainField_lt hwf hF.domain
  have hu : ∀ u ∈ r.digitValues, ir.reader e u = ir.committedRead a u := fun u hu => by
    have hk' := kind_of_privCellB (hF.cells u (List.mem_append_left _ hu)).1
    rw [reader_of_priv e hk', he, ir.bindAsg_val_of_isBound _ (by rw [hk']; rfl),
      committedRead_of_priv _ hk']
  funext i
  have hrd : ir.reader e v i = ir.evalE (ir.committedRead a) (ir.valueField v) x i := by
    simp only [reader, fuel, read, hk, he, bindAsg]
  rw [hrd]
  have hdec : ∀ c < ir.charOf (ir.domainField d),
      (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K) :=
    fun c hc => hL.decode_natCast _ hf c hc
  have hmap : ∀ f, r.digitValues.map (fun u => (castElt (ir.committedRead a u i) : (I f).K)) =
      r.digitValues.map fun u => castElt (ir.reader e u i) :=
    fun f => List.map_congr_left fun u hu' => by rw [hu u hu']
  unfold boundDigitsOk at hbd
  rcases hrec with rfl | ⟨cst, es, rfl, hkc, -, -⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' hkx
      rw [hk] at hkx
      injection hkx with hx'
      subst hx'
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf, castElt_evalE hvf, evalE_of_digitsExprOk _ hdec hx,
        evalE_of_digitsExprOk _ hdec hx, hmap]
    · cases hx
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
    obtain ⟨⟨-, hvf⟩, hx⟩ := hbd
    split at hx
    · rename_i x' c' u' hkx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨hu', -⟩, hx⟩ := hx
      rw [hu'] at hkx
      rw [hk] at hkx
      injection hkx with hx'
      subst hx'
      refine (castElt_inj_of_eq hvf).1 ?_
      rw [castElt_evalE hvf, castElt_evalE hvf, evalE_add, evalE_add, evalE_scale_const,
        evalE_scale_const, evalE_leaf, evalE_leaf, evalE_of_digitsExprOk _ hdec hx,
        evalE_of_digitsExprOk _ hdec hx, hmap, reader_of_constant e hkc]
      simp only [committedRead, hkc]
    · cases hx

end

end GordieHowe.RealizedProgram
