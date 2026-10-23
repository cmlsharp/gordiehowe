-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Committed

@[expose] public section

/-!
# GordieHowe: completeness certificates, the lookup digits

The digits of a two-sided or digit lookup are generated as its digits (`Gen.lookupDigit`): the
honest committed value at digit `j` is digit `j` in base `T` of the record's integer reading in the
environment of the execution (`genCommitted_lookupDigit`; of `N − 1` minus it for the second set,
`genCommitted_lookupSecond`; both in `GordieHowe/Language/Completeness/Bound.lean`, with the
lookup's facts `DigitLookupFactsC`). At the source environment of the honest committed values the
digits are the record's (`digitsRead_srcEnvC`), so they are below their bases
(`digitsBelow_srcEnvCC` in `GordieHowe/Language/Completeness/CommDigits.lean`) and the lookup's reconstruction and top rows hold (`holds_reconRowC`,
`holds_topRowC`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **The reconstruction row of a two-sided or digit lookup holds** at a reader where the record is
a natural below `N` and the digits are its digits. -/
theorem holds_reconRowC (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {G : Gens} {e : ir.Env I} {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hF : ir.DigitLookupFactsC G pid d rec N r) {q : PredBody}
    (hq : ir.reconMatch d rec r q = true)
    (hnat : ∀ i < ir.exprLen rec, IsNatBelow N (ir.evalWith (ir.reader e) d rec i))
    (hdig : ir.DigitsRead (ir.reader e) d rec N r) : ir.HoldsWith (ir.reader e) q := by
  have hf := domainField_lt hwf hF.domain
  have hchar := charP_field hI hf
  unfold reconMatch at hq
  split at hq
  · rename_i d' L z m
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨⟨hd, hz⟩, hp⟩ := hq
    subst d'
    rcases hpl : peel r.digits L with _ | ⟨h, ts⟩
    · rw [hpl] at hp
      cases hp
    rw [hpl] at hp
    simp only [Bool.and_eq_true] at hp
    obtain ⟨hm, hch⟩ := hp
    obtain ⟨hev, hlen⟩ := peel_spec (ir.reader e) (ir.domainField d) r.digits L hpl
    have hlenh := exprLen_of_needleMatches hwf.refsOrdered hm
    intro i hi
    rw [hlen, hlenh] at hi
    obtain ⟨hn, hnN⟩ := natCast_toNat_of_isNatBelow hL hf hF.rangeLe (hnat i hi)
    have hp0 : 0 < ir.charOf (ir.domainField d) := lt_of_le_of_lt (Nat.zero_le _)
      (lt_of_lt_of_le hnN hF.rangeLe)
    have hT : (I (ir.domainField d)).toNat (ir.evalWith (ir.reader e) d rec i) <
        r.base ^ r.digitValues.length := by
      rw [hF.len]
      exact lt_of_lt_of_le hnN hF.honestRange
    change ir.evalE _ _ L i = ir.evalE _ _ (.leaf z) i
    rw [evalE_leaf_constAll_reader hL e hz hf hp0 hi, hev i,
      evalE_of_needleMatches hwf.refsOrdered hm,
      chainOk_sum (I (ir.domainField d)).decode (fun c hc => hL.decode_natCast _ hf c hc)
        (fun u => castElt (ir.reader e u i)) 1 ts r.digitValues hch,
      map_eq_map_range r.digitValues _ _ fun j hj => hdig.first j hj i hi,
      digitsVal_range_digits, Nat.mod_eq_of_lt hT]
    change ir.evalWith (ir.reader e) d rec i + _ = _
    rw [hn]
    push_cast
    ring
  · cases hq

/-- **The top row of a two-sided lookup holds** at a reader where the record is a natural below `N`
and the digits are its digits. -/
theorem holds_topRowC (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {G : Gens} {e : ir.Env I} {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hF : ir.DigitLookupFactsC G pid d rec N r) (hk : r.kind = .twoSided) {q : PredBody}
    (hq : ir.topMatch d N rec r q = true)
    (hnat : ∀ i < ir.exprLen rec, IsNatBelow N (ir.evalWith (ir.reader e) d rec i))
    (hdig : ir.DigitsRead (ir.reader e) d rec N r) : ir.HoldsWith (ir.reader e) q := by
  have hf := domainField_lt hwf hF.domain
  have hchar := charP_field hI hf
  unfold topMatch at hq
  split at hq
  · rename_i d' L z m
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨⟨hd, hz⟩, hp⟩ := hq
    subst d'
    rcases hpl : peel r.digits L with _ | ⟨h, ts⟩
    · rw [hpl] at hp
      cases hp
    rw [hpl] at hp
    split at hp
    · rename_i top c rec' ts' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨⟨hc, hm⟩, hch⟩, htop⟩, hsz⟩ := hp
      obtain ⟨hev, hlen⟩ := peel_spec (ir.reader e) (ir.domainField d) r.digits L hpl
      have hlenh : ir.exprLen (.add (.leaf top) (.scale (.const c) rec')) = ir.exprLen rec := by
        simp only [exprLen, Expr.len]
        exact hsz
      intro i hi
      rw [hlen, hlenh] at hi
      obtain ⟨hn, hnN⟩ := natCast_toNat_of_isNatBelow hL hf hF.rangeLe (hnat i hi)
      set n := (I (ir.domainField d)).toNat (ir.evalWith (ir.reader e) d rec i) with hndef
      have hN1 : N - 1 < ir.charOf (ir.domainField d) := by
        have := hF.rangeLe
        omega
      have hT : N - 1 - n < r.base ^ r.second.length := by
        rw [hF.second.1 hk]
        have := hF.honestRange
        omega
      have hcK : (c : (I (ir.domainField d)).K) = -1 := by
        rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, hc, CharP.cast_eq_zero]
      change ir.evalE _ _ L i = ir.evalE _ _ (.leaf z) i
      rw [evalE_leaf_constAll_reader hL e hz hf (lt_of_le_of_lt (Nat.zero_le _) hN1) hi, hev i,
        evalE_add, evalE_leaf_constAll_reader hL e htop hf hN1 hi, evalE_scale_const,
        hL.decode_natCast _ hf c (by simp only [charOf] at hc; omega), hcK, evalE_of_needleMatches hwf.refsOrdered hm,
        chainOk_sum (I (ir.domainField d)).decode (fun c hc => hL.decode_natCast _ hf c hc)
          (fun u => castElt (ir.reader e u i)) 1 ts r.second hch,
        map_eq_map_range r.second _ _ fun j hj => hdig.second j hj i hi,
        digitsVal_range_digits, Nat.mod_eq_of_lt hT]
      change _ + -1 * ir.evalWith (ir.reader e) d rec i + _ = _
      rw [← hn, Nat.cast_sub (by omega : n ≤ N - 1)]
      push_cast
      ring
    · cases hp
  · cases hq

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include hwf hI hL R hA in
/-- **A source value reading no challenge and no late value** reads at the source environment of
the honest committed values as in the environment of the execution at the default challenges. -/
theorem reader_srcEnvC_eq_exec0 {w : ℕ}
    (hw : ir.IsSourceValue w) (he : (ir.readsT.getD w []).isEmpty = true) :
    ir.reader SE w = ir.reader (ir.execEnv I x s 0 (ir.chal0 I)) w := by
  rw [(agreeOnSourceVals_srcEnvC hwf hI hL R hA π).reader_eq R.sourceValid R.srcNoMessage hw]
  exact reader_execEnv_congr_of_isEmpty hwf x s l 0 c (ir.chal0 I) he

include hwf hI hL R hA in
/-- **The record of a two-sided or digit lookup reads alike** at the source environment of the
honest committed values and in the environment of the execution at the default challenges. -/
theorem evalWith_rec_srcEnvC {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hF : ir.DigitLookupFactsC G pid d rec N r) :
    ir.evalWith (ir.reader SE) d rec =
      ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d rec :=
  funext fun i => congrFun (evalE_congr fun w hw =>
    reader_srcEnvC_eq_exec0 hwf hI hL R hA π (hF.recReads w hw).1 (hF.recReads w hw).2) i

include hwf hI hL R hA in
/-- **The honest digits of a two-sided or digit lookup are the record's** at the source environment
of the honest committed values. -/
theorem digitsRead_srcEnvC {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r) :
    ir.DigitsRead (ir.reader SE) d rec N r := by
  refine ⟨fun j hj i hi => ?_, fun j hj i hi => ?_⟩
  · obtain ⟨hc, hsz, hf, -⟩ := hF.cells _ (List.mem_append_left _ (List.getElem_mem hj))
    rw [reader_srcEnvL_of_privCellB x _ _ c π hc (by rw [hsz]; exact hi),
      genCommitted_lookupDigit x s hb hF hj, castElt_natCast hf,
      evalWith_rec_srcEnvC hwf hI hL R hA π hF]
  · obtain ⟨hc, hsz, hf, -⟩ := hF.cells _ (List.mem_append_right _ (List.getElem_mem hj))
    rw [reader_srcEnvL_of_privCellB x _ _ c π hc (by rw [hsz]; exact hi),
      genCommitted_lookupSecond x s hb hF hj, castElt_natCast hf,
      evalWith_rec_srcEnvC hwf hI hL R hA π hF]

/-- **A predicate whose body is a lookup is a predicate of the program**: past the predicates the
default predicate is no lookup. -/
theorem lt_of_body_mem {pid d : ℕ} {recs : List Expr} {set : InSet} {real : InRealization}
    (hb : (ir.predicate pid).body = .mem d recs set real) : pid < ir.predicates.length := by
  by_contra h
  simp only [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h),
    Option.getD_none] at hb
  cases hb

include hwf hI hL R hA in
/-- **The record of a two-sided or digit lookup is a natural below `N`** at the source environment
of the honest committed values: the lookup is a source predicate, which holds there
(`sourceSatAt_srcEnvC`). -/
theorem recNat_srcEnvC {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r) :
    ∀ i < ir.exprLen rec, IsNatBelow N (ir.evalWith (ir.reader SE) d rec i) := by
  have hin : ir.HoldsAt SE (ir.predicate pid).body :=
    (sourceSatAt_srcEnvC hwf hI hL R hA π).preds _ (predicate_mem (lt_of_body_mem hb)) hF.source
  rw [hb] at hin
  exact fun i hi => (inRows_range_iff _ d rec i N).1 (hin i hi)

end

end GordieHowe.RealizedProgram
