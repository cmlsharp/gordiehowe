-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Committed
public import GordieHowe.Language.Honest.Exec

@[expose] public section

/-!
# GordieHowe: completeness certificates, the execution of the source program

The facts an application's execution of its source program (`RealizedProgram.SourceExecution`)
reads, at the committed facts of a completeness certificate (`CommittedFacts`, with the values
bound to their digits reading no pad copy, `BoundNoCopy`): a value bound to its digits lies in its subfield type where the source program holds
(`inTypeC_bound_of_sat`), so the source program accepts where it holds
(`sourceAcceptingAtC_of_sat`);
a source environment and the execution read off its committed values agree on the source values
(`agreeOnSourceValsC_srcEnv_execOf`), so the execution accepts (`sourceAcceptingAtC_of_srcEnv`) and
its field-form `mod_q`s hold as their field equations (`fieldEqsAtC_of_srcEnv`) where the source
environment does.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **A value bound to its digits lies in its subfield type** where the source program holds and
the node's subgroup contains `1`: its record `v` or `v + c` is a natural below its lookup's range
(the lookup's `in`, a source predicate), so `v` is the cast of an integer. -/
theorem inTypeC_bound_of_sat (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes)
    {G : Gens} (hB : ir.BoundRecs) (hD : ir.DigitLookupsC G) {e : ir.Env I}
    (hsat : ir.SourceSatAt e) {v : ℕ} (hv : v < ir.values.length)
    (hb : (ir.value v).kind.isBound = true) {E : String} (ht : (ir.value v).type = .sub E)
    (h1 : (1 : (I (ir.valueField v)).K) ∈ (I (ir.valueField v)).node E) {i : ℕ}
    (hi : i < (ir.value v).size) :
    (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i) := by
  obtain ⟨-, hBv⟩ := hB v hv hb
  obtain ⟨pid, hpid, d, rec, N, r, hbody, hk, hnc, hbd, hrec⟩ := exists_of_boundRecB hBv
  have hF := hD pid hpid d rec N r hbody hk (by rw [hnc]; rfl)
  have hint : ∀ z : ℤ, ((z : ℤ) : (I (ir.valueField v)).K) ∈ (I (ir.valueField v)).node E :=
    fun z => by simpa using AddSubgroup.zsmul_mem _ h1 z
  have hin := hsat.preds _ (predicate_mem hpid) hF.source
  rw [hbody] at hin
  rw [ht]
  change ir.reader e v i ∈ (I (ir.valueField v)).node E
  have hvf : ir.valueField v = ir.domainField d := by
    rcases hrec with rfl | ⟨c, es, rfl, -, -, -⟩ <;> unfold boundDigitsOk at hbd <;>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd <;> exact hbd.1.2
  rcases hrec with rfl | ⟨c, es, rfl, hkc, hes, hlt⟩
  · obtain ⟨n, -, hn⟩ := (inRows_range_iff _ d (.leaf v) i N).1 (hin i hi)
    simp only [evalWith, evalE_leaf] at hn
    rw [← castElt_castElt_of_eq hvf (ir.reader e v i), ← hn, castElt_natCast hvf.symm]
    simpa using hint n
  · have hcl : c < ir.values.length := by
      by_contra hcl
      rw [value_eq_default (Nat.le_of_not_lt hcl)] at hkc
      cases hkc
    obtain ⟨n, -, hn⟩ := (inRows_range_iff _ d (.add (.leaf v) (.leaf c)) i N).1 (hin i hi)
    simp only [evalWith, evalE_add, evalE_leaf] at hn
    have hck : ir.reader e c i = ((es.getD i 0 : ℕ) : (I (ir.valueField c)).K) := by
      rw [reader_of_constant e hkc i, hL.decode_natCast _ (valueField_lt hwf hcl) _ ?_]
      rw [List.getD_eq_getElem?_getD]
      cases h : es[i]? with
      | none =>
        simp only [Option.getD_none]
        have := charP_field hI (valueField_lt hwf hcl)
        exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.valueField c)).K _)
      | some k => exact hlt k (List.mem_of_getElem? h)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, (castElt (ir.reader e c i) : (I (ir.domainField d)).K) =
        ((z : ℤ) : (I (ir.domainField d)).K) := by
      by_cases hcf : ir.valueField c = ir.domainField d
      · exact ⟨(es.getD i 0 : ℕ), by rw [hck, castElt_natCast hcf, Int.cast_natCast]⟩
      · exact ⟨0, by rw [castElt_of_ne hcf]; simp⟩
    have hv' : (castElt (ir.reader e v i) : (I (ir.domainField d)).K) =
        (((n : ℤ) - z : ℤ) : (I (ir.domainField d)).K) := by
      push_cast
      rw [hn, hz]
      ring
    have h1d : (1 : (I (ir.domainField d)).K) ∈ (I (ir.domainField d)).node E := by
      have h := castElt_mem_node hvf h1
      rwa [castElt_one_of_eq hvf] at h
    have hw : ((((n : ℤ) - z : ℤ)) : (I (ir.domainField d)).K) ∈ (I (ir.domainField d)).node E := by
      simpa using AddSubgroup.zsmul_mem _ h1d ((n : ℤ) - z)
    rw [← castElt_castElt_of_eq hvf (ir.reader e v i)]
    exact castElt_mem_node hvf.symm (hv' ▸ hw)

/-- **The source program accepts where it holds**, every `kpriv` source value whose type no node
states is of type `Field`, has a Boolean check (`boolCheckB`) or is bound to its digits with a
subfield type whose node's subgroup contains `1` (`hone`), and every source cross-field `equal`
reads bits. -/
theorem sourceAcceptingAtC_of_sat (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes)
    {G : Gens} (hB : ir.BoundRecs) (hD : ir.DigitLookupsC G) {e : ir.Env I}
    (hsat : ir.SourceSatAt e) (hk : ir.KprivTyped) (hone : ir.BoundOneMem I)
    (hcb : ir.CrossBitsAt I e) :
    ir.SourceAcceptingAt I e where
  sat := hsat
  crossBits := hcb
  types v hv hsrc hkp i hi := by
    by_cases hts : (ir.value v).typeSource = .node
    · exact hsat.types v hv hsrc hts i hi
    rcases hk v hv hsrc hkp hts with ht | hb | ⟨hbd, hnb⟩
    · rw [ht]
      trivial
    swap
    · rcases hty : (ir.value v).type with _ | E | _
      · exact absurd hty hnb
      · have h := inTypeC_bound_of_sat hwf hI hL hB hD hsat hv hbd hty (hone v hv hbd E hty) hi
        rwa [hty] at h
      · trivial
    unfold boolCheckB at hb
    split at hb
    · rename_i q hq
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      obtain ⟨⟨⟨hql, hty⟩, hsq⟩, hb⟩ := hb
      split at hb
      · rename_i d a b c' m hbody
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
        obtain ⟨⟨⟨ha, hb2⟩, hc2⟩, hf⟩ := hb
        rw [ha, hb2, hc2] at hbody
        have hh := hsat.preds _ (predicate_mem hql) hsq
        rw [hbody] at hh
        have hhi := hh i (by simp only [exprLen, Expr.len]; exact hi)
        simp only [evalWith, evalE, Expr.eval] at hhi
        rw [hty]
        have hx : (castElt (ir.reader e v i) : (I (ir.domainField d)).K) = 0 ∨
            (castElt (ir.reader e v i) : (I (ir.domainField d)).K) = 1 :=
          eq_zero_or_one_of_mul_self hhi
        revert hx
        generalize ir.reader e v i = z
        revert z
        rw [hf]
        intro z hx
        simpa [FieldInterp.InType] using hx
      · cases hb
    · cases hb

/-- **A source environment and the execution read off its committed values agree on the source
values** (`agreeOnSourceVals_srcEnv_of`): the execution's phase-`0` values are `V` read off by
`execOf` (a value bound to its digits as their number), and a bound value reads its digits' number
below its size and `0` past it. -/
theorem agreeOnSourceValsC_srcEnv_execOf (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {G : Gens} (R : ir.CommittedFacts I G) (hbc : ir.BoundNoCopy)
    (x V l : ir.Valuation I)
    (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) :
    Env.AgreeOnSourceVals (ir.srcEnvL I x V l c π) (ir.execEnv I x (ir.execOf I V) l c) :=
  agreeOnSourceVals_srcEnv_of (s := ir.execOf I V) (l := l) c π (fun _ _ _ _ _ => rfl)
    R.srcNoPadCopy (fun u _ hb => by
      funext i
      obtain ⟨e, he⟩ : ∃ e, (ir.value u).kind = .bound e := by
        revert hb
        cases (ir.value u).kind <;> simp [Kind.isBound]
      split_ifs with hi
      · simp only [execOf, hb, ite_true]
        exact congrFun (bindAsg_bound_pads hbc V π 0 he) i
      · exact bindAsgC_bound_zero_past hwf hI hL R.boundRecs R.digitLookups V π (lt_of_isBound hb)
          hb (by omega))
    fun u _ hb => by
      funext i
      simp only [execOf, hb, Bool.false_eq_true, ite_false]

/-- **The execution accepts where the source program holds at a source environment**: at honest
committed values `V`, where the source program holds and its cross-field `equal`s read bits, every
`kpriv` source value whose type no node states having a checked type (`KprivTyped`), the execution
of the phase-`0` values read off `V` (`execOf`) accepts. -/
theorem sourceAcceptingAtC_of_srcEnv (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {G : Gens} (R : ir.CommittedFacts I G) (hbc : ir.BoundNoCopy)
    {x V l : ir.Valuation I}
    {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads}
    (hk : ir.KprivTyped) (hone : ir.BoundOneMem I)
    (hsat : ir.SourceSatAt (ir.srcEnvL I x V l c π))
    (hcb : ir.CrossBitsAt I (ir.srcEnvL I x V l c π)) :
    ir.SourceAcceptingAt I (ir.execEnv I x (ir.execOf I V) l c) :=
  have h := agreeOnSourceValsC_srcEnv_execOf hwf hI hL R hbc x V l c π
  sourceAcceptingAtC_of_sat hwf hI hL R.boundRecs R.digitLookups
    ((h.sourceSatAt_congr R.sourceValid R.srcNoMessage).1 hsat) hk hone
    (h.crossBitsAt R.sourceValid R.srcNoMessage hcb)

/-- **The execution's field-form `mod_q`s hold as their field equations where their rows hold at a
source environment** (`fieldEqsAt_of_rows`). -/
theorem fieldEqsAtC_of_srcEnv (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {G : Gens} (R : ir.CommittedFacts I G) (hbc : ir.BoundNoCopy)
    (hB : ir.fieldRowsB = true)
    {x V l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads}
    (hH : ∀ r < ir.predicates.length, ir.fieldRowRealB r = true →
      ir.HoldsAt (ir.srcEnvL I x V l c π) (ir.predicate r).body) :
    ir.FieldEqsAt I (ir.execEnv I x (ir.execOf I V) l c) :=
  (agreeOnSourceValsC_srcEnv_execOf hwf hI hL R hbc x V l c π).fieldEqsAt R.sourceValid
    R.srcNoMessage
    (fieldEqsAt_of_rows hwf hI hL hB hH)


end

end GordieHowe.RealizedProgram
