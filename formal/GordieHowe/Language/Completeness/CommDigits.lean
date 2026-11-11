-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Digits
public import GordieHoweNative.Language.Completeness.Reader
public import GordieHowe.Language.RealizedProgram.Reader

@[expose] public section

/-!
# GordieHowe: completeness certificates, the committed digits of a quotient

A source `mod_q` in the committed-digits form commits its quotient's radix-`R` digits `D_j`, each
the record of a digit lookup `lk` whose digits are generated as committed digits
(`Gen.commDigit m j lk k`): the honest committed value at digit `k` of `lk` is digit `k` in the
lookup's base `T` of digit `j` of the honest quotient read in the environment of the execution
(`genCommitted_commDigit`). The facts of such a lookup (`CommLookupFactsC`, decided by
`commLookupCB`) and of the `mod_q` (`CommModFactsC`, decided by `commModCB`);
the lookups of the quotient digits are named by the field equation's derivation (`commRowCB`).

A quotient digit the planner looks up directly is itself the committed record of a direct lookup,
generated as `Gen.commDigit m j lk 0` (`genCommitted_commDirect`); its facts are `CommDirectFactsC`,
decided by `commDirectCB` (`commRecCB`: either kind).

At the source environment of the honest committed values, the honest quotient lies below `R^K`
and the sides satisfy `e − e' = q·qlo + q·Q` (`commQuot_specC`), each record reads its honest
quotient digit (`commRec_srcEnvC`, `commDirect_srcEnvC`), so the lookup holds (`holds_commInC`),
the field equation holds
(`holds_commRowC`) and the digits of every two-sided and digit lookup are below their bases
(`digitsBelow_srcEnvCC`).

The definitions are in `GordieHoweNative/Language/Completeness/CommDigits.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {S : Structure}
  {L : ℕ → ℕ → Option Ivl}

/-- **A committed-digits lookup passing its check** has one record and a range, its `mod_q` of the
same domain, and its facts. -/
theorem commLookupFactsC_of_B {G : Gens} {lk m j : ℕ} (h : ir.commLookupCB G lk m j = true) :
    ∃ d rec N r q e e' real, (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r) ∧
      (ir.predicate m).body = .mod d q e e' real ∧
        ir.CommLookupFactsC G lk d rec N r m j q e e' real := by
  unfold commLookupCB at h
  split at h
  · rename_i d rec N r d' q e e' real hb hbm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hF⟩ := h
    exact ⟨d', rec, N, r, q, e, e', real, hb, hbm, hF⟩
  · cases h

/-- **A direct lookup passing its check** has one record, a value, and a range, its `mod_q` of the
same domain, and its facts. -/
theorem commDirectFactsC_of_B {G : Gens} {lk m j : ℕ} (h : ir.commDirectCB G lk m j = true) :
    ∃ d v N r q e e' real, (ir.predicate lk).body = .mem d [.leaf v] (.range N) (.lookup r) ∧
      (ir.predicate m).body = .mod d q e e' real ∧ ir.CommDirectFactsC G lk d v N r m j e real := by
  unfold commDirectCB at h
  split at h
  · rename_i d v N r d' q e e' real hb hbm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hF⟩ := h
    exact ⟨d', v, N, r, q, e, e', real, hb, hbm, hF⟩
  · cases h

variable (ir primeNodes S) in
/-- **`PReader.commModCB` at the program and the source values' intervals is `commModCB`.** -/
theorem commModCB_ofProgram (m : ℕ) :
    @PReader.commModCB (ir.srcLeafIvl primeNodes S) ir (PReader.ofProgram ir) m =
      ir.commModCB primeNodes S m := by
  unfold PReader.commModCB commModCB
  simp only [PReader.ofProgram_predicate]
  cases (ir.predicate m).body
  case mod d q e e' real =>
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      PReader.ofProgram_reads]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · intro h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.source, h.form⟩, h.qpos⟩, h.char⟩, h.lhs⟩, h.rhs⟩, h.lo⟩, h.hi⟩,
        h.radixPos⟩, h.noChal⟩
  all_goals rfl

/-- **A `mod_q` passing `commModCB`** has its body and its honest-quotient facts. -/
theorem commModFactsC_of_B {m : ℕ} (h : ir.commModCB primeNodes S m = true) :
    ∃ d q e e' real, (ir.predicate m).body = .mod d q e e' real ∧
      ir.CommModFactsC (ir.srcLeafIvl primeNodes S) m d q e e' real := by
  unfold commModCB at h
  split at h
  · rename_i d q e e' real hb
    exact ⟨d, q, e, e', real, hb, of_decide_eq_true h⟩
  · cases h

/-- **A `mod_q` with its honest-quotient facts is a predicate of the program**: past the
predicates the default predicate is no source predicate. -/
theorem lt_of_commModFactsC {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (_hM : ir.CommModFactsC L m d q e e' real) : m < ir.predicates.length := by
  by_contra h
  simp only [predicate_eq_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h),
    Option.getD_none] at hb
  cases hb

/-- **The honest committed value at a committed digit**: digit `k` in the lookup's base `T` of
digit `j` in the radix `R` of the honest quotient read in the environment of the execution. -/
theorem genCommitted_commDigit {G : Gens} {lk d N m j q : ℕ} {rec e e' : Expr}
    {r : LookupRealization} {real : ModRealization} (x s : ir.Valuation I)
    (hb : (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommLookupFactsC G lk d rec N r m j q e e' real) {k : ℕ}
    (hk : k < r.digitValues.length) (i : ℕ) :
    ir.genCommitted I G x s r.digitValues[k] i =
      ((ir.commQuot (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) m i / real.radix ^ j %
        real.radix / r.base ^ k % r.base : ℕ) : (I (ir.valueField r.digitValues[k])).K) := by
  obtain ⟨-, -, -, hns⟩ := hF.cells _ (List.getElem_mem hk)
  simp only [genCommitted, withGens, if_neg hns, hF.own k hk, commDigitNat, hbm, hb, lookupOf?]

variable (ir primeNodes) in
/-- **`commRowCB` at the program.** -/
theorem commRowCB_eq (S : Structure) (G : Gens) (m : ℕ) (lks : List ℕ) (pr : Predicate) :
    ir.commRowCB primeNodes S G m lks pr =
      match (ir.predicate m).body with
      | .mod d q e e' real =>
        ir.commModCB primeNodes S m && ir.commRowB d q e e' real pr.body &&
          lks.length == real.digits.length &&
          (List.range lks.length).all fun j => ir.commRecCB G (lks.getD j 0) m j
      | _ => false :=
  rfl

/-- **The honest committed value at a directly looked-up quotient digit**: digit `j` in the radix
`R` of the honest quotient read in the environment of the execution (below `R ≤ T`, so its digit
`0` in the lookup's base `T` is itself). -/
theorem genCommitted_commDirect {G : Gens} {lk d v N m j q : ℕ} {e e' : Expr}
    {r : LookupRealization} {real : ModRealization} (x s : ir.Valuation I)
    (hb : (ir.predicate lk).body = .mem d [.leaf v] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommDirectFactsC G lk d v N r m j e real) (hR : 0 < real.radix) (i : ℕ) :
    ir.genCommitted I G x s v i =
      ((ir.commQuot (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) m i / real.radix ^ j %
        real.radix : ℕ) : (I (ir.valueField v)).K) := by
  obtain ⟨-, -, -, hns⟩ := hF.cell
  simp only [genCommitted, withGens, if_neg hns, hF.own, commDigitNat, hbm, hb, lookupOf?,
    pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ hR) hF.radixBase)]

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include hwf hI hL R hA in
/-- **The honest quotient reads alike** in the environment of the execution at the default
challenges and at the source environment of the honest committed values: its sides read source
values that read no challenge and no late value. -/
theorem commQuot_exec0C {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (hM : ir.CommModFactsC L m d q e e' real) (i : ℕ) :
    ir.commQuot (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) m i =
      ir.commQuot (ir.reader SE) m i := by
  have hm := lt_of_commModFactsC hb hM
  have hS : ∀ z, (d, z) ∈ (ir.predicate m).body.exprs → (∀ w ∈ ir.exprNodes z,
      (ir.readsT.getD w []).isEmpty = true) → ∀ w ∈ ir.exprNodes z,
      ir.reader (ir.execEnv I x s 0 (ir.chal0 I)) w = ir.reader SE w := fun z hz hn w hw =>
    (reader_srcEnvC_eq_exec0 hwf hI hL R hA π (R.sourceValid.preds _ (predicate_mem hm) hM.source w
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, z), hz, hw⟩))) (hn w hw)).symm
  unfold commQuot
  rw [hb]
  simp only
  rw [evalIntWith_congr (hS e (by rw [hb]; simp [PredBody.exprs])
      fun w hw => hM.noChal w (List.mem_append_left _ hw)),
    evalIntWith_congr (hS e' (by rw [hb]; simp [PredBody.exprs])
      fun w hw => hM.noChal w (List.mem_append_right _ hw))]

include hwf hI hL R hA in
/-- **The honest quotient of a committed-digits `mod_q` at the source environment** of the honest
committed values where the execution accepts (`CommQuotSpec`): the source `mod_q`
makes `e − e' = q z` over the integers, the sides' intervals from the source values bound them
(`exprIvl_within_of`), so `qlo ≤ z < qlo + R^K`, and the honest quotient is `z − qlo`. -/
theorem commQuot_specC (hbd : ir.StmtBounded I x) {m d q : ℕ} {e e' : Expr}
    {real : ModRealization} (hb : (ir.predicate m).body = .mod d q e e' real)
    (hM : ir.CommModFactsC (ir.srcLeafIvl primeNodes S) m d q e e' real) {i : ℕ}
    (hi : i < ir.exprLen e) :
    ir.CommQuotSpec (ir.reader SE) d q e e' real i (ir.commQuot (ir.reader SE) m i) := by
  have hm := lt_of_commModFactsC hb hM
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges
  have hmod := hsat.preds _ (predicate_mem hm) hM.source
  rw [hb] at hmod
  have hpo := hwf.predicates _ (predicate_mem hm)
  rw [hb] at hpo
  have he := hpo.1 (d, e) (by simp [PredBody.exprs])
  have he' := hpo.1 (d, e') (by simp [PredBody.exprs])
  have hlen : ir.exprLen e = ir.exprLen e' := hpo.2
  obtain ⟨⟨h1, h2⟩, hc⟩ := exprIvl_within_of hwf hI hL hIF hlok he.1 hM.char he.2 hM.lhs hi
  obtain ⟨⟨h3, h4⟩, hc'⟩ := exprIvl_within_of hwf hI hL hIF hlok he'.1 hM.char he'.2 hM.rhs
    (by rw [← hlen]; exact hi)
  simp only at h1 h2 h3 h4 hc hc'
  obtain ⟨z, hz⟩ := hmod i hi
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hM.qpos
  have hlo := hM.lo
  have hhi := hM.hi
  have hzlo : real.quotientLo ≤ z := by
    by_contra hc0
    have : (q : ℤ) * z ≤ q * (real.quotientLo - 1) := mul_le_mul_of_nonneg_left (by omega) hq0.le
    linarith
  have hzhi : z < real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ) := by
    by_contra hc0
    have : (q : ℤ) * (real.quotientLo + ((real.radix ^ real.digits.length : ℕ) : ℤ)) ≤ q * z :=
      mul_le_mul_of_nonneg_left (by omega) hq0.le
    linarith
  have hQ : ir.commQuot (ir.reader SE) m i = (z - real.quotientLo).toNat := by
    unfold commQuot
    rw [hb]
    simp only
    rw [hz, Int.mul_ediv_cancel_left _ (by omega)]
  have hzz : (((z - real.quotientLo).toNat : ℕ) : ℤ) = z - real.quotientLo :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨?_, ?_⟩
  · rw [hQ]
    omega
  · rw [← hc, ← hc', hQ, ← Int.cast_natCast (R := (I (ir.domainField d)).K), ← Int.cast_sub,
      ← Int.cast_add]
    congr 1
    push_cast
    rw [hzz]
    linear_combination hz

include hwf hI hL R hA in
/-- **A committed-digits lookup's record reads its honest quotient digit** at the source
environment of the honest committed values: the record is the number of its
digits (`digitsExprOk`), each digit `k` in base `T` of the quotient digit
(`genCommitted_commDigit`), which lies below `R ≤ T^k`. -/
theorem commRec_srcEnvC {lk d N m j q : ℕ} {rec e e' : Expr}
    {r : LookupRealization} {real : ModRealization}
    (hb : (ir.predicate lk).body = .mem d [rec] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommLookupFactsC G lk d rec N r m j q e e' real)
    (hM : ir.CommModFactsC L m d q e e' real) {i : ℕ} (hi : i < ir.exprLen rec) :
    ir.evalWith (ir.reader SE) d rec i =
      ((ir.commQuot (ir.reader SE) m i / real.radix ^ j % real.radix : ℕ) :
        (I (ir.domainField d)).K) := by
  have hf := domainField_lt hwf hF.domain
  have hlt : ir.commQuot (ir.reader SE) m i / real.radix ^ j % real.radix <
      r.base ^ r.digitValues.length := by
    rw [hF.len]
    exact lt_of_lt_of_le (Nat.mod_lt _ hM.radixPos) hF.radixDigits
  unfold evalWith
  rw [← evalE_unref hwf, evalE_of_digitsExprOk_digits hL hf hF.expr (n := ir.commQuot
      (ir.reader SE) m i / real.radix ^ j % real.radix) fun k hk => ?_,
    Nat.mod_eq_of_lt hlt]
  obtain ⟨hc, hsz, hfu, -⟩ := hF.cells _ (List.getElem_mem hk)
  rw [reader_srcEnvL_of_privCellB x _ _ c π hc (by rw [hsz]; exact hi),
    genCommitted_commDigit x s hb hbm hF hk, castElt_natCast hfu,
    commQuot_exec0C hwf hI hL R hA π hbm hM]

include hwf hI hL R hA in
/-- **A directly looked-up quotient digit reads its honest value** at the source environment of the
honest committed values: the record is a committed cell generated as digit `j` of the honest
quotient (`genCommitted_commDirect`). -/
theorem commDirect_srcEnvC {lk d v N m j q : ℕ} {e e' : Expr}
    {r : LookupRealization} {real : ModRealization}
    (hb : (ir.predicate lk).body = .mem d [.leaf v] (.range N) (.lookup r))
    (hbm : (ir.predicate m).body = .mod d q e e' real)
    (hF : ir.CommDirectFactsC G lk d v N r m j e real)
    (hM : ir.CommModFactsC L m d q e e' real) {i : ℕ} (hi : i < ir.exprLen e) :
    ir.evalWith (ir.reader SE) d (.leaf v) i =
      ((ir.commQuot (ir.reader SE) m i / real.radix ^ j % real.radix : ℕ) :
        (I (ir.domainField d)).K) := by
  obtain ⟨hc, hsz, hfu, -⟩ := hF.cell
  unfold evalWith
  rw [evalE_leaf, reader_srcEnvL_of_privCellB x _ _ c π hc (by rw [hsz]; exact hi),
    genCommitted_commDirect x s hb hbm hF hM.radixPos, castElt_natCast hfu,
    commQuot_exec0C hwf hI hL R hA π hbm hM]

include hwf hI hL R hA in
/-- **A digit or direct lookup whose record is a quotient digit holds** at the source environment
of the honest committed values: the record reads its honest quotient digit (`commRec_srcEnvC`,
`commDirect_srcEnvC`), below `R ≤ N`. -/
theorem holds_commInC {lk m j : ℕ} (h : ir.commRecCB G lk m j = true)
    (hm : ir.commModCB primeNodes S m = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate lk).body := by
  obtain ⟨d₁, q₁, e₁, e₁', real₁, hbm₁, hM⟩ := commModFactsC_of_B hm
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨d, rec, N, r, q, e, e', real, hb, hbm, hF⟩ := commLookupFactsC_of_B h
    rw [hbm] at hbm₁
    simp only [PredBody.mod.injEq] at hbm₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₁
    rw [hb]
    intro i hi
    simp only [List.headD_cons] at hi
    exact (inRows_range_iff _ d rec i N).2
      ⟨_, lt_of_lt_of_le (Nat.mod_lt _ hM.radixPos) hF.radixLe,
        (commRec_srcEnvC hwf hI hL R hA π hb hbm hF hM hi).symm⟩
  · obtain ⟨d, v, N, r, q, e, e', real, hb, hbm, hF⟩ := commDirectFactsC_of_B h
    rw [hbm] at hbm₁
    simp only [PredBody.mod.injEq] at hbm₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₁
    rw [hb]
    intro i hi
    simp only [List.headD_cons, exprLen_leaf] at hi
    exact (inRows_range_iff _ d (.leaf v) i N).2
      ⟨_, lt_of_lt_of_le (Nat.mod_lt _ hM.radixPos) hF.radixLe,
        (commDirect_srcEnvC hwf hI hL R hA π hb hbm hF hM
          (by rw [← hF.cell.2.1]; exact hi)).symm⟩

include hwf hI hL R hA in
/-- **The field equation of a committed-digits `mod_q` holds** at the source environment of the
honest committed values where the execution accepts: the row reads
`e − e' − q·qlo − q·Σ_j R^j D_j` (`evalE_of_commPeel`, `commShift_spec`, `sum_zipIdx_mul`), each
quotient digit `D_j` is the record of the lookup `lks[j]` and reads digit `j` of the honest
quotient `Q` (`commRec_srcEnvC`), so `Σ_j R^j D_j = Q` below `R^K`, and `e − e' = q·qlo + q·Q`
(`commQuot_specC`). -/
theorem holds_commRowC (hbd : ir.StmtBounded I x) {m : ℕ} {lks : List ℕ} {pr : Predicate}
    (h : ir.commRowCB primeNodes S G m lks pr = true) : ir.HoldsWith (ir.reader SE) pr.body := by
  set rd := ir.reader SE with hrd
  rw [commRowCB_eq] at h
  split at h
  · rename_i d q e e' real hbm
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨hmB, hrow⟩, hlks⟩, hlk⟩ := h
    obtain ⟨d₁, q₁, e₁, e₁', real₁, hbm₁, hM⟩ := commModFactsC_of_B hmB
    rw [hbm] at hbm₁
    simp only [PredBody.mod.injEq] at hbm₁
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₁
    have hm := lt_of_commModFactsC hbm hM
    have hpo := hwf.predicates _ (predicate_mem hm)
    rw [hbm] at hpo
    have hd : d < ir.domains.length := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
    have hf := domainField_lt hwf hd
    obtain ⟨-, hchar, -, hdec0⟩ := modData hwf hI hL hd hM.char
    have hdec : ∀ c' < ir.charOf (ir.domainField d),
        (I (ir.domainField d)).decode c' = (c' : (I (ir.domainField d)).K) := hdec0
    have hp0 : 0 < ir.charOf (ir.domainField d) := by have := hM.char; omega
    obtain ⟨hshl, hshc⟩ := commShift_spec (K := (I (ir.domainField d)).K) hp0 q real
    unfold commRowB at hrow
    split at hrow
    · rename_i d' L z t hbody
      simp only [Bool.and_eq_true, beq_iff_eq] at hrow
      obtain ⟨⟨hd', hz⟩, hmt⟩ := hrow
      subst d'
      split at hmt
      · rename_i hh hpeel
        obtain ⟨hev, hlenL⟩ := evalE_of_commPeel rd hdec _ L hpeel
        obtain ⟨hhe, hhl⟩ := evalE_of_commHeadB rd (d := d) hdec
          (fun _ hc _ hi' => evalE_leaf_constAll_reader hL SE hc hf hshl hi') hmt
        rw [hbody]
        intro i hi
        rw [hlenL, hhl] at hi
        have hQ := commQuot_specC hwf hI hL R hA π hbd hbm hM hi
        have hdig : ∀ j (hj : j < real.digits.length),
            ir.evalE rd (ir.domainField d) real.digits[j] i =
              ((ir.commQuot rd m i / real.radix ^ j % real.radix : ℕ) :
                (I (ir.domainField d)).K) := by
          intro j hj
          rcases Bool.or_eq_true_iff.1 (hlk j (by rw [hlks]; exact hj)) with hj' | hj'
          · obtain ⟨d₂, rec, N, r, q₂, e₂, e₂', real₂, hb₂, hbm₂, hF⟩ := commLookupFactsC_of_B hj'
            rw [hbm] at hbm₂
            simp only [PredBody.mod.injEq] at hbm₂
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₂
            have hD : real.digits[j] = rec := by
              have h0 := hF.isDigit
              rw [List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at h0
              exact Expr.eq_of_beq h0
            rw [hD]
            exact commRec_srcEnvC hwf hI hL R hA π hb₂ hbm hF hM (by rw [hF.recLen]; exact hi)
          · obtain ⟨d₂, v, N, r, q₂, e₂, e₂', real₂, hb₂, hbm₂, hF⟩ := commDirectFactsC_of_B hj'
            rw [hbm] at hbm₂
            simp only [PredBody.mod.injEq] at hbm₂
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbm₂
            have hD : real.digits[j] = .leaf v := by
              have h0 := hF.isDigit
              rw [List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at h0
              exact Expr.eq_of_beq h0
            rw [hD]
            exact commDirect_srcEnvC hwf hI hL R hA π hb₂ hbm hF hM hi
        have hsum : digitsVal (real.radix : (I (ir.domainField d)).K)
            (real.digits.map fun D => ir.evalE rd (ir.domainField d) D i) =
              ((ir.commQuot rd m i : ℕ) : (I (ir.domainField d)).K) := by
          rw [map_eq_map_range real.digits _ _ hdig, digitsVal_range_digits,
            Nat.mod_eq_of_lt hQ.lt]
        have hsides := hQ.sides
        simp only [evalWith] at hsides ⊢
        rw [hev i, hhe i hi,
          evalE_leaf_constAll_reader hL _ hz hf hp0 hi,
          hshc, List.map_reverse, List.sum_reverse,
          sum_zipIdx_mul q real.radix (fun D => ir.evalE rd (ir.domainField d) D i) real.digits 0,
          hsum]
        push_cast at hsides ⊢
        linear_combination hsides
      · cases hmt
    · cases hrow
  · cases h

include hwf hI hL R hA in
/-- **The digits of the two-sided and digit lookups are below their bases** at the source
environment of the honest committed values, where every such lookup has its facts, its digits
generated as its digits (`DigitLookupFactsC`) or as the committed digits of a quotient
(`commLookupCB`). -/
theorem digitsBelow_srcEnvCC
    (hD : ∀ pid < ir.predicates.length, ∀ d rec N r,
      (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) →
        (r.kind = .twoSided ∨ r.kind = .digits) →
          ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true)
    (hshape : ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
      (r.kind = .twoSided ∨ r.kind = .digits) →
        ∃ d rec N, (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r)) :
    DigitsBelow (ir.reader SE) := by
  intro pid hpid r hr hk u hu i hi
  obtain ⟨d, rec, N, hb⟩ := hshape pid hpid r hr hk
  rcases hD pid hpid d rec N r hb hk with hF | ⟨m, j, hc⟩
  · have hdig := digitsRead_srcEnvC hwf hI hL R hA π hb hF
    obtain ⟨hc, hsz, hf, -⟩ := hF.cells u hu
    rw [reader_srcEnvL_of_privCellB x _ _ c π hc hi]
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [genCommitted_lookupDigit x s hb hF hj]
      exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [genCommitted_lookupSecond x s hb hF hj]
      exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩
  · obtain ⟨d', rec', N', r', q, e, e', real, hb', hbm, hF⟩ := commLookupFactsC_of_B hc
    rw [hb] at hb'
    simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq,
      InRealization.lookup.injEq] at hb'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
    rw [hF.second, List.append_nil] at hu
    have hcell := (hF.cells u hu).1
    rw [reader_srcEnvL_of_privCellB x _ _ c π hcell hi]
    obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
    rw [genCommitted_commDigit x s hb hbm hF hk']
    exact ⟨_, Nat.mod_lt _ (by have := hF.baseGt; omega), rfl⟩

/-- **A committed-digits lookup's digits are committed cells**, from either form of a lookup's
facts. -/
theorem privCellB_of_lookupFactsC {pid d N : ℕ} {rec : Expr} {r : LookupRealization}
    (hb : (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r))
    (hF : ir.DigitLookupFactsC G pid d rec N r ∨ ∃ m j, ir.commLookupCB G pid m j = true)
    {u : ℕ} (hu : u ∈ r.digitValues ++ r.second) : ir.privCellB u = true := by
  rcases hF with hF | ⟨m, j, hc⟩
  · exact (hF.cells u hu).1
  · obtain ⟨d', rec', N', r', q, e, e', real, hb', -, hF⟩ := commLookupFactsC_of_B hc
    rw [hb] at hb'
    simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq,
      InRealization.lookup.injEq] at hb'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
    rw [hF.second, List.append_nil] at hu
    exact (hF.cells u hu).1

end

end GordieHowe.RealizedProgram
